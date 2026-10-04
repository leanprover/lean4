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
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_41_ = lean_unsigned_to_nat(0u);
v___x_42_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v___x_41_);
lean_ctor_set(v___x_42_, 2, v___x_41_);
lean_ctor_set(v___x_42_, 3, v___x_41_);
lean_ctor_set(v___x_42_, 4, v___x_40_);
lean_ctor_set(v___x_42_, 5, v___x_40_);
lean_ctor_set(v___x_42_, 6, v___x_40_);
lean_ctor_set(v___x_42_, 7, v___x_40_);
lean_ctor_set(v___x_42_, 8, v___x_40_);
lean_ctor_set(v___x_42_, 9, v___x_40_);
lean_ctor_set(v___x_42_, 10, v___x_40_);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_unsigned_to_nat(32u);
v___x_44_ = lean_mk_empty_array_with_capacity(v___x_43_);
v___x_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4(void){
_start:
{
size_t v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_46_ = ((size_t)5ULL);
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = lean_unsigned_to_nat(32u);
v___x_49_ = lean_mk_empty_array_with_capacity(v___x_48_);
v___x_50_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3);
v___x_51_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v___x_49_);
lean_ctor_set(v___x_51_, 2, v___x_47_);
lean_ctor_set(v___x_51_, 3, v___x_47_);
lean_ctor_set_usize(v___x_51_, 4, v___x_46_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = lean_box(1);
v___x_53_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4);
v___x_54_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_55_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
lean_ctor_set(v___x_55_, 2, v___x_52_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_56_, lean_object* v___y_57_){
_start:
{
lean_object* v___x_59_; lean_object* v_env_60_; uint8_t v___x_61_; lean_object* v_env_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v_scopes_65_; lean_object* v___x_66_; lean_object* v_opts_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_59_ = lean_st_ref_get(v___y_57_);
v_env_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc_ref(v_env_60_);
lean_dec(v___x_59_);
v___x_61_ = 0;
v_env_62_ = l_Lean_Environment_setRecordingDeps(v_env_60_, v___x_61_);
v___x_63_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_64_ = lean_st_ref_get(v___y_57_);
v_scopes_65_ = lean_ctor_get(v___x_64_, 2);
lean_inc(v_scopes_65_);
lean_dec(v___x_64_);
v___x_66_ = l_List_head_x21___redArg(v___x_63_, v_scopes_65_);
lean_dec(v_scopes_65_);
v_opts_67_ = lean_ctor_get(v___x_66_, 1);
lean_inc_ref(v_opts_67_);
lean_dec(v___x_66_);
v___x_68_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_69_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5);
v___x_70_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_70_, 0, v_env_62_);
lean_ctor_set(v___x_70_, 1, v___x_68_);
lean_ctor_set(v___x_70_, 2, v___x_69_);
lean_ctor_set(v___x_70_, 3, v_opts_67_);
v___x_71_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v_msgData_56_);
v___x_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msgData_73_, v___y_74_);
lean_dec(v___y_74_);
return v_res_76_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_box(1);
v___x_78_ = l_Lean_MessageData_ofFormat(v___x_77_);
return v___x_78_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__2));
v___x_83_ = l_Lean_MessageData_ofFormat(v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8(lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
return v_x_84_;
}
else
{
lean_object* v_head_86_; lean_object* v_tail_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_109_; 
v_head_86_ = lean_ctor_get(v_x_85_, 0);
v_tail_87_ = lean_ctor_get(v_x_85_, 1);
v_isSharedCheck_109_ = !lean_is_exclusive(v_x_85_);
if (v_isSharedCheck_109_ == 0)
{
v___x_89_ = v_x_85_;
v_isShared_90_ = v_isSharedCheck_109_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_tail_87_);
lean_inc(v_head_86_);
lean_dec(v_x_85_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_109_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v_before_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_107_; 
v_before_91_ = lean_ctor_get(v_head_86_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v_head_86_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; 
v_unused_108_ = lean_ctor_get(v_head_86_, 1);
lean_dec(v_unused_108_);
v___x_93_ = v_head_86_;
v_isShared_94_ = v_isSharedCheck_107_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_before_91_);
lean_dec(v_head_86_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_107_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_95_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0);
if (v_isShared_94_ == 0)
{
lean_ctor_set_tag(v___x_93_, 7);
lean_ctor_set(v___x_93_, 1, v___x_95_);
lean_ctor_set(v___x_93_, 0, v_x_84_);
v___x_97_ = v___x_93_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_x_84_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v___x_95_);
v___x_97_ = v_reuseFailAlloc_106_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_98_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3);
if (v_isShared_90_ == 0)
{
lean_ctor_set_tag(v___x_89_, 7);
lean_ctor_set(v___x_89_, 1, v___x_98_);
lean_ctor_set(v___x_89_, 0, v___x_97_);
v___x_100_ = v___x_89_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_97_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v___x_98_);
v___x_100_ = v_reuseFailAlloc_105_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = l_Lean_MessageData_ofSyntax(v_before_91_);
v___x_102_ = l_Lean_indentD(v___x_101_);
v___x_103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_100_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v_x_84_ = v___x_103_;
v_x_85_ = v_tail_87_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(lean_object* v_opts_110_, lean_object* v_opt_111_){
_start:
{
lean_object* v_name_112_; lean_object* v_defValue_113_; lean_object* v_map_114_; lean_object* v___x_115_; 
v_name_112_ = lean_ctor_get(v_opt_111_, 0);
v_defValue_113_ = lean_ctor_get(v_opt_111_, 1);
v_map_114_ = lean_ctor_get(v_opts_110_, 0);
v___x_115_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_114_, v_name_112_);
if (lean_obj_tag(v___x_115_) == 0)
{
uint8_t v___x_116_; 
v___x_116_ = lean_unbox(v_defValue_113_);
return v___x_116_;
}
else
{
lean_object* v_val_117_; 
v_val_117_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_val_117_);
lean_dec_ref_known(v___x_115_, 1);
if (lean_obj_tag(v_val_117_) == 1)
{
uint8_t v_v_118_; 
v_v_118_ = lean_ctor_get_uint8(v_val_117_, 0);
lean_dec_ref_known(v_val_117_, 0);
return v_v_118_;
}
else
{
uint8_t v___x_119_; 
lean_dec(v_val_117_);
v___x_119_ = lean_unbox(v_defValue_113_);
return v___x_119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_opts_120_, lean_object* v_opt_121_){
_start:
{
uint8_t v_res_122_; lean_object* v_r_123_; 
v_res_122_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(v_opts_120_, v_opt_121_);
lean_dec_ref(v_opt_121_);
lean_dec_ref(v_opts_120_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__1));
v___x_128_ = l_Lean_MessageData_ofFormat(v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(lean_object* v_msgData_129_, lean_object* v_macroStack_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v_scopes_135_; lean_object* v___x_136_; lean_object* v_opts_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_133_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_134_ = lean_st_ref_get(v___y_131_);
v_scopes_135_ = lean_ctor_get(v___x_134_, 2);
lean_inc(v_scopes_135_);
lean_dec(v___x_134_);
v___x_136_ = l_List_head_x21___redArg(v___x_133_, v_scopes_135_);
lean_dec(v_scopes_135_);
v_opts_137_ = lean_ctor_get(v___x_136_, 1);
lean_inc_ref(v_opts_137_);
lean_dec(v___x_136_);
v___x_138_ = l_Lean_Elab_pp_macroStack;
v___x_139_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(v_opts_137_, v___x_138_);
lean_dec_ref(v_opts_137_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
lean_dec(v_macroStack_130_);
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v_msgData_129_);
return v___x_140_;
}
else
{
if (lean_obj_tag(v_macroStack_130_) == 0)
{
lean_object* v___x_141_; 
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v_msgData_129_);
return v___x_141_;
}
else
{
lean_object* v_head_142_; lean_object* v_after_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_158_; 
v_head_142_ = lean_ctor_get(v_macroStack_130_, 0);
lean_inc(v_head_142_);
v_after_143_ = lean_ctor_get(v_head_142_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v_head_142_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; 
v_unused_159_ = lean_ctor_get(v_head_142_, 0);
lean_dec(v_unused_159_);
v___x_145_ = v_head_142_;
v_isShared_146_ = v_isSharedCheck_158_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_after_143_);
lean_dec(v_head_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_158_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_147_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0);
if (v_isShared_146_ == 0)
{
lean_ctor_set_tag(v___x_145_, 7);
lean_ctor_set(v___x_145_, 1, v___x_147_);
lean_ctor_set(v___x_145_, 0, v_msgData_129_);
v___x_149_ = v___x_145_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_msgData_129_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v___x_147_);
v___x_149_ = v_reuseFailAlloc_157_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_msgData_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_150_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2);
v___x_151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = l_Lean_MessageData_ofSyntax(v_after_143_);
v___x_153_ = l_Lean_indentD(v___x_152_);
v_msgData_154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_154_, 0, v___x_151_);
lean_ctor_set(v_msgData_154_, 1, v___x_153_);
v___x_155_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8(v_msgData_154_, v_macroStack_130_);
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_msgData_160_, lean_object* v_macroStack_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_msgData_160_, v_macroStack_161_, v___y_162_);
lean_dec(v___y_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(lean_object* v_msg_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Elab_Command_getRef___redArg(v___y_166_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v_macroStack_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v_a_174_; lean_object* v___x_175_; lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_184_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_a_170_);
lean_dec_ref_known(v___x_169_, 1);
v_macroStack_171_ = lean_ctor_get(v___y_166_, 4);
v___x_172_ = l_Lean_Elab_getBetterRef(v_a_170_, v_macroStack_171_);
lean_dec(v_a_170_);
v___x_173_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msg_165_, v___y_167_);
v_a_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_174_);
lean_dec_ref(v___x_173_);
lean_inc(v_macroStack_171_);
v___x_175_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_a_174_, v_macroStack_171_, v___y_167_);
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_184_ == 0)
{
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_184_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_184_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_172_);
lean_ctor_set(v___x_180_, 1, v_a_176_);
if (v_isShared_179_ == 0)
{
lean_ctor_set_tag(v___x_178_, 1);
lean_ctor_set(v___x_178_, 0, v___x_180_);
v___x_182_ = v___x_178_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec_ref(v_msg_165_);
v_a_185_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_169_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_169_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg___boxed(lean_object* v_msg_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(lean_object* v_ref_198_, lean_object* v_msg_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Elab_Command_getRef___redArg(v___y_200_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v_a_204_; lean_object* v_fileName_205_; lean_object* v_fileMap_206_; lean_object* v_currRecDepth_207_; lean_object* v_cmdPos_208_; lean_object* v_macroStack_209_; lean_object* v_quotContext_x3f_210_; lean_object* v_currMacroScope_211_; lean_object* v_snap_x3f_212_; lean_object* v_cancelTk_x3f_213_; uint8_t v_suppressElabErrors_214_; lean_object* v_ref_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_a_204_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_a_204_);
lean_dec_ref_known(v___x_203_, 1);
v_fileName_205_ = lean_ctor_get(v___y_200_, 0);
v_fileMap_206_ = lean_ctor_get(v___y_200_, 1);
v_currRecDepth_207_ = lean_ctor_get(v___y_200_, 2);
v_cmdPos_208_ = lean_ctor_get(v___y_200_, 3);
v_macroStack_209_ = lean_ctor_get(v___y_200_, 4);
v_quotContext_x3f_210_ = lean_ctor_get(v___y_200_, 5);
v_currMacroScope_211_ = lean_ctor_get(v___y_200_, 6);
v_snap_x3f_212_ = lean_ctor_get(v___y_200_, 8);
v_cancelTk_x3f_213_ = lean_ctor_get(v___y_200_, 9);
v_suppressElabErrors_214_ = lean_ctor_get_uint8(v___y_200_, sizeof(void*)*10);
v_ref_215_ = l_Lean_replaceRef(v_ref_198_, v_a_204_);
lean_dec(v_a_204_);
lean_inc(v_cancelTk_x3f_213_);
lean_inc(v_snap_x3f_212_);
lean_inc(v_currMacroScope_211_);
lean_inc(v_quotContext_x3f_210_);
lean_inc(v_macroStack_209_);
lean_inc(v_cmdPos_208_);
lean_inc(v_currRecDepth_207_);
lean_inc_ref(v_fileMap_206_);
lean_inc_ref(v_fileName_205_);
v___x_216_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_216_, 0, v_fileName_205_);
lean_ctor_set(v___x_216_, 1, v_fileMap_206_);
lean_ctor_set(v___x_216_, 2, v_currRecDepth_207_);
lean_ctor_set(v___x_216_, 3, v_cmdPos_208_);
lean_ctor_set(v___x_216_, 4, v_macroStack_209_);
lean_ctor_set(v___x_216_, 5, v_quotContext_x3f_210_);
lean_ctor_set(v___x_216_, 6, v_currMacroScope_211_);
lean_ctor_set(v___x_216_, 7, v_ref_215_);
lean_ctor_set(v___x_216_, 8, v_snap_x3f_212_);
lean_ctor_set(v___x_216_, 9, v_cancelTk_x3f_213_);
lean_ctor_set_uint8(v___x_216_, sizeof(void*)*10, v_suppressElabErrors_214_);
v___x_217_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_199_, v___x_216_, v___y_201_);
lean_dec_ref_known(v___x_216_, 10);
return v___x_217_;
}
else
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
lean_dec_ref(v_msg_199_);
v_a_218_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_203_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_203_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg___boxed(lean_object* v_ref_226_, lean_object* v_msg_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_ref_226_, v_msg_227_, v___y_228_, v___y_229_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v_ref_226_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(lean_object* v_k_235_, lean_object* v_as_236_, size_t v_sz_237_, size_t v_i_238_, lean_object* v_b_239_){
_start:
{
uint8_t v___x_240_; 
v___x_240_ = lean_usize_dec_lt(v_i_238_, v_sz_237_);
if (v___x_240_ == 0)
{
lean_dec(v_k_235_);
lean_inc_ref(v_b_239_);
return v_b_239_;
}
else
{
lean_object* v___x_241_; lean_object* v_a_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_241_ = lean_box(0);
v_a_242_ = lean_array_uget_borrowed(v_as_236_, v_i_238_);
lean_inc(v_a_242_);
v___x_243_ = l_Lean_Syntax_getKind(v_a_242_);
lean_inc(v_k_235_);
v___x_244_ = l_Lean_Elab_Command_checkRuleKind(v___x_243_, v_k_235_);
lean_dec(v___x_243_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; size_t v___x_246_; size_t v___x_247_; 
v___x_245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0));
v___x_246_ = ((size_t)1ULL);
v___x_247_ = lean_usize_add(v_i_238_, v___x_246_);
v_i_238_ = v___x_247_;
v_b_239_ = v___x_245_;
goto _start;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec(v_k_235_);
lean_inc(v_a_242_);
v___x_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_249_, 0, v_a_242_);
v___x_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_241_);
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___boxed(lean_object* v_k_252_, lean_object* v_as_253_, lean_object* v_sz_254_, lean_object* v_i_255_, lean_object* v_b_256_){
_start:
{
size_t v_sz_boxed_257_; size_t v_i_boxed_258_; lean_object* v_res_259_; 
v_sz_boxed_257_ = lean_unbox_usize(v_sz_254_);
lean_dec(v_sz_254_);
v_i_boxed_258_ = lean_unbox_usize(v_i_255_);
lean_dec(v_i_255_);
v_res_259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(v_k_252_, v_as_253_, v_sz_boxed_257_, v_i_boxed_258_, v_b_256_);
lean_dec_ref(v_b_256_);
lean_dec_ref(v_as_253_);
return v_res_259_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__0));
v___x_262_ = l_Lean_stringToMessageData(v___x_261_);
return v___x_262_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__2));
v___x_265_ = l_Lean_stringToMessageData(v___x_264_);
return v___x_265_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12(void){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Array_mkArray0___redArg();
return v___x_279_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__16));
v___x_286_ = l_Lean_stringToMessageData(v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(lean_object* v_k_287_, size_t v_sz_288_, size_t v_i_289_, lean_object* v_bs_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
uint8_t v___x_294_; 
v___x_294_ = lean_usize_dec_lt(v_i_289_, v_sz_288_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
lean_dec(v_k_287_);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v_bs_290_);
return v___x_295_;
}
else
{
lean_object* v_v_296_; lean_object* v___x_297_; lean_object* v_bs_x27_298_; lean_object* v_a_300_; lean_object* v___y_306_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_v_296_ = lean_array_uget(v_bs_290_, v_i_289_);
v___x_297_ = lean_unsigned_to_nat(0u);
v_bs_x27_298_ = lean_array_uset(v_bs_290_, v_i_289_, v___x_297_);
v___x_325_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8));
lean_inc(v_v_296_);
v___x_326_ = l_Lean_Syntax_isOfKind(v_v_296_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
lean_dec(v_v_296_);
v___x_327_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
v___y_306_ = v___x_327_;
goto v___jp_305_;
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = l_Lean_Syntax_getArg(v_v_296_, v___x_328_);
lean_inc(v___x_329_);
v___x_330_ = l_Lean_Syntax_matchesNull(v___x_329_, v___x_328_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
lean_dec(v___x_329_);
lean_dec(v_v_296_);
v___x_331_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
v___y_306_ = v___x_331_;
goto v___jp_305_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___x_349_; lean_object* v_pat_350_; lean_object* v___y_352_; lean_object* v___y_353_; uint8_t v___x_405_; 
v___x_332_ = lean_box(0);
v___x_333_ = l_Lean_Syntax_getArg(v___x_329_, v___x_297_);
lean_dec(v___x_329_);
v___x_334_ = lean_unsigned_to_nat(3u);
v___x_335_ = l_Lean_Syntax_getArg(v_v_296_, v___x_334_);
v___x_349_ = l_Lean_Syntax_getArgs(v___x_333_);
lean_dec(v___x_333_);
v_pat_350_ = lean_array_get_borrowed(v___x_332_, v___x_349_, v___x_297_);
v___x_405_ = l_Lean_Syntax_isQuot(v_pat_350_);
if (v___x_405_ == 0)
{
if (v___x_330_ == 0)
{
v___y_352_ = v___y_291_;
v___y_353_ = v___y_292_;
goto v___jp_351_;
}
else
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
if (lean_obj_tag(v___x_406_) == 0)
{
lean_dec_ref_known(v___x_406_, 1);
v___y_352_ = v___y_291_;
v___y_353_ = v___y_292_;
goto v___jp_351_;
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec_ref(v___x_349_);
lean_dec(v___x_335_);
lean_dec_ref(v_bs_x27_298_);
lean_dec(v_v_296_);
lean_dec(v_k_287_);
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
else
{
v___y_352_ = v___y_291_;
v___y_353_ = v___y_292_;
goto v___jp_351_;
}
v___jp_336_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_339_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9));
lean_inc_n(v___y_337_, 4);
v___x_340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_340_, 0, v___y_337_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_342_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
v___x_343_ = l_Array_append___redArg(v___x_342_, v___y_338_);
lean_dec_ref(v___y_338_);
v___x_344_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_344_, 0, v___y_337_);
lean_ctor_set(v___x_344_, 1, v___x_341_);
lean_ctor_set(v___x_344_, 2, v___x_343_);
v___x_345_ = l_Lean_Syntax_node1(v___y_337_, v___x_341_, v___x_344_);
v___x_346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13));
v___x_347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_347_, 0, v___y_337_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = l_Lean_Syntax_node4(v___y_337_, v___x_325_, v___x_340_, v___x_345_, v___x_347_, v___x_335_);
v_a_300_ = v___x_348_;
goto v___jp_299_;
}
v___jp_351_:
{
lean_object* v_quoted_354_; lean_object* v_k_x27_355_; uint8_t v___x_356_; 
lean_inc(v_pat_350_);
v_quoted_354_ = l_Lean_Syntax_getQuotContent(v_pat_350_);
lean_inc(v_quoted_354_);
v_k_x27_355_ = l_Lean_Syntax_getKind(v_quoted_354_);
lean_inc(v_k_287_);
v___x_356_ = l_Lean_Elab_Command_checkRuleKind(v_k_x27_355_, v_k_287_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__15));
v___x_358_ = lean_name_eq(v_k_x27_355_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec(v_quoted_354_);
lean_dec_ref(v___x_349_);
lean_dec(v___x_335_);
v___x_359_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17);
v___x_360_ = l_Lean_MessageData_ofName(v_k_x27_355_);
v___x_361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3);
v___x_363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_v_296_, v___x_363_, v___y_352_, v___y_353_);
lean_dec(v_v_296_);
v___y_306_ = v___x_364_;
goto v___jp_305_;
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; size_t v_sz_367_; size_t v___x_368_; lean_object* v___x_369_; lean_object* v_fst_370_; 
lean_dec(v_k_x27_355_);
v___x_365_ = l_Lean_Syntax_getArgs(v_quoted_354_);
lean_dec(v_quoted_354_);
v___x_366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0));
v_sz_367_ = lean_array_size(v___x_365_);
v___x_368_ = ((size_t)0ULL);
lean_inc(v_k_287_);
v___x_369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(v_k_287_, v___x_365_, v_sz_367_, v___x_368_, v___x_366_);
lean_dec_ref(v___x_365_);
v_fst_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_fst_370_);
lean_dec_ref(v___x_369_);
if (lean_obj_tag(v_fst_370_) == 0)
{
lean_dec_ref(v___x_349_);
lean_dec(v___x_335_);
v___y_317_ = v___y_353_;
v___y_318_ = v___y_352_;
goto v___jp_316_;
}
else
{
lean_object* v_val_371_; 
v_val_371_ = lean_ctor_get(v_fst_370_, 0);
lean_inc(v_val_371_);
lean_dec_ref_known(v_fst_370_, 1);
if (lean_obj_tag(v_val_371_) == 0)
{
lean_dec_ref(v___x_349_);
lean_dec(v___x_335_);
v___y_317_ = v___y_353_;
v___y_318_ = v___y_352_;
goto v___jp_316_;
}
else
{
lean_object* v_val_372_; lean_object* v_pat_373_; lean_object* v_pats_374_; lean_object* v___x_375_; 
lean_dec(v_v_296_);
v_val_372_ = lean_ctor_get(v_val_371_, 0);
lean_inc(v_val_372_);
lean_dec_ref_known(v_val_371_, 1);
lean_inc(v_pat_350_);
v_pat_373_ = l_Lean_Syntax_setArg(v_pat_350_, v___x_328_, v_val_372_);
v_pats_374_ = lean_array_set(v___x_349_, v___x_297_, v_pat_373_);
v___x_375_ = l_Lean_Elab_Command_getRef___redArg(v___y_352_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_376_);
lean_dec_ref_known(v___x_375_, 1);
v___x_377_ = l_Lean_SourceInfo_fromRef(v_a_376_, v___x_356_);
lean_dec(v_a_376_);
v___x_378_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_352_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_quotContext_x3f_379_; 
lean_dec_ref_known(v___x_378_, 1);
v_quotContext_x3f_379_ = lean_ctor_get(v___y_352_, 5);
if (lean_obj_tag(v_quotContext_x3f_379_) == 0)
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_353_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_dec_ref_known(v___x_380_, 1);
v___y_337_ = v___x_377_;
v___y_338_ = v_pats_374_;
goto v___jp_336_;
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec(v___x_377_);
lean_dec_ref(v_pats_374_);
lean_dec(v___x_335_);
lean_dec_ref(v_bs_x27_298_);
lean_dec(v_k_287_);
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
v___y_337_ = v___x_377_;
v___y_338_ = v_pats_374_;
goto v___jp_336_;
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec(v___x_377_);
lean_dec_ref(v_pats_374_);
lean_dec(v___x_335_);
lean_dec_ref(v_bs_x27_298_);
lean_dec(v_k_287_);
v_a_389_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_378_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_378_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec_ref(v_pats_374_);
lean_dec(v___x_335_);
lean_dec_ref(v_bs_x27_298_);
lean_dec(v_k_287_);
v_a_397_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_375_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_375_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_x27_355_);
lean_dec(v_quoted_354_);
lean_dec_ref(v___x_349_);
lean_dec(v___x_335_);
v_a_300_ = v_v_296_;
goto v___jp_299_;
}
}
}
}
v___jp_299_:
{
size_t v___x_301_; size_t v___x_302_; lean_object* v___x_303_; 
v___x_301_ = ((size_t)1ULL);
v___x_302_ = lean_usize_add(v_i_289_, v___x_301_);
v___x_303_ = lean_array_uset(v_bs_x27_298_, v_i_289_, v_a_300_);
v_i_289_ = v___x_302_;
v_bs_290_ = v___x_303_;
goto _start;
}
v___jp_305_:
{
if (lean_obj_tag(v___y_306_) == 0)
{
lean_object* v_a_307_; 
v_a_307_ = lean_ctor_get(v___y_306_, 0);
lean_inc(v_a_307_);
lean_dec_ref_known(v___y_306_, 1);
v_a_300_ = v_a_307_;
goto v___jp_299_;
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec_ref(v_bs_x27_298_);
lean_dec(v_k_287_);
v_a_308_ = lean_ctor_get(v___y_306_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___y_306_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___y_306_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___y_306_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
v___jp_316_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_319_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1);
lean_inc(v_k_287_);
v___x_320_ = l_Lean_MessageData_ofName(v_k_287_);
v___x_321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3);
v___x_323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_321_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_v_296_, v___x_323_, v___y_318_, v___y_317_);
lean_dec(v_v_296_);
v___y_306_ = v___x_324_;
goto v___jp_305_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___boxed(lean_object* v_k_415_, lean_object* v_sz_416_, lean_object* v_i_417_, lean_object* v_bs_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
size_t v_sz_boxed_422_; size_t v_i_boxed_423_; lean_object* v_res_424_; 
v_sz_boxed_422_ = lean_unbox_usize(v_sz_416_);
lean_dec(v_sz_416_);
v_i_boxed_423_ = lean_unbox_usize(v_i_417_);
lean_dec(v_i_417_);
v_res_424_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(v_k_415_, v_sz_boxed_422_, v_i_boxed_423_, v_bs_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
return v_res_424_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__4(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__3));
v___x_430_ = l_String_toRawSubstring_x27(v___x_429_);
return v___x_430_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__7));
v___x_436_ = l_String_toRawSubstring_x27(v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__19(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__18));
v___x_449_ = l_String_toRawSubstring_x27(v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__26(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__25));
v___x_464_ = l_String_toRawSubstring_x27(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux(lean_object* v_doc_x3f_491_, lean_object* v_attrs_x3f_492_, lean_object* v_attrKind_493_, lean_object* v_tk_494_, lean_object* v_k_495_, lean_object* v_alts_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
size_t v_sz_500_; size_t v___x_501_; lean_object* v___x_502_; 
v_sz_500_ = lean_array_size(v_alts_496_);
v___x_501_ = ((size_t)0ULL);
lean_inc(v_k_495_);
v___x_502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(v_k_495_, v_sz_500_, v___x_501_, v_alts_496_, v_a_497_, v_a_498_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_687_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_687_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_687_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_687_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v_a_624_; lean_object* v___x_633_; 
v___x_633_ = l_Lean_Elab_Command_getRef___redArg(v_a_497_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; uint8_t v___x_635_; lean_object* v___y_637_; lean_object* v___x_657_; lean_object* v___x_676_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
v___x_635_ = 0;
v___x_657_ = l_Lean_SourceInfo_fromRef(v_a_634_, v___x_635_);
lean_dec(v_a_634_);
v___x_676_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_497_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_quotContext_x3f_677_; 
lean_dec_ref_known(v___x_676_, 1);
v_quotContext_x3f_677_ = lean_ctor_get(v_a_497_, 5);
if (lean_obj_tag(v_quotContext_x3f_677_) == 0)
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v_a_498_);
lean_dec_ref(v___x_678_);
goto v___jp_658_;
}
else
{
goto v___jp_658_;
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec(v___x_657_);
lean_del_object(v___x_505_);
lean_dec(v_a_503_);
lean_dec(v_k_495_);
lean_dec(v_attrKind_493_);
lean_dec(v_doc_x3f_491_);
v_a_679_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_676_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_676_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
v___jp_636_:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_493_);
v___x_639_ = l_Lean_Elab_Command_getRef___redArg(v_a_497_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_639_, 1);
v___x_641_ = l_Lean_SourceInfo_fromRef(v_a_640_, v___x_635_);
lean_dec(v_a_640_);
v___x_642_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_497_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_quotContext_x3f_643_; 
v_quotContext_x3f_643_ = lean_ctor_get(v_a_497_, 5);
if (lean_obj_tag(v_quotContext_x3f_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_645_; lean_object* v_a_646_; 
v_a_644_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_642_, 1);
v___x_645_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v_a_498_);
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref(v___x_645_);
v___y_620_ = v___y_637_;
v___y_621_ = v___x_638_;
v___y_622_ = v_a_644_;
v___y_623_ = v___x_641_;
v_a_624_ = v_a_646_;
goto v___jp_619_;
}
else
{
lean_object* v_a_647_; lean_object* v_val_648_; 
v_a_647_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v___x_642_, 1);
v_val_648_ = lean_ctor_get(v_quotContext_x3f_643_, 0);
lean_inc(v_val_648_);
v___y_620_ = v___y_637_;
v___y_621_ = v___x_638_;
v___y_622_ = v_a_647_;
v___y_623_ = v___x_641_;
v_a_624_ = v_val_648_;
goto v___jp_619_;
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec(v___x_641_);
lean_dec(v___x_638_);
lean_dec_ref(v___y_637_);
lean_del_object(v___x_505_);
lean_dec(v_a_503_);
lean_dec(v_k_495_);
lean_dec(v_doc_x3f_491_);
v_a_649_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_642_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_642_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
else
{
lean_dec(v___x_638_);
lean_dec_ref(v___y_637_);
lean_del_object(v___x_505_);
lean_dec(v_a_503_);
lean_dec(v_k_495_);
lean_dec(v_doc_x3f_491_);
return v___x_639_;
}
}
v___jp_658_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_659_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__35));
v___x_660_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__37));
v___x_661_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__38));
lean_inc_n(v___x_657_, 2);
v___x_662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_657_);
lean_ctor_set(v___x_662_, 1, v___x_660_);
lean_inc(v_k_495_);
v___x_663_ = l_Lean_mkIdent(v_k_495_);
v___x_664_ = l_Lean_Syntax_node2(v___x_657_, v___x_661_, v___x_662_, v___x_663_);
lean_inc(v_attrKind_493_);
v___x_665_ = l_Lean_Syntax_node2(v___x_657_, v___x_659_, v_attrKind_493_, v___x_664_);
if (lean_obj_tag(v_attrs_x3f_492_) == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_666_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_667_ = lean_unsigned_to_nat(1u);
v___x_668_ = lean_mk_empty_array_with_capacity(v___x_667_);
v___x_669_ = lean_array_push(v___x_668_, v___x_665_);
v___x_670_ = l_Lean_Syntax_SepArray_ofElems(v___x_666_, v___x_669_);
lean_dec_ref(v___x_669_);
v___y_637_ = v___x_670_;
goto v___jp_636_;
}
else
{
lean_object* v_val_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_val_671_ = lean_ctor_get(v_attrs_x3f_492_, 0);
v___x_672_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_673_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_671_);
v___x_674_ = lean_array_push(v___x_673_, v___x_665_);
v___x_675_ = l_Lean_Syntax_SepArray_ofElems(v___x_672_, v___x_674_);
lean_dec_ref(v___x_674_);
v___y_637_ = v___x_675_;
goto v___jp_636_;
}
}
}
else
{
lean_del_object(v___x_505_);
lean_dec(v_a_503_);
lean_dec(v_k_495_);
lean_dec(v_attrKind_493_);
lean_dec(v_doc_x3f_491_);
return v___x_633_;
}
v___jp_507_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
lean_inc_ref_n(v___y_517_, 3);
v___x_519_ = l_Array_append___redArg(v___y_517_, v___y_518_);
lean_dec_ref(v___y_518_);
lean_inc_n(v___y_510_, 8);
lean_inc_n(v___y_515_, 29);
v___x_520_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_520_, 0, v___y_515_);
lean_ctor_set(v___x_520_, 1, v___y_510_);
lean_ctor_set(v___x_520_, 2, v___x_519_);
v___x_521_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5));
v___x_522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6));
v___x_523_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
lean_inc_ref_n(v___y_516_, 9);
v___x_524_ = l_Lean_Name_mkStr4(v___y_516_, v___x_521_, v___x_522_, v___x_523_);
v___x_525_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
v___x_526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_526_, 0, v___y_515_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = l_Array_append___redArg(v___y_517_, v___y_509_);
lean_dec_ref(v___y_509_);
v___x_528_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_528_, 0, v___y_515_);
lean_ctor_set(v___x_528_, 1, v___y_510_);
lean_ctor_set(v___x_528_, 2, v___x_527_);
v___x_529_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
v___x_530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_530_, 0, v___y_515_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = l_Lean_Syntax_node3(v___y_515_, v___x_524_, v___x_526_, v___x_528_, v___x_530_);
v___x_532_ = l_Lean_Syntax_node1(v___y_515_, v___y_510_, v___x_531_);
lean_inc_ref(v___y_512_);
v___x_533_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_533_, 0, v___y_515_);
lean_ctor_set(v___x_533_, 1, v___y_512_);
v___x_534_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__4, &l_Lean_Elab_Command_elabMacroRulesAux___closed__4_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__4);
v___x_535_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__5));
lean_inc_n(v___y_514_, 3);
lean_inc_n(v___y_511_, 3);
v___x_536_ = l_Lean_addMacroScope(v___y_511_, v___x_535_, v___y_514_);
v___x_537_ = lean_box(0);
v___x_538_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_538_, 0, v___y_515_);
lean_ctor_set(v___x_538_, 1, v___x_534_);
lean_ctor_set(v___x_538_, 2, v___x_536_);
lean_ctor_set(v___x_538_, 3, v___x_537_);
v___x_539_ = 1;
v___x_540_ = l_Lean_mkIdentFrom(v_tk_494_, v_k_495_, v___x_539_);
v___x_541_ = l_Lean_Syntax_node2(v___y_515_, v___y_510_, v___x_538_, v___x_540_);
v___x_542_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__6));
v___x_543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_543_, 0, v___y_515_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__7));
v___x_545_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__8, &l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8);
v___x_546_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__9));
v___x_547_ = l_Lean_addMacroScope(v___y_511_, v___x_546_, v___y_514_);
v___x_548_ = l_Lean_Name_mkStr2(v___y_516_, v___x_544_);
lean_inc(v___x_548_);
v___x_549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v___x_537_);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
v___x_551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v___x_537_);
v___x_552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_549_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_553_, 0, v___y_515_);
lean_ctor_set(v___x_553_, 1, v___x_545_);
lean_ctor_set(v___x_553_, 2, v___x_547_);
lean_ctor_set(v___x_553_, 3, v___x_552_);
v___x_554_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
v___x_555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_555_, 0, v___y_515_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__11));
v___x_557_ = l_Lean_Name_mkStr4(v___y_516_, v___x_521_, v___x_522_, v___x_556_);
v___x_558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_558_, 0, v___y_515_);
lean_ctor_set(v___x_558_, 1, v___x_556_);
v___x_559_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__12));
v___x_560_ = l_Lean_Name_mkStr4(v___y_516_, v___x_521_, v___x_522_, v___x_559_);
v___x_561_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7));
v___x_562_ = l_Lean_Name_mkStr4(v___y_516_, v___x_521_, v___x_522_, v___x_561_);
v___x_563_ = l_Array_append___redArg(v___y_517_, v_a_503_);
lean_dec(v_a_503_);
v___x_564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9));
v___x_565_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_565_, 0, v___y_515_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__13));
v___x_567_ = l_Lean_Name_mkStr4(v___y_516_, v___x_521_, v___x_522_, v___x_566_);
v___x_568_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__14));
v___x_569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_569_, 0, v___y_515_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = l_Lean_Syntax_node1(v___y_515_, v___x_567_, v___x_569_);
v___x_571_ = l_Lean_Syntax_node1(v___y_515_, v___y_510_, v___x_570_);
v___x_572_ = l_Lean_Syntax_node1(v___y_515_, v___y_510_, v___x_571_);
v___x_573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13));
v___x_574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_574_, 0, v___y_515_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__15));
v___x_576_ = l_Lean_Name_mkStr4(v___y_516_, v___x_521_, v___x_522_, v___x_575_);
v___x_577_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__16));
v___x_578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_578_, 0, v___y_515_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__17));
v___x_580_ = l_Lean_Name_mkStr4(v___y_516_, v___x_521_, v___x_522_, v___x_579_);
v___x_581_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__19, &l_Lean_Elab_Command_elabMacroRulesAux___closed__19_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__19);
v___x_582_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__20));
v___x_583_ = l_Lean_addMacroScope(v___y_511_, v___x_582_, v___y_514_);
v___x_584_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__24));
v___x_585_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_585_, 0, v___y_515_);
lean_ctor_set(v___x_585_, 1, v___x_581_);
lean_ctor_set(v___x_585_, 2, v___x_583_);
lean_ctor_set(v___x_585_, 3, v___x_584_);
v___x_586_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__26, &l_Lean_Elab_Command_elabMacroRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__26);
v___x_587_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__27));
v___x_588_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__28));
v___x_589_ = l_Lean_Name_mkStr4(v___y_516_, v___x_544_, v___x_587_, v___x_588_);
lean_inc_n(v___x_589_, 2);
v___x_590_ = l_Lean_addMacroScope(v___y_511_, v___x_589_, v___y_514_);
v___x_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set(v___x_591_, 1, v___x_537_);
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_589_);
v___x_593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v___x_537_);
v___x_594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_591_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_595_, 0, v___y_515_);
lean_ctor_set(v___x_595_, 1, v___x_586_);
lean_ctor_set(v___x_595_, 2, v___x_590_);
lean_ctor_set(v___x_595_, 3, v___x_594_);
v___x_596_ = l_Lean_Syntax_node1(v___y_515_, v___y_510_, v___x_595_);
v___x_597_ = l_Lean_Syntax_node2(v___y_515_, v___x_580_, v___x_585_, v___x_596_);
v___x_598_ = l_Lean_Syntax_node2(v___y_515_, v___x_576_, v___x_578_, v___x_597_);
v___x_599_ = l_Lean_Syntax_node4(v___y_515_, v___x_562_, v___x_565_, v___x_572_, v___x_574_, v___x_598_);
v___x_600_ = lean_array_push(v___x_563_, v___x_599_);
v___x_601_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_601_, 0, v___y_515_);
lean_ctor_set(v___x_601_, 1, v___y_510_);
lean_ctor_set(v___x_601_, 2, v___x_600_);
v___x_602_ = l_Lean_Syntax_node1(v___y_515_, v___x_560_, v___x_601_);
v___x_603_ = l_Lean_Syntax_node2(v___y_515_, v___x_557_, v___x_558_, v___x_602_);
v___x_604_ = lean_unsigned_to_nat(9u);
v___x_605_ = lean_mk_empty_array_with_capacity(v___x_604_);
v___x_606_ = lean_array_push(v___x_605_, v___x_520_);
v___x_607_ = lean_array_push(v___x_606_, v___x_532_);
v___x_608_ = lean_array_push(v___x_607_, v___y_513_);
v___x_609_ = lean_array_push(v___x_608_, v___x_533_);
v___x_610_ = lean_array_push(v___x_609_, v___x_541_);
v___x_611_ = lean_array_push(v___x_610_, v___x_543_);
v___x_612_ = lean_array_push(v___x_611_, v___x_553_);
v___x_613_ = lean_array_push(v___x_612_, v___x_555_);
v___x_614_ = lean_array_push(v___x_613_, v___x_603_);
lean_inc(v___y_508_);
v___x_615_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_615_, 0, v___y_515_);
lean_ctor_set(v___x_615_, 1, v___y_508_);
lean_ctor_set(v___x_615_, 2, v___x_614_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_615_);
v___x_617_ = v___x_505_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
v___jp_619_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_625_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4));
v___x_626_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__31));
v___x_627_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__32));
v___x_628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_629_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
if (lean_obj_tag(v_doc_x3f_491_) == 1)
{
lean_object* v_val_630_; lean_object* v___x_631_; 
v_val_630_ = lean_ctor_get(v_doc_x3f_491_, 0);
lean_inc(v_val_630_);
lean_dec_ref_known(v_doc_x3f_491_, 1);
v___x_631_ = l_Array_mkArray1___redArg(v_val_630_);
v___y_508_ = v___x_627_;
v___y_509_ = v___y_620_;
v___y_510_ = v___x_628_;
v___y_511_ = v_a_624_;
v___y_512_ = v___x_626_;
v___y_513_ = v___y_621_;
v___y_514_ = v___y_622_;
v___y_515_ = v___y_623_;
v___y_516_ = v___x_625_;
v___y_517_ = v___x_629_;
v___y_518_ = v___x_631_;
goto v___jp_507_;
}
else
{
lean_object* v___x_632_; 
lean_dec(v_doc_x3f_491_);
v___x_632_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__33));
v___y_508_ = v___x_627_;
v___y_509_ = v___y_620_;
v___y_510_ = v___x_628_;
v___y_511_ = v_a_624_;
v___y_512_ = v___x_626_;
v___y_513_ = v___y_621_;
v___y_514_ = v___y_622_;
v___y_515_ = v___y_623_;
v___y_516_ = v___x_625_;
v___y_517_ = v___x_629_;
v___y_518_ = v___x_632_;
goto v___jp_507_;
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_dec(v_k_495_);
lean_dec(v_attrKind_493_);
lean_dec(v_doc_x3f_491_);
v_a_688_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_502_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_502_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux___boxed(lean_object* v_doc_x3f_696_, lean_object* v_attrs_x3f_697_, lean_object* v_attrKind_698_, lean_object* v_tk_699_, lean_object* v_k_700_, lean_object* v_alts_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_Elab_Command_elabMacroRulesAux(v_doc_x3f_696_, v_attrs_x3f_697_, v_attrKind_698_, v_tk_699_, v_k_700_, v_alts_701_, v_a_702_, v_a_703_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
lean_dec(v_tk_699_);
lean_dec(v_attrs_x3f_697_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(lean_object* v_00_u03b1_706_, lean_object* v_ref_707_, lean_object* v_msg_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_ref_707_, v_msg_708_, v___y_709_, v___y_710_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___boxed(lean_object* v_00_u03b1_713_, lean_object* v_ref_714_, lean_object* v_msg_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(v_00_u03b1_713_, v_ref_714_, v_msg_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v_ref_714_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3(lean_object* v_msgData_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msgData_720_, v___y_722_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3(v_msgData_725_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(lean_object* v_00_u03b1_730_, lean_object* v_msg_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_731_, v___y_732_, v___y_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___boxed(lean_object* v_00_u03b1_736_, lean_object* v_msg_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(v_00_u03b1_736_, v_msg_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4(lean_object* v_msgData_742_, lean_object* v_macroStack_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_msgData_742_, v_macroStack_743_, v___y_745_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___boxed(lean_object* v_msgData_748_, lean_object* v_macroStack_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4(v_msgData_748_, v_macroStack_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(lean_object* v___y_754_, uint8_t v_isExporting_755_, lean_object* v_a_x3f_756_){
_start:
{
lean_object* v___x_758_; lean_object* v_env_759_; lean_object* v_messages_760_; lean_object* v_scopes_761_; lean_object* v_usedQuotCtxts_762_; lean_object* v_nextMacroScope_763_; lean_object* v_maxRecDepth_764_; lean_object* v_ngen_765_; lean_object* v_auxDeclNGen_766_; lean_object* v_infoState_767_; lean_object* v_traceState_768_; lean_object* v_snapshotTasks_769_; lean_object* v_prevLinterStates_770_; lean_object* v_codeQualityEntryTasks_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_782_; 
v___x_758_ = lean_st_ref_take(v___y_754_);
v_env_759_ = lean_ctor_get(v___x_758_, 0);
v_messages_760_ = lean_ctor_get(v___x_758_, 1);
v_scopes_761_ = lean_ctor_get(v___x_758_, 2);
v_usedQuotCtxts_762_ = lean_ctor_get(v___x_758_, 3);
v_nextMacroScope_763_ = lean_ctor_get(v___x_758_, 4);
v_maxRecDepth_764_ = lean_ctor_get(v___x_758_, 5);
v_ngen_765_ = lean_ctor_get(v___x_758_, 6);
v_auxDeclNGen_766_ = lean_ctor_get(v___x_758_, 7);
v_infoState_767_ = lean_ctor_get(v___x_758_, 8);
v_traceState_768_ = lean_ctor_get(v___x_758_, 9);
v_snapshotTasks_769_ = lean_ctor_get(v___x_758_, 10);
v_prevLinterStates_770_ = lean_ctor_get(v___x_758_, 11);
v_codeQualityEntryTasks_771_ = lean_ctor_get(v___x_758_, 12);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_782_ == 0)
{
v___x_773_ = v___x_758_;
v_isShared_774_ = v_isSharedCheck_782_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_codeQualityEntryTasks_771_);
lean_inc(v_prevLinterStates_770_);
lean_inc(v_snapshotTasks_769_);
lean_inc(v_traceState_768_);
lean_inc(v_infoState_767_);
lean_inc(v_auxDeclNGen_766_);
lean_inc(v_ngen_765_);
lean_inc(v_maxRecDepth_764_);
lean_inc(v_nextMacroScope_763_);
lean_inc(v_usedQuotCtxts_762_);
lean_inc(v_scopes_761_);
lean_inc(v_messages_760_);
lean_inc(v_env_759_);
lean_dec(v___x_758_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_782_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_775_ = lean_box(0);
v___x_776_ = l_Lean_Environment_setExporting(v_env_759_, v_isExporting_755_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_776_);
v___x_778_ = v___x_773_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_messages_760_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v_scopes_761_);
lean_ctor_set(v_reuseFailAlloc_781_, 3, v_usedQuotCtxts_762_);
lean_ctor_set(v_reuseFailAlloc_781_, 4, v_nextMacroScope_763_);
lean_ctor_set(v_reuseFailAlloc_781_, 5, v_maxRecDepth_764_);
lean_ctor_set(v_reuseFailAlloc_781_, 6, v_ngen_765_);
lean_ctor_set(v_reuseFailAlloc_781_, 7, v_auxDeclNGen_766_);
lean_ctor_set(v_reuseFailAlloc_781_, 8, v_infoState_767_);
lean_ctor_set(v_reuseFailAlloc_781_, 9, v_traceState_768_);
lean_ctor_set(v_reuseFailAlloc_781_, 10, v_snapshotTasks_769_);
lean_ctor_set(v_reuseFailAlloc_781_, 11, v_prevLinterStates_770_);
lean_ctor_set(v_reuseFailAlloc_781_, 12, v_codeQualityEntryTasks_771_);
v___x_778_ = v_reuseFailAlloc_781_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_st_ref_put(v___y_754_, v___x_778_);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_775_);
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0___boxed(lean_object* v___y_783_, lean_object* v_isExporting_784_, lean_object* v_a_x3f_785_, lean_object* v___y_786_){
_start:
{
uint8_t v_isExporting_boxed_787_; lean_object* v_res_788_; 
v_isExporting_boxed_787_ = lean_unbox(v_isExporting_784_);
v_res_788_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_783_, v_isExporting_boxed_787_, v_a_x3f_785_);
lean_dec(v_a_x3f_785_);
lean_dec(v___y_783_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(lean_object* v_x_789_, uint8_t v_isExporting_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_794_; lean_object* v_env_795_; lean_object* v___x_796_; uint8_t v_isModule_797_; 
v___x_794_ = lean_st_ref_get(v___y_792_);
v_env_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc_ref(v_env_795_);
lean_dec(v___x_794_);
v___x_796_ = l_Lean_Environment_header(v_env_795_);
v_isModule_797_ = lean_ctor_get_uint8(v___x_796_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_796_);
if (v_isModule_797_ == 0)
{
lean_object* v___x_798_; 
lean_dec_ref(v_env_795_);
lean_inc(v___y_792_);
lean_inc_ref(v___y_791_);
v___x_798_ = lean_apply_3(v_x_789_, v___y_791_, v___y_792_, lean_box(0));
return v___x_798_;
}
else
{
uint8_t v_isExporting_799_; 
v_isExporting_799_ = lean_ctor_get_uint8(v_env_795_, sizeof(void*)*13);
lean_dec_ref(v_env_795_);
if (v_isExporting_790_ == 0)
{
if (v_isExporting_799_ == 0)
{
lean_object* v___x_853_; 
lean_inc(v___y_792_);
lean_inc_ref(v___y_791_);
v___x_853_ = lean_apply_3(v_x_789_, v___y_791_, v___y_792_, lean_box(0));
return v___x_853_;
}
else
{
goto v___jp_800_;
}
}
else
{
if (v_isExporting_799_ == 0)
{
goto v___jp_800_;
}
else
{
lean_object* v___x_854_; 
lean_inc(v___y_792_);
lean_inc_ref(v___y_791_);
v___x_854_ = lean_apply_3(v_x_789_, v___y_791_, v___y_792_, lean_box(0));
return v___x_854_;
}
}
v___jp_800_:
{
lean_object* v___x_801_; lean_object* v_env_802_; lean_object* v_messages_803_; lean_object* v_scopes_804_; lean_object* v_usedQuotCtxts_805_; lean_object* v_nextMacroScope_806_; lean_object* v_maxRecDepth_807_; lean_object* v_ngen_808_; lean_object* v_auxDeclNGen_809_; lean_object* v_infoState_810_; lean_object* v_traceState_811_; lean_object* v_snapshotTasks_812_; lean_object* v_prevLinterStates_813_; lean_object* v_codeQualityEntryTasks_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_852_; 
v___x_801_ = lean_st_ref_take(v___y_792_);
v_env_802_ = lean_ctor_get(v___x_801_, 0);
v_messages_803_ = lean_ctor_get(v___x_801_, 1);
v_scopes_804_ = lean_ctor_get(v___x_801_, 2);
v_usedQuotCtxts_805_ = lean_ctor_get(v___x_801_, 3);
v_nextMacroScope_806_ = lean_ctor_get(v___x_801_, 4);
v_maxRecDepth_807_ = lean_ctor_get(v___x_801_, 5);
v_ngen_808_ = lean_ctor_get(v___x_801_, 6);
v_auxDeclNGen_809_ = lean_ctor_get(v___x_801_, 7);
v_infoState_810_ = lean_ctor_get(v___x_801_, 8);
v_traceState_811_ = lean_ctor_get(v___x_801_, 9);
v_snapshotTasks_812_ = lean_ctor_get(v___x_801_, 10);
v_prevLinterStates_813_ = lean_ctor_get(v___x_801_, 11);
v_codeQualityEntryTasks_814_ = lean_ctor_get(v___x_801_, 12);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_852_ == 0)
{
v___x_816_ = v___x_801_;
v_isShared_817_ = v_isSharedCheck_852_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_codeQualityEntryTasks_814_);
lean_inc(v_prevLinterStates_813_);
lean_inc(v_snapshotTasks_812_);
lean_inc(v_traceState_811_);
lean_inc(v_infoState_810_);
lean_inc(v_auxDeclNGen_809_);
lean_inc(v_ngen_808_);
lean_inc(v_maxRecDepth_807_);
lean_inc(v_nextMacroScope_806_);
lean_inc(v_usedQuotCtxts_805_);
lean_inc(v_scopes_804_);
lean_inc(v_messages_803_);
lean_inc(v_env_802_);
lean_dec(v___x_801_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_852_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_818_ = l_Lean_Environment_setExporting(v_env_802_, v_isExporting_790_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_818_);
v___x_820_ = v___x_816_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_messages_803_);
lean_ctor_set(v_reuseFailAlloc_851_, 2, v_scopes_804_);
lean_ctor_set(v_reuseFailAlloc_851_, 3, v_usedQuotCtxts_805_);
lean_ctor_set(v_reuseFailAlloc_851_, 4, v_nextMacroScope_806_);
lean_ctor_set(v_reuseFailAlloc_851_, 5, v_maxRecDepth_807_);
lean_ctor_set(v_reuseFailAlloc_851_, 6, v_ngen_808_);
lean_ctor_set(v_reuseFailAlloc_851_, 7, v_auxDeclNGen_809_);
lean_ctor_set(v_reuseFailAlloc_851_, 8, v_infoState_810_);
lean_ctor_set(v_reuseFailAlloc_851_, 9, v_traceState_811_);
lean_ctor_set(v_reuseFailAlloc_851_, 10, v_snapshotTasks_812_);
lean_ctor_set(v_reuseFailAlloc_851_, 11, v_prevLinterStates_813_);
lean_ctor_set(v_reuseFailAlloc_851_, 12, v_codeQualityEntryTasks_814_);
v___x_820_ = v_reuseFailAlloc_851_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_821_; lean_object* v_r_822_; 
v___x_821_ = lean_st_ref_put(v___y_792_, v___x_820_);
lean_inc(v___y_792_);
lean_inc_ref(v___y_791_);
v_r_822_ = lean_apply_3(v_x_789_, v___y_791_, v___y_792_, lean_box(0));
if (lean_obj_tag(v_r_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_839_; 
v_a_823_ = lean_ctor_get(v_r_822_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v_r_822_);
if (v_isSharedCheck_839_ == 0)
{
v___x_825_ = v_r_822_;
v_isShared_826_ = v_isSharedCheck_839_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v_r_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_839_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
lean_inc(v_a_823_);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 1);
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_838_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v___x_829_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_792_, v_isExporting_799_, v___x_828_);
lean_dec_ref(v___x_828_);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; 
v_unused_837_ = lean_ctor_get(v___x_829_, 0);
lean_dec(v_unused_837_);
v___x_831_ = v___x_829_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_dec(v___x_829_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v_a_823_);
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_823_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
v_a_840_ = lean_ctor_get(v_r_822_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v_r_822_, 1);
v___x_841_ = lean_box(0);
v___x_842_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_792_, v_isExporting_799_, v___x_841_);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v___x_842_, 0);
lean_dec(v_unused_850_);
v___x_844_ = v___x_842_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_dec(v___x_842_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set_tag(v___x_844_, 1);
lean_ctor_set(v___x_844_, 0, v_a_840_);
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_840_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___boxed(lean_object* v_x_855_, lean_object* v_isExporting_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
uint8_t v_isExporting_boxed_860_; lean_object* v_res_861_; 
v_isExporting_boxed_860_ = lean_unbox(v_isExporting_856_);
v_res_861_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v_x_855_, v_isExporting_boxed_860_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0(lean_object* v_00_u03b1_862_, lean_object* v_x_863_, uint8_t v_isExporting_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v_x_863_, v_isExporting_864_, v___y_865_, v___y_866_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___boxed(lean_object* v_00_u03b1_869_, lean_object* v_x_870_, lean_object* v_isExporting_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
uint8_t v_isExporting_boxed_875_; lean_object* v_res_876_; 
v_isExporting_boxed_875_ = lean_unbox(v_isExporting_871_);
v_res_876_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0(v_00_u03b1_869_, v_x_870_, v_isExporting_boxed_875_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0(lean_object* v___x_877_, lean_object* v___x_878_, lean_object* v_doc_x3f_879_, lean_object* v_attrs_x3f_880_, lean_object* v_attrKind_881_, lean_object* v_tk_882_, lean_object* v_alts_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_Elab_Command_getRef___redArg(v___y_884_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v_fileName_889_; lean_object* v_fileMap_890_; lean_object* v_currRecDepth_891_; lean_object* v_cmdPos_892_; lean_object* v_macroStack_893_; lean_object* v_quotContext_x3f_894_; lean_object* v_currMacroScope_895_; lean_object* v_snap_x3f_896_; lean_object* v_cancelTk_x3f_897_; uint8_t v_suppressElabErrors_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_917_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_887_, 1);
v_fileName_889_ = lean_ctor_get(v___y_884_, 0);
v_fileMap_890_ = lean_ctor_get(v___y_884_, 1);
v_currRecDepth_891_ = lean_ctor_get(v___y_884_, 2);
v_cmdPos_892_ = lean_ctor_get(v___y_884_, 3);
v_macroStack_893_ = lean_ctor_get(v___y_884_, 4);
v_quotContext_x3f_894_ = lean_ctor_get(v___y_884_, 5);
v_currMacroScope_895_ = lean_ctor_get(v___y_884_, 6);
v_snap_x3f_896_ = lean_ctor_get(v___y_884_, 8);
v_cancelTk_x3f_897_ = lean_ctor_get(v___y_884_, 9);
v_suppressElabErrors_898_ = lean_ctor_get_uint8(v___y_884_, sizeof(void*)*10);
v_isSharedCheck_917_ = !lean_is_exclusive(v___y_884_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; 
v_unused_918_ = lean_ctor_get(v___y_884_, 7);
lean_dec(v_unused_918_);
v___x_900_ = v___y_884_;
v_isShared_901_ = v_isSharedCheck_917_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_cancelTk_x3f_897_);
lean_inc(v_snap_x3f_896_);
lean_inc(v_currMacroScope_895_);
lean_inc(v_quotContext_x3f_894_);
lean_inc(v_macroStack_893_);
lean_inc(v_cmdPos_892_);
lean_inc(v_currRecDepth_891_);
lean_inc(v_fileMap_890_);
lean_inc(v_fileName_889_);
lean_dec(v___y_884_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_917_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v_ref_902_; lean_object* v___x_904_; 
v_ref_902_ = l_Lean_replaceRef(v___x_877_, v_a_888_);
lean_dec(v_a_888_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 7, v_ref_902_);
v___x_904_ = v___x_900_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_fileName_889_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_fileMap_890_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v_currRecDepth_891_);
lean_ctor_set(v_reuseFailAlloc_916_, 3, v_cmdPos_892_);
lean_ctor_set(v_reuseFailAlloc_916_, 4, v_macroStack_893_);
lean_ctor_set(v_reuseFailAlloc_916_, 5, v_quotContext_x3f_894_);
lean_ctor_set(v_reuseFailAlloc_916_, 6, v_currMacroScope_895_);
lean_ctor_set(v_reuseFailAlloc_916_, 7, v_ref_902_);
lean_ctor_set(v_reuseFailAlloc_916_, 8, v_snap_x3f_896_);
lean_ctor_set(v_reuseFailAlloc_916_, 9, v_cancelTk_x3f_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_916_, sizeof(void*)*10, v_suppressElabErrors_898_);
v___x_904_ = v_reuseFailAlloc_916_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_905_; 
v___x_905_ = l_Lean_Elab_Command_resolveSyntaxKind(v___x_878_, v___x_904_, v___y_885_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_907_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
lean_dec_ref_known(v___x_905_, 1);
v___x_907_ = l_Lean_Elab_Command_elabMacroRulesAux(v_doc_x3f_879_, v_attrs_x3f_880_, v_attrKind_881_, v_tk_882_, v_a_906_, v_alts_883_, v___x_904_, v___y_885_);
lean_dec_ref(v___x_904_);
return v___x_907_;
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_dec_ref(v___x_904_);
lean_dec_ref(v_alts_883_);
lean_dec(v_attrKind_881_);
lean_dec(v_doc_x3f_879_);
v_a_908_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_905_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_905_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_884_);
lean_dec_ref(v_alts_883_);
lean_dec(v_attrKind_881_);
lean_dec(v_doc_x3f_879_);
lean_dec(v___x_878_);
return v___x_887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0___boxed(lean_object* v___x_919_, lean_object* v___x_920_, lean_object* v_doc_x3f_921_, lean_object* v_attrs_x3f_922_, lean_object* v_attrKind_923_, lean_object* v_tk_924_, lean_object* v_alts_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_Elab_Command_elabMacroRules___lam__0(v___x_919_, v___x_920_, v_doc_x3f_921_, v_attrs_x3f_922_, v_attrKind_923_, v_tk_924_, v_alts_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec(v_tk_924_);
lean_dec(v_attrs_x3f_922_);
lean_dec(v___x_919_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5(lean_object* v___x_933_, lean_object* v___x_934_, lean_object* v_attrKind_935_, lean_object* v___x_936_, lean_object* v___x_937_, lean_object* v_attrs_x3f_938_, lean_object* v___x_939_, lean_object* v___x_940_, lean_object* v___x_941_, lean_object* v_doc_x3f_942_, lean_object* v_kind_x3f_943_, lean_object* v_alts_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_Elab_Command_getRef___redArg(v___y_945_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_1026_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_1026_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_1026_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
uint8_t v___x_953_; lean_object* v___x_954_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___x_1015_; 
v___x_953_ = 0;
v___x_954_ = l_Lean_SourceInfo_fromRef(v_a_949_, v___x_953_);
lean_dec(v_a_949_);
v___x_1015_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_945_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_quotContext_x3f_1016_; 
lean_dec_ref_known(v___x_1015_, 1);
v_quotContext_x3f_1016_ = lean_ctor_get(v___y_945_, 5);
if (lean_obj_tag(v_quotContext_x3f_1016_) == 0)
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_946_);
lean_dec_ref(v___x_1017_);
goto v___jp_1009_;
}
else
{
goto v___jp_1009_;
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec(v___x_954_);
lean_del_object(v___x_951_);
lean_dec(v_kind_x3f_943_);
lean_dec(v_doc_x3f_942_);
lean_dec_ref(v___x_941_);
lean_dec_ref(v___x_940_);
lean_dec_ref(v___x_939_);
lean_dec_ref(v___x_936_);
lean_dec(v_attrKind_935_);
lean_dec(v___x_934_);
lean_dec(v___x_933_);
v_a_1018_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1015_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1015_);
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
v___jp_955_:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
lean_inc_ref_n(v___y_957_, 2);
v___x_962_ = l_Array_append___redArg(v___y_957_, v___y_961_);
lean_dec_ref(v___y_961_);
lean_inc_n(v___y_956_, 2);
lean_inc_n(v___x_954_, 3);
v___x_963_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_963_, 0, v___x_954_);
lean_ctor_set(v___x_963_, 1, v___y_956_);
lean_ctor_set(v___x_963_, 2, v___x_962_);
v___x_964_ = l_Array_append___redArg(v___y_957_, v_alts_944_);
v___x_965_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_965_, 0, v___x_954_);
lean_ctor_set(v___x_965_, 1, v___y_956_);
lean_ctor_set(v___x_965_, 2, v___x_964_);
v___x_966_ = l_Lean_Syntax_node1(v___x_954_, v___x_933_, v___x_965_);
v___x_967_ = l_Lean_Syntax_node6(v___x_954_, v___x_934_, v___y_959_, v___y_958_, v_attrKind_935_, v___y_960_, v___x_963_, v___x_966_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_967_);
v___x_969_ = v___x_951_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
v___jp_971_:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
lean_inc_ref(v___y_973_);
v___x_976_ = l_Array_append___redArg(v___y_973_, v___y_975_);
lean_dec_ref(v___y_975_);
lean_inc(v___y_972_);
lean_inc_n(v___x_954_, 2);
v___x_977_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_977_, 0, v___x_954_);
lean_ctor_set(v___x_977_, 1, v___y_972_);
lean_ctor_set(v___x_977_, 2, v___x_976_);
v___x_978_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_954_);
lean_ctor_set(v___x_978_, 1, v___x_936_);
if (lean_obj_tag(v_kind_x3f_943_) == 0)
{
lean_object* v___x_979_; 
v___x_979_ = lean_mk_empty_array_with_capacity(v___x_937_);
v___y_956_ = v___y_972_;
v___y_957_ = v___y_973_;
v___y_958_ = v___x_977_;
v___y_959_ = v___y_974_;
v___y_960_ = v___x_978_;
v___y_961_ = v___x_979_;
goto v___jp_955_;
}
else
{
lean_object* v_val_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_val_980_ = lean_ctor_get(v_kind_x3f_943_, 0);
lean_inc(v_val_980_);
lean_dec_ref_known(v_kind_x3f_943_, 1);
v___x_981_ = l_Lean_mkIdent(v_val_980_);
v___x_982_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0));
lean_inc_n(v___x_954_, 4);
v___x_983_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_954_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1));
v___x_985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_954_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
v___x_987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_954_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2));
v___x_989_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_954_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = l_Array_mkArray5___redArg(v___x_983_, v___x_985_, v___x_987_, v___x_981_, v___x_989_);
v___y_956_ = v___y_972_;
v___y_957_ = v___y_973_;
v___y_958_ = v___x_977_;
v___y_959_ = v___y_974_;
v___y_960_ = v___x_978_;
v___y_961_ = v___x_990_;
goto v___jp_955_;
}
}
v___jp_991_:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
lean_inc_ref(v___y_993_);
v___x_995_ = l_Array_append___redArg(v___y_993_, v___y_994_);
lean_dec_ref(v___y_994_);
lean_inc(v___y_992_);
lean_inc(v___x_954_);
v___x_996_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_996_, 0, v___x_954_);
lean_ctor_set(v___x_996_, 1, v___y_992_);
lean_ctor_set(v___x_996_, 2, v___x_995_);
if (lean_obj_tag(v_attrs_x3f_938_) == 1)
{
lean_object* v_val_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_val_997_ = lean_ctor_get(v_attrs_x3f_938_, 0);
v___x_998_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
v___x_999_ = l_Lean_Name_mkStr4(v___x_939_, v___x_940_, v___x_941_, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
lean_inc_n(v___x_954_, 4);
v___x_1001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_954_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
lean_inc_ref(v___y_993_);
v___x_1002_ = l_Array_append___redArg(v___y_993_, v_val_997_);
lean_inc(v___y_992_);
v___x_1003_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1003_, 0, v___x_954_);
lean_ctor_set(v___x_1003_, 1, v___y_992_);
lean_ctor_set(v___x_1003_, 2, v___x_1002_);
v___x_1004_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
v___x_1005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_954_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l_Lean_Syntax_node3(v___x_954_, v___x_999_, v___x_1001_, v___x_1003_, v___x_1005_);
v___x_1007_ = l_Array_mkArray1___redArg(v___x_1006_);
v___y_972_ = v___y_992_;
v___y_973_ = v___y_993_;
v___y_974_ = v___x_996_;
v___y_975_ = v___x_1007_;
goto v___jp_971_;
}
else
{
lean_object* v___x_1008_; 
lean_dec_ref(v___x_941_);
lean_dec_ref(v___x_940_);
lean_dec_ref(v___x_939_);
v___x_1008_ = lean_mk_empty_array_with_capacity(v___x_937_);
v___y_972_ = v___y_992_;
v___y_973_ = v___y_993_;
v___y_974_ = v___x_996_;
v___y_975_ = v___x_1008_;
goto v___jp_971_;
}
}
v___jp_1009_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1011_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
if (lean_obj_tag(v_doc_x3f_942_) == 1)
{
lean_object* v_val_1012_; lean_object* v___x_1013_; 
v_val_1012_ = lean_ctor_get(v_doc_x3f_942_, 0);
lean_inc(v_val_1012_);
lean_dec_ref_known(v_doc_x3f_942_, 1);
v___x_1013_ = l_Array_mkArray1___redArg(v_val_1012_);
v___y_992_ = v___x_1010_;
v___y_993_ = v___x_1011_;
v___y_994_ = v___x_1013_;
goto v___jp_991_;
}
else
{
lean_object* v___x_1014_; 
lean_dec(v_doc_x3f_942_);
v___x_1014_ = lean_mk_empty_array_with_capacity(v___x_937_);
v___y_992_ = v___x_1010_;
v___y_993_ = v___x_1011_;
v___y_994_ = v___x_1014_;
goto v___jp_991_;
}
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v_kind_x3f_943_);
lean_dec(v_doc_x3f_942_);
lean_dec_ref(v___x_941_);
lean_dec_ref(v___x_940_);
lean_dec_ref(v___x_939_);
lean_dec_ref(v___x_936_);
lean_dec(v_attrKind_935_);
lean_dec(v___x_934_);
lean_dec(v___x_933_);
v_a_1027_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_948_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_948_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5___boxed(lean_object* v___x_1035_, lean_object* v___x_1036_, lean_object* v_attrKind_1037_, lean_object* v___x_1038_, lean_object* v___x_1039_, lean_object* v_attrs_x3f_1040_, lean_object* v___x_1041_, lean_object* v___x_1042_, lean_object* v___x_1043_, lean_object* v_doc_x3f_1044_, lean_object* v_kind_x3f_1045_, lean_object* v_alts_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Elab_Command_elabMacroRules___lam__5(v___x_1035_, v___x_1036_, v_attrKind_1037_, v___x_1038_, v___x_1039_, v_attrs_x3f_1040_, v___x_1041_, v___x_1042_, v___x_1043_, v_doc_x3f_1044_, v_kind_x3f_1045_, v_alts_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec_ref(v_alts_1046_);
lean_dec(v_attrs_x3f_1040_);
lean_dec(v___x_1039_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1(lean_object* v_stx_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v___y_1108_; uint8_t v___y_1109_; uint8_t v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; uint8_t v___y_1113_; uint8_t v___y_1117_; lean_object* v___y_1118_; uint8_t v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; uint8_t v___y_1122_; lean_object* v___y_1126_; uint8_t v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; uint8_t v___y_1130_; uint8_t v___y_1131_; lean_object* v___y_1135_; lean_object* v___y_1136_; uint8_t v___y_1137_; uint8_t v___y_1138_; lean_object* v___y_1139_; uint8_t v___y_1140_; lean_object* v___y_1144_; lean_object* v___y_1145_; uint8_t v___y_1146_; uint8_t v___y_1147_; lean_object* v___y_1148_; uint8_t v___y_1149_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; 
v___x_1152_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4));
v___x_1153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5));
v___x_1154_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0));
v___x_1155_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1));
lean_inc(v_stx_1103_);
v___x_1156_ = l_Lean_Syntax_isOfKind(v_stx_1103_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1222_; 
lean_dec(v_stx_1103_);
v___x_1222_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1222_;
}
else
{
lean_object* v___x_1223_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v_a_1236_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; uint8_t v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; uint8_t v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; uint8_t v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v_attrs_x3f_1361_; lean_object* v_doc_x3f_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1223_ = lean_unsigned_to_nat(0u);
v___x_1536_ = l_Lean_Syntax_getArg(v_stx_1103_, v___x_1223_);
v___x_1537_ = l_Lean_Syntax_isNone(v___x_1536_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1538_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1536_);
v___x_1539_ = l_Lean_Syntax_matchesNull(v___x_1536_, v___x_1538_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; 
lean_dec(v___x_1536_);
lean_dec(v_stx_1103_);
v___x_1540_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1540_;
}
else
{
lean_object* v_doc_x3f_1541_; 
v_doc_x3f_1541_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1223_);
lean_dec(v___x_1536_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1544_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17));
lean_inc(v_doc_x3f_1541_);
v___x_1545_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1541_, v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; 
lean_dec(v_doc_x3f_1541_);
lean_dec(v_stx_1103_);
v___x_1546_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1546_;
}
else
{
goto v___jp_1542_;
}
}
else
{
goto v___jp_1542_;
}
v___jp_1542_:
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1543_, 0, v_doc_x3f_1541_);
v_doc_x3f_1520_ = v___x_1543_;
v___y_1521_ = v___y_1104_;
v___y_1522_ = v___y_1105_;
goto v___jp_1519_;
}
}
}
else
{
lean_object* v___x_1547_; 
lean_dec(v___x_1536_);
v___x_1547_ = lean_box(0);
v_doc_x3f_1520_ = v___x_1547_;
v___y_1521_ = v___y_1104_;
v___y_1522_ = v___y_1105_;
goto v___jp_1519_;
}
v___jp_1224_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__31));
v___x_1238_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__32));
v___x_1239_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
if (lean_obj_tag(v___y_1225_) == 1)
{
lean_object* v_val_1240_; lean_object* v___x_1241_; 
v_val_1240_ = lean_ctor_get(v___y_1225_, 0);
lean_inc(v_val_1240_);
lean_dec_ref_known(v___y_1225_, 1);
v___x_1241_ = l_Array_mkArray1___redArg(v_val_1240_);
v___y_1158_ = v___x_1239_;
v___y_1159_ = v___x_1238_;
v___y_1160_ = v_a_1236_;
v___y_1161_ = v___y_1233_;
v___y_1162_ = v___y_1232_;
v___y_1163_ = v___x_1237_;
v___y_1164_ = v___y_1228_;
v___y_1165_ = v___y_1227_;
v___y_1166_ = v___y_1226_;
v___y_1167_ = v___y_1229_;
v___y_1168_ = v___y_1231_;
v___y_1169_ = v___y_1230_;
v___y_1170_ = v___y_1235_;
v___y_1171_ = v___y_1234_;
v___y_1172_ = v___x_1241_;
goto v___jp_1157_;
}
else
{
lean_object* v___x_1242_; 
lean_dec(v___y_1225_);
v___x_1242_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__33));
v___y_1158_ = v___x_1239_;
v___y_1159_ = v___x_1238_;
v___y_1160_ = v_a_1236_;
v___y_1161_ = v___y_1233_;
v___y_1162_ = v___y_1232_;
v___y_1163_ = v___x_1237_;
v___y_1164_ = v___y_1228_;
v___y_1165_ = v___y_1227_;
v___y_1166_ = v___y_1226_;
v___y_1167_ = v___y_1229_;
v___y_1168_ = v___y_1231_;
v___y_1169_ = v___y_1230_;
v___y_1170_ = v___y_1235_;
v___y_1171_ = v___y_1234_;
v___y_1172_ = v___x_1242_;
goto v___jp_1157_;
}
}
v___jp_1243_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = l_Lean_Parser_Command_visibility_ofAttrKind(v___y_1247_);
v___x_1258_ = l_Lean_Elab_Command_getRef___redArg(v___y_1252_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___x_1258_, 1);
v___x_1260_ = l_Lean_SourceInfo_fromRef(v_a_1259_, v___y_1251_);
lean_dec(v_a_1259_);
v___x_1261_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1252_);
lean_dec_ref(v___y_1252_);
if (lean_obj_tag(v___x_1261_) == 0)
{
if (lean_obj_tag(v___y_1246_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1263_; lean_object* v_a_1264_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v___x_1263_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_1245_);
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref(v___x_1263_);
v___y_1225_ = v___y_1244_;
v___y_1226_ = v___y_1248_;
v___y_1227_ = v___y_1249_;
v___y_1228_ = v___y_1250_;
v___y_1229_ = v___x_1257_;
v___y_1230_ = v___y_1253_;
v___y_1231_ = v___y_1254_;
v___y_1232_ = v___y_1256_;
v___y_1233_ = v___x_1260_;
v___y_1234_ = v_a_1262_;
v___y_1235_ = v___y_1255_;
v_a_1236_ = v_a_1264_;
goto v___jp_1224_;
}
else
{
lean_object* v_a_1265_; lean_object* v_val_1266_; 
v_a_1265_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v___x_1261_, 1);
v_val_1266_ = lean_ctor_get(v___y_1246_, 0);
lean_inc(v_val_1266_);
v___y_1225_ = v___y_1244_;
v___y_1226_ = v___y_1248_;
v___y_1227_ = v___y_1249_;
v___y_1228_ = v___y_1250_;
v___y_1229_ = v___x_1257_;
v___y_1230_ = v___y_1253_;
v___y_1231_ = v___y_1254_;
v___y_1232_ = v___y_1256_;
v___y_1233_ = v___x_1260_;
v___y_1234_ = v_a_1265_;
v___y_1235_ = v___y_1255_;
v_a_1236_ = v_val_1266_;
goto v___jp_1224_;
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec(v___x_1260_);
lean_dec(v___x_1257_);
lean_dec_ref(v___y_1256_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec(v___y_1244_);
v_a_1267_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1261_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1261_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
else
{
lean_dec(v___x_1257_);
lean_dec_ref(v___y_1256_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec(v___y_1244_);
return v___x_1258_;
}
}
v___jp_1275_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1291_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__34));
lean_inc_ref(v___y_1288_);
v___x_1292_ = l_Lean_Name_mkStr4(v___x_1152_, v___x_1153_, v___y_1288_, v___x_1291_);
v___x_1293_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__37));
v___x_1294_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__38));
lean_inc_n(v___y_1289_, 2);
v___x_1295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___y_1289_);
lean_ctor_set(v___x_1295_, 1, v___x_1293_);
lean_inc(v___y_1284_);
v___x_1296_ = l_Lean_Syntax_node2(v___y_1289_, v___x_1294_, v___x_1295_, v___y_1284_);
lean_inc(v___y_1280_);
v___x_1297_ = l_Lean_Syntax_node2(v___y_1289_, v___x_1292_, v___y_1280_, v___x_1296_);
if (lean_obj_tag(v___y_1279_) == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1298_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_1299_ = lean_mk_empty_array_with_capacity(v___y_1281_);
v___x_1300_ = lean_array_push(v___x_1299_, v___x_1297_);
v___x_1301_ = l_Lean_Syntax_SepArray_ofElems(v___x_1298_, v___x_1300_);
lean_dec_ref(v___x_1300_);
v___y_1244_ = v___y_1276_;
v___y_1245_ = v___y_1277_;
v___y_1246_ = v___y_1278_;
v___y_1247_ = v___y_1280_;
v___y_1248_ = v___y_1282_;
v___y_1249_ = v___y_1283_;
v___y_1250_ = v___y_1284_;
v___y_1251_ = v___y_1285_;
v___y_1252_ = v___y_1286_;
v___y_1253_ = v___y_1287_;
v___y_1254_ = v___y_1288_;
v___y_1255_ = v___y_1290_;
v___y_1256_ = v___x_1301_;
goto v___jp_1243_;
}
else
{
lean_object* v_val_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v_val_1302_ = lean_ctor_get(v___y_1279_, 0);
lean_inc(v_val_1302_);
lean_dec_ref_known(v___y_1279_, 1);
v___x_1303_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_1304_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1302_);
lean_dec(v_val_1302_);
v___x_1305_ = lean_array_push(v___x_1304_, v___x_1297_);
v___x_1306_ = l_Lean_Syntax_SepArray_ofElems(v___x_1303_, v___x_1305_);
lean_dec_ref(v___x_1305_);
v___y_1244_ = v___y_1276_;
v___y_1245_ = v___y_1277_;
v___y_1246_ = v___y_1278_;
v___y_1247_ = v___y_1280_;
v___y_1248_ = v___y_1282_;
v___y_1249_ = v___y_1283_;
v___y_1250_ = v___y_1284_;
v___y_1251_ = v___y_1285_;
v___y_1252_ = v___y_1286_;
v___y_1253_ = v___y_1287_;
v___y_1254_ = v___y_1288_;
v___y_1255_ = v___y_1290_;
v___y_1256_ = v___x_1306_;
goto v___jp_1243_;
}
}
v___jp_1307_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1322_ = l_Lean_Syntax_getArg(v___y_1321_, v___y_1310_);
lean_dec(v___y_1321_);
v___x_1323_ = lean_mk_empty_array_with_capacity(v___y_1314_);
lean_inc(v___y_1315_);
v___x_1324_ = lean_array_push(v___x_1323_, v___y_1315_);
lean_inc(v___x_1322_);
v___x_1325_ = lean_array_push(v___x_1324_, v___x_1322_);
v___x_1326_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1327_ = lean_box(2);
v___x_1328_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
lean_ctor_set(v___x_1328_, 1, v___x_1326_);
lean_ctor_set(v___x_1328_, 2, v___x_1325_);
v___x_1329_ = l_Lean_Elab_Command_getRef___redArg(v___y_1320_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v_fileName_1331_; lean_object* v_fileMap_1332_; lean_object* v_currRecDepth_1333_; lean_object* v_cmdPos_1334_; lean_object* v_macroStack_1335_; lean_object* v_quotContext_x3f_1336_; lean_object* v_currMacroScope_1337_; lean_object* v_snap_x3f_1338_; lean_object* v_cancelTk_x3f_1339_; uint8_t v_suppressElabErrors_1340_; lean_object* v_ref_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v___x_1329_, 1);
v_fileName_1331_ = lean_ctor_get(v___y_1320_, 0);
v_fileMap_1332_ = lean_ctor_get(v___y_1320_, 1);
v_currRecDepth_1333_ = lean_ctor_get(v___y_1320_, 2);
v_cmdPos_1334_ = lean_ctor_get(v___y_1320_, 3);
v_macroStack_1335_ = lean_ctor_get(v___y_1320_, 4);
v_quotContext_x3f_1336_ = lean_ctor_get(v___y_1320_, 5);
v_currMacroScope_1337_ = lean_ctor_get(v___y_1320_, 6);
v_snap_x3f_1338_ = lean_ctor_get(v___y_1320_, 8);
v_cancelTk_x3f_1339_ = lean_ctor_get(v___y_1320_, 9);
v_suppressElabErrors_1340_ = lean_ctor_get_uint8(v___y_1320_, sizeof(void*)*10);
v_ref_1341_ = l_Lean_replaceRef(v___x_1328_, v_a_1330_);
lean_dec(v_a_1330_);
lean_dec_ref_known(v___x_1328_, 3);
lean_inc(v_cancelTk_x3f_1339_);
lean_inc(v_snap_x3f_1338_);
lean_inc(v_currMacroScope_1337_);
lean_inc(v_quotContext_x3f_1336_);
lean_inc(v_macroStack_1335_);
lean_inc(v_cmdPos_1334_);
lean_inc(v_currRecDepth_1333_);
lean_inc_ref(v_fileMap_1332_);
lean_inc_ref(v_fileName_1331_);
v___x_1342_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1342_, 0, v_fileName_1331_);
lean_ctor_set(v___x_1342_, 1, v_fileMap_1332_);
lean_ctor_set(v___x_1342_, 2, v_currRecDepth_1333_);
lean_ctor_set(v___x_1342_, 3, v_cmdPos_1334_);
lean_ctor_set(v___x_1342_, 4, v_macroStack_1335_);
lean_ctor_set(v___x_1342_, 5, v_quotContext_x3f_1336_);
lean_ctor_set(v___x_1342_, 6, v_currMacroScope_1337_);
lean_ctor_set(v___x_1342_, 7, v_ref_1341_);
lean_ctor_set(v___x_1342_, 8, v_snap_x3f_1338_);
lean_ctor_set(v___x_1342_, 9, v_cancelTk_x3f_1339_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*10, v_suppressElabErrors_1340_);
v___x_1343_ = l_Lean_Elab_Command_getRef___redArg(v___x_1342_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
v___x_1345_ = l_Lean_SourceInfo_fromRef(v_a_1344_, v___y_1317_);
lean_dec(v_a_1344_);
v___x_1346_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_1342_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_dec_ref_known(v___x_1346_, 1);
if (lean_obj_tag(v_quotContext_x3f_1336_) == 0)
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_1309_);
lean_dec_ref(v___x_1347_);
v___y_1276_ = v___y_1308_;
v___y_1277_ = v___y_1309_;
v___y_1278_ = v_quotContext_x3f_1336_;
v___y_1279_ = v___y_1311_;
v___y_1280_ = v___y_1312_;
v___y_1281_ = v___y_1313_;
v___y_1282_ = v___x_1322_;
v___y_1283_ = v___y_1315_;
v___y_1284_ = v___y_1316_;
v___y_1285_ = v___y_1317_;
v___y_1286_ = v___x_1342_;
v___y_1287_ = v___y_1319_;
v___y_1288_ = v___y_1318_;
v___y_1289_ = v___x_1345_;
v___y_1290_ = v___x_1326_;
goto v___jp_1275_;
}
else
{
v___y_1276_ = v___y_1308_;
v___y_1277_ = v___y_1309_;
v___y_1278_ = v_quotContext_x3f_1336_;
v___y_1279_ = v___y_1311_;
v___y_1280_ = v___y_1312_;
v___y_1281_ = v___y_1313_;
v___y_1282_ = v___x_1322_;
v___y_1283_ = v___y_1315_;
v___y_1284_ = v___y_1316_;
v___y_1285_ = v___y_1317_;
v___y_1286_ = v___x_1342_;
v___y_1287_ = v___y_1319_;
v___y_1288_ = v___y_1318_;
v___y_1289_ = v___x_1345_;
v___y_1290_ = v___x_1326_;
goto v___jp_1275_;
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_dec(v___x_1345_);
lean_dec_ref_known(v___x_1342_, 10);
lean_dec(v___x_1322_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec(v___y_1308_);
v_a_1348_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1346_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1346_);
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
else
{
lean_dec_ref_known(v___x_1342_, 10);
lean_dec(v___x_1322_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec(v___y_1308_);
return v___x_1343_;
}
}
else
{
lean_dec_ref_known(v___x_1328_, 3);
lean_dec(v___x_1322_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec(v___y_1308_);
return v___x_1329_;
}
}
v___jp_1356_:
{
lean_object* v___x_1362_; lean_object* v_attrKind_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1362_ = lean_unsigned_to_nat(2u);
v_attrKind_1363_ = l_Lean_Syntax_getArg(v_stx_1103_, v___x_1362_);
v___x_1364_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6));
v___x_1365_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9));
lean_inc(v_attrKind_1363_);
v___x_1366_ = l_Lean_Syntax_isOfKind(v_attrKind_1363_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; 
lean_dec(v_attrKind_1363_);
lean_dec(v_attrs_x3f_1361_);
lean_dec(v___y_1357_);
lean_dec(v_stx_1103_);
v___x_1367_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1367_;
}
else
{
lean_object* v___x_1368_; lean_object* v_tk_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1368_ = lean_unsigned_to_nat(3u);
v_tk_1369_ = l_Lean_Syntax_getArg(v_stx_1103_, v___x_1368_);
v___x_1370_ = lean_unsigned_to_nat(4u);
v___x_1371_ = l_Lean_Syntax_getArg(v_stx_1103_, v___x_1370_);
lean_inc(v___x_1371_);
v___x_1372_ = l_Lean_Syntax_matchesNull(v___x_1371_, v___x_1223_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1371_);
v___x_1374_ = l_Lean_Syntax_matchesNull(v___x_1371_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; 
lean_dec(v___x_1371_);
lean_dec(v_tk_1369_);
lean_dec(v_attrKind_1363_);
lean_dec(v_attrs_x3f_1361_);
lean_dec(v___y_1357_);
lean_dec(v_stx_1103_);
v___x_1375_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1376_ = l_Lean_Syntax_getArg(v_stx_1103_, v___x_1373_);
lean_dec(v_stx_1103_);
v___x_1377_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10));
lean_inc(v___x_1376_);
v___x_1378_ = l_Lean_Syntax_isOfKind(v___x_1376_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
lean_dec(v___x_1376_);
lean_dec(v___x_1371_);
lean_dec(v_tk_1369_);
lean_dec(v_attrKind_1363_);
lean_dec(v_attrs_x3f_1361_);
lean_dec(v___y_1357_);
v___x_1379_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1379_;
}
else
{
lean_object* v_kind_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v_kind_1380_ = l_Lean_Syntax_getArg(v___x_1371_, v___x_1368_);
lean_dec(v___x_1371_);
v___x_1381_ = l_Lean_Syntax_getArg(v___x_1376_, v___x_1223_);
lean_dec(v___x_1376_);
lean_inc(v___x_1381_);
v___x_1382_ = l_Lean_Syntax_matchesNull(v___x_1381_, v___y_1360_);
if (v___x_1382_ == 0)
{
lean_object* v_alts_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___f_1392_; 
v_alts_1383_ = l_Lean_Syntax_getArgs(v___x_1381_);
lean_dec(v___x_1381_);
v___x_1384_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1385_ = lean_box(2);
lean_inc_ref(v_alts_1383_);
v___x_1386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
lean_ctor_set(v___x_1386_, 1, v___x_1384_);
lean_ctor_set(v___x_1386_, 2, v_alts_1383_);
v___x_1387_ = lean_mk_empty_array_with_capacity(v___x_1362_);
lean_inc(v_tk_1369_);
v___x_1388_ = lean_array_push(v___x_1387_, v_tk_1369_);
v___x_1389_ = lean_array_push(v___x_1388_, v___x_1386_);
v___x_1390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1385_);
lean_ctor_set(v___x_1390_, 1, v___x_1384_);
lean_ctor_set(v___x_1390_, 2, v___x_1389_);
v___x_1391_ = l_Lean_TSyntax_getId(v_kind_1380_);
lean_dec(v_kind_1380_);
lean_inc(v_attrKind_1363_);
v___f_1392_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1392_, 0, v___x_1390_);
lean_closure_set(v___f_1392_, 1, v___x_1391_);
lean_closure_set(v___f_1392_, 2, v___y_1357_);
lean_closure_set(v___f_1392_, 3, v_attrs_x3f_1361_);
lean_closure_set(v___f_1392_, 4, v_attrKind_1363_);
lean_closure_set(v___f_1392_, 5, v_tk_1369_);
lean_closure_set(v___f_1392_, 6, v_alts_1383_);
if (v___x_1366_ == 0)
{
lean_dec(v_attrKind_1363_);
v___y_1126_ = v___y_1358_;
v___y_1127_ = v___x_1382_;
v___y_1128_ = v___y_1359_;
v___y_1129_ = v___f_1392_;
v___y_1130_ = v___x_1378_;
v___y_1131_ = v___x_1366_;
goto v___jp_1125_;
}
else
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = l_Lean_Syntax_getArg(v_attrKind_1363_, v___x_1223_);
lean_dec(v_attrKind_1363_);
lean_inc(v___x_1393_);
v___x_1394_ = l_Lean_Syntax_matchesNull(v___x_1393_, v___y_1360_);
if (v___x_1394_ == 0)
{
lean_dec(v___x_1393_);
v___y_1126_ = v___y_1358_;
v___y_1127_ = v___x_1382_;
v___y_1128_ = v___y_1359_;
v___y_1129_ = v___f_1392_;
v___y_1130_ = v___x_1378_;
v___y_1131_ = v___x_1394_;
goto v___jp_1125_;
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1395_ = l_Lean_Syntax_getArg(v___x_1393_, v___x_1223_);
lean_dec(v___x_1393_);
v___x_1396_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1397_ = l_Lean_Syntax_isOfKind(v___x_1395_, v___x_1396_);
if (v___x_1397_ == 0)
{
v___y_1126_ = v___y_1358_;
v___y_1127_ = v___x_1382_;
v___y_1128_ = v___y_1359_;
v___y_1129_ = v___f_1392_;
v___y_1130_ = v___x_1378_;
v___y_1131_ = v___x_1397_;
goto v___jp_1125_;
}
else
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1392_, v___x_1382_, v___y_1359_, v___y_1358_);
return v___x_1398_;
}
}
}
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; 
v___x_1399_ = l_Lean_Syntax_getArg(v___x_1381_, v___x_1223_);
v___x_1400_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8));
lean_inc(v___x_1399_);
v___x_1401_ = l_Lean_Syntax_isOfKind(v___x_1399_, v___x_1400_);
if (v___x_1401_ == 0)
{
lean_object* v_alts_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___f_1411_; 
lean_dec(v___x_1399_);
v_alts_1402_ = l_Lean_Syntax_getArgs(v___x_1381_);
lean_dec(v___x_1381_);
v___x_1403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1404_ = lean_box(2);
lean_inc_ref(v_alts_1402_);
v___x_1405_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
lean_ctor_set(v___x_1405_, 1, v___x_1403_);
lean_ctor_set(v___x_1405_, 2, v_alts_1402_);
v___x_1406_ = lean_mk_empty_array_with_capacity(v___x_1362_);
lean_inc(v_tk_1369_);
v___x_1407_ = lean_array_push(v___x_1406_, v_tk_1369_);
v___x_1408_ = lean_array_push(v___x_1407_, v___x_1405_);
v___x_1409_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1404_);
lean_ctor_set(v___x_1409_, 1, v___x_1403_);
lean_ctor_set(v___x_1409_, 2, v___x_1408_);
v___x_1410_ = l_Lean_TSyntax_getId(v_kind_1380_);
lean_dec(v_kind_1380_);
lean_inc(v_attrKind_1363_);
v___f_1411_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1411_, 0, v___x_1409_);
lean_closure_set(v___f_1411_, 1, v___x_1410_);
lean_closure_set(v___f_1411_, 2, v___y_1357_);
lean_closure_set(v___f_1411_, 3, v_attrs_x3f_1361_);
lean_closure_set(v___f_1411_, 4, v_attrKind_1363_);
lean_closure_set(v___f_1411_, 5, v_tk_1369_);
lean_closure_set(v___f_1411_, 6, v_alts_1402_);
if (v___x_1366_ == 0)
{
lean_dec(v_attrKind_1363_);
v___y_1135_ = v___f_1411_;
v___y_1136_ = v___y_1358_;
v___y_1137_ = v___x_1382_;
v___y_1138_ = v___x_1401_;
v___y_1139_ = v___y_1359_;
v___y_1140_ = v___x_1366_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1412_ = l_Lean_Syntax_getArg(v_attrKind_1363_, v___x_1223_);
lean_dec(v_attrKind_1363_);
lean_inc(v___x_1412_);
v___x_1413_ = l_Lean_Syntax_matchesNull(v___x_1412_, v___y_1360_);
if (v___x_1413_ == 0)
{
lean_dec(v___x_1412_);
v___y_1135_ = v___f_1411_;
v___y_1136_ = v___y_1358_;
v___y_1137_ = v___x_1382_;
v___y_1138_ = v___x_1401_;
v___y_1139_ = v___y_1359_;
v___y_1140_ = v___x_1413_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1414_ = l_Lean_Syntax_getArg(v___x_1412_, v___x_1223_);
lean_dec(v___x_1412_);
v___x_1415_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1416_ = l_Lean_Syntax_isOfKind(v___x_1414_, v___x_1415_);
if (v___x_1416_ == 0)
{
v___y_1135_ = v___f_1411_;
v___y_1136_ = v___y_1358_;
v___y_1137_ = v___x_1382_;
v___y_1138_ = v___x_1401_;
v___y_1139_ = v___y_1359_;
v___y_1140_ = v___x_1416_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1411_, v___x_1401_, v___y_1359_, v___y_1358_);
return v___x_1417_;
}
}
}
}
else
{
lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1418_ = l_Lean_Syntax_getArg(v___x_1399_, v___y_1360_);
lean_inc(v___x_1418_);
v___x_1419_ = l_Lean_Syntax_matchesNull(v___x_1418_, v___y_1360_);
if (v___x_1419_ == 0)
{
lean_object* v_alts_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___f_1429_; 
lean_dec(v___x_1418_);
lean_dec(v___x_1399_);
v_alts_1420_ = l_Lean_Syntax_getArgs(v___x_1381_);
lean_dec(v___x_1381_);
v___x_1421_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1422_ = lean_box(2);
lean_inc_ref(v_alts_1420_);
v___x_1423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
lean_ctor_set(v___x_1423_, 1, v___x_1421_);
lean_ctor_set(v___x_1423_, 2, v_alts_1420_);
v___x_1424_ = lean_mk_empty_array_with_capacity(v___x_1362_);
lean_inc(v_tk_1369_);
v___x_1425_ = lean_array_push(v___x_1424_, v_tk_1369_);
v___x_1426_ = lean_array_push(v___x_1425_, v___x_1423_);
v___x_1427_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1422_);
lean_ctor_set(v___x_1427_, 1, v___x_1421_);
lean_ctor_set(v___x_1427_, 2, v___x_1426_);
v___x_1428_ = l_Lean_TSyntax_getId(v_kind_1380_);
lean_dec(v_kind_1380_);
lean_inc(v_attrKind_1363_);
v___f_1429_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1429_, 0, v___x_1427_);
lean_closure_set(v___f_1429_, 1, v___x_1428_);
lean_closure_set(v___f_1429_, 2, v___y_1357_);
lean_closure_set(v___f_1429_, 3, v_attrs_x3f_1361_);
lean_closure_set(v___f_1429_, 4, v_attrKind_1363_);
lean_closure_set(v___f_1429_, 5, v_tk_1369_);
lean_closure_set(v___f_1429_, 6, v_alts_1420_);
if (v___x_1366_ == 0)
{
lean_dec(v_attrKind_1363_);
v___y_1117_ = v___x_1419_;
v___y_1118_ = v___y_1358_;
v___y_1119_ = v___x_1401_;
v___y_1120_ = v___y_1359_;
v___y_1121_ = v___f_1429_;
v___y_1122_ = v___x_1366_;
goto v___jp_1116_;
}
else
{
lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1430_ = l_Lean_Syntax_getArg(v_attrKind_1363_, v___x_1223_);
lean_dec(v_attrKind_1363_);
lean_inc(v___x_1430_);
v___x_1431_ = l_Lean_Syntax_matchesNull(v___x_1430_, v___y_1360_);
if (v___x_1431_ == 0)
{
lean_dec(v___x_1430_);
v___y_1117_ = v___x_1419_;
v___y_1118_ = v___y_1358_;
v___y_1119_ = v___x_1401_;
v___y_1120_ = v___y_1359_;
v___y_1121_ = v___f_1429_;
v___y_1122_ = v___x_1431_;
goto v___jp_1116_;
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1432_ = l_Lean_Syntax_getArg(v___x_1430_, v___x_1223_);
lean_dec(v___x_1430_);
v___x_1433_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1434_ = l_Lean_Syntax_isOfKind(v___x_1432_, v___x_1433_);
if (v___x_1434_ == 0)
{
v___y_1117_ = v___x_1419_;
v___y_1118_ = v___y_1358_;
v___y_1119_ = v___x_1401_;
v___y_1120_ = v___y_1359_;
v___y_1121_ = v___f_1429_;
v___y_1122_ = v___x_1434_;
goto v___jp_1116_;
}
else
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1429_, v___x_1419_, v___y_1359_, v___y_1358_);
return v___x_1435_;
}
}
}
}
else
{
lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = l_Lean_Syntax_getArg(v___x_1418_, v___x_1223_);
lean_dec(v___x_1418_);
lean_inc(v___x_1436_);
v___x_1437_ = l_Lean_Syntax_matchesNull(v___x_1436_, v___y_1360_);
if (v___x_1437_ == 0)
{
lean_object* v_alts_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___f_1447_; 
lean_dec(v___x_1436_);
lean_dec(v___x_1399_);
v_alts_1438_ = l_Lean_Syntax_getArgs(v___x_1381_);
lean_dec(v___x_1381_);
v___x_1439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1440_ = lean_box(2);
lean_inc_ref(v_alts_1438_);
v___x_1441_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
lean_ctor_set(v___x_1441_, 1, v___x_1439_);
lean_ctor_set(v___x_1441_, 2, v_alts_1438_);
v___x_1442_ = lean_mk_empty_array_with_capacity(v___x_1362_);
lean_inc(v_tk_1369_);
v___x_1443_ = lean_array_push(v___x_1442_, v_tk_1369_);
v___x_1444_ = lean_array_push(v___x_1443_, v___x_1441_);
v___x_1445_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1440_);
lean_ctor_set(v___x_1445_, 1, v___x_1439_);
lean_ctor_set(v___x_1445_, 2, v___x_1444_);
v___x_1446_ = l_Lean_TSyntax_getId(v_kind_1380_);
lean_dec(v_kind_1380_);
lean_inc(v_attrKind_1363_);
v___f_1447_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1447_, 0, v___x_1445_);
lean_closure_set(v___f_1447_, 1, v___x_1446_);
lean_closure_set(v___f_1447_, 2, v___y_1357_);
lean_closure_set(v___f_1447_, 3, v_attrs_x3f_1361_);
lean_closure_set(v___f_1447_, 4, v_attrKind_1363_);
lean_closure_set(v___f_1447_, 5, v_tk_1369_);
lean_closure_set(v___f_1447_, 6, v_alts_1438_);
if (v___x_1366_ == 0)
{
lean_dec(v_attrKind_1363_);
v___y_1144_ = v___f_1447_;
v___y_1145_ = v___y_1358_;
v___y_1146_ = v___x_1419_;
v___y_1147_ = v___x_1437_;
v___y_1148_ = v___y_1359_;
v___y_1149_ = v___x_1366_;
goto v___jp_1143_;
}
else
{
lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1448_ = l_Lean_Syntax_getArg(v_attrKind_1363_, v___x_1223_);
lean_dec(v_attrKind_1363_);
lean_inc(v___x_1448_);
v___x_1449_ = l_Lean_Syntax_matchesNull(v___x_1448_, v___y_1360_);
if (v___x_1449_ == 0)
{
lean_dec(v___x_1448_);
v___y_1144_ = v___f_1447_;
v___y_1145_ = v___y_1358_;
v___y_1146_ = v___x_1419_;
v___y_1147_ = v___x_1437_;
v___y_1148_ = v___y_1359_;
v___y_1149_ = v___x_1449_;
goto v___jp_1143_;
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___x_1450_ = l_Lean_Syntax_getArg(v___x_1448_, v___x_1223_);
lean_dec(v___x_1448_);
v___x_1451_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1452_ = l_Lean_Syntax_isOfKind(v___x_1450_, v___x_1451_);
if (v___x_1452_ == 0)
{
v___y_1144_ = v___f_1447_;
v___y_1145_ = v___y_1358_;
v___y_1146_ = v___x_1419_;
v___y_1147_ = v___x_1437_;
v___y_1148_ = v___y_1359_;
v___y_1149_ = v___x_1452_;
goto v___jp_1143_;
}
else
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1447_, v___x_1437_, v___y_1359_, v___y_1358_);
return v___x_1453_;
}
}
}
}
else
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_Syntax_getArg(v___x_1436_, v___x_1223_);
lean_dec(v___x_1436_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1455_; uint8_t v___x_1456_; 
v___x_1455_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14));
lean_inc(v___x_1454_);
v___x_1456_ = l_Lean_Syntax_isOfKind(v___x_1454_, v___x_1455_);
if (v___x_1456_ == 0)
{
lean_object* v_alts_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___f_1466_; 
lean_dec(v___x_1454_);
lean_dec(v___x_1399_);
v_alts_1457_ = l_Lean_Syntax_getArgs(v___x_1381_);
lean_dec(v___x_1381_);
v___x_1458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1459_ = lean_box(2);
lean_inc_ref(v_alts_1457_);
v___x_1460_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
lean_ctor_set(v___x_1460_, 1, v___x_1458_);
lean_ctor_set(v___x_1460_, 2, v_alts_1457_);
v___x_1461_ = lean_mk_empty_array_with_capacity(v___x_1362_);
lean_inc(v_tk_1369_);
v___x_1462_ = lean_array_push(v___x_1461_, v_tk_1369_);
v___x_1463_ = lean_array_push(v___x_1462_, v___x_1460_);
v___x_1464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1459_);
lean_ctor_set(v___x_1464_, 1, v___x_1458_);
lean_ctor_set(v___x_1464_, 2, v___x_1463_);
v___x_1465_ = l_Lean_TSyntax_getId(v_kind_1380_);
lean_dec(v_kind_1380_);
lean_inc(v_attrKind_1363_);
v___f_1466_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1466_, 0, v___x_1464_);
lean_closure_set(v___f_1466_, 1, v___x_1465_);
lean_closure_set(v___f_1466_, 2, v___y_1357_);
lean_closure_set(v___f_1466_, 3, v_attrs_x3f_1361_);
lean_closure_set(v___f_1466_, 4, v_attrKind_1363_);
lean_closure_set(v___f_1466_, 5, v_tk_1369_);
lean_closure_set(v___f_1466_, 6, v_alts_1457_);
if (v___x_1366_ == 0)
{
lean_dec(v_attrKind_1363_);
v___y_1108_ = v___y_1358_;
v___y_1109_ = v___x_1372_;
v___y_1110_ = v___x_1437_;
v___y_1111_ = v___f_1466_;
v___y_1112_ = v___y_1359_;
v___y_1113_ = v___x_1366_;
goto v___jp_1107_;
}
else
{
lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1467_ = l_Lean_Syntax_getArg(v_attrKind_1363_, v___x_1223_);
lean_dec(v_attrKind_1363_);
lean_inc(v___x_1467_);
v___x_1468_ = l_Lean_Syntax_matchesNull(v___x_1467_, v___y_1360_);
if (v___x_1468_ == 0)
{
lean_dec(v___x_1467_);
v___y_1108_ = v___y_1358_;
v___y_1109_ = v___x_1372_;
v___y_1110_ = v___x_1437_;
v___y_1111_ = v___f_1466_;
v___y_1112_ = v___y_1359_;
v___y_1113_ = v___x_1468_;
goto v___jp_1107_;
}
else
{
lean_object* v___x_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1469_ = l_Lean_Syntax_getArg(v___x_1467_, v___x_1223_);
lean_dec(v___x_1467_);
v___x_1470_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1471_ = l_Lean_Syntax_isOfKind(v___x_1469_, v___x_1470_);
if (v___x_1471_ == 0)
{
v___y_1108_ = v___y_1358_;
v___y_1109_ = v___x_1372_;
v___y_1110_ = v___x_1437_;
v___y_1111_ = v___f_1466_;
v___y_1112_ = v___y_1359_;
v___y_1113_ = v___x_1471_;
goto v___jp_1107_;
}
else
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1466_, v___x_1372_, v___y_1359_, v___y_1358_);
return v___x_1472_;
}
}
}
}
else
{
lean_dec(v___x_1381_);
v___y_1308_ = v___y_1357_;
v___y_1309_ = v___y_1358_;
v___y_1310_ = v___x_1368_;
v___y_1311_ = v_attrs_x3f_1361_;
v___y_1312_ = v_attrKind_1363_;
v___y_1313_ = v___y_1360_;
v___y_1314_ = v___x_1362_;
v___y_1315_ = v_tk_1369_;
v___y_1316_ = v_kind_1380_;
v___y_1317_ = v___x_1372_;
v___y_1318_ = v___x_1364_;
v___y_1319_ = v___x_1454_;
v___y_1320_ = v___y_1359_;
v___y_1321_ = v___x_1399_;
goto v___jp_1307_;
}
}
else
{
lean_dec(v___x_1381_);
v___y_1308_ = v___y_1357_;
v___y_1309_ = v___y_1358_;
v___y_1310_ = v___x_1368_;
v___y_1311_ = v_attrs_x3f_1361_;
v___y_1312_ = v_attrKind_1363_;
v___y_1313_ = v___y_1360_;
v___y_1314_ = v___x_1362_;
v___y_1315_ = v_tk_1369_;
v___y_1316_ = v_kind_1380_;
v___y_1317_ = v___x_1372_;
v___y_1318_ = v___x_1364_;
v___y_1319_ = v___x_1454_;
v___y_1320_ = v___y_1359_;
v___y_1321_ = v___x_1399_;
goto v___jp_1307_;
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
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
lean_dec(v___x_1371_);
v___x_1473_ = lean_unsigned_to_nat(5u);
v___x_1474_ = l_Lean_Syntax_getArg(v_stx_1103_, v___x_1473_);
lean_dec(v_stx_1103_);
v___x_1475_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10));
lean_inc(v___x_1474_);
v___x_1476_ = l_Lean_Syntax_isOfKind(v___x_1474_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
lean_dec(v___x_1474_);
lean_dec(v_tk_1369_);
lean_dec(v_attrKind_1363_);
lean_dec(v_attrs_x3f_1361_);
lean_dec(v___y_1357_);
v___x_1477_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1477_;
}
else
{
lean_object* v___f_1478_; lean_object* v___x_1479_; lean_object* v_alts_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___f_1478_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__5___boxed), 15, 10);
lean_closure_set(v___f_1478_, 0, v___x_1475_);
lean_closure_set(v___f_1478_, 1, v___x_1155_);
lean_closure_set(v___f_1478_, 2, v_attrKind_1363_);
lean_closure_set(v___f_1478_, 3, v___x_1154_);
lean_closure_set(v___f_1478_, 4, v___x_1223_);
lean_closure_set(v___f_1478_, 5, v_attrs_x3f_1361_);
lean_closure_set(v___f_1478_, 6, v___x_1152_);
lean_closure_set(v___f_1478_, 7, v___x_1153_);
lean_closure_set(v___f_1478_, 8, v___x_1364_);
lean_closure_set(v___f_1478_, 9, v___y_1357_);
v___x_1479_ = l_Lean_Syntax_getArg(v___x_1474_, v___x_1223_);
lean_dec(v___x_1474_);
v_alts_1480_ = l_Lean_Syntax_getArgs(v___x_1479_);
lean_dec(v___x_1479_);
v___x_1481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1482_ = lean_box(2);
lean_inc_ref(v_alts_1480_);
v___x_1483_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
lean_ctor_set(v___x_1483_, 1, v___x_1481_);
lean_ctor_set(v___x_1483_, 2, v_alts_1480_);
v___x_1484_ = lean_mk_empty_array_with_capacity(v___x_1362_);
v___x_1485_ = lean_array_push(v___x_1484_, v_tk_1369_);
v___x_1486_ = lean_array_push(v___x_1485_, v___x_1483_);
v___x_1487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1482_);
lean_ctor_set(v___x_1487_, 1, v___x_1481_);
lean_ctor_set(v___x_1487_, 2, v___x_1486_);
v___x_1488_ = l_Lean_Elab_Command_getRef___redArg(v___y_1359_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v_fileName_1490_; lean_object* v_fileMap_1491_; lean_object* v_currRecDepth_1492_; lean_object* v_cmdPos_1493_; lean_object* v_macroStack_1494_; lean_object* v_quotContext_x3f_1495_; lean_object* v_currMacroScope_1496_; lean_object* v_snap_x3f_1497_; lean_object* v_cancelTk_x3f_1498_; uint8_t v_suppressElabErrors_1499_; lean_object* v_ref_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1488_, 1);
v_fileName_1490_ = lean_ctor_get(v___y_1359_, 0);
v_fileMap_1491_ = lean_ctor_get(v___y_1359_, 1);
v_currRecDepth_1492_ = lean_ctor_get(v___y_1359_, 2);
v_cmdPos_1493_ = lean_ctor_get(v___y_1359_, 3);
v_macroStack_1494_ = lean_ctor_get(v___y_1359_, 4);
v_quotContext_x3f_1495_ = lean_ctor_get(v___y_1359_, 5);
v_currMacroScope_1496_ = lean_ctor_get(v___y_1359_, 6);
v_snap_x3f_1497_ = lean_ctor_get(v___y_1359_, 8);
v_cancelTk_x3f_1498_ = lean_ctor_get(v___y_1359_, 9);
v_suppressElabErrors_1499_ = lean_ctor_get_uint8(v___y_1359_, sizeof(void*)*10);
v_ref_1500_ = l_Lean_replaceRef(v___x_1487_, v_a_1489_);
lean_dec(v_a_1489_);
lean_dec_ref_known(v___x_1487_, 3);
lean_inc(v_cancelTk_x3f_1498_);
lean_inc(v_snap_x3f_1497_);
lean_inc(v_currMacroScope_1496_);
lean_inc(v_quotContext_x3f_1495_);
lean_inc(v_macroStack_1494_);
lean_inc(v_cmdPos_1493_);
lean_inc(v_currRecDepth_1492_);
lean_inc_ref(v_fileMap_1491_);
lean_inc_ref(v_fileName_1490_);
v___x_1501_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1501_, 0, v_fileName_1490_);
lean_ctor_set(v___x_1501_, 1, v_fileMap_1491_);
lean_ctor_set(v___x_1501_, 2, v_currRecDepth_1492_);
lean_ctor_set(v___x_1501_, 3, v_cmdPos_1493_);
lean_ctor_set(v___x_1501_, 4, v_macroStack_1494_);
lean_ctor_set(v___x_1501_, 5, v_quotContext_x3f_1495_);
lean_ctor_set(v___x_1501_, 6, v_currMacroScope_1496_);
lean_ctor_set(v___x_1501_, 7, v_ref_1500_);
lean_ctor_set(v___x_1501_, 8, v_snap_x3f_1497_);
lean_ctor_set(v___x_1501_, 9, v_cancelTk_x3f_1498_);
lean_ctor_set_uint8(v___x_1501_, sizeof(void*)*10, v_suppressElabErrors_1499_);
v___x_1502_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(v_alts_1480_, v___x_1154_, v___f_1478_, v___x_1501_, v___y_1358_);
lean_dec_ref_known(v___x_1501_, 10);
lean_dec_ref(v_alts_1480_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
v_a_1511_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1502_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1502_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1487_, 3);
lean_dec_ref(v_alts_1480_);
lean_dec_ref(v___f_1478_);
return v___x_1488_;
}
}
}
}
}
v___jp_1519_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1523_ = lean_unsigned_to_nat(1u);
v___x_1524_ = l_Lean_Syntax_getArg(v_stx_1103_, v___x_1523_);
v___x_1525_ = l_Lean_Syntax_isNone(v___x_1524_);
if (v___x_1525_ == 0)
{
uint8_t v___x_1526_; 
lean_inc(v___x_1524_);
v___x_1526_ = l_Lean_Syntax_matchesNull(v___x_1524_, v___x_1523_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; 
lean_dec(v___x_1524_);
lean_dec(v_doc_x3f_1520_);
lean_dec(v_stx_1103_);
v___x_1527_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1527_;
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1528_ = l_Lean_Syntax_getArg(v___x_1524_, v___x_1223_);
lean_dec(v___x_1524_);
v___x_1529_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15));
lean_inc(v___x_1528_);
v___x_1530_ = l_Lean_Syntax_isOfKind(v___x_1528_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; 
lean_dec(v___x_1528_);
lean_dec(v_doc_x3f_1520_);
lean_dec(v_stx_1103_);
v___x_1531_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1531_;
}
else
{
lean_object* v___x_1532_; lean_object* v_attrs_x3f_1533_; lean_object* v___x_1534_; 
v___x_1532_ = l_Lean_Syntax_getArg(v___x_1528_, v___x_1523_);
lean_dec(v___x_1528_);
v_attrs_x3f_1533_ = l_Lean_Syntax_getArgs(v___x_1532_);
lean_dec(v___x_1532_);
v___x_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_attrs_x3f_1533_);
v___y_1357_ = v_doc_x3f_1520_;
v___y_1358_ = v___y_1522_;
v___y_1359_ = v___y_1521_;
v___y_1360_ = v___x_1523_;
v_attrs_x3f_1361_ = v___x_1534_;
goto v___jp_1356_;
}
}
}
else
{
lean_object* v___x_1535_; 
lean_dec(v___x_1524_);
v___x_1535_ = lean_box(0);
v___y_1357_ = v_doc_x3f_1520_;
v___y_1358_ = v___y_1522_;
v___y_1359_ = v___y_1521_;
v___y_1360_ = v___x_1523_;
v_attrs_x3f_1361_ = v___x_1535_;
goto v___jp_1356_;
}
}
}
v___jp_1107_:
{
if (v___y_1113_ == 0)
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1111_, v___y_1110_, v___y_1112_, v___y_1108_);
return v___x_1114_;
}
else
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1111_, v___y_1109_, v___y_1112_, v___y_1108_);
return v___x_1115_;
}
}
v___jp_1116_:
{
if (v___y_1122_ == 0)
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1121_, v___y_1119_, v___y_1120_, v___y_1118_);
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1121_, v___y_1117_, v___y_1120_, v___y_1118_);
return v___x_1124_;
}
}
v___jp_1125_:
{
if (v___y_1131_ == 0)
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1129_, v___y_1130_, v___y_1128_, v___y_1126_);
return v___x_1132_;
}
else
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1129_, v___y_1127_, v___y_1128_, v___y_1126_);
return v___x_1133_;
}
}
v___jp_1134_:
{
if (v___y_1140_ == 0)
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1135_, v___y_1137_, v___y_1139_, v___y_1136_);
return v___x_1141_;
}
else
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1135_, v___y_1138_, v___y_1139_, v___y_1136_);
return v___x_1142_;
}
}
v___jp_1143_:
{
if (v___y_1149_ == 0)
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1144_, v___y_1146_, v___y_1148_, v___y_1145_);
return v___x_1150_;
}
else
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1144_, v___y_1147_, v___y_1148_, v___y_1145_);
return v___x_1151_;
}
}
v___jp_1157_:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_inc_ref_n(v___y_1158_, 3);
v___x_1173_ = l_Array_append___redArg(v___y_1158_, v___y_1172_);
lean_dec_ref(v___y_1172_);
lean_inc_n(v___y_1170_, 6);
lean_inc_n(v___y_1161_, 17);
v___x_1174_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1174_, 0, v___y_1161_);
lean_ctor_set(v___x_1174_, 1, v___y_1170_);
lean_ctor_set(v___x_1174_, 2, v___x_1173_);
v___x_1175_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
lean_inc_ref_n(v___y_1168_, 2);
v___x_1176_ = l_Lean_Name_mkStr4(v___x_1152_, v___x_1153_, v___y_1168_, v___x_1175_);
v___x_1177_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
v___x_1178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___y_1161_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = l_Array_append___redArg(v___y_1158_, v___y_1162_);
lean_dec_ref(v___y_1162_);
v___x_1180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1180_, 0, v___y_1161_);
lean_ctor_set(v___x_1180_, 1, v___y_1170_);
lean_ctor_set(v___x_1180_, 2, v___x_1179_);
v___x_1181_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
v___x_1182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___y_1161_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = l_Lean_Syntax_node3(v___y_1161_, v___x_1176_, v___x_1178_, v___x_1180_, v___x_1182_);
v___x_1184_ = l_Lean_Syntax_node1(v___y_1161_, v___y_1170_, v___x_1183_);
lean_inc_ref(v___y_1163_);
v___x_1185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___y_1161_);
lean_ctor_set(v___x_1185_, 1, v___y_1163_);
v___x_1186_ = l_Lean_TSyntax_getId(v___y_1164_);
v___x_1187_ = l_Lean_mkIdentFrom(v___y_1165_, v___x_1186_, v___x_1156_);
lean_dec(v___y_1165_);
v___x_1188_ = l_Lean_Syntax_node2(v___y_1161_, v___y_1170_, v___x_1187_, v___y_1164_);
v___x_1189_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__6));
v___x_1190_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___y_1161_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
v___x_1191_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__8, &l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8);
v___x_1192_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__9));
v___x_1193_ = l_Lean_addMacroScope(v___y_1160_, v___x_1192_, v___y_1171_);
v___x_1194_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6));
v___x_1195_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1195_, 0, v___y_1161_);
lean_ctor_set(v___x_1195_, 1, v___x_1191_);
lean_ctor_set(v___x_1195_, 2, v___x_1193_);
lean_ctor_set(v___x_1195_, 3, v___x_1194_);
v___x_1196_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
v___x_1197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___y_1161_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__11));
v___x_1199_ = l_Lean_Name_mkStr4(v___x_1152_, v___x_1153_, v___y_1168_, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___y_1161_);
lean_ctor_set(v___x_1200_, 1, v___x_1198_);
v___x_1201_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7));
v___x_1202_ = l_Lean_Name_mkStr4(v___x_1152_, v___x_1153_, v___y_1168_, v___x_1201_);
v___x_1203_ = l_Lean_Syntax_node1(v___y_1161_, v___y_1170_, v___y_1169_);
v___x_1204_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1204_, 0, v___y_1161_);
lean_ctor_set(v___x_1204_, 1, v___y_1170_);
lean_ctor_set(v___x_1204_, 2, v___y_1158_);
v___x_1205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13));
v___x_1206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___y_1161_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = l_Lean_Syntax_node4(v___y_1161_, v___x_1202_, v___x_1203_, v___x_1204_, v___x_1206_, v___y_1166_);
v___x_1208_ = l_Lean_Syntax_node2(v___y_1161_, v___x_1199_, v___x_1200_, v___x_1207_);
v___x_1209_ = lean_unsigned_to_nat(9u);
v___x_1210_ = lean_mk_empty_array_with_capacity(v___x_1209_);
v___x_1211_ = lean_array_push(v___x_1210_, v___x_1174_);
v___x_1212_ = lean_array_push(v___x_1211_, v___x_1184_);
v___x_1213_ = lean_array_push(v___x_1212_, v___y_1167_);
v___x_1214_ = lean_array_push(v___x_1213_, v___x_1185_);
v___x_1215_ = lean_array_push(v___x_1214_, v___x_1188_);
v___x_1216_ = lean_array_push(v___x_1215_, v___x_1190_);
v___x_1217_ = lean_array_push(v___x_1216_, v___x_1195_);
v___x_1218_ = lean_array_push(v___x_1217_, v___x_1197_);
v___x_1219_ = lean_array_push(v___x_1218_, v___x_1208_);
lean_inc(v___y_1159_);
v___x_1220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1220_, 0, v___y_1161_);
lean_ctor_set(v___x_1220_, 1, v___y_1159_);
lean_ctor_set(v___x_1220_, 2, v___x_1219_);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___boxed(lean_object* v_stx_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_Elab_Command_elabMacroRules___lam__1(v_stx_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules(lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v___f_1558_; lean_object* v___x_1559_; 
v___f_1558_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___closed__0));
v___x_1559_ = l_Lean_Elab_Command_adaptExpander(v___f_1558_, v_a_1554_, v_a_1555_, v_a_1556_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___boxed(lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_Elab_Command_elabMacroRules(v_a_1560_, v_a_1561_, v_a_1562_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1(){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1572_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1573_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1));
v___x_1574_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1));
v___x_1575_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___boxed), 4, 0);
v___x_1576_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1572_, v___x_1573_, v___x_1574_, v___x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___boxed(lean_object* v_a_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1();
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3(){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1605_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1));
v___x_1606_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6));
v___x_1607_ = l_Lean_addBuiltinDeclarationRanges(v___x_1605_, v___x_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___boxed(lean_object* v_a_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3();
return v_res_1609_;
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
