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
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t l_Lean_Elab_Command_checkRuleKind(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
v___x_37_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
v___x_42_ = lean_alloc_ctor(0, 10, 0);
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
lean_object* v___x_59_; lean_object* v_env_60_; lean_object* v___x_61_; lean_object* v_scopes_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v_opts_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_59_ = lean_st_ref_get(v___y_57_);
v_env_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc_ref(v_env_60_);
lean_dec(v___x_59_);
v___x_61_ = lean_st_ref_get(v___y_57_);
v_scopes_62_ = lean_ctor_get(v___x_61_, 2);
lean_inc(v_scopes_62_);
lean_dec(v___x_61_);
v___x_63_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_64_ = l_List_head_x21___redArg(v___x_63_, v_scopes_62_);
lean_dec(v_scopes_62_);
v_opts_65_ = lean_ctor_get(v___x_64_, 1);
lean_inc_ref(v_opts_65_);
lean_dec(v___x_64_);
v___x_66_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_67_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5);
v___x_68_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_68_, 0, v_env_60_);
lean_ctor_set(v___x_68_, 1, v___x_66_);
lean_ctor_set(v___x_68_, 2, v___x_67_);
lean_ctor_set(v___x_68_, 3, v_opts_65_);
v___x_69_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v_msgData_56_);
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msgData_71_, v___y_72_);
lean_dec(v___y_72_);
return v_res_74_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_box(1);
v___x_76_ = l_Lean_MessageData_ofFormat(v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__2));
v___x_81_ = l_Lean_MessageData_ofFormat(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8(lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
return v_x_82_;
}
else
{
lean_object* v_head_84_; lean_object* v_tail_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_107_; 
v_head_84_ = lean_ctor_get(v_x_83_, 0);
v_tail_85_ = lean_ctor_get(v_x_83_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v_x_83_);
if (v_isSharedCheck_107_ == 0)
{
v___x_87_ = v_x_83_;
v_isShared_88_ = v_isSharedCheck_107_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_tail_85_);
lean_inc(v_head_84_);
lean_dec(v_x_83_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_107_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v_before_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_105_; 
v_before_89_ = lean_ctor_get(v_head_84_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v_head_84_);
if (v_isSharedCheck_105_ == 0)
{
lean_object* v_unused_106_; 
v_unused_106_ = lean_ctor_get(v_head_84_, 1);
lean_dec(v_unused_106_);
v___x_91_ = v_head_84_;
v_isShared_92_ = v_isSharedCheck_105_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_before_89_);
lean_dec(v_head_84_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_105_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_93_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0);
if (v_isShared_92_ == 0)
{
lean_ctor_set_tag(v___x_91_, 7);
lean_ctor_set(v___x_91_, 1, v___x_93_);
lean_ctor_set(v___x_91_, 0, v_x_82_);
v___x_95_ = v___x_91_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_x_82_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v___x_93_);
v___x_95_ = v_reuseFailAlloc_104_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_96_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3);
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 7);
lean_ctor_set(v___x_87_, 1, v___x_96_);
lean_ctor_set(v___x_87_, 0, v___x_95_);
v___x_98_ = v___x_87_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_95_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___x_96_);
v___x_98_ = v_reuseFailAlloc_103_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = l_Lean_MessageData_ofSyntax(v_before_89_);
v___x_100_ = l_Lean_indentD(v___x_99_);
v___x_101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_98_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v_x_82_ = v___x_101_;
v_x_83_ = v_tail_85_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(lean_object* v_opts_108_, lean_object* v_opt_109_){
_start:
{
lean_object* v_name_110_; lean_object* v_defValue_111_; lean_object* v_map_112_; lean_object* v___x_113_; 
v_name_110_ = lean_ctor_get(v_opt_109_, 0);
v_defValue_111_ = lean_ctor_get(v_opt_109_, 1);
v_map_112_ = lean_ctor_get(v_opts_108_, 0);
v___x_113_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_112_, v_name_110_);
if (lean_obj_tag(v___x_113_) == 0)
{
uint8_t v___x_114_; 
v___x_114_ = lean_unbox(v_defValue_111_);
return v___x_114_;
}
else
{
lean_object* v_val_115_; 
v_val_115_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_val_115_);
lean_dec_ref_known(v___x_113_, 1);
if (lean_obj_tag(v_val_115_) == 1)
{
uint8_t v_v_116_; 
v_v_116_ = lean_ctor_get_uint8(v_val_115_, 0);
lean_dec_ref_known(v_val_115_, 0);
return v_v_116_;
}
else
{
uint8_t v___x_117_; 
lean_dec(v_val_115_);
v___x_117_ = lean_unbox(v_defValue_111_);
return v___x_117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_opts_118_, lean_object* v_opt_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(v_opts_118_, v_opt_119_);
lean_dec_ref(v_opt_119_);
lean_dec_ref(v_opts_118_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__1));
v___x_126_ = l_Lean_MessageData_ofFormat(v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(lean_object* v_msgData_127_, lean_object* v_macroStack_128_, lean_object* v___y_129_){
_start:
{
lean_object* v___x_131_; lean_object* v_scopes_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v_opts_135_; lean_object* v___x_136_; uint8_t v___x_137_; uint8_t v___x_138_; 
v___x_131_ = lean_st_ref_get(v___y_129_);
v_scopes_132_ = lean_ctor_get(v___x_131_, 2);
lean_inc(v_scopes_132_);
lean_dec(v___x_131_);
v___x_133_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_134_ = l_List_head_x21___redArg(v___x_133_, v_scopes_132_);
lean_dec(v_scopes_132_);
v_opts_135_ = lean_ctor_get(v___x_134_, 1);
lean_inc_ref(v_opts_135_);
lean_dec(v___x_134_);
v___x_136_ = l_Lean_Elab_pp_macroStack;
v___x_137_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(v_opts_135_, v___x_136_);
lean_dec_ref(v_opts_135_);
v___x_138_ = lean_bool_not(v___x_137_);
if (v___x_138_ == 0)
{
if (lean_obj_tag(v_macroStack_128_) == 0)
{
lean_object* v___x_139_; 
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v_msgData_127_);
return v___x_139_;
}
else
{
lean_object* v_head_140_; lean_object* v_after_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_156_; 
v_head_140_ = lean_ctor_get(v_macroStack_128_, 0);
lean_inc(v_head_140_);
v_after_141_ = lean_ctor_get(v_head_140_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v_head_140_);
if (v_isSharedCheck_156_ == 0)
{
lean_object* v_unused_157_; 
v_unused_157_ = lean_ctor_get(v_head_140_, 0);
lean_dec(v_unused_157_);
v___x_143_ = v_head_140_;
v_isShared_144_ = v_isSharedCheck_156_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_after_141_);
lean_dec(v_head_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_156_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_145_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0);
if (v_isShared_144_ == 0)
{
lean_ctor_set_tag(v___x_143_, 7);
lean_ctor_set(v___x_143_, 1, v___x_145_);
lean_ctor_set(v___x_143_, 0, v_msgData_127_);
v___x_147_ = v___x_143_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_msgData_127_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v___x_145_);
v___x_147_ = v_reuseFailAlloc_155_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v_msgData_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_148_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2);
v___x_149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v___x_150_ = l_Lean_MessageData_ofSyntax(v_after_141_);
v___x_151_ = l_Lean_indentD(v___x_150_);
v_msgData_152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_152_, 0, v___x_149_);
lean_ctor_set(v_msgData_152_, 1, v___x_151_);
v___x_153_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8(v_msgData_152_, v_macroStack_128_);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
}
}
else
{
lean_object* v___x_158_; 
lean_dec(v_macroStack_128_);
v___x_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_158_, 0, v_msgData_127_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_msgData_159_, lean_object* v_macroStack_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_msgData_159_, v_macroStack_160_, v___y_161_);
lean_dec(v___y_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(lean_object* v_msg_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_Elab_Command_getRef___redArg(v___y_165_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v_macroStack_170_; lean_object* v___x_171_; lean_object* v_a_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_183_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_a_169_);
lean_dec_ref_known(v___x_168_, 1);
v_macroStack_170_ = lean_ctor_get(v___y_165_, 4);
v___x_171_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msg_164_, v___y_166_);
v_a_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_172_);
lean_dec_ref(v___x_171_);
v___x_173_ = l_Lean_Elab_getBetterRef(v_a_169_, v_macroStack_170_);
lean_dec(v_a_169_);
lean_inc(v_macroStack_170_);
v___x_174_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_a_172_, v_macroStack_170_, v___y_166_);
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_183_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_173_);
lean_ctor_set(v___x_179_, 1, v_a_175_);
if (v_isShared_178_ == 0)
{
lean_ctor_set_tag(v___x_177_, 1);
lean_ctor_set(v___x_177_, 0, v___x_179_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
lean_dec_ref(v_msg_164_);
v_a_184_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_168_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_168_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg___boxed(lean_object* v_msg_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(lean_object* v_ref_197_, lean_object* v_msg_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Elab_Command_getRef___redArg(v___y_199_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v_fileName_204_; lean_object* v_fileMap_205_; lean_object* v_currRecDepth_206_; lean_object* v_cmdPos_207_; lean_object* v_macroStack_208_; lean_object* v_quotContext_x3f_209_; lean_object* v_currMacroScope_210_; lean_object* v_snap_x3f_211_; lean_object* v_cancelTk_x3f_212_; uint8_t v_suppressElabErrors_213_; lean_object* v_ref_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
lean_dec_ref_known(v___x_202_, 1);
v_fileName_204_ = lean_ctor_get(v___y_199_, 0);
v_fileMap_205_ = lean_ctor_get(v___y_199_, 1);
v_currRecDepth_206_ = lean_ctor_get(v___y_199_, 2);
v_cmdPos_207_ = lean_ctor_get(v___y_199_, 3);
v_macroStack_208_ = lean_ctor_get(v___y_199_, 4);
v_quotContext_x3f_209_ = lean_ctor_get(v___y_199_, 5);
v_currMacroScope_210_ = lean_ctor_get(v___y_199_, 6);
v_snap_x3f_211_ = lean_ctor_get(v___y_199_, 8);
v_cancelTk_x3f_212_ = lean_ctor_get(v___y_199_, 9);
v_suppressElabErrors_213_ = lean_ctor_get_uint8(v___y_199_, sizeof(void*)*10);
v_ref_214_ = l_Lean_replaceRef(v_ref_197_, v_a_203_);
lean_dec(v_a_203_);
lean_inc(v_cancelTk_x3f_212_);
lean_inc(v_snap_x3f_211_);
lean_inc(v_currMacroScope_210_);
lean_inc(v_quotContext_x3f_209_);
lean_inc(v_macroStack_208_);
lean_inc(v_cmdPos_207_);
lean_inc(v_currRecDepth_206_);
lean_inc_ref(v_fileMap_205_);
lean_inc_ref(v_fileName_204_);
v___x_215_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_215_, 0, v_fileName_204_);
lean_ctor_set(v___x_215_, 1, v_fileMap_205_);
lean_ctor_set(v___x_215_, 2, v_currRecDepth_206_);
lean_ctor_set(v___x_215_, 3, v_cmdPos_207_);
lean_ctor_set(v___x_215_, 4, v_macroStack_208_);
lean_ctor_set(v___x_215_, 5, v_quotContext_x3f_209_);
lean_ctor_set(v___x_215_, 6, v_currMacroScope_210_);
lean_ctor_set(v___x_215_, 7, v_ref_214_);
lean_ctor_set(v___x_215_, 8, v_snap_x3f_211_);
lean_ctor_set(v___x_215_, 9, v_cancelTk_x3f_212_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*10, v_suppressElabErrors_213_);
v___x_216_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_198_, v___x_215_, v___y_200_);
lean_dec_ref_known(v___x_215_, 10);
return v___x_216_;
}
else
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
lean_dec_ref(v_msg_198_);
v_a_217_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_202_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_202_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg___boxed(lean_object* v_ref_225_, lean_object* v_msg_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_ref_225_, v_msg_226_, v___y_227_, v___y_228_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v_ref_225_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(lean_object* v_k_234_, lean_object* v_as_235_, size_t v_sz_236_, size_t v_i_237_, lean_object* v_b_238_){
_start:
{
uint8_t v___x_239_; 
v___x_239_ = lean_usize_dec_lt(v_i_237_, v_sz_236_);
if (v___x_239_ == 0)
{
lean_dec(v_k_234_);
lean_inc_ref(v_b_238_);
return v_b_238_;
}
else
{
lean_object* v___x_240_; lean_object* v_a_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_240_ = lean_box(0);
v_a_241_ = lean_array_uget_borrowed(v_as_235_, v_i_237_);
lean_inc(v_a_241_);
v___x_242_ = l_Lean_Syntax_getKind(v_a_241_);
lean_inc(v_k_234_);
v___x_243_ = l_Lean_Elab_Command_checkRuleKind(v___x_242_, v_k_234_);
lean_dec(v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; size_t v___x_245_; size_t v___x_246_; 
v___x_244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0));
v___x_245_ = ((size_t)1ULL);
v___x_246_ = lean_usize_add(v_i_237_, v___x_245_);
v_i_237_ = v___x_246_;
v_b_238_ = v___x_244_;
goto _start;
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v_k_234_);
lean_inc(v_a_241_);
v___x_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_248_, 0, v_a_241_);
v___x_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_240_);
return v___x_250_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___boxed(lean_object* v_k_251_, lean_object* v_as_252_, lean_object* v_sz_253_, lean_object* v_i_254_, lean_object* v_b_255_){
_start:
{
size_t v_sz_boxed_256_; size_t v_i_boxed_257_; lean_object* v_res_258_; 
v_sz_boxed_256_ = lean_unbox_usize(v_sz_253_);
lean_dec(v_sz_253_);
v_i_boxed_257_ = lean_unbox_usize(v_i_254_);
lean_dec(v_i_254_);
v_res_258_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(v_k_251_, v_as_252_, v_sz_boxed_256_, v_i_boxed_257_, v_b_255_);
lean_dec_ref(v_b_255_);
lean_dec_ref(v_as_252_);
return v_res_258_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__0));
v___x_261_ = l_Lean_stringToMessageData(v___x_260_);
return v___x_261_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__2));
v___x_264_ = l_Lean_stringToMessageData(v___x_263_);
return v___x_264_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12(void){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Array_mkArray0(lean_box(0));
return v___x_278_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__16));
v___x_285_ = l_Lean_stringToMessageData(v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(lean_object* v_k_286_, size_t v_sz_287_, size_t v_i_288_, lean_object* v_bs_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
uint8_t v___x_293_; 
v___x_293_ = lean_usize_dec_lt(v_i_288_, v_sz_287_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; 
lean_dec(v_k_286_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v_bs_289_);
return v___x_294_;
}
else
{
lean_object* v_v_295_; lean_object* v___x_296_; lean_object* v_bs_x27_297_; lean_object* v_a_299_; lean_object* v___y_305_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_v_295_ = lean_array_uget(v_bs_289_, v_i_288_);
v___x_296_ = lean_unsigned_to_nat(0u);
v_bs_x27_297_ = lean_array_uset(v_bs_289_, v_i_288_, v___x_296_);
v___x_324_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8));
lean_inc(v_v_295_);
v___x_325_ = l_Lean_Syntax_isOfKind(v_v_295_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
lean_dec(v_v_295_);
v___x_326_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
v___y_305_ = v___x_326_;
goto v___jp_304_;
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_327_ = lean_unsigned_to_nat(1u);
v___x_328_ = l_Lean_Syntax_getArg(v_v_295_, v___x_327_);
lean_inc(v___x_328_);
v___x_329_ = l_Lean_Syntax_matchesNull(v___x_328_, v___x_327_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
lean_dec(v___x_328_);
lean_dec(v_v_295_);
v___x_330_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
v___y_305_ = v___x_330_;
goto v___jp_304_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v_pat_349_; lean_object* v___y_351_; lean_object* v___y_352_; uint8_t v___x_404_; uint8_t v___x_405_; 
v___x_331_ = l_Lean_Syntax_getArg(v___x_328_, v___x_296_);
lean_dec(v___x_328_);
v___x_332_ = lean_unsigned_to_nat(3u);
v___x_333_ = l_Lean_Syntax_getArg(v_v_295_, v___x_332_);
v___x_347_ = l_Lean_Syntax_getArgs(v___x_331_);
lean_dec(v___x_331_);
v___x_348_ = lean_box(0);
v_pat_349_ = lean_array_get(v___x_348_, v___x_347_, v___x_296_);
v___x_404_ = l_Lean_Syntax_isQuot(v_pat_349_);
v___x_405_ = lean_bool_not(v___x_404_);
if (v___x_405_ == 0)
{
v___y_351_ = v___y_290_;
v___y_352_ = v___y_291_;
goto v___jp_350_;
}
else
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
if (lean_obj_tag(v___x_406_) == 0)
{
lean_dec_ref_known(v___x_406_, 1);
v___y_351_ = v___y_290_;
v___y_352_ = v___y_291_;
goto v___jp_350_;
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec(v_pat_349_);
lean_dec_ref(v___x_347_);
lean_dec(v___x_333_);
lean_dec_ref(v_bs_x27_297_);
lean_dec(v_v_295_);
lean_dec(v_k_286_);
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
v___jp_334_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9));
lean_inc_n(v___y_335_, 4);
v___x_338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_338_, 0, v___y_335_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_340_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
v___x_341_ = l_Array_append___redArg(v___x_340_, v___y_336_);
lean_dec_ref(v___y_336_);
v___x_342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_342_, 0, v___y_335_);
lean_ctor_set(v___x_342_, 1, v___x_339_);
lean_ctor_set(v___x_342_, 2, v___x_341_);
v___x_343_ = l_Lean_Syntax_node1(v___y_335_, v___x_339_, v___x_342_);
v___x_344_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13));
v___x_345_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_345_, 0, v___y_335_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = l_Lean_Syntax_node4(v___y_335_, v___x_324_, v___x_338_, v___x_343_, v___x_345_, v___x_333_);
v_a_299_ = v___x_346_;
goto v___jp_298_;
}
v___jp_350_:
{
lean_object* v_quoted_353_; lean_object* v_k_x27_354_; uint8_t v___x_355_; 
lean_inc(v_pat_349_);
v_quoted_353_ = l_Lean_Syntax_getQuotContent(v_pat_349_);
lean_inc(v_quoted_353_);
v_k_x27_354_ = l_Lean_Syntax_getKind(v_quoted_353_);
lean_inc(v_k_286_);
v___x_355_ = l_Lean_Elab_Command_checkRuleKind(v_k_x27_354_, v_k_286_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__15));
v___x_357_ = lean_name_eq(v_k_x27_354_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
lean_dec(v_quoted_353_);
lean_dec(v_pat_349_);
lean_dec_ref(v___x_347_);
lean_dec(v___x_333_);
v___x_358_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17);
v___x_359_ = l_Lean_MessageData_ofName(v_k_x27_354_);
v___x_360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3);
v___x_362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_v_295_, v___x_362_, v___y_351_, v___y_352_);
lean_dec(v_v_295_);
v___y_305_ = v___x_363_;
goto v___jp_304_;
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; size_t v_sz_366_; size_t v___x_367_; lean_object* v___x_368_; lean_object* v_fst_369_; 
lean_dec(v_k_x27_354_);
v___x_364_ = l_Lean_Syntax_getArgs(v_quoted_353_);
lean_dec(v_quoted_353_);
v___x_365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0));
v_sz_366_ = lean_array_size(v___x_364_);
v___x_367_ = ((size_t)0ULL);
lean_inc(v_k_286_);
v___x_368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(v_k_286_, v___x_364_, v_sz_366_, v___x_367_, v___x_365_);
lean_dec_ref(v___x_364_);
v_fst_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_fst_369_);
lean_dec_ref(v___x_368_);
if (lean_obj_tag(v_fst_369_) == 0)
{
lean_dec(v_pat_349_);
lean_dec_ref(v___x_347_);
lean_dec(v___x_333_);
v___y_316_ = v___y_351_;
v___y_317_ = v___y_352_;
goto v___jp_315_;
}
else
{
lean_object* v_val_370_; 
v_val_370_ = lean_ctor_get(v_fst_369_, 0);
lean_inc(v_val_370_);
lean_dec_ref_known(v_fst_369_, 1);
if (lean_obj_tag(v_val_370_) == 0)
{
lean_dec(v_pat_349_);
lean_dec_ref(v___x_347_);
lean_dec(v___x_333_);
v___y_316_ = v___y_351_;
v___y_317_ = v___y_352_;
goto v___jp_315_;
}
else
{
lean_object* v_val_371_; lean_object* v___x_372_; 
lean_dec(v_v_295_);
v_val_371_ = lean_ctor_get(v_val_370_, 0);
lean_inc(v_val_371_);
lean_dec_ref_known(v_val_370_, 1);
v___x_372_ = l_Lean_Elab_Command_getRef___redArg(v___y_351_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_374_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_373_);
lean_dec_ref_known(v___x_372_, 1);
v___x_374_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_351_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_quotContext_x3f_375_; lean_object* v_pat_376_; lean_object* v_pats_377_; lean_object* v___x_378_; 
lean_dec_ref_known(v___x_374_, 1);
v_quotContext_x3f_375_ = lean_ctor_get(v___y_351_, 5);
v_pat_376_ = l_Lean_Syntax_setArg(v_pat_349_, v___x_327_, v_val_371_);
v_pats_377_ = lean_array_set(v___x_347_, v___x_296_, v_pat_376_);
v___x_378_ = l_Lean_SourceInfo_fromRef(v_a_373_, v___x_355_);
lean_dec(v_a_373_);
if (lean_obj_tag(v_quotContext_x3f_375_) == 0)
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_352_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_dec_ref_known(v___x_379_, 1);
v___y_335_ = v___x_378_;
v___y_336_ = v_pats_377_;
goto v___jp_334_;
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec(v___x_378_);
lean_dec_ref(v_pats_377_);
lean_dec(v___x_333_);
lean_dec_ref(v_bs_x27_297_);
lean_dec(v_k_286_);
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
else
{
v___y_335_ = v___x_378_;
v___y_336_ = v_pats_377_;
goto v___jp_334_;
}
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec(v_a_373_);
lean_dec(v_val_371_);
lean_dec(v_pat_349_);
lean_dec_ref(v___x_347_);
lean_dec(v___x_333_);
lean_dec_ref(v_bs_x27_297_);
lean_dec(v_k_286_);
v_a_388_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_374_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_374_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_dec(v_val_371_);
lean_dec(v_pat_349_);
lean_dec_ref(v___x_347_);
lean_dec(v___x_333_);
lean_dec_ref(v_bs_x27_297_);
lean_dec(v_k_286_);
v_a_396_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_372_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_372_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_x27_354_);
lean_dec(v_quoted_353_);
lean_dec(v_pat_349_);
lean_dec_ref(v___x_347_);
lean_dec(v___x_333_);
v_a_299_ = v_v_295_;
goto v___jp_298_;
}
}
}
}
v___jp_298_:
{
size_t v___x_300_; size_t v___x_301_; lean_object* v___x_302_; 
v___x_300_ = ((size_t)1ULL);
v___x_301_ = lean_usize_add(v_i_288_, v___x_300_);
v___x_302_ = lean_array_uset(v_bs_x27_297_, v_i_288_, v_a_299_);
v_i_288_ = v___x_301_;
v_bs_289_ = v___x_302_;
goto _start;
}
v___jp_304_:
{
if (lean_obj_tag(v___y_305_) == 0)
{
lean_object* v_a_306_; 
v_a_306_ = lean_ctor_get(v___y_305_, 0);
lean_inc(v_a_306_);
lean_dec_ref_known(v___y_305_, 1);
v_a_299_ = v_a_306_;
goto v___jp_298_;
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec_ref(v_bs_x27_297_);
lean_dec(v_k_286_);
v_a_307_ = lean_ctor_get(v___y_305_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___y_305_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___y_305_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___y_305_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
v___jp_315_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_318_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1);
lean_inc(v_k_286_);
v___x_319_ = l_Lean_MessageData_ofName(v_k_286_);
v___x_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3);
v___x_322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_v_295_, v___x_322_, v___y_316_, v___y_317_);
lean_dec(v_v_295_);
v___y_305_ = v___x_323_;
goto v___jp_304_;
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
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_685_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_685_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_685_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_685_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v_a_624_; lean_object* v___x_633_; 
v___x_633_ = l_Lean_Elab_Command_getRef___redArg(v_a_497_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
v___x_635_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_497_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_quotContext_x3f_636_; uint8_t v___x_637_; lean_object* v___y_639_; lean_object* v___x_657_; 
lean_dec_ref_known(v___x_635_, 1);
v_quotContext_x3f_636_ = lean_ctor_get(v_a_497_, 5);
v___x_637_ = 0;
v___x_657_ = l_Lean_SourceInfo_fromRef(v_a_634_, v___x_637_);
lean_dec(v_a_634_);
if (lean_obj_tag(v_quotContext_x3f_636_) == 0)
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v_a_498_);
lean_dec_ref(v___x_676_);
goto v___jp_658_;
}
else
{
goto v___jp_658_;
}
v___jp_638_:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Elab_Command_getRef___redArg(v_a_497_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_642_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v___x_640_, 1);
v___x_642_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_497_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_642_, 1);
v___x_644_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_493_);
v___x_645_ = l_Lean_SourceInfo_fromRef(v_a_641_, v___x_637_);
lean_dec(v_a_641_);
if (lean_obj_tag(v_quotContext_x3f_636_) == 0)
{
lean_object* v___x_646_; lean_object* v_a_647_; 
v___x_646_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v_a_498_);
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref(v___x_646_);
v___y_620_ = v___y_639_;
v___y_621_ = v_a_643_;
v___y_622_ = v___x_645_;
v___y_623_ = v___x_644_;
v_a_624_ = v_a_647_;
goto v___jp_619_;
}
else
{
lean_object* v_val_648_; 
v_val_648_ = lean_ctor_get(v_quotContext_x3f_636_, 0);
lean_inc(v_val_648_);
v___y_620_ = v___y_639_;
v___y_621_ = v_a_643_;
v___y_622_ = v___x_645_;
v___y_623_ = v___x_644_;
v_a_624_ = v_val_648_;
goto v___jp_619_;
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec(v_a_641_);
lean_dec_ref(v___y_639_);
lean_del_object(v___x_505_);
lean_dec(v_a_503_);
lean_dec(v_k_495_);
lean_dec(v_attrKind_493_);
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
lean_dec_ref(v___y_639_);
lean_del_object(v___x_505_);
lean_dec(v_a_503_);
lean_dec(v_k_495_);
lean_dec(v_attrKind_493_);
lean_dec(v_doc_x3f_491_);
return v___x_640_;
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
v___y_639_ = v___x_670_;
goto v___jp_638_;
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
v___y_639_ = v___x_675_;
goto v___jp_638_;
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec(v_a_634_);
lean_del_object(v___x_505_);
lean_dec(v_a_503_);
lean_dec(v_k_495_);
lean_dec(v_attrKind_493_);
lean_dec(v_doc_x3f_491_);
v_a_677_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_635_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_635_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
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
lean_inc_ref_n(v___y_514_, 3);
v___x_519_ = l_Array_append___redArg(v___y_514_, v___y_518_);
lean_dec_ref(v___y_518_);
lean_inc_n(v___y_510_, 8);
lean_inc_n(v___y_517_, 29);
v___x_520_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_520_, 0, v___y_517_);
lean_ctor_set(v___x_520_, 1, v___y_510_);
lean_ctor_set(v___x_520_, 2, v___x_519_);
v___x_521_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5));
v___x_522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6));
v___x_523_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
lean_inc_ref_n(v___y_515_, 9);
v___x_524_ = l_Lean_Name_mkStr4(v___y_515_, v___x_521_, v___x_522_, v___x_523_);
v___x_525_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
v___x_526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_526_, 0, v___y_517_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = l_Array_append___redArg(v___y_514_, v___y_509_);
lean_dec_ref(v___y_509_);
v___x_528_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_528_, 0, v___y_517_);
lean_ctor_set(v___x_528_, 1, v___y_510_);
lean_ctor_set(v___x_528_, 2, v___x_527_);
v___x_529_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
v___x_530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_530_, 0, v___y_517_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = l_Lean_Syntax_node3(v___y_517_, v___x_524_, v___x_526_, v___x_528_, v___x_530_);
v___x_532_ = l_Lean_Syntax_node1(v___y_517_, v___y_510_, v___x_531_);
lean_inc_ref(v___y_508_);
v___x_533_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_533_, 0, v___y_517_);
lean_ctor_set(v___x_533_, 1, v___y_508_);
v___x_534_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__4, &l_Lean_Elab_Command_elabMacroRulesAux___closed__4_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__4);
v___x_535_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__5));
lean_inc_n(v___y_511_, 3);
lean_inc_n(v___y_512_, 3);
v___x_536_ = l_Lean_addMacroScope(v___y_512_, v___x_535_, v___y_511_);
v___x_537_ = lean_box(0);
v___x_538_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_538_, 0, v___y_517_);
lean_ctor_set(v___x_538_, 1, v___x_534_);
lean_ctor_set(v___x_538_, 2, v___x_536_);
lean_ctor_set(v___x_538_, 3, v___x_537_);
v___x_539_ = 1;
v___x_540_ = l_Lean_mkIdentFrom(v_tk_494_, v_k_495_, v___x_539_);
v___x_541_ = l_Lean_Syntax_node2(v___y_517_, v___y_510_, v___x_538_, v___x_540_);
v___x_542_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__6));
v___x_543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_543_, 0, v___y_517_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__7));
v___x_545_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__8, &l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8);
v___x_546_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__9));
v___x_547_ = l_Lean_addMacroScope(v___y_512_, v___x_546_, v___y_511_);
v___x_548_ = l_Lean_Name_mkStr2(v___y_515_, v___x_544_);
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
lean_ctor_set(v___x_553_, 0, v___y_517_);
lean_ctor_set(v___x_553_, 1, v___x_545_);
lean_ctor_set(v___x_553_, 2, v___x_547_);
lean_ctor_set(v___x_553_, 3, v___x_552_);
v___x_554_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
v___x_555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_555_, 0, v___y_517_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__11));
v___x_557_ = l_Lean_Name_mkStr4(v___y_515_, v___x_521_, v___x_522_, v___x_556_);
v___x_558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_558_, 0, v___y_517_);
lean_ctor_set(v___x_558_, 1, v___x_556_);
v___x_559_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__12));
v___x_560_ = l_Lean_Name_mkStr4(v___y_515_, v___x_521_, v___x_522_, v___x_559_);
v___x_561_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7));
v___x_562_ = l_Lean_Name_mkStr4(v___y_515_, v___x_521_, v___x_522_, v___x_561_);
v___x_563_ = l_Array_append___redArg(v___y_514_, v_a_503_);
lean_dec(v_a_503_);
v___x_564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9));
v___x_565_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_565_, 0, v___y_517_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__13));
v___x_567_ = l_Lean_Name_mkStr4(v___y_515_, v___x_521_, v___x_522_, v___x_566_);
v___x_568_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__14));
v___x_569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_569_, 0, v___y_517_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = l_Lean_Syntax_node1(v___y_517_, v___x_567_, v___x_569_);
v___x_571_ = l_Lean_Syntax_node1(v___y_517_, v___y_510_, v___x_570_);
v___x_572_ = l_Lean_Syntax_node1(v___y_517_, v___y_510_, v___x_571_);
v___x_573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13));
v___x_574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_574_, 0, v___y_517_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__15));
v___x_576_ = l_Lean_Name_mkStr4(v___y_515_, v___x_521_, v___x_522_, v___x_575_);
v___x_577_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__16));
v___x_578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_578_, 0, v___y_517_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__17));
v___x_580_ = l_Lean_Name_mkStr4(v___y_515_, v___x_521_, v___x_522_, v___x_579_);
v___x_581_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__19, &l_Lean_Elab_Command_elabMacroRulesAux___closed__19_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__19);
v___x_582_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__20));
v___x_583_ = l_Lean_addMacroScope(v___y_512_, v___x_582_, v___y_511_);
v___x_584_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__24));
v___x_585_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_585_, 0, v___y_517_);
lean_ctor_set(v___x_585_, 1, v___x_581_);
lean_ctor_set(v___x_585_, 2, v___x_583_);
lean_ctor_set(v___x_585_, 3, v___x_584_);
v___x_586_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__26, &l_Lean_Elab_Command_elabMacroRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__26);
v___x_587_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__27));
v___x_588_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__28));
v___x_589_ = l_Lean_Name_mkStr4(v___y_515_, v___x_544_, v___x_587_, v___x_588_);
lean_inc_n(v___x_589_, 2);
v___x_590_ = l_Lean_addMacroScope(v___y_512_, v___x_589_, v___y_511_);
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
lean_ctor_set(v___x_595_, 0, v___y_517_);
lean_ctor_set(v___x_595_, 1, v___x_586_);
lean_ctor_set(v___x_595_, 2, v___x_590_);
lean_ctor_set(v___x_595_, 3, v___x_594_);
v___x_596_ = l_Lean_Syntax_node1(v___y_517_, v___y_510_, v___x_595_);
v___x_597_ = l_Lean_Syntax_node2(v___y_517_, v___x_580_, v___x_585_, v___x_596_);
v___x_598_ = l_Lean_Syntax_node2(v___y_517_, v___x_576_, v___x_578_, v___x_597_);
v___x_599_ = l_Lean_Syntax_node4(v___y_517_, v___x_562_, v___x_565_, v___x_572_, v___x_574_, v___x_598_);
v___x_600_ = lean_array_push(v___x_563_, v___x_599_);
v___x_601_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_601_, 0, v___y_517_);
lean_ctor_set(v___x_601_, 1, v___y_510_);
lean_ctor_set(v___x_601_, 2, v___x_600_);
v___x_602_ = l_Lean_Syntax_node1(v___y_517_, v___x_560_, v___x_601_);
v___x_603_ = l_Lean_Syntax_node2(v___y_517_, v___x_557_, v___x_558_, v___x_602_);
v___x_604_ = lean_unsigned_to_nat(9u);
v___x_605_ = lean_mk_empty_array_with_capacity(v___x_604_);
v___x_606_ = lean_array_push(v___x_605_, v___x_520_);
v___x_607_ = lean_array_push(v___x_606_, v___x_532_);
v___x_608_ = lean_array_push(v___x_607_, v___y_516_);
v___x_609_ = lean_array_push(v___x_608_, v___x_533_);
v___x_610_ = lean_array_push(v___x_609_, v___x_541_);
v___x_611_ = lean_array_push(v___x_610_, v___x_543_);
v___x_612_ = lean_array_push(v___x_611_, v___x_553_);
v___x_613_ = lean_array_push(v___x_612_, v___x_555_);
v___x_614_ = lean_array_push(v___x_613_, v___x_603_);
lean_inc(v___y_513_);
v___x_615_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_615_, 0, v___y_517_);
lean_ctor_set(v___x_615_, 1, v___y_513_);
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
v___y_508_ = v___x_626_;
v___y_509_ = v___y_620_;
v___y_510_ = v___x_628_;
v___y_511_ = v___y_621_;
v___y_512_ = v_a_624_;
v___y_513_ = v___x_627_;
v___y_514_ = v___x_629_;
v___y_515_ = v___x_625_;
v___y_516_ = v___y_623_;
v___y_517_ = v___y_622_;
v___y_518_ = v___x_631_;
goto v___jp_507_;
}
else
{
lean_object* v___x_632_; 
lean_dec(v_doc_x3f_491_);
v___x_632_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__33));
v___y_508_ = v___x_626_;
v___y_509_ = v___y_620_;
v___y_510_ = v___x_628_;
v___y_511_ = v___y_621_;
v___y_512_ = v_a_624_;
v___y_513_ = v___x_627_;
v___y_514_ = v___x_629_;
v___y_515_ = v___x_625_;
v___y_516_ = v___y_623_;
v___y_517_ = v___y_622_;
v___y_518_ = v___x_632_;
goto v___jp_507_;
}
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_dec(v_k_495_);
lean_dec(v_attrKind_493_);
lean_dec(v_doc_x3f_491_);
v_a_686_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_502_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_502_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux___boxed(lean_object* v_doc_x3f_694_, lean_object* v_attrs_x3f_695_, lean_object* v_attrKind_696_, lean_object* v_tk_697_, lean_object* v_k_698_, lean_object* v_alts_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_Elab_Command_elabMacroRulesAux(v_doc_x3f_694_, v_attrs_x3f_695_, v_attrKind_696_, v_tk_697_, v_k_698_, v_alts_699_, v_a_700_, v_a_701_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
lean_dec(v_tk_697_);
lean_dec(v_attrs_x3f_695_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(lean_object* v_00_u03b1_704_, lean_object* v_ref_705_, lean_object* v_msg_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_ref_705_, v_msg_706_, v___y_707_, v___y_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___boxed(lean_object* v_00_u03b1_711_, lean_object* v_ref_712_, lean_object* v_msg_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(v_00_u03b1_711_, v_ref_712_, v_msg_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v_ref_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3(lean_object* v_msgData_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msgData_718_, v___y_720_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3(v_msgData_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(lean_object* v_00_u03b1_728_, lean_object* v_msg_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_729_, v___y_730_, v___y_731_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___boxed(lean_object* v_00_u03b1_734_, lean_object* v_msg_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(v_00_u03b1_734_, v_msg_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4(lean_object* v_msgData_740_, lean_object* v_macroStack_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_msgData_740_, v_macroStack_741_, v___y_743_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___boxed(lean_object* v_msgData_746_, lean_object* v_macroStack_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4(v_msgData_746_, v_macroStack_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(lean_object* v___y_752_, uint8_t v_isExporting_753_, lean_object* v_a_x3f_754_){
_start:
{
lean_object* v___x_756_; lean_object* v_env_757_; lean_object* v_messages_758_; lean_object* v_scopes_759_; lean_object* v_usedQuotCtxts_760_; lean_object* v_nextMacroScope_761_; lean_object* v_maxRecDepth_762_; lean_object* v_ngen_763_; lean_object* v_auxDeclNGen_764_; lean_object* v_infoState_765_; lean_object* v_traceState_766_; lean_object* v_snapshotTasks_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_778_; 
v___x_756_ = lean_st_ref_take(v___y_752_);
v_env_757_ = lean_ctor_get(v___x_756_, 0);
v_messages_758_ = lean_ctor_get(v___x_756_, 1);
v_scopes_759_ = lean_ctor_get(v___x_756_, 2);
v_usedQuotCtxts_760_ = lean_ctor_get(v___x_756_, 3);
v_nextMacroScope_761_ = lean_ctor_get(v___x_756_, 4);
v_maxRecDepth_762_ = lean_ctor_get(v___x_756_, 5);
v_ngen_763_ = lean_ctor_get(v___x_756_, 6);
v_auxDeclNGen_764_ = lean_ctor_get(v___x_756_, 7);
v_infoState_765_ = lean_ctor_get(v___x_756_, 8);
v_traceState_766_ = lean_ctor_get(v___x_756_, 9);
v_snapshotTasks_767_ = lean_ctor_get(v___x_756_, 10);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_778_ == 0)
{
v___x_769_ = v___x_756_;
v_isShared_770_ = v_isSharedCheck_778_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_snapshotTasks_767_);
lean_inc(v_traceState_766_);
lean_inc(v_infoState_765_);
lean_inc(v_auxDeclNGen_764_);
lean_inc(v_ngen_763_);
lean_inc(v_maxRecDepth_762_);
lean_inc(v_nextMacroScope_761_);
lean_inc(v_usedQuotCtxts_760_);
lean_inc(v_scopes_759_);
lean_inc(v_messages_758_);
lean_inc(v_env_757_);
lean_dec(v___x_756_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_778_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_771_ = l_Lean_Environment_setExporting(v_env_757_, v_isExporting_753_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_771_);
v___x_773_ = v___x_769_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_messages_758_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_scopes_759_);
lean_ctor_set(v_reuseFailAlloc_777_, 3, v_usedQuotCtxts_760_);
lean_ctor_set(v_reuseFailAlloc_777_, 4, v_nextMacroScope_761_);
lean_ctor_set(v_reuseFailAlloc_777_, 5, v_maxRecDepth_762_);
lean_ctor_set(v_reuseFailAlloc_777_, 6, v_ngen_763_);
lean_ctor_set(v_reuseFailAlloc_777_, 7, v_auxDeclNGen_764_);
lean_ctor_set(v_reuseFailAlloc_777_, 8, v_infoState_765_);
lean_ctor_set(v_reuseFailAlloc_777_, 9, v_traceState_766_);
lean_ctor_set(v_reuseFailAlloc_777_, 10, v_snapshotTasks_767_);
v___x_773_ = v_reuseFailAlloc_777_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_st_ref_set(v___y_752_, v___x_773_);
v___x_775_ = lean_box(0);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0___boxed(lean_object* v___y_779_, lean_object* v_isExporting_780_, lean_object* v_a_x3f_781_, lean_object* v___y_782_){
_start:
{
uint8_t v_isExporting_boxed_783_; lean_object* v_res_784_; 
v_isExporting_boxed_783_ = lean_unbox(v_isExporting_780_);
v_res_784_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_779_, v_isExporting_boxed_783_, v_a_x3f_781_);
lean_dec(v_a_x3f_781_);
lean_dec(v___y_779_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(lean_object* v_x_785_, uint8_t v_isExporting_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; lean_object* v_env_791_; uint8_t v_isExporting_792_; lean_object* v___x_793_; uint8_t v_isModule_794_; uint8_t v___y_847_; uint8_t v___x_849_; 
v___x_790_ = lean_st_ref_get(v___y_788_);
v_env_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc_ref(v_env_791_);
lean_dec(v___x_790_);
v_isExporting_792_ = lean_ctor_get_uint8(v_env_791_, sizeof(void*)*8);
v___x_793_ = l_Lean_Environment_header(v_env_791_);
lean_dec_ref(v_env_791_);
v_isModule_794_ = lean_ctor_get_uint8(v___x_793_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_793_);
v___x_849_ = lean_bool_not(v_isModule_794_);
if (v___x_849_ == 0)
{
if (v_isExporting_792_ == 0)
{
if (v_isExporting_786_ == 0)
{
lean_object* v___x_850_; 
lean_inc(v___y_788_);
lean_inc_ref(v___y_787_);
v___x_850_ = lean_apply_3(v_x_785_, v___y_787_, v___y_788_, lean_box(0));
return v___x_850_;
}
else
{
goto v___jp_795_;
}
}
else
{
v___y_847_ = v_isExporting_786_;
goto v___jp_846_;
}
}
else
{
v___y_847_ = v___x_849_;
goto v___jp_846_;
}
v___jp_795_:
{
lean_object* v___x_796_; lean_object* v_env_797_; lean_object* v_messages_798_; lean_object* v_scopes_799_; lean_object* v_usedQuotCtxts_800_; lean_object* v_nextMacroScope_801_; lean_object* v_maxRecDepth_802_; lean_object* v_ngen_803_; lean_object* v_auxDeclNGen_804_; lean_object* v_infoState_805_; lean_object* v_traceState_806_; lean_object* v_snapshotTasks_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_845_; 
v___x_796_ = lean_st_ref_take(v___y_788_);
v_env_797_ = lean_ctor_get(v___x_796_, 0);
v_messages_798_ = lean_ctor_get(v___x_796_, 1);
v_scopes_799_ = lean_ctor_get(v___x_796_, 2);
v_usedQuotCtxts_800_ = lean_ctor_get(v___x_796_, 3);
v_nextMacroScope_801_ = lean_ctor_get(v___x_796_, 4);
v_maxRecDepth_802_ = lean_ctor_get(v___x_796_, 5);
v_ngen_803_ = lean_ctor_get(v___x_796_, 6);
v_auxDeclNGen_804_ = lean_ctor_get(v___x_796_, 7);
v_infoState_805_ = lean_ctor_get(v___x_796_, 8);
v_traceState_806_ = lean_ctor_get(v___x_796_, 9);
v_snapshotTasks_807_ = lean_ctor_get(v___x_796_, 10);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_845_ == 0)
{
v___x_809_ = v___x_796_;
v_isShared_810_ = v_isSharedCheck_845_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_snapshotTasks_807_);
lean_inc(v_traceState_806_);
lean_inc(v_infoState_805_);
lean_inc(v_auxDeclNGen_804_);
lean_inc(v_ngen_803_);
lean_inc(v_maxRecDepth_802_);
lean_inc(v_nextMacroScope_801_);
lean_inc(v_usedQuotCtxts_800_);
lean_inc(v_scopes_799_);
lean_inc(v_messages_798_);
lean_inc(v_env_797_);
lean_dec(v___x_796_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_845_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_811_ = l_Lean_Environment_setExporting(v_env_797_, v_isExporting_786_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_811_);
v___x_813_ = v___x_809_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v_messages_798_);
lean_ctor_set(v_reuseFailAlloc_844_, 2, v_scopes_799_);
lean_ctor_set(v_reuseFailAlloc_844_, 3, v_usedQuotCtxts_800_);
lean_ctor_set(v_reuseFailAlloc_844_, 4, v_nextMacroScope_801_);
lean_ctor_set(v_reuseFailAlloc_844_, 5, v_maxRecDepth_802_);
lean_ctor_set(v_reuseFailAlloc_844_, 6, v_ngen_803_);
lean_ctor_set(v_reuseFailAlloc_844_, 7, v_auxDeclNGen_804_);
lean_ctor_set(v_reuseFailAlloc_844_, 8, v_infoState_805_);
lean_ctor_set(v_reuseFailAlloc_844_, 9, v_traceState_806_);
lean_ctor_set(v_reuseFailAlloc_844_, 10, v_snapshotTasks_807_);
v___x_813_ = v_reuseFailAlloc_844_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; lean_object* v_r_815_; 
v___x_814_ = lean_st_ref_set(v___y_788_, v___x_813_);
lean_inc(v___y_788_);
lean_inc_ref(v___y_787_);
v_r_815_ = lean_apply_3(v_x_785_, v___y_787_, v___y_788_, lean_box(0));
if (lean_obj_tag(v_r_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_832_; 
v_a_816_ = lean_ctor_get(v_r_815_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v_r_815_);
if (v_isSharedCheck_832_ == 0)
{
v___x_818_ = v_r_815_;
v_isShared_819_ = v_isSharedCheck_832_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v_r_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_832_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
lean_inc(v_a_816_);
if (v_isShared_819_ == 0)
{
lean_ctor_set_tag(v___x_818_, 1);
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_831_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
v___x_822_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_788_, v_isExporting_792_, v___x_821_);
lean_dec_ref(v___x_821_);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; 
v_unused_830_ = lean_ctor_get(v___x_822_, 0);
lean_dec(v_unused_830_);
v___x_824_ = v___x_822_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_dec(v___x_822_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v_a_816_);
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_816_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
v_a_833_ = lean_ctor_get(v_r_815_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v_r_815_, 1);
v___x_834_ = lean_box(0);
v___x_835_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_788_, v_isExporting_792_, v___x_834_);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v___x_835_, 0);
lean_dec(v_unused_843_);
v___x_837_ = v___x_835_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_dec(v___x_835_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set_tag(v___x_837_, 1);
lean_ctor_set(v___x_837_, 0, v_a_833_);
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_833_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
}
v___jp_846_:
{
if (v___y_847_ == 0)
{
goto v___jp_795_;
}
else
{
lean_object* v___x_848_; 
lean_inc(v___y_788_);
lean_inc_ref(v___y_787_);
v___x_848_ = lean_apply_3(v_x_785_, v___y_787_, v___y_788_, lean_box(0));
return v___x_848_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___boxed(lean_object* v_x_851_, lean_object* v_isExporting_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
uint8_t v_isExporting_boxed_856_; lean_object* v_res_857_; 
v_isExporting_boxed_856_ = lean_unbox(v_isExporting_852_);
v_res_857_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v_x_851_, v_isExporting_boxed_856_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0(lean_object* v_00_u03b1_858_, lean_object* v_x_859_, uint8_t v_isExporting_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v_x_859_, v_isExporting_860_, v___y_861_, v___y_862_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___boxed(lean_object* v_00_u03b1_865_, lean_object* v_x_866_, lean_object* v_isExporting_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
uint8_t v_isExporting_boxed_871_; lean_object* v_res_872_; 
v_isExporting_boxed_871_ = lean_unbox(v_isExporting_867_);
v_res_872_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0(v_00_u03b1_865_, v_x_866_, v_isExporting_boxed_871_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0(lean_object* v___x_873_, lean_object* v___x_874_, lean_object* v_doc_x3f_875_, lean_object* v_attrs_x3f_876_, lean_object* v_attrKind_877_, lean_object* v_tk_878_, lean_object* v_alts_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_Elab_Command_getRef___redArg(v___y_880_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v_fileName_885_; lean_object* v_fileMap_886_; lean_object* v_currRecDepth_887_; lean_object* v_cmdPos_888_; lean_object* v_macroStack_889_; lean_object* v_quotContext_x3f_890_; lean_object* v_currMacroScope_891_; lean_object* v_snap_x3f_892_; lean_object* v_cancelTk_x3f_893_; uint8_t v_suppressElabErrors_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_913_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
v_fileName_885_ = lean_ctor_get(v___y_880_, 0);
v_fileMap_886_ = lean_ctor_get(v___y_880_, 1);
v_currRecDepth_887_ = lean_ctor_get(v___y_880_, 2);
v_cmdPos_888_ = lean_ctor_get(v___y_880_, 3);
v_macroStack_889_ = lean_ctor_get(v___y_880_, 4);
v_quotContext_x3f_890_ = lean_ctor_get(v___y_880_, 5);
v_currMacroScope_891_ = lean_ctor_get(v___y_880_, 6);
v_snap_x3f_892_ = lean_ctor_get(v___y_880_, 8);
v_cancelTk_x3f_893_ = lean_ctor_get(v___y_880_, 9);
v_suppressElabErrors_894_ = lean_ctor_get_uint8(v___y_880_, sizeof(void*)*10);
v_isSharedCheck_913_ = !lean_is_exclusive(v___y_880_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; 
v_unused_914_ = lean_ctor_get(v___y_880_, 7);
lean_dec(v_unused_914_);
v___x_896_ = v___y_880_;
v_isShared_897_ = v_isSharedCheck_913_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_cancelTk_x3f_893_);
lean_inc(v_snap_x3f_892_);
lean_inc(v_currMacroScope_891_);
lean_inc(v_quotContext_x3f_890_);
lean_inc(v_macroStack_889_);
lean_inc(v_cmdPos_888_);
lean_inc(v_currRecDepth_887_);
lean_inc(v_fileMap_886_);
lean_inc(v_fileName_885_);
lean_dec(v___y_880_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_913_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_ref_898_; lean_object* v___x_900_; 
v_ref_898_ = l_Lean_replaceRef(v___x_873_, v_a_884_);
lean_dec(v_a_884_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 7, v_ref_898_);
v___x_900_ = v___x_896_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_fileName_885_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_fileMap_886_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_currRecDepth_887_);
lean_ctor_set(v_reuseFailAlloc_912_, 3, v_cmdPos_888_);
lean_ctor_set(v_reuseFailAlloc_912_, 4, v_macroStack_889_);
lean_ctor_set(v_reuseFailAlloc_912_, 5, v_quotContext_x3f_890_);
lean_ctor_set(v_reuseFailAlloc_912_, 6, v_currMacroScope_891_);
lean_ctor_set(v_reuseFailAlloc_912_, 7, v_ref_898_);
lean_ctor_set(v_reuseFailAlloc_912_, 8, v_snap_x3f_892_);
lean_ctor_set(v_reuseFailAlloc_912_, 9, v_cancelTk_x3f_893_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*10, v_suppressElabErrors_894_);
v___x_900_ = v_reuseFailAlloc_912_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_Elab_Command_resolveSyntaxKind(v___x_874_, v___x_900_, v___y_881_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_903_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_901_, 1);
v___x_903_ = l_Lean_Elab_Command_elabMacroRulesAux(v_doc_x3f_875_, v_attrs_x3f_876_, v_attrKind_877_, v_tk_878_, v_a_902_, v_alts_879_, v___x_900_, v___y_881_);
lean_dec_ref(v___x_900_);
return v___x_903_;
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec_ref(v___x_900_);
lean_dec_ref(v_alts_879_);
lean_dec(v_attrKind_877_);
lean_dec(v_doc_x3f_875_);
v_a_904_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_901_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_901_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_880_);
lean_dec_ref(v_alts_879_);
lean_dec(v_attrKind_877_);
lean_dec(v_doc_x3f_875_);
lean_dec(v___x_874_);
return v___x_883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0___boxed(lean_object* v___x_915_, lean_object* v___x_916_, lean_object* v_doc_x3f_917_, lean_object* v_attrs_x3f_918_, lean_object* v_attrKind_919_, lean_object* v_tk_920_, lean_object* v_alts_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_Elab_Command_elabMacroRules___lam__0(v___x_915_, v___x_916_, v_doc_x3f_917_, v_attrs_x3f_918_, v_attrKind_919_, v_tk_920_, v_alts_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec(v_tk_920_);
lean_dec(v_attrs_x3f_918_);
lean_dec(v___x_915_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5(lean_object* v___x_929_, lean_object* v___x_930_, lean_object* v_attrKind_931_, lean_object* v___x_932_, lean_object* v___x_933_, lean_object* v_attrs_x3f_934_, lean_object* v___x_935_, lean_object* v___x_936_, lean_object* v___x_937_, lean_object* v_doc_x3f_938_, lean_object* v_kind_x3f_939_, lean_object* v_alts_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_Elab_Command_getRef___redArg(v___y_941_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v___x_946_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_944_, 1);
v___x_946_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_941_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_1014_; 
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; 
v_unused_1015_ = lean_ctor_get(v___x_946_, 0);
lean_dec(v_unused_1015_);
v___x_948_ = v___x_946_;
v_isShared_949_ = v_isSharedCheck_1014_;
goto v_resetjp_947_;
}
else
{
lean_dec(v___x_946_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_1014_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v_quotContext_x3f_950_; uint8_t v___x_951_; lean_object* v___x_952_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; 
v_quotContext_x3f_950_ = lean_ctor_get(v___y_941_, 5);
v___x_951_ = 0;
v___x_952_ = l_Lean_SourceInfo_fromRef(v_a_945_, v___x_951_);
lean_dec(v_a_945_);
if (lean_obj_tag(v_quotContext_x3f_950_) == 0)
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_942_);
lean_dec_ref(v___x_1013_);
goto v___jp_1007_;
}
else
{
goto v___jp_1007_;
}
v___jp_953_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_967_; 
lean_inc_ref_n(v___y_957_, 2);
v___x_960_ = l_Array_append___redArg(v___y_957_, v___y_959_);
lean_dec_ref(v___y_959_);
lean_inc_n(v___y_954_, 2);
lean_inc_n(v___x_952_, 3);
v___x_961_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_961_, 0, v___x_952_);
lean_ctor_set(v___x_961_, 1, v___y_954_);
lean_ctor_set(v___x_961_, 2, v___x_960_);
v___x_962_ = l_Array_append___redArg(v___y_957_, v_alts_940_);
v___x_963_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_963_, 0, v___x_952_);
lean_ctor_set(v___x_963_, 1, v___y_954_);
lean_ctor_set(v___x_963_, 2, v___x_962_);
v___x_964_ = l_Lean_Syntax_node1(v___x_952_, v___x_929_, v___x_963_);
v___x_965_ = l_Lean_Syntax_node6(v___x_952_, v___x_930_, v___y_955_, v___y_958_, v_attrKind_931_, v___y_956_, v___x_961_, v___x_964_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_965_);
v___x_967_ = v___x_948_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
v___jp_969_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
lean_inc_ref(v___y_972_);
v___x_974_ = l_Array_append___redArg(v___y_972_, v___y_973_);
lean_dec_ref(v___y_973_);
lean_inc(v___y_970_);
lean_inc_n(v___x_952_, 2);
v___x_975_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_975_, 0, v___x_952_);
lean_ctor_set(v___x_975_, 1, v___y_970_);
lean_ctor_set(v___x_975_, 2, v___x_974_);
v___x_976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_952_);
lean_ctor_set(v___x_976_, 1, v___x_932_);
if (lean_obj_tag(v_kind_x3f_939_) == 0)
{
lean_object* v___x_977_; 
v___x_977_ = lean_mk_empty_array_with_capacity(v___x_933_);
v___y_954_ = v___y_970_;
v___y_955_ = v___y_971_;
v___y_956_ = v___x_976_;
v___y_957_ = v___y_972_;
v___y_958_ = v___x_975_;
v___y_959_ = v___x_977_;
goto v___jp_953_;
}
else
{
lean_object* v_val_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_val_978_ = lean_ctor_get(v_kind_x3f_939_, 0);
lean_inc(v_val_978_);
lean_dec_ref_known(v_kind_x3f_939_, 1);
v___x_979_ = l_Lean_mkIdent(v_val_978_);
v___x_980_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0));
lean_inc_n(v___x_952_, 4);
v___x_981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_952_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1));
v___x_983_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_952_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
v___x_985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_952_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2));
v___x_987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_952_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = l_Array_mkArray5___redArg(v___x_981_, v___x_983_, v___x_985_, v___x_979_, v___x_987_);
v___y_954_ = v___y_970_;
v___y_955_ = v___y_971_;
v___y_956_ = v___x_976_;
v___y_957_ = v___y_972_;
v___y_958_ = v___x_975_;
v___y_959_ = v___x_988_;
goto v___jp_953_;
}
}
v___jp_989_:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
lean_inc_ref(v___y_991_);
v___x_993_ = l_Array_append___redArg(v___y_991_, v___y_992_);
lean_dec_ref(v___y_992_);
lean_inc(v___y_990_);
lean_inc(v___x_952_);
v___x_994_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_994_, 0, v___x_952_);
lean_ctor_set(v___x_994_, 1, v___y_990_);
lean_ctor_set(v___x_994_, 2, v___x_993_);
if (lean_obj_tag(v_attrs_x3f_934_) == 1)
{
lean_object* v_val_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v_val_995_ = lean_ctor_get(v_attrs_x3f_934_, 0);
v___x_996_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
v___x_997_ = l_Lean_Name_mkStr4(v___x_935_, v___x_936_, v___x_937_, v___x_996_);
v___x_998_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
lean_inc_n(v___x_952_, 4);
v___x_999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_952_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
lean_inc_ref(v___y_991_);
v___x_1000_ = l_Array_append___redArg(v___y_991_, v_val_995_);
lean_inc(v___y_990_);
v___x_1001_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1001_, 0, v___x_952_);
lean_ctor_set(v___x_1001_, 1, v___y_990_);
lean_ctor_set(v___x_1001_, 2, v___x_1000_);
v___x_1002_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
v___x_1003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_952_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = l_Lean_Syntax_node3(v___x_952_, v___x_997_, v___x_999_, v___x_1001_, v___x_1003_);
v___x_1005_ = l_Array_mkArray1___redArg(v___x_1004_);
v___y_970_ = v___y_990_;
v___y_971_ = v___x_994_;
v___y_972_ = v___y_991_;
v___y_973_ = v___x_1005_;
goto v___jp_969_;
}
else
{
lean_object* v___x_1006_; 
lean_dec_ref(v___x_937_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v___x_935_);
v___x_1006_ = lean_mk_empty_array_with_capacity(v___x_933_);
v___y_970_ = v___y_990_;
v___y_971_ = v___x_994_;
v___y_972_ = v___y_991_;
v___y_973_ = v___x_1006_;
goto v___jp_969_;
}
}
v___jp_1007_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1009_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
if (lean_obj_tag(v_doc_x3f_938_) == 1)
{
lean_object* v_val_1010_; lean_object* v___x_1011_; 
v_val_1010_ = lean_ctor_get(v_doc_x3f_938_, 0);
lean_inc(v_val_1010_);
lean_dec_ref_known(v_doc_x3f_938_, 1);
v___x_1011_ = l_Array_mkArray1___redArg(v_val_1010_);
v___y_990_ = v___x_1008_;
v___y_991_ = v___x_1009_;
v___y_992_ = v___x_1011_;
goto v___jp_989_;
}
else
{
lean_object* v___x_1012_; 
lean_dec(v_doc_x3f_938_);
v___x_1012_ = lean_mk_empty_array_with_capacity(v___x_933_);
v___y_990_ = v___x_1008_;
v___y_991_ = v___x_1009_;
v___y_992_ = v___x_1012_;
goto v___jp_989_;
}
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec(v_a_945_);
lean_dec(v_kind_x3f_939_);
lean_dec(v_doc_x3f_938_);
lean_dec_ref(v___x_937_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_932_);
lean_dec(v_attrKind_931_);
lean_dec(v___x_930_);
lean_dec(v___x_929_);
v_a_1016_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_946_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_946_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
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
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v_kind_x3f_939_);
lean_dec(v_doc_x3f_938_);
lean_dec_ref(v___x_937_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_932_);
lean_dec(v_attrKind_931_);
lean_dec(v___x_930_);
lean_dec(v___x_929_);
v_a_1024_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_944_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_944_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5___boxed(lean_object* v___x_1032_, lean_object* v___x_1033_, lean_object* v_attrKind_1034_, lean_object* v___x_1035_, lean_object* v___x_1036_, lean_object* v_attrs_x3f_1037_, lean_object* v___x_1038_, lean_object* v___x_1039_, lean_object* v___x_1040_, lean_object* v_doc_x3f_1041_, lean_object* v_kind_x3f_1042_, lean_object* v_alts_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_Elab_Command_elabMacroRules___lam__5(v___x_1032_, v___x_1033_, v_attrKind_1034_, v___x_1035_, v___x_1036_, v_attrs_x3f_1037_, v___x_1038_, v___x_1039_, v___x_1040_, v_doc_x3f_1041_, v_kind_x3f_1042_, v_alts_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec_ref(v_alts_1043_);
lean_dec(v_attrs_x3f_1037_);
lean_dec(v___x_1036_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1(lean_object* v_stx_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; uint8_t v___y_1108_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; uint8_t v___y_1115_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; uint8_t v___y_1122_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; uint8_t v___y_1129_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; uint8_t v___y_1136_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; 
v___x_1139_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4));
v___x_1140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5));
v___x_1141_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0));
v___x_1142_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1));
lean_inc(v_stx_1100_);
v___x_1143_ = l_Lean_Syntax_isOfKind(v_stx_1100_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1209_; 
lean_dec(v_stx_1100_);
v___x_1209_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1209_;
}
else
{
lean_object* v___x_1210_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v_a_1223_; uint8_t v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; uint8_t v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v_attrs_x3f_1298_; lean_object* v_doc_x3f_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1210_ = lean_unsigned_to_nat(0u);
v___x_1502_ = l_Lean_Syntax_getArg(v_stx_1100_, v___x_1210_);
v___x_1503_ = l_Lean_Syntax_isNone(v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; uint8_t v___x_1505_; 
v___x_1504_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1502_);
v___x_1505_ = l_Lean_Syntax_matchesNull(v___x_1502_, v___x_1504_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; 
lean_dec(v___x_1502_);
lean_dec(v_stx_1100_);
v___x_1506_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1506_;
}
else
{
lean_object* v_doc_x3f_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v_doc_x3f_1507_ = l_Lean_Syntax_getArg(v___x_1502_, v___x_1210_);
lean_dec(v___x_1502_);
v___x_1508_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17));
lean_inc(v_doc_x3f_1507_);
v___x_1509_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1507_, v___x_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; 
lean_dec(v_doc_x3f_1507_);
lean_dec(v_stx_1100_);
v___x_1510_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1510_;
}
else
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_doc_x3f_1507_);
v_doc_x3f_1486_ = v___x_1511_;
v___y_1487_ = v___y_1101_;
v___y_1488_ = v___y_1102_;
goto v___jp_1485_;
}
}
}
else
{
lean_object* v___x_1512_; 
lean_dec(v___x_1502_);
v___x_1512_ = lean_box(0);
v_doc_x3f_1486_ = v___x_1512_;
v___y_1487_ = v___y_1101_;
v___y_1488_ = v___y_1102_;
goto v___jp_1485_;
}
v___jp_1211_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__31));
v___x_1225_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__32));
v___x_1226_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
if (lean_obj_tag(v___y_1213_) == 1)
{
lean_object* v_val_1227_; lean_object* v___x_1228_; 
v_val_1227_ = lean_ctor_get(v___y_1213_, 0);
lean_inc(v_val_1227_);
lean_dec_ref_known(v___y_1213_, 1);
v___x_1228_ = l_Array_mkArray1___redArg(v_val_1227_);
v___y_1145_ = v___y_1212_;
v___y_1146_ = v___x_1224_;
v___y_1147_ = v___x_1226_;
v___y_1148_ = v_a_1223_;
v___y_1149_ = v___y_1215_;
v___y_1150_ = v___y_1216_;
v___y_1151_ = v___y_1221_;
v___y_1152_ = v___y_1222_;
v___y_1153_ = v___y_1214_;
v___y_1154_ = v___y_1217_;
v___y_1155_ = v___y_1218_;
v___y_1156_ = v___y_1219_;
v___y_1157_ = v___x_1225_;
v___y_1158_ = v___y_1220_;
v___y_1159_ = v___x_1228_;
goto v___jp_1144_;
}
else
{
lean_object* v___x_1229_; 
lean_dec(v___y_1213_);
v___x_1229_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__33));
v___y_1145_ = v___y_1212_;
v___y_1146_ = v___x_1224_;
v___y_1147_ = v___x_1226_;
v___y_1148_ = v_a_1223_;
v___y_1149_ = v___y_1215_;
v___y_1150_ = v___y_1216_;
v___y_1151_ = v___y_1221_;
v___y_1152_ = v___y_1222_;
v___y_1153_ = v___y_1214_;
v___y_1154_ = v___y_1217_;
v___y_1155_ = v___y_1218_;
v___y_1156_ = v___y_1219_;
v___y_1157_ = v___x_1225_;
v___y_1158_ = v___y_1220_;
v___y_1159_ = v___x_1229_;
goto v___jp_1144_;
}
}
v___jp_1230_:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_Elab_Command_getRef___redArg(v___y_1234_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1246_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
v___x_1246_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1234_);
lean_dec_ref(v___y_1234_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v___x_1248_ = l_Lean_Parser_Command_visibility_ofAttrKind(v___y_1235_);
v___x_1249_ = l_Lean_SourceInfo_fromRef(v_a_1245_, v___y_1231_);
lean_dec(v_a_1245_);
if (lean_obj_tag(v___y_1239_) == 0)
{
lean_object* v___x_1250_; lean_object* v_a_1251_; 
v___x_1250_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_1236_);
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref(v___x_1250_);
v___y_1212_ = v___y_1243_;
v___y_1213_ = v___y_1238_;
v___y_1214_ = v___x_1249_;
v___y_1215_ = v___y_1232_;
v___y_1216_ = v___y_1233_;
v___y_1217_ = v___y_1240_;
v___y_1218_ = v___x_1248_;
v___y_1219_ = v___y_1241_;
v___y_1220_ = v___y_1242_;
v___y_1221_ = v_a_1247_;
v___y_1222_ = v___y_1237_;
v_a_1223_ = v_a_1251_;
goto v___jp_1211_;
}
else
{
lean_object* v_val_1252_; 
v_val_1252_ = lean_ctor_get(v___y_1239_, 0);
lean_inc(v_val_1252_);
v___y_1212_ = v___y_1243_;
v___y_1213_ = v___y_1238_;
v___y_1214_ = v___x_1249_;
v___y_1215_ = v___y_1232_;
v___y_1216_ = v___y_1233_;
v___y_1217_ = v___y_1240_;
v___y_1218_ = v___x_1248_;
v___y_1219_ = v___y_1241_;
v___y_1220_ = v___y_1242_;
v___y_1221_ = v_a_1247_;
v___y_1222_ = v___y_1237_;
v_a_1223_ = v_val_1252_;
goto v___jp_1211_;
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec(v_a_1245_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1235_);
lean_dec(v___y_1233_);
lean_dec(v___y_1232_);
v_a_1253_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1246_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1246_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
else
{
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec(v___y_1232_);
return v___x_1244_;
}
}
v___jp_1261_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1277_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__34));
lean_inc_ref(v___y_1269_);
v___x_1278_ = l_Lean_Name_mkStr4(v___x_1139_, v___x_1140_, v___y_1269_, v___x_1277_);
v___x_1279_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__37));
v___x_1280_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__38));
lean_inc_n(v___y_1276_, 2);
v___x_1281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___y_1276_);
lean_ctor_set(v___x_1281_, 1, v___x_1279_);
lean_inc(v___y_1264_);
v___x_1282_ = l_Lean_Syntax_node2(v___y_1276_, v___x_1280_, v___x_1281_, v___y_1264_);
lean_inc(v___y_1266_);
v___x_1283_ = l_Lean_Syntax_node2(v___y_1276_, v___x_1278_, v___y_1266_, v___x_1282_);
if (lean_obj_tag(v___y_1271_) == 0)
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1284_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_1285_ = lean_mk_empty_array_with_capacity(v___y_1267_);
v___x_1286_ = lean_array_push(v___x_1285_, v___x_1283_);
v___x_1287_ = l_Lean_Syntax_SepArray_ofElems(v___x_1284_, v___x_1286_);
lean_dec_ref(v___x_1286_);
v___y_1231_ = v___y_1262_;
v___y_1232_ = v___y_1263_;
v___y_1233_ = v___y_1264_;
v___y_1234_ = v___y_1265_;
v___y_1235_ = v___y_1266_;
v___y_1236_ = v___y_1268_;
v___y_1237_ = v___y_1269_;
v___y_1238_ = v___y_1270_;
v___y_1239_ = v___y_1272_;
v___y_1240_ = v___y_1273_;
v___y_1241_ = v___y_1274_;
v___y_1242_ = v___y_1275_;
v___y_1243_ = v___x_1287_;
goto v___jp_1230_;
}
else
{
lean_object* v_val_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v_val_1288_ = lean_ctor_get(v___y_1271_, 0);
lean_inc(v_val_1288_);
lean_dec_ref_known(v___y_1271_, 1);
v___x_1289_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_1290_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1288_);
lean_dec(v_val_1288_);
v___x_1291_ = lean_array_push(v___x_1290_, v___x_1283_);
v___x_1292_ = l_Lean_Syntax_SepArray_ofElems(v___x_1289_, v___x_1291_);
lean_dec_ref(v___x_1291_);
v___y_1231_ = v___y_1262_;
v___y_1232_ = v___y_1263_;
v___y_1233_ = v___y_1264_;
v___y_1234_ = v___y_1265_;
v___y_1235_ = v___y_1266_;
v___y_1236_ = v___y_1268_;
v___y_1237_ = v___y_1269_;
v___y_1238_ = v___y_1270_;
v___y_1239_ = v___y_1272_;
v___y_1240_ = v___y_1273_;
v___y_1241_ = v___y_1274_;
v___y_1242_ = v___y_1275_;
v___y_1243_ = v___x_1292_;
goto v___jp_1230_;
}
}
v___jp_1293_:
{
lean_object* v___x_1299_; lean_object* v_attrKind_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1299_ = lean_unsigned_to_nat(2u);
v_attrKind_1300_ = l_Lean_Syntax_getArg(v_stx_1100_, v___x_1299_);
v___x_1301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6));
v___x_1302_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9));
lean_inc(v_attrKind_1300_);
v___x_1303_ = l_Lean_Syntax_isOfKind(v_attrKind_1300_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; 
lean_dec(v_attrKind_1300_);
lean_dec(v_attrs_x3f_1298_);
lean_dec(v___y_1295_);
lean_dec(v_stx_1100_);
v___x_1304_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1304_;
}
else
{
lean_object* v___x_1305_; lean_object* v_tk_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1305_ = lean_unsigned_to_nat(3u);
v_tk_1306_ = l_Lean_Syntax_getArg(v_stx_1100_, v___x_1305_);
v___x_1307_ = lean_unsigned_to_nat(4u);
v___x_1308_ = l_Lean_Syntax_getArg(v_stx_1100_, v___x_1307_);
lean_inc(v___x_1308_);
v___x_1309_ = l_Lean_Syntax_matchesNull(v___x_1308_, v___x_1210_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1308_);
v___x_1311_ = l_Lean_Syntax_matchesNull(v___x_1308_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; 
lean_dec(v___x_1308_);
lean_dec(v_tk_1306_);
lean_dec(v_attrKind_1300_);
lean_dec(v_attrs_x3f_1298_);
lean_dec(v___y_1295_);
lean_dec(v_stx_1100_);
v___x_1312_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1312_;
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1313_ = l_Lean_Syntax_getArg(v_stx_1100_, v___x_1310_);
lean_dec(v_stx_1100_);
v___x_1314_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10));
lean_inc(v___x_1313_);
v___x_1315_ = l_Lean_Syntax_isOfKind(v___x_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; 
lean_dec(v___x_1313_);
lean_dec(v___x_1308_);
lean_dec(v_tk_1306_);
lean_dec(v_attrKind_1300_);
lean_dec(v_attrs_x3f_1298_);
lean_dec(v___y_1295_);
v___x_1316_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1316_;
}
else
{
lean_object* v_kind_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v_kind_1317_ = l_Lean_Syntax_getArg(v___x_1308_, v___x_1305_);
lean_dec(v___x_1308_);
v___x_1318_ = l_Lean_Syntax_getArg(v___x_1313_, v___x_1210_);
lean_dec(v___x_1313_);
lean_inc(v___x_1318_);
v___x_1319_ = l_Lean_Syntax_matchesNull(v___x_1318_, v___y_1297_);
if (v___x_1319_ == 0)
{
lean_object* v_alts_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___f_1329_; 
v_alts_1320_ = l_Lean_Syntax_getArgs(v___x_1318_);
lean_dec(v___x_1318_);
v___x_1321_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1322_ = lean_box(2);
lean_inc_ref(v_alts_1320_);
v___x_1323_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
lean_ctor_set(v___x_1323_, 1, v___x_1321_);
lean_ctor_set(v___x_1323_, 2, v_alts_1320_);
v___x_1324_ = lean_mk_empty_array_with_capacity(v___x_1299_);
lean_inc(v_tk_1306_);
v___x_1325_ = lean_array_push(v___x_1324_, v_tk_1306_);
v___x_1326_ = lean_array_push(v___x_1325_, v___x_1323_);
v___x_1327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1322_);
lean_ctor_set(v___x_1327_, 1, v___x_1321_);
lean_ctor_set(v___x_1327_, 2, v___x_1326_);
v___x_1328_ = l_Lean_TSyntax_getId(v_kind_1317_);
lean_dec(v_kind_1317_);
lean_inc(v_attrKind_1300_);
v___f_1329_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1329_, 0, v___x_1327_);
lean_closure_set(v___f_1329_, 1, v___x_1328_);
lean_closure_set(v___f_1329_, 2, v___y_1295_);
lean_closure_set(v___f_1329_, 3, v_attrs_x3f_1298_);
lean_closure_set(v___f_1329_, 4, v_attrKind_1300_);
lean_closure_set(v___f_1329_, 5, v_tk_1306_);
lean_closure_set(v___f_1329_, 6, v_alts_1320_);
if (v___x_1303_ == 0)
{
lean_dec(v_attrKind_1300_);
v___y_1119_ = v___f_1329_;
v___y_1120_ = v___y_1294_;
v___y_1121_ = v___y_1296_;
v___y_1122_ = v___x_1319_;
goto v___jp_1118_;
}
else
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = l_Lean_Syntax_getArg(v_attrKind_1300_, v___x_1210_);
lean_dec(v_attrKind_1300_);
lean_inc(v___x_1330_);
v___x_1331_ = l_Lean_Syntax_matchesNull(v___x_1330_, v___y_1297_);
if (v___x_1331_ == 0)
{
lean_dec(v___x_1330_);
v___y_1119_ = v___f_1329_;
v___y_1120_ = v___y_1294_;
v___y_1121_ = v___y_1296_;
v___y_1122_ = v___x_1331_;
goto v___jp_1118_;
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1332_ = l_Lean_Syntax_getArg(v___x_1330_, v___x_1210_);
lean_dec(v___x_1330_);
v___x_1333_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1334_ = l_Lean_Syntax_isOfKind(v___x_1332_, v___x_1333_);
if (v___x_1334_ == 0)
{
v___y_1119_ = v___f_1329_;
v___y_1120_ = v___y_1294_;
v___y_1121_ = v___y_1296_;
v___y_1122_ = v___x_1334_;
goto v___jp_1118_;
}
else
{
v___y_1119_ = v___f_1329_;
v___y_1120_ = v___y_1294_;
v___y_1121_ = v___y_1296_;
v___y_1122_ = v___x_1143_;
goto v___jp_1118_;
}
}
}
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1335_ = l_Lean_Syntax_getArg(v___x_1318_, v___x_1210_);
v___x_1336_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8));
lean_inc(v___x_1335_);
v___x_1337_ = l_Lean_Syntax_isOfKind(v___x_1335_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_object* v_alts_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___f_1347_; 
lean_dec(v___x_1335_);
v_alts_1338_ = l_Lean_Syntax_getArgs(v___x_1318_);
lean_dec(v___x_1318_);
v___x_1339_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1340_ = lean_box(2);
lean_inc_ref(v_alts_1338_);
v___x_1341_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set(v___x_1341_, 1, v___x_1339_);
lean_ctor_set(v___x_1341_, 2, v_alts_1338_);
v___x_1342_ = lean_mk_empty_array_with_capacity(v___x_1299_);
lean_inc(v_tk_1306_);
v___x_1343_ = lean_array_push(v___x_1342_, v_tk_1306_);
v___x_1344_ = lean_array_push(v___x_1343_, v___x_1341_);
v___x_1345_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1340_);
lean_ctor_set(v___x_1345_, 1, v___x_1339_);
lean_ctor_set(v___x_1345_, 2, v___x_1344_);
v___x_1346_ = l_Lean_TSyntax_getId(v_kind_1317_);
lean_dec(v_kind_1317_);
lean_inc(v_attrKind_1300_);
v___f_1347_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1347_, 0, v___x_1345_);
lean_closure_set(v___f_1347_, 1, v___x_1346_);
lean_closure_set(v___f_1347_, 2, v___y_1295_);
lean_closure_set(v___f_1347_, 3, v_attrs_x3f_1298_);
lean_closure_set(v___f_1347_, 4, v_attrKind_1300_);
lean_closure_set(v___f_1347_, 5, v_tk_1306_);
lean_closure_set(v___f_1347_, 6, v_alts_1338_);
if (v___x_1303_ == 0)
{
lean_dec(v_attrKind_1300_);
v___y_1126_ = v___y_1294_;
v___y_1127_ = v___f_1347_;
v___y_1128_ = v___y_1296_;
v___y_1129_ = v___x_1337_;
goto v___jp_1125_;
}
else
{
lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1348_ = l_Lean_Syntax_getArg(v_attrKind_1300_, v___x_1210_);
lean_dec(v_attrKind_1300_);
lean_inc(v___x_1348_);
v___x_1349_ = l_Lean_Syntax_matchesNull(v___x_1348_, v___y_1297_);
if (v___x_1349_ == 0)
{
lean_dec(v___x_1348_);
v___y_1126_ = v___y_1294_;
v___y_1127_ = v___f_1347_;
v___y_1128_ = v___y_1296_;
v___y_1129_ = v___x_1349_;
goto v___jp_1125_;
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1350_ = l_Lean_Syntax_getArg(v___x_1348_, v___x_1210_);
lean_dec(v___x_1348_);
v___x_1351_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1352_ = l_Lean_Syntax_isOfKind(v___x_1350_, v___x_1351_);
if (v___x_1352_ == 0)
{
v___y_1126_ = v___y_1294_;
v___y_1127_ = v___f_1347_;
v___y_1128_ = v___y_1296_;
v___y_1129_ = v___x_1352_;
goto v___jp_1125_;
}
else
{
v___y_1126_ = v___y_1294_;
v___y_1127_ = v___f_1347_;
v___y_1128_ = v___y_1296_;
v___y_1129_ = v___x_1143_;
goto v___jp_1125_;
}
}
}
}
else
{
lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1353_ = l_Lean_Syntax_getArg(v___x_1335_, v___y_1297_);
lean_inc(v___x_1353_);
v___x_1354_ = l_Lean_Syntax_matchesNull(v___x_1353_, v___y_1297_);
if (v___x_1354_ == 0)
{
lean_object* v_alts_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___f_1364_; 
lean_dec(v___x_1353_);
lean_dec(v___x_1335_);
v_alts_1355_ = l_Lean_Syntax_getArgs(v___x_1318_);
lean_dec(v___x_1318_);
v___x_1356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1357_ = lean_box(2);
lean_inc_ref(v_alts_1355_);
v___x_1358_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v___x_1356_);
lean_ctor_set(v___x_1358_, 2, v_alts_1355_);
v___x_1359_ = lean_mk_empty_array_with_capacity(v___x_1299_);
lean_inc(v_tk_1306_);
v___x_1360_ = lean_array_push(v___x_1359_, v_tk_1306_);
v___x_1361_ = lean_array_push(v___x_1360_, v___x_1358_);
v___x_1362_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1357_);
lean_ctor_set(v___x_1362_, 1, v___x_1356_);
lean_ctor_set(v___x_1362_, 2, v___x_1361_);
v___x_1363_ = l_Lean_TSyntax_getId(v_kind_1317_);
lean_dec(v_kind_1317_);
lean_inc(v_attrKind_1300_);
v___f_1364_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1364_, 0, v___x_1362_);
lean_closure_set(v___f_1364_, 1, v___x_1363_);
lean_closure_set(v___f_1364_, 2, v___y_1295_);
lean_closure_set(v___f_1364_, 3, v_attrs_x3f_1298_);
lean_closure_set(v___f_1364_, 4, v_attrKind_1300_);
lean_closure_set(v___f_1364_, 5, v_tk_1306_);
lean_closure_set(v___f_1364_, 6, v_alts_1355_);
if (v___x_1303_ == 0)
{
lean_dec(v_attrKind_1300_);
v___y_1112_ = v___f_1364_;
v___y_1113_ = v___y_1294_;
v___y_1114_ = v___y_1296_;
v___y_1115_ = v___x_1354_;
goto v___jp_1111_;
}
else
{
lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1365_ = l_Lean_Syntax_getArg(v_attrKind_1300_, v___x_1210_);
lean_dec(v_attrKind_1300_);
lean_inc(v___x_1365_);
v___x_1366_ = l_Lean_Syntax_matchesNull(v___x_1365_, v___y_1297_);
if (v___x_1366_ == 0)
{
lean_dec(v___x_1365_);
v___y_1112_ = v___f_1364_;
v___y_1113_ = v___y_1294_;
v___y_1114_ = v___y_1296_;
v___y_1115_ = v___x_1366_;
goto v___jp_1111_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1367_ = l_Lean_Syntax_getArg(v___x_1365_, v___x_1210_);
lean_dec(v___x_1365_);
v___x_1368_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1369_ = l_Lean_Syntax_isOfKind(v___x_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
v___y_1112_ = v___f_1364_;
v___y_1113_ = v___y_1294_;
v___y_1114_ = v___y_1296_;
v___y_1115_ = v___x_1369_;
goto v___jp_1111_;
}
else
{
v___y_1112_ = v___f_1364_;
v___y_1113_ = v___y_1294_;
v___y_1114_ = v___y_1296_;
v___y_1115_ = v___x_1143_;
goto v___jp_1111_;
}
}
}
}
else
{
lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1370_ = l_Lean_Syntax_getArg(v___x_1353_, v___x_1210_);
lean_dec(v___x_1353_);
lean_inc(v___x_1370_);
v___x_1371_ = l_Lean_Syntax_matchesNull(v___x_1370_, v___y_1297_);
if (v___x_1371_ == 0)
{
lean_object* v_alts_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___f_1381_; 
lean_dec(v___x_1370_);
lean_dec(v___x_1335_);
v_alts_1372_ = l_Lean_Syntax_getArgs(v___x_1318_);
lean_dec(v___x_1318_);
v___x_1373_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1374_ = lean_box(2);
lean_inc_ref(v_alts_1372_);
v___x_1375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v___x_1373_);
lean_ctor_set(v___x_1375_, 2, v_alts_1372_);
v___x_1376_ = lean_mk_empty_array_with_capacity(v___x_1299_);
lean_inc(v_tk_1306_);
v___x_1377_ = lean_array_push(v___x_1376_, v_tk_1306_);
v___x_1378_ = lean_array_push(v___x_1377_, v___x_1375_);
v___x_1379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1374_);
lean_ctor_set(v___x_1379_, 1, v___x_1373_);
lean_ctor_set(v___x_1379_, 2, v___x_1378_);
v___x_1380_ = l_Lean_TSyntax_getId(v_kind_1317_);
lean_dec(v_kind_1317_);
lean_inc(v_attrKind_1300_);
v___f_1381_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1381_, 0, v___x_1379_);
lean_closure_set(v___f_1381_, 1, v___x_1380_);
lean_closure_set(v___f_1381_, 2, v___y_1295_);
lean_closure_set(v___f_1381_, 3, v_attrs_x3f_1298_);
lean_closure_set(v___f_1381_, 4, v_attrKind_1300_);
lean_closure_set(v___f_1381_, 5, v_tk_1306_);
lean_closure_set(v___f_1381_, 6, v_alts_1372_);
if (v___x_1303_ == 0)
{
lean_dec(v_attrKind_1300_);
v___y_1133_ = v___y_1294_;
v___y_1134_ = v___y_1296_;
v___y_1135_ = v___f_1381_;
v___y_1136_ = v___x_1371_;
goto v___jp_1132_;
}
else
{
lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1382_ = l_Lean_Syntax_getArg(v_attrKind_1300_, v___x_1210_);
lean_dec(v_attrKind_1300_);
lean_inc(v___x_1382_);
v___x_1383_ = l_Lean_Syntax_matchesNull(v___x_1382_, v___y_1297_);
if (v___x_1383_ == 0)
{
lean_dec(v___x_1382_);
v___y_1133_ = v___y_1294_;
v___y_1134_ = v___y_1296_;
v___y_1135_ = v___f_1381_;
v___y_1136_ = v___x_1383_;
goto v___jp_1132_;
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1384_ = l_Lean_Syntax_getArg(v___x_1382_, v___x_1210_);
lean_dec(v___x_1382_);
v___x_1385_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1386_ = l_Lean_Syntax_isOfKind(v___x_1384_, v___x_1385_);
if (v___x_1386_ == 0)
{
v___y_1133_ = v___y_1294_;
v___y_1134_ = v___y_1296_;
v___y_1135_ = v___f_1381_;
v___y_1136_ = v___x_1386_;
goto v___jp_1132_;
}
else
{
v___y_1133_ = v___y_1294_;
v___y_1134_ = v___y_1296_;
v___y_1135_ = v___f_1381_;
v___y_1136_ = v___x_1143_;
goto v___jp_1132_;
}
}
}
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1387_ = l_Lean_Syntax_getArg(v___x_1370_, v___x_1210_);
lean_dec(v___x_1370_);
v___x_1388_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14));
lean_inc(v___x_1387_);
v___x_1389_ = l_Lean_Syntax_isOfKind(v___x_1387_, v___x_1388_);
if (v___x_1389_ == 0)
{
lean_object* v_alts_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___f_1399_; 
lean_dec(v___x_1387_);
lean_dec(v___x_1335_);
v_alts_1390_ = l_Lean_Syntax_getArgs(v___x_1318_);
lean_dec(v___x_1318_);
v___x_1391_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1392_ = lean_box(2);
lean_inc_ref(v_alts_1390_);
v___x_1393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
lean_ctor_set(v___x_1393_, 1, v___x_1391_);
lean_ctor_set(v___x_1393_, 2, v_alts_1390_);
v___x_1394_ = lean_mk_empty_array_with_capacity(v___x_1299_);
lean_inc(v_tk_1306_);
v___x_1395_ = lean_array_push(v___x_1394_, v_tk_1306_);
v___x_1396_ = lean_array_push(v___x_1395_, v___x_1393_);
v___x_1397_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1392_);
lean_ctor_set(v___x_1397_, 1, v___x_1391_);
lean_ctor_set(v___x_1397_, 2, v___x_1396_);
v___x_1398_ = l_Lean_TSyntax_getId(v_kind_1317_);
lean_dec(v_kind_1317_);
lean_inc(v_attrKind_1300_);
v___f_1399_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1399_, 0, v___x_1397_);
lean_closure_set(v___f_1399_, 1, v___x_1398_);
lean_closure_set(v___f_1399_, 2, v___y_1295_);
lean_closure_set(v___f_1399_, 3, v_attrs_x3f_1298_);
lean_closure_set(v___f_1399_, 4, v_attrKind_1300_);
lean_closure_set(v___f_1399_, 5, v_tk_1306_);
lean_closure_set(v___f_1399_, 6, v_alts_1390_);
if (v___x_1303_ == 0)
{
lean_dec(v_attrKind_1300_);
v___y_1105_ = v___f_1399_;
v___y_1106_ = v___y_1294_;
v___y_1107_ = v___y_1296_;
v___y_1108_ = v___x_1389_;
goto v___jp_1104_;
}
else
{
lean_object* v___x_1400_; uint8_t v___x_1401_; 
v___x_1400_ = l_Lean_Syntax_getArg(v_attrKind_1300_, v___x_1210_);
lean_dec(v_attrKind_1300_);
lean_inc(v___x_1400_);
v___x_1401_ = l_Lean_Syntax_matchesNull(v___x_1400_, v___y_1297_);
if (v___x_1401_ == 0)
{
lean_dec(v___x_1400_);
v___y_1105_ = v___f_1399_;
v___y_1106_ = v___y_1294_;
v___y_1107_ = v___y_1296_;
v___y_1108_ = v___x_1389_;
goto v___jp_1104_;
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1402_ = l_Lean_Syntax_getArg(v___x_1400_, v___x_1210_);
lean_dec(v___x_1400_);
v___x_1403_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1404_ = l_Lean_Syntax_isOfKind(v___x_1402_, v___x_1403_);
if (v___x_1404_ == 0)
{
v___y_1105_ = v___f_1399_;
v___y_1106_ = v___y_1294_;
v___y_1107_ = v___y_1296_;
v___y_1108_ = v___x_1389_;
goto v___jp_1104_;
}
else
{
v___y_1105_ = v___f_1399_;
v___y_1106_ = v___y_1294_;
v___y_1107_ = v___y_1296_;
v___y_1108_ = v___x_1143_;
goto v___jp_1104_;
}
}
}
}
else
{
lean_object* v___x_1405_; 
lean_dec(v___x_1318_);
v___x_1405_ = l_Lean_Elab_Command_getRef___redArg(v___y_1294_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v_fileName_1407_; lean_object* v_fileMap_1408_; lean_object* v_currRecDepth_1409_; lean_object* v_cmdPos_1410_; lean_object* v_macroStack_1411_; lean_object* v_quotContext_x3f_1412_; lean_object* v_currMacroScope_1413_; lean_object* v_snap_x3f_1414_; lean_object* v_cancelTk_x3f_1415_; uint8_t v_suppressElabErrors_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v_ref_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v_fileName_1407_ = lean_ctor_get(v___y_1294_, 0);
v_fileMap_1408_ = lean_ctor_get(v___y_1294_, 1);
v_currRecDepth_1409_ = lean_ctor_get(v___y_1294_, 2);
v_cmdPos_1410_ = lean_ctor_get(v___y_1294_, 3);
v_macroStack_1411_ = lean_ctor_get(v___y_1294_, 4);
v_quotContext_x3f_1412_ = lean_ctor_get(v___y_1294_, 5);
v_currMacroScope_1413_ = lean_ctor_get(v___y_1294_, 6);
v_snap_x3f_1414_ = lean_ctor_get(v___y_1294_, 8);
v_cancelTk_x3f_1415_ = lean_ctor_get(v___y_1294_, 9);
v_suppressElabErrors_1416_ = lean_ctor_get_uint8(v___y_1294_, sizeof(void*)*10);
v___x_1417_ = l_Lean_Syntax_getArg(v___x_1335_, v___x_1305_);
lean_dec(v___x_1335_);
v___x_1418_ = lean_mk_empty_array_with_capacity(v___x_1299_);
lean_inc(v_tk_1306_);
v___x_1419_ = lean_array_push(v___x_1418_, v_tk_1306_);
lean_inc(v___x_1417_);
v___x_1420_ = lean_array_push(v___x_1419_, v___x_1417_);
v___x_1421_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1422_ = lean_box(2);
v___x_1423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
lean_ctor_set(v___x_1423_, 1, v___x_1421_);
lean_ctor_set(v___x_1423_, 2, v___x_1420_);
v_ref_1424_ = l_Lean_replaceRef(v___x_1423_, v_a_1406_);
lean_dec(v_a_1406_);
lean_dec_ref_known(v___x_1423_, 3);
lean_inc(v_cancelTk_x3f_1415_);
lean_inc(v_snap_x3f_1414_);
lean_inc(v_currMacroScope_1413_);
lean_inc(v_quotContext_x3f_1412_);
lean_inc(v_macroStack_1411_);
lean_inc(v_cmdPos_1410_);
lean_inc(v_currRecDepth_1409_);
lean_inc_ref(v_fileMap_1408_);
lean_inc_ref(v_fileName_1407_);
v___x_1425_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1425_, 0, v_fileName_1407_);
lean_ctor_set(v___x_1425_, 1, v_fileMap_1408_);
lean_ctor_set(v___x_1425_, 2, v_currRecDepth_1409_);
lean_ctor_set(v___x_1425_, 3, v_cmdPos_1410_);
lean_ctor_set(v___x_1425_, 4, v_macroStack_1411_);
lean_ctor_set(v___x_1425_, 5, v_quotContext_x3f_1412_);
lean_ctor_set(v___x_1425_, 6, v_currMacroScope_1413_);
lean_ctor_set(v___x_1425_, 7, v_ref_1424_);
lean_ctor_set(v___x_1425_, 8, v_snap_x3f_1414_);
lean_ctor_set(v___x_1425_, 9, v_cancelTk_x3f_1415_);
lean_ctor_set_uint8(v___x_1425_, sizeof(void*)*10, v_suppressElabErrors_1416_);
v___x_1426_ = l_Lean_Elab_Command_getRef___redArg(v___x_1425_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_1425_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v___x_1429_; 
lean_dec_ref_known(v___x_1428_, 1);
v___x_1429_ = l_Lean_SourceInfo_fromRef(v_a_1427_, v___x_1309_);
lean_dec(v_a_1427_);
if (lean_obj_tag(v_quotContext_x3f_1412_) == 0)
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_1296_);
lean_dec_ref(v___x_1430_);
v___y_1262_ = v___x_1309_;
v___y_1263_ = v___x_1387_;
v___y_1264_ = v_kind_1317_;
v___y_1265_ = v___x_1425_;
v___y_1266_ = v_attrKind_1300_;
v___y_1267_ = v___y_1297_;
v___y_1268_ = v___y_1296_;
v___y_1269_ = v___x_1301_;
v___y_1270_ = v___y_1295_;
v___y_1271_ = v_attrs_x3f_1298_;
v___y_1272_ = v_quotContext_x3f_1412_;
v___y_1273_ = v_tk_1306_;
v___y_1274_ = v___x_1417_;
v___y_1275_ = v___x_1421_;
v___y_1276_ = v___x_1429_;
goto v___jp_1261_;
}
else
{
v___y_1262_ = v___x_1309_;
v___y_1263_ = v___x_1387_;
v___y_1264_ = v_kind_1317_;
v___y_1265_ = v___x_1425_;
v___y_1266_ = v_attrKind_1300_;
v___y_1267_ = v___y_1297_;
v___y_1268_ = v___y_1296_;
v___y_1269_ = v___x_1301_;
v___y_1270_ = v___y_1295_;
v___y_1271_ = v_attrs_x3f_1298_;
v___y_1272_ = v_quotContext_x3f_1412_;
v___y_1273_ = v_tk_1306_;
v___y_1274_ = v___x_1417_;
v___y_1275_ = v___x_1421_;
v___y_1276_ = v___x_1429_;
goto v___jp_1261_;
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec(v_a_1427_);
lean_dec_ref_known(v___x_1425_, 10);
lean_dec(v___x_1417_);
lean_dec(v___x_1387_);
lean_dec(v_kind_1317_);
lean_dec(v_tk_1306_);
lean_dec(v_attrKind_1300_);
lean_dec(v_attrs_x3f_1298_);
lean_dec(v___y_1295_);
v_a_1431_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1428_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1428_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1425_, 10);
lean_dec(v___x_1417_);
lean_dec(v___x_1387_);
lean_dec(v_kind_1317_);
lean_dec(v_tk_1306_);
lean_dec(v_attrKind_1300_);
lean_dec(v_attrs_x3f_1298_);
lean_dec(v___y_1295_);
return v___x_1426_;
}
}
else
{
lean_dec(v___x_1387_);
lean_dec(v___x_1335_);
lean_dec(v_kind_1317_);
lean_dec(v_tk_1306_);
lean_dec(v_attrKind_1300_);
lean_dec(v_attrs_x3f_1298_);
lean_dec(v___y_1295_);
return v___x_1405_;
}
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
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
lean_dec(v___x_1308_);
v___x_1439_ = lean_unsigned_to_nat(5u);
v___x_1440_ = l_Lean_Syntax_getArg(v_stx_1100_, v___x_1439_);
lean_dec(v_stx_1100_);
v___x_1441_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10));
lean_inc(v___x_1440_);
v___x_1442_ = l_Lean_Syntax_isOfKind(v___x_1440_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_dec(v___x_1440_);
lean_dec(v_tk_1306_);
lean_dec(v_attrKind_1300_);
lean_dec(v_attrs_x3f_1298_);
lean_dec(v___y_1295_);
v___x_1443_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1443_;
}
else
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_Elab_Command_getRef___redArg(v___y_1294_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v_fileName_1446_; lean_object* v_fileMap_1447_; lean_object* v_currRecDepth_1448_; lean_object* v_cmdPos_1449_; lean_object* v_macroStack_1450_; lean_object* v_quotContext_x3f_1451_; lean_object* v_currMacroScope_1452_; lean_object* v_snap_x3f_1453_; lean_object* v_cancelTk_x3f_1454_; uint8_t v_suppressElabErrors_1455_; lean_object* v___x_1456_; lean_object* v_alts_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___f_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v_ref_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v_fileName_1446_ = lean_ctor_get(v___y_1294_, 0);
v_fileMap_1447_ = lean_ctor_get(v___y_1294_, 1);
v_currRecDepth_1448_ = lean_ctor_get(v___y_1294_, 2);
v_cmdPos_1449_ = lean_ctor_get(v___y_1294_, 3);
v_macroStack_1450_ = lean_ctor_get(v___y_1294_, 4);
v_quotContext_x3f_1451_ = lean_ctor_get(v___y_1294_, 5);
v_currMacroScope_1452_ = lean_ctor_get(v___y_1294_, 6);
v_snap_x3f_1453_ = lean_ctor_get(v___y_1294_, 8);
v_cancelTk_x3f_1454_ = lean_ctor_get(v___y_1294_, 9);
v_suppressElabErrors_1455_ = lean_ctor_get_uint8(v___y_1294_, sizeof(void*)*10);
v___x_1456_ = l_Lean_Syntax_getArg(v___x_1440_, v___x_1210_);
lean_dec(v___x_1440_);
v_alts_1457_ = l_Lean_Syntax_getArgs(v___x_1456_);
lean_dec(v___x_1456_);
v___x_1458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1459_ = lean_box(2);
lean_inc_ref(v_alts_1457_);
v___x_1460_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
lean_ctor_set(v___x_1460_, 1, v___x_1458_);
lean_ctor_set(v___x_1460_, 2, v_alts_1457_);
v___f_1461_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__5___boxed), 15, 10);
lean_closure_set(v___f_1461_, 0, v___x_1441_);
lean_closure_set(v___f_1461_, 1, v___x_1142_);
lean_closure_set(v___f_1461_, 2, v_attrKind_1300_);
lean_closure_set(v___f_1461_, 3, v___x_1141_);
lean_closure_set(v___f_1461_, 4, v___x_1210_);
lean_closure_set(v___f_1461_, 5, v_attrs_x3f_1298_);
lean_closure_set(v___f_1461_, 6, v___x_1139_);
lean_closure_set(v___f_1461_, 7, v___x_1140_);
lean_closure_set(v___f_1461_, 8, v___x_1301_);
lean_closure_set(v___f_1461_, 9, v___y_1295_);
v___x_1462_ = lean_mk_empty_array_with_capacity(v___x_1299_);
v___x_1463_ = lean_array_push(v___x_1462_, v_tk_1306_);
v___x_1464_ = lean_array_push(v___x_1463_, v___x_1460_);
v___x_1465_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1459_);
lean_ctor_set(v___x_1465_, 1, v___x_1458_);
lean_ctor_set(v___x_1465_, 2, v___x_1464_);
v_ref_1466_ = l_Lean_replaceRef(v___x_1465_, v_a_1445_);
lean_dec(v_a_1445_);
lean_dec_ref_known(v___x_1465_, 3);
lean_inc(v_cancelTk_x3f_1454_);
lean_inc(v_snap_x3f_1453_);
lean_inc(v_currMacroScope_1452_);
lean_inc(v_quotContext_x3f_1451_);
lean_inc(v_macroStack_1450_);
lean_inc(v_cmdPos_1449_);
lean_inc(v_currRecDepth_1448_);
lean_inc_ref(v_fileMap_1447_);
lean_inc_ref(v_fileName_1446_);
v___x_1467_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1467_, 0, v_fileName_1446_);
lean_ctor_set(v___x_1467_, 1, v_fileMap_1447_);
lean_ctor_set(v___x_1467_, 2, v_currRecDepth_1448_);
lean_ctor_set(v___x_1467_, 3, v_cmdPos_1449_);
lean_ctor_set(v___x_1467_, 4, v_macroStack_1450_);
lean_ctor_set(v___x_1467_, 5, v_quotContext_x3f_1451_);
lean_ctor_set(v___x_1467_, 6, v_currMacroScope_1452_);
lean_ctor_set(v___x_1467_, 7, v_ref_1466_);
lean_ctor_set(v___x_1467_, 8, v_snap_x3f_1453_);
lean_ctor_set(v___x_1467_, 9, v_cancelTk_x3f_1454_);
lean_ctor_set_uint8(v___x_1467_, sizeof(void*)*10, v_suppressElabErrors_1455_);
v___x_1468_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(v_alts_1457_, v___x_1141_, v___f_1461_, v___x_1467_, v___y_1296_);
lean_dec_ref_known(v___x_1467_, 10);
lean_dec_ref(v_alts_1457_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1468_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1468_);
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
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
v_a_1477_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1468_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1468_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
else
{
lean_dec(v___x_1440_);
lean_dec(v_tk_1306_);
lean_dec(v_attrKind_1300_);
lean_dec(v_attrs_x3f_1298_);
lean_dec(v___y_1295_);
return v___x_1444_;
}
}
}
}
}
v___jp_1485_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1489_ = lean_unsigned_to_nat(1u);
v___x_1490_ = l_Lean_Syntax_getArg(v_stx_1100_, v___x_1489_);
v___x_1491_ = l_Lean_Syntax_isNone(v___x_1490_);
if (v___x_1491_ == 0)
{
uint8_t v___x_1492_; 
lean_inc(v___x_1490_);
v___x_1492_ = l_Lean_Syntax_matchesNull(v___x_1490_, v___x_1489_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; 
lean_dec(v___x_1490_);
lean_dec(v_doc_x3f_1486_);
lean_dec(v_stx_1100_);
v___x_1493_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1493_;
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1494_ = l_Lean_Syntax_getArg(v___x_1490_, v___x_1210_);
lean_dec(v___x_1490_);
v___x_1495_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15));
lean_inc(v___x_1494_);
v___x_1496_ = l_Lean_Syntax_isOfKind(v___x_1494_, v___x_1495_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; 
lean_dec(v___x_1494_);
lean_dec(v_doc_x3f_1486_);
lean_dec(v_stx_1100_);
v___x_1497_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1497_;
}
else
{
lean_object* v___x_1498_; lean_object* v_attrs_x3f_1499_; lean_object* v___x_1500_; 
v___x_1498_ = l_Lean_Syntax_getArg(v___x_1494_, v___x_1489_);
lean_dec(v___x_1494_);
v_attrs_x3f_1499_ = l_Lean_Syntax_getArgs(v___x_1498_);
lean_dec(v___x_1498_);
v___x_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1500_, 0, v_attrs_x3f_1499_);
v___y_1294_ = v___y_1487_;
v___y_1295_ = v_doc_x3f_1486_;
v___y_1296_ = v___y_1488_;
v___y_1297_ = v___x_1489_;
v_attrs_x3f_1298_ = v___x_1500_;
goto v___jp_1293_;
}
}
}
else
{
lean_object* v___x_1501_; 
lean_dec(v___x_1490_);
v___x_1501_ = lean_box(0);
v___y_1294_ = v___y_1487_;
v___y_1295_ = v_doc_x3f_1486_;
v___y_1296_ = v___y_1488_;
v___y_1297_ = v___x_1489_;
v_attrs_x3f_1298_ = v___x_1501_;
goto v___jp_1293_;
}
}
}
v___jp_1104_:
{
uint8_t v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = lean_bool_not(v___y_1108_);
v___x_1110_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1105_, v___x_1109_, v___y_1106_, v___y_1107_);
return v___x_1110_;
}
v___jp_1111_:
{
uint8_t v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_bool_not(v___y_1115_);
v___x_1117_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1112_, v___x_1116_, v___y_1113_, v___y_1114_);
return v___x_1117_;
}
v___jp_1118_:
{
uint8_t v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_bool_not(v___y_1122_);
v___x_1124_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1119_, v___x_1123_, v___y_1120_, v___y_1121_);
return v___x_1124_;
}
v___jp_1125_:
{
uint8_t v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_bool_not(v___y_1129_);
v___x_1131_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1127_, v___x_1130_, v___y_1126_, v___y_1128_);
return v___x_1131_;
}
v___jp_1132_:
{
uint8_t v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_bool_not(v___y_1136_);
v___x_1138_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1135_, v___x_1137_, v___y_1133_, v___y_1134_);
return v___x_1138_;
}
v___jp_1144_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
lean_inc_ref_n(v___y_1147_, 3);
v___x_1160_ = l_Array_append___redArg(v___y_1147_, v___y_1159_);
lean_dec_ref(v___y_1159_);
lean_inc_n(v___y_1158_, 6);
lean_inc_n(v___y_1153_, 17);
v___x_1161_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1161_, 0, v___y_1153_);
lean_ctor_set(v___x_1161_, 1, v___y_1158_);
lean_ctor_set(v___x_1161_, 2, v___x_1160_);
v___x_1162_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
lean_inc_ref_n(v___y_1152_, 2);
v___x_1163_ = l_Lean_Name_mkStr4(v___x_1139_, v___x_1140_, v___y_1152_, v___x_1162_);
v___x_1164_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
v___x_1165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___y_1153_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = l_Array_append___redArg(v___y_1147_, v___y_1145_);
lean_dec_ref(v___y_1145_);
v___x_1167_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1167_, 0, v___y_1153_);
lean_ctor_set(v___x_1167_, 1, v___y_1158_);
lean_ctor_set(v___x_1167_, 2, v___x_1166_);
v___x_1168_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
v___x_1169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___y_1153_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = l_Lean_Syntax_node3(v___y_1153_, v___x_1163_, v___x_1165_, v___x_1167_, v___x_1169_);
v___x_1171_ = l_Lean_Syntax_node1(v___y_1153_, v___y_1158_, v___x_1170_);
lean_inc_ref(v___y_1146_);
v___x_1172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___y_1153_);
lean_ctor_set(v___x_1172_, 1, v___y_1146_);
v___x_1173_ = l_Lean_TSyntax_getId(v___y_1150_);
v___x_1174_ = l_Lean_mkIdentFrom(v___y_1154_, v___x_1173_, v___x_1143_);
lean_dec(v___y_1154_);
v___x_1175_ = l_Lean_Syntax_node2(v___y_1153_, v___y_1158_, v___x_1174_, v___y_1150_);
v___x_1176_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__6));
v___x_1177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___y_1153_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__8, &l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8);
v___x_1179_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__9));
v___x_1180_ = l_Lean_addMacroScope(v___y_1148_, v___x_1179_, v___y_1151_);
v___x_1181_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6));
v___x_1182_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1182_, 0, v___y_1153_);
lean_ctor_set(v___x_1182_, 1, v___x_1178_);
lean_ctor_set(v___x_1182_, 2, v___x_1180_);
lean_ctor_set(v___x_1182_, 3, v___x_1181_);
v___x_1183_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
v___x_1184_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___y_1153_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__11));
v___x_1186_ = l_Lean_Name_mkStr4(v___x_1139_, v___x_1140_, v___y_1152_, v___x_1185_);
v___x_1187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___y_1153_);
lean_ctor_set(v___x_1187_, 1, v___x_1185_);
v___x_1188_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7));
v___x_1189_ = l_Lean_Name_mkStr4(v___x_1139_, v___x_1140_, v___y_1152_, v___x_1188_);
v___x_1190_ = l_Lean_Syntax_node1(v___y_1153_, v___y_1158_, v___y_1149_);
v___x_1191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1191_, 0, v___y_1153_);
lean_ctor_set(v___x_1191_, 1, v___y_1158_);
lean_ctor_set(v___x_1191_, 2, v___y_1147_);
v___x_1192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13));
v___x_1193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___y_1153_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = l_Lean_Syntax_node4(v___y_1153_, v___x_1189_, v___x_1190_, v___x_1191_, v___x_1193_, v___y_1156_);
v___x_1195_ = l_Lean_Syntax_node2(v___y_1153_, v___x_1186_, v___x_1187_, v___x_1194_);
v___x_1196_ = lean_unsigned_to_nat(9u);
v___x_1197_ = lean_mk_empty_array_with_capacity(v___x_1196_);
v___x_1198_ = lean_array_push(v___x_1197_, v___x_1161_);
v___x_1199_ = lean_array_push(v___x_1198_, v___x_1171_);
v___x_1200_ = lean_array_push(v___x_1199_, v___y_1155_);
v___x_1201_ = lean_array_push(v___x_1200_, v___x_1172_);
v___x_1202_ = lean_array_push(v___x_1201_, v___x_1175_);
v___x_1203_ = lean_array_push(v___x_1202_, v___x_1177_);
v___x_1204_ = lean_array_push(v___x_1203_, v___x_1182_);
v___x_1205_ = lean_array_push(v___x_1204_, v___x_1184_);
v___x_1206_ = lean_array_push(v___x_1205_, v___x_1195_);
lean_inc(v___y_1157_);
v___x_1207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1207_, 0, v___y_1153_);
lean_ctor_set(v___x_1207_, 1, v___y_1157_);
lean_ctor_set(v___x_1207_, 2, v___x_1206_);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___boxed(lean_object* v_stx_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_Elab_Command_elabMacroRules___lam__1(v_stx_1513_, v___y_1514_, v___y_1515_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules(lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v___f_1523_; lean_object* v___x_1524_; 
v___f_1523_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___closed__0));
v___x_1524_ = l_Lean_Elab_Command_adaptExpander(v___f_1523_, v_a_1519_, v_a_1520_, v_a_1521_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___boxed(lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_Elab_Command_elabMacroRules(v_a_1525_, v_a_1526_, v_a_1527_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1(){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1537_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1538_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1));
v___x_1539_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1));
v___x_1540_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___boxed), 4, 0);
v___x_1541_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1537_, v___x_1538_, v___x_1539_, v___x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___boxed(lean_object* v_a_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1();
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3(){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1570_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1));
v___x_1571_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6));
v___x_1572_ = l_Lean_addBuiltinDeclarationRanges(v___x_1570_, v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___boxed(lean_object* v_a_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3();
return v_res_1574_;
}
}
lean_object* runtime_initialize_Lean_Elab_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_AuxDef(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_MacroRules(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
