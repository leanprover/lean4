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
lean_object* v___x_131_; lean_object* v_scopes_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v_opts_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
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
if (v___x_137_ == 0)
{
lean_object* v___x_138_; 
lean_dec(v_macroStack_128_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v_msgData_127_);
return v___x_138_;
}
else
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_msgData_158_, lean_object* v_macroStack_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_msgData_158_, v_macroStack_159_, v___y_160_);
lean_dec(v___y_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(lean_object* v_msg_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Elab_Command_getRef___redArg(v___y_164_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v_macroStack_169_; lean_object* v___x_170_; lean_object* v_a_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_182_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_a_168_);
lean_dec_ref_known(v___x_167_, 1);
v_macroStack_169_ = lean_ctor_get(v___y_164_, 4);
v___x_170_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msg_163_, v___y_165_);
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref(v___x_170_);
v___x_172_ = l_Lean_Elab_getBetterRef(v_a_168_, v_macroStack_169_);
lean_dec(v_a_168_);
lean_inc(v_macroStack_169_);
v___x_173_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_a_171_, v_macroStack_169_, v___y_165_);
v_a_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_182_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_172_);
lean_ctor_set(v___x_178_, 1, v_a_174_);
if (v_isShared_177_ == 0)
{
lean_ctor_set_tag(v___x_176_, 1);
lean_ctor_set(v___x_176_, 0, v___x_178_);
v___x_180_ = v___x_176_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
else
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
lean_dec_ref(v_msg_163_);
v_a_183_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v___x_167_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_167_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg___boxed(lean_object* v_msg_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_191_, v___y_192_, v___y_193_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(lean_object* v_ref_196_, lean_object* v_msg_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Elab_Command_getRef___redArg(v___y_198_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v_fileName_203_; lean_object* v_fileMap_204_; lean_object* v_currRecDepth_205_; lean_object* v_cmdPos_206_; lean_object* v_macroStack_207_; lean_object* v_quotContext_x3f_208_; lean_object* v_currMacroScope_209_; lean_object* v_snap_x3f_210_; lean_object* v_cancelTk_x3f_211_; uint8_t v_suppressElabErrors_212_; lean_object* v_ref_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_a_202_);
lean_dec_ref_known(v___x_201_, 1);
v_fileName_203_ = lean_ctor_get(v___y_198_, 0);
v_fileMap_204_ = lean_ctor_get(v___y_198_, 1);
v_currRecDepth_205_ = lean_ctor_get(v___y_198_, 2);
v_cmdPos_206_ = lean_ctor_get(v___y_198_, 3);
v_macroStack_207_ = lean_ctor_get(v___y_198_, 4);
v_quotContext_x3f_208_ = lean_ctor_get(v___y_198_, 5);
v_currMacroScope_209_ = lean_ctor_get(v___y_198_, 6);
v_snap_x3f_210_ = lean_ctor_get(v___y_198_, 8);
v_cancelTk_x3f_211_ = lean_ctor_get(v___y_198_, 9);
v_suppressElabErrors_212_ = lean_ctor_get_uint8(v___y_198_, sizeof(void*)*10);
v_ref_213_ = l_Lean_replaceRef(v_ref_196_, v_a_202_);
lean_dec(v_a_202_);
lean_inc(v_cancelTk_x3f_211_);
lean_inc(v_snap_x3f_210_);
lean_inc(v_currMacroScope_209_);
lean_inc(v_quotContext_x3f_208_);
lean_inc(v_macroStack_207_);
lean_inc(v_cmdPos_206_);
lean_inc(v_currRecDepth_205_);
lean_inc_ref(v_fileMap_204_);
lean_inc_ref(v_fileName_203_);
v___x_214_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_214_, 0, v_fileName_203_);
lean_ctor_set(v___x_214_, 1, v_fileMap_204_);
lean_ctor_set(v___x_214_, 2, v_currRecDepth_205_);
lean_ctor_set(v___x_214_, 3, v_cmdPos_206_);
lean_ctor_set(v___x_214_, 4, v_macroStack_207_);
lean_ctor_set(v___x_214_, 5, v_quotContext_x3f_208_);
lean_ctor_set(v___x_214_, 6, v_currMacroScope_209_);
lean_ctor_set(v___x_214_, 7, v_ref_213_);
lean_ctor_set(v___x_214_, 8, v_snap_x3f_210_);
lean_ctor_set(v___x_214_, 9, v_cancelTk_x3f_211_);
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*10, v_suppressElabErrors_212_);
v___x_215_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_197_, v___x_214_, v___y_199_);
lean_dec_ref_known(v___x_214_, 10);
return v___x_215_;
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec_ref(v_msg_197_);
v_a_216_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_201_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_201_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg___boxed(lean_object* v_ref_224_, lean_object* v_msg_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_ref_224_, v_msg_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v_ref_224_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(lean_object* v_k_233_, lean_object* v_as_234_, size_t v_sz_235_, size_t v_i_236_, lean_object* v_b_237_){
_start:
{
uint8_t v___x_238_; 
v___x_238_ = lean_usize_dec_lt(v_i_236_, v_sz_235_);
if (v___x_238_ == 0)
{
lean_dec(v_k_233_);
lean_inc_ref(v_b_237_);
return v_b_237_;
}
else
{
lean_object* v___x_239_; lean_object* v_a_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_239_ = lean_box(0);
v_a_240_ = lean_array_uget_borrowed(v_as_234_, v_i_236_);
lean_inc(v_a_240_);
v___x_241_ = l_Lean_Syntax_getKind(v_a_240_);
lean_inc(v_k_233_);
v___x_242_ = l_Lean_Elab_Command_checkRuleKind(v___x_241_, v_k_233_);
lean_dec(v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; size_t v___x_244_; size_t v___x_245_; 
v___x_243_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0));
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_add(v_i_236_, v___x_244_);
v_i_236_ = v___x_245_;
v_b_237_ = v___x_243_;
goto _start;
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec(v_k_233_);
lean_inc(v_a_240_);
v___x_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_247_, 0, v_a_240_);
v___x_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_239_);
return v___x_249_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___boxed(lean_object* v_k_250_, lean_object* v_as_251_, lean_object* v_sz_252_, lean_object* v_i_253_, lean_object* v_b_254_){
_start:
{
size_t v_sz_boxed_255_; size_t v_i_boxed_256_; lean_object* v_res_257_; 
v_sz_boxed_255_ = lean_unbox_usize(v_sz_252_);
lean_dec(v_sz_252_);
v_i_boxed_256_ = lean_unbox_usize(v_i_253_);
lean_dec(v_i_253_);
v_res_257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(v_k_250_, v_as_251_, v_sz_boxed_255_, v_i_boxed_256_, v_b_254_);
lean_dec_ref(v_b_254_);
lean_dec_ref(v_as_251_);
return v_res_257_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__0));
v___x_260_ = l_Lean_stringToMessageData(v___x_259_);
return v___x_260_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__2));
v___x_263_ = l_Lean_stringToMessageData(v___x_262_);
return v___x_263_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12(void){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Array_mkArray0(lean_box(0));
return v___x_277_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__16));
v___x_284_ = l_Lean_stringToMessageData(v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(lean_object* v_k_285_, size_t v_sz_286_, size_t v_i_287_, lean_object* v_bs_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
uint8_t v___x_292_; 
v___x_292_ = lean_usize_dec_lt(v_i_287_, v_sz_286_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
lean_dec(v_k_285_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v_bs_288_);
return v___x_293_;
}
else
{
lean_object* v_v_294_; lean_object* v___x_295_; lean_object* v_bs_x27_296_; lean_object* v_a_298_; lean_object* v___y_304_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_v_294_ = lean_array_uget(v_bs_288_, v_i_287_);
v___x_295_ = lean_unsigned_to_nat(0u);
v_bs_x27_296_ = lean_array_uset(v_bs_288_, v_i_287_, v___x_295_);
v___x_323_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8));
lean_inc(v_v_294_);
v___x_324_ = l_Lean_Syntax_isOfKind(v_v_294_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; 
lean_dec(v_v_294_);
v___x_325_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
v___y_304_ = v___x_325_;
goto v___jp_303_;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_326_ = lean_unsigned_to_nat(1u);
v___x_327_ = l_Lean_Syntax_getArg(v_v_294_, v___x_326_);
lean_inc(v___x_327_);
v___x_328_ = l_Lean_Syntax_matchesNull(v___x_327_, v___x_326_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
lean_dec(v___x_327_);
lean_dec(v_v_294_);
v___x_329_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
v___y_304_ = v___x_329_;
goto v___jp_303_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v_pat_348_; lean_object* v___y_350_; lean_object* v___y_351_; uint8_t v___x_403_; 
v___x_330_ = l_Lean_Syntax_getArg(v___x_327_, v___x_295_);
lean_dec(v___x_327_);
v___x_331_ = lean_unsigned_to_nat(3u);
v___x_332_ = l_Lean_Syntax_getArg(v_v_294_, v___x_331_);
v___x_346_ = l_Lean_Syntax_getArgs(v___x_330_);
lean_dec(v___x_330_);
v___x_347_ = lean_box(0);
v_pat_348_ = lean_array_get(v___x_347_, v___x_346_, v___x_295_);
v___x_403_ = l_Lean_Syntax_isQuot(v_pat_348_);
if (v___x_403_ == 0)
{
if (v___x_328_ == 0)
{
v___y_350_ = v___y_289_;
v___y_351_ = v___y_290_;
goto v___jp_349_;
}
else
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
if (lean_obj_tag(v___x_404_) == 0)
{
lean_dec_ref_known(v___x_404_, 1);
v___y_350_ = v___y_289_;
v___y_351_ = v___y_290_;
goto v___jp_349_;
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v_pat_348_);
lean_dec_ref(v___x_346_);
lean_dec(v___x_332_);
lean_dec_ref(v_bs_x27_296_);
lean_dec(v_v_294_);
lean_dec(v_k_285_);
v_a_405_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_404_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_404_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
else
{
v___y_350_ = v___y_289_;
v___y_351_ = v___y_290_;
goto v___jp_349_;
}
v___jp_333_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_336_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9));
lean_inc_n(v___y_335_, 4);
v___x_337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_337_, 0, v___y_335_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_339_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
v___x_340_ = l_Array_append___redArg(v___x_339_, v___y_334_);
lean_dec_ref(v___y_334_);
v___x_341_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_341_, 0, v___y_335_);
lean_ctor_set(v___x_341_, 1, v___x_338_);
lean_ctor_set(v___x_341_, 2, v___x_340_);
v___x_342_ = l_Lean_Syntax_node1(v___y_335_, v___x_338_, v___x_341_);
v___x_343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13));
v___x_344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_344_, 0, v___y_335_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = l_Lean_Syntax_node4(v___y_335_, v___x_323_, v___x_337_, v___x_342_, v___x_344_, v___x_332_);
v_a_298_ = v___x_345_;
goto v___jp_297_;
}
v___jp_349_:
{
lean_object* v_quoted_352_; lean_object* v_k_x27_353_; uint8_t v___x_354_; 
lean_inc(v_pat_348_);
v_quoted_352_ = l_Lean_Syntax_getQuotContent(v_pat_348_);
lean_inc(v_quoted_352_);
v_k_x27_353_ = l_Lean_Syntax_getKind(v_quoted_352_);
lean_inc(v_k_285_);
v___x_354_ = l_Lean_Elab_Command_checkRuleKind(v_k_x27_353_, v_k_285_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__15));
v___x_356_ = lean_name_eq(v_k_x27_353_, v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec(v_quoted_352_);
lean_dec(v_pat_348_);
lean_dec_ref(v___x_346_);
lean_dec(v___x_332_);
v___x_357_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17);
v___x_358_ = l_Lean_MessageData_ofName(v_k_x27_353_);
v___x_359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3);
v___x_361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_v_294_, v___x_361_, v___y_350_, v___y_351_);
lean_dec(v_v_294_);
v___y_304_ = v___x_362_;
goto v___jp_303_;
}
else
{
lean_object* v___x_363_; lean_object* v___x_364_; size_t v_sz_365_; size_t v___x_366_; lean_object* v___x_367_; lean_object* v_fst_368_; 
lean_dec(v_k_x27_353_);
v___x_363_ = l_Lean_Syntax_getArgs(v_quoted_352_);
lean_dec(v_quoted_352_);
v___x_364_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0));
v_sz_365_ = lean_array_size(v___x_363_);
v___x_366_ = ((size_t)0ULL);
lean_inc(v_k_285_);
v___x_367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(v_k_285_, v___x_363_, v_sz_365_, v___x_366_, v___x_364_);
lean_dec_ref(v___x_363_);
v_fst_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_fst_368_);
lean_dec_ref(v___x_367_);
if (lean_obj_tag(v_fst_368_) == 0)
{
lean_dec(v_pat_348_);
lean_dec_ref(v___x_346_);
lean_dec(v___x_332_);
v___y_315_ = v___y_351_;
v___y_316_ = v___y_350_;
goto v___jp_314_;
}
else
{
lean_object* v_val_369_; 
v_val_369_ = lean_ctor_get(v_fst_368_, 0);
lean_inc(v_val_369_);
lean_dec_ref_known(v_fst_368_, 1);
if (lean_obj_tag(v_val_369_) == 0)
{
lean_dec(v_pat_348_);
lean_dec_ref(v___x_346_);
lean_dec(v___x_332_);
v___y_315_ = v___y_351_;
v___y_316_ = v___y_350_;
goto v___jp_314_;
}
else
{
lean_object* v_val_370_; lean_object* v___x_371_; 
lean_dec(v_v_294_);
v_val_370_ = lean_ctor_get(v_val_369_, 0);
lean_inc(v_val_370_);
lean_dec_ref_known(v_val_369_, 1);
v___x_371_ = l_Lean_Elab_Command_getRef___redArg(v___y_350_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_373_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_371_, 1);
v___x_373_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_350_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_quotContext_x3f_374_; lean_object* v_pat_375_; lean_object* v_pats_376_; lean_object* v___x_377_; 
lean_dec_ref_known(v___x_373_, 1);
v_quotContext_x3f_374_ = lean_ctor_get(v___y_350_, 5);
v_pat_375_ = l_Lean_Syntax_setArg(v_pat_348_, v___x_326_, v_val_370_);
v_pats_376_ = lean_array_set(v___x_346_, v___x_295_, v_pat_375_);
v___x_377_ = l_Lean_SourceInfo_fromRef(v_a_372_, v___x_354_);
lean_dec(v_a_372_);
if (lean_obj_tag(v_quotContext_x3f_374_) == 0)
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_351_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_dec_ref_known(v___x_378_, 1);
v___y_334_ = v_pats_376_;
v___y_335_ = v___x_377_;
goto v___jp_333_;
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
lean_dec(v___x_377_);
lean_dec_ref(v_pats_376_);
lean_dec(v___x_332_);
lean_dec_ref(v_bs_x27_296_);
lean_dec(v_k_285_);
v_a_379_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_378_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_378_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
else
{
v___y_334_ = v_pats_376_;
v___y_335_ = v___x_377_;
goto v___jp_333_;
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec(v_a_372_);
lean_dec(v_val_370_);
lean_dec(v_pat_348_);
lean_dec_ref(v___x_346_);
lean_dec(v___x_332_);
lean_dec_ref(v_bs_x27_296_);
lean_dec(v_k_285_);
v_a_387_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_373_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_373_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec(v_val_370_);
lean_dec(v_pat_348_);
lean_dec_ref(v___x_346_);
lean_dec(v___x_332_);
lean_dec_ref(v_bs_x27_296_);
lean_dec(v_k_285_);
v_a_395_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_371_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_371_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_x27_353_);
lean_dec(v_quoted_352_);
lean_dec(v_pat_348_);
lean_dec_ref(v___x_346_);
lean_dec(v___x_332_);
v_a_298_ = v_v_294_;
goto v___jp_297_;
}
}
}
}
v___jp_297_:
{
size_t v___x_299_; size_t v___x_300_; lean_object* v___x_301_; 
v___x_299_ = ((size_t)1ULL);
v___x_300_ = lean_usize_add(v_i_287_, v___x_299_);
v___x_301_ = lean_array_uset(v_bs_x27_296_, v_i_287_, v_a_298_);
v_i_287_ = v___x_300_;
v_bs_288_ = v___x_301_;
goto _start;
}
v___jp_303_:
{
if (lean_obj_tag(v___y_304_) == 0)
{
lean_object* v_a_305_; 
v_a_305_ = lean_ctor_get(v___y_304_, 0);
lean_inc(v_a_305_);
lean_dec_ref_known(v___y_304_, 1);
v_a_298_ = v_a_305_;
goto v___jp_297_;
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec_ref(v_bs_x27_296_);
lean_dec(v_k_285_);
v_a_306_ = lean_ctor_get(v___y_304_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___y_304_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___y_304_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___y_304_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
v___jp_314_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_317_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1);
lean_inc(v_k_285_);
v___x_318_ = l_Lean_MessageData_ofName(v_k_285_);
v___x_319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3);
v___x_321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_v_294_, v___x_321_, v___y_316_, v___y_315_);
lean_dec(v_v_294_);
v___y_304_ = v___x_322_;
goto v___jp_303_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___boxed(lean_object* v_k_413_, lean_object* v_sz_414_, lean_object* v_i_415_, lean_object* v_bs_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
size_t v_sz_boxed_420_; size_t v_i_boxed_421_; lean_object* v_res_422_; 
v_sz_boxed_420_ = lean_unbox_usize(v_sz_414_);
lean_dec(v_sz_414_);
v_i_boxed_421_ = lean_unbox_usize(v_i_415_);
lean_dec(v_i_415_);
v_res_422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(v_k_413_, v_sz_boxed_420_, v_i_boxed_421_, v_bs_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
return v_res_422_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__4(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__3));
v___x_428_ = l_String_toRawSubstring_x27(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__7));
v___x_434_ = l_String_toRawSubstring_x27(v___x_433_);
return v___x_434_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__19(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__18));
v___x_447_ = l_String_toRawSubstring_x27(v___x_446_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__26(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__25));
v___x_462_ = l_String_toRawSubstring_x27(v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux(lean_object* v_doc_x3f_489_, lean_object* v_attrs_x3f_490_, lean_object* v_attrKind_491_, lean_object* v_tk_492_, lean_object* v_k_493_, lean_object* v_alts_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
size_t v_sz_498_; size_t v___x_499_; lean_object* v___x_500_; 
v_sz_498_ = lean_array_size(v_alts_494_);
v___x_499_ = ((size_t)0ULL);
lean_inc(v_k_493_);
v___x_500_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(v_k_493_, v_sz_498_, v___x_499_, v_alts_494_, v_a_495_, v_a_496_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_683_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_683_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_683_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_683_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v_a_622_; lean_object* v___x_631_; 
v___x_631_ = l_Lean_Elab_Command_getRef___redArg(v_a_495_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_633_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_631_, 1);
v___x_633_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_495_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_quotContext_x3f_634_; uint8_t v___x_635_; lean_object* v___y_637_; lean_object* v___x_655_; 
lean_dec_ref_known(v___x_633_, 1);
v_quotContext_x3f_634_ = lean_ctor_get(v_a_495_, 5);
v___x_635_ = 0;
v___x_655_ = l_Lean_SourceInfo_fromRef(v_a_632_, v___x_635_);
lean_dec(v_a_632_);
if (lean_obj_tag(v_quotContext_x3f_634_) == 0)
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v_a_496_);
lean_dec_ref(v___x_674_);
goto v___jp_656_;
}
else
{
goto v___jp_656_;
}
v___jp_636_:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Elab_Command_getRef___redArg(v_a_495_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_640_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_638_, 1);
v___x_640_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_495_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v___x_640_, 1);
v___x_642_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_491_);
v___x_643_ = l_Lean_SourceInfo_fromRef(v_a_639_, v___x_635_);
lean_dec(v_a_639_);
if (lean_obj_tag(v_quotContext_x3f_634_) == 0)
{
lean_object* v___x_644_; lean_object* v_a_645_; 
v___x_644_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v_a_496_);
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref(v___x_644_);
v___y_618_ = v___y_637_;
v___y_619_ = v_a_641_;
v___y_620_ = v___x_643_;
v___y_621_ = v___x_642_;
v_a_622_ = v_a_645_;
goto v___jp_617_;
}
else
{
lean_object* v_val_646_; 
v_val_646_ = lean_ctor_get(v_quotContext_x3f_634_, 0);
lean_inc(v_val_646_);
v___y_618_ = v___y_637_;
v___y_619_ = v_a_641_;
v___y_620_ = v___x_643_;
v___y_621_ = v___x_642_;
v_a_622_ = v_val_646_;
goto v___jp_617_;
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec(v_a_639_);
lean_dec_ref(v___y_637_);
lean_del_object(v___x_503_);
lean_dec(v_a_501_);
lean_dec(v_k_493_);
lean_dec(v_attrKind_491_);
lean_dec(v_doc_x3f_489_);
v_a_647_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_640_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_640_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
else
{
lean_dec_ref(v___y_637_);
lean_del_object(v___x_503_);
lean_dec(v_a_501_);
lean_dec(v_k_493_);
lean_dec(v_attrKind_491_);
lean_dec(v_doc_x3f_489_);
return v___x_638_;
}
}
v___jp_656_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_657_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__35));
v___x_658_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__37));
v___x_659_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__38));
lean_inc_n(v___x_655_, 2);
v___x_660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_655_);
lean_ctor_set(v___x_660_, 1, v___x_658_);
lean_inc(v_k_493_);
v___x_661_ = l_Lean_mkIdent(v_k_493_);
v___x_662_ = l_Lean_Syntax_node2(v___x_655_, v___x_659_, v___x_660_, v___x_661_);
lean_inc(v_attrKind_491_);
v___x_663_ = l_Lean_Syntax_node2(v___x_655_, v___x_657_, v_attrKind_491_, v___x_662_);
if (lean_obj_tag(v_attrs_x3f_490_) == 0)
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_664_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = lean_mk_empty_array_with_capacity(v___x_665_);
v___x_667_ = lean_array_push(v___x_666_, v___x_663_);
v___x_668_ = l_Lean_Syntax_SepArray_ofElems(v___x_664_, v___x_667_);
lean_dec_ref(v___x_667_);
v___y_637_ = v___x_668_;
goto v___jp_636_;
}
else
{
lean_object* v_val_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_val_669_ = lean_ctor_get(v_attrs_x3f_490_, 0);
v___x_670_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_671_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_669_);
v___x_672_ = lean_array_push(v___x_671_, v___x_663_);
v___x_673_ = l_Lean_Syntax_SepArray_ofElems(v___x_670_, v___x_672_);
lean_dec_ref(v___x_672_);
v___y_637_ = v___x_673_;
goto v___jp_636_;
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec(v_a_632_);
lean_del_object(v___x_503_);
lean_dec(v_a_501_);
lean_dec(v_k_493_);
lean_dec(v_attrKind_491_);
lean_dec(v_doc_x3f_489_);
v_a_675_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_633_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_633_);
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
else
{
lean_del_object(v___x_503_);
lean_dec(v_a_501_);
lean_dec(v_k_493_);
lean_dec(v_attrKind_491_);
lean_dec(v_doc_x3f_489_);
return v___x_631_;
}
v___jp_505_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
lean_inc_ref_n(v___y_515_, 3);
v___x_517_ = l_Array_append___redArg(v___y_515_, v___y_516_);
lean_dec_ref(v___y_516_);
lean_inc_n(v___y_511_, 8);
lean_inc_n(v___y_510_, 29);
v___x_518_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_518_, 0, v___y_510_);
lean_ctor_set(v___x_518_, 1, v___y_511_);
lean_ctor_set(v___x_518_, 2, v___x_517_);
v___x_519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5));
v___x_520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6));
v___x_521_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
lean_inc_ref_n(v___y_508_, 9);
v___x_522_ = l_Lean_Name_mkStr4(v___y_508_, v___x_519_, v___x_520_, v___x_521_);
v___x_523_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
v___x_524_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_524_, 0, v___y_510_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = l_Array_append___redArg(v___y_515_, v___y_507_);
lean_dec_ref(v___y_507_);
v___x_526_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_526_, 0, v___y_510_);
lean_ctor_set(v___x_526_, 1, v___y_511_);
lean_ctor_set(v___x_526_, 2, v___x_525_);
v___x_527_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
v___x_528_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_528_, 0, v___y_510_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = l_Lean_Syntax_node3(v___y_510_, v___x_522_, v___x_524_, v___x_526_, v___x_528_);
v___x_530_ = l_Lean_Syntax_node1(v___y_510_, v___y_511_, v___x_529_);
lean_inc_ref(v___y_506_);
v___x_531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_531_, 0, v___y_510_);
lean_ctor_set(v___x_531_, 1, v___y_506_);
v___x_532_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__4, &l_Lean_Elab_Command_elabMacroRulesAux___closed__4_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__4);
v___x_533_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__5));
lean_inc_n(v___y_509_, 3);
lean_inc_n(v___y_514_, 3);
v___x_534_ = l_Lean_addMacroScope(v___y_514_, v___x_533_, v___y_509_);
v___x_535_ = lean_box(0);
v___x_536_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_536_, 0, v___y_510_);
lean_ctor_set(v___x_536_, 1, v___x_532_);
lean_ctor_set(v___x_536_, 2, v___x_534_);
lean_ctor_set(v___x_536_, 3, v___x_535_);
v___x_537_ = 1;
v___x_538_ = l_Lean_mkIdentFrom(v_tk_492_, v_k_493_, v___x_537_);
v___x_539_ = l_Lean_Syntax_node2(v___y_510_, v___y_511_, v___x_536_, v___x_538_);
v___x_540_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__6));
v___x_541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_541_, 0, v___y_510_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__7));
v___x_543_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__8, &l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8);
v___x_544_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__9));
v___x_545_ = l_Lean_addMacroScope(v___y_514_, v___x_544_, v___y_509_);
v___x_546_ = l_Lean_Name_mkStr2(v___y_508_, v___x_542_);
lean_inc(v___x_546_);
v___x_547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v___x_535_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_546_);
v___x_549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v___x_535_);
v___x_550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_547_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_551_, 0, v___y_510_);
lean_ctor_set(v___x_551_, 1, v___x_543_);
lean_ctor_set(v___x_551_, 2, v___x_545_);
lean_ctor_set(v___x_551_, 3, v___x_550_);
v___x_552_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
v___x_553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_553_, 0, v___y_510_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__11));
v___x_555_ = l_Lean_Name_mkStr4(v___y_508_, v___x_519_, v___x_520_, v___x_554_);
v___x_556_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_556_, 0, v___y_510_);
lean_ctor_set(v___x_556_, 1, v___x_554_);
v___x_557_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__12));
v___x_558_ = l_Lean_Name_mkStr4(v___y_508_, v___x_519_, v___x_520_, v___x_557_);
v___x_559_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7));
v___x_560_ = l_Lean_Name_mkStr4(v___y_508_, v___x_519_, v___x_520_, v___x_559_);
v___x_561_ = l_Array_append___redArg(v___y_515_, v_a_501_);
lean_dec(v_a_501_);
v___x_562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9));
v___x_563_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_563_, 0, v___y_510_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__13));
v___x_565_ = l_Lean_Name_mkStr4(v___y_508_, v___x_519_, v___x_520_, v___x_564_);
v___x_566_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__14));
v___x_567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_567_, 0, v___y_510_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = l_Lean_Syntax_node1(v___y_510_, v___x_565_, v___x_567_);
v___x_569_ = l_Lean_Syntax_node1(v___y_510_, v___y_511_, v___x_568_);
v___x_570_ = l_Lean_Syntax_node1(v___y_510_, v___y_511_, v___x_569_);
v___x_571_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13));
v___x_572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_572_, 0, v___y_510_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__15));
v___x_574_ = l_Lean_Name_mkStr4(v___y_508_, v___x_519_, v___x_520_, v___x_573_);
v___x_575_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__16));
v___x_576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_576_, 0, v___y_510_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__17));
v___x_578_ = l_Lean_Name_mkStr4(v___y_508_, v___x_519_, v___x_520_, v___x_577_);
v___x_579_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__19, &l_Lean_Elab_Command_elabMacroRulesAux___closed__19_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__19);
v___x_580_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__20));
v___x_581_ = l_Lean_addMacroScope(v___y_514_, v___x_580_, v___y_509_);
v___x_582_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__24));
v___x_583_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_583_, 0, v___y_510_);
lean_ctor_set(v___x_583_, 1, v___x_579_);
lean_ctor_set(v___x_583_, 2, v___x_581_);
lean_ctor_set(v___x_583_, 3, v___x_582_);
v___x_584_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__26, &l_Lean_Elab_Command_elabMacroRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__26);
v___x_585_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__27));
v___x_586_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__28));
v___x_587_ = l_Lean_Name_mkStr4(v___y_508_, v___x_542_, v___x_585_, v___x_586_);
lean_inc_n(v___x_587_, 2);
v___x_588_ = l_Lean_addMacroScope(v___y_514_, v___x_587_, v___y_509_);
v___x_589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_587_);
lean_ctor_set(v___x_589_, 1, v___x_535_);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_587_);
v___x_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
lean_ctor_set(v___x_591_, 1, v___x_535_);
v___x_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_589_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_593_, 0, v___y_510_);
lean_ctor_set(v___x_593_, 1, v___x_584_);
lean_ctor_set(v___x_593_, 2, v___x_588_);
lean_ctor_set(v___x_593_, 3, v___x_592_);
v___x_594_ = l_Lean_Syntax_node1(v___y_510_, v___y_511_, v___x_593_);
v___x_595_ = l_Lean_Syntax_node2(v___y_510_, v___x_578_, v___x_583_, v___x_594_);
v___x_596_ = l_Lean_Syntax_node2(v___y_510_, v___x_574_, v___x_576_, v___x_595_);
v___x_597_ = l_Lean_Syntax_node4(v___y_510_, v___x_560_, v___x_563_, v___x_570_, v___x_572_, v___x_596_);
v___x_598_ = lean_array_push(v___x_561_, v___x_597_);
v___x_599_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_599_, 0, v___y_510_);
lean_ctor_set(v___x_599_, 1, v___y_511_);
lean_ctor_set(v___x_599_, 2, v___x_598_);
v___x_600_ = l_Lean_Syntax_node1(v___y_510_, v___x_558_, v___x_599_);
v___x_601_ = l_Lean_Syntax_node2(v___y_510_, v___x_555_, v___x_556_, v___x_600_);
v___x_602_ = lean_unsigned_to_nat(9u);
v___x_603_ = lean_mk_empty_array_with_capacity(v___x_602_);
v___x_604_ = lean_array_push(v___x_603_, v___x_518_);
v___x_605_ = lean_array_push(v___x_604_, v___x_530_);
v___x_606_ = lean_array_push(v___x_605_, v___y_513_);
v___x_607_ = lean_array_push(v___x_606_, v___x_531_);
v___x_608_ = lean_array_push(v___x_607_, v___x_539_);
v___x_609_ = lean_array_push(v___x_608_, v___x_541_);
v___x_610_ = lean_array_push(v___x_609_, v___x_551_);
v___x_611_ = lean_array_push(v___x_610_, v___x_553_);
v___x_612_ = lean_array_push(v___x_611_, v___x_601_);
lean_inc(v___y_512_);
v___x_613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_613_, 0, v___y_510_);
lean_ctor_set(v___x_613_, 1, v___y_512_);
lean_ctor_set(v___x_613_, 2, v___x_612_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_613_);
v___x_615_ = v___x_503_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
v___jp_617_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_623_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4));
v___x_624_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__31));
v___x_625_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__32));
v___x_626_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_627_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
if (lean_obj_tag(v_doc_x3f_489_) == 1)
{
lean_object* v_val_628_; lean_object* v___x_629_; 
v_val_628_ = lean_ctor_get(v_doc_x3f_489_, 0);
lean_inc(v_val_628_);
lean_dec_ref_known(v_doc_x3f_489_, 1);
v___x_629_ = l_Array_mkArray1___redArg(v_val_628_);
v___y_506_ = v___x_624_;
v___y_507_ = v___y_618_;
v___y_508_ = v___x_623_;
v___y_509_ = v___y_619_;
v___y_510_ = v___y_620_;
v___y_511_ = v___x_626_;
v___y_512_ = v___x_625_;
v___y_513_ = v___y_621_;
v___y_514_ = v_a_622_;
v___y_515_ = v___x_627_;
v___y_516_ = v___x_629_;
goto v___jp_505_;
}
else
{
lean_object* v___x_630_; 
lean_dec(v_doc_x3f_489_);
v___x_630_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__33));
v___y_506_ = v___x_624_;
v___y_507_ = v___y_618_;
v___y_508_ = v___x_623_;
v___y_509_ = v___y_619_;
v___y_510_ = v___y_620_;
v___y_511_ = v___x_626_;
v___y_512_ = v___x_625_;
v___y_513_ = v___y_621_;
v___y_514_ = v_a_622_;
v___y_515_ = v___x_627_;
v___y_516_ = v___x_630_;
goto v___jp_505_;
}
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec(v_k_493_);
lean_dec(v_attrKind_491_);
lean_dec(v_doc_x3f_489_);
v_a_684_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_500_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_500_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux___boxed(lean_object* v_doc_x3f_692_, lean_object* v_attrs_x3f_693_, lean_object* v_attrKind_694_, lean_object* v_tk_695_, lean_object* v_k_696_, lean_object* v_alts_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Elab_Command_elabMacroRulesAux(v_doc_x3f_692_, v_attrs_x3f_693_, v_attrKind_694_, v_tk_695_, v_k_696_, v_alts_697_, v_a_698_, v_a_699_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_tk_695_);
lean_dec(v_attrs_x3f_693_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(lean_object* v_00_u03b1_702_, lean_object* v_ref_703_, lean_object* v_msg_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_ref_703_, v_msg_704_, v___y_705_, v___y_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___boxed(lean_object* v_00_u03b1_709_, lean_object* v_ref_710_, lean_object* v_msg_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(v_00_u03b1_709_, v_ref_710_, v_msg_711_, v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v_ref_710_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3(lean_object* v_msgData_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msgData_716_, v___y_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3(v_msgData_721_, v___y_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(lean_object* v_00_u03b1_726_, lean_object* v_msg_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_727_, v___y_728_, v___y_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___boxed(lean_object* v_00_u03b1_732_, lean_object* v_msg_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(v_00_u03b1_732_, v_msg_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4(lean_object* v_msgData_738_, lean_object* v_macroStack_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_msgData_738_, v_macroStack_739_, v___y_741_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___boxed(lean_object* v_msgData_744_, lean_object* v_macroStack_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4(v_msgData_744_, v_macroStack_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(lean_object* v___y_750_, uint8_t v_isExporting_751_, lean_object* v_a_x3f_752_){
_start:
{
lean_object* v___x_754_; lean_object* v_env_755_; lean_object* v_messages_756_; lean_object* v_scopes_757_; lean_object* v_usedQuotCtxts_758_; lean_object* v_nextMacroScope_759_; lean_object* v_maxRecDepth_760_; lean_object* v_ngen_761_; lean_object* v_auxDeclNGen_762_; lean_object* v_infoState_763_; lean_object* v_traceState_764_; lean_object* v_snapshotTasks_765_; lean_object* v_prevLinterStates_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_777_; 
v___x_754_ = lean_st_ref_take(v___y_750_);
v_env_755_ = lean_ctor_get(v___x_754_, 0);
v_messages_756_ = lean_ctor_get(v___x_754_, 1);
v_scopes_757_ = lean_ctor_get(v___x_754_, 2);
v_usedQuotCtxts_758_ = lean_ctor_get(v___x_754_, 3);
v_nextMacroScope_759_ = lean_ctor_get(v___x_754_, 4);
v_maxRecDepth_760_ = lean_ctor_get(v___x_754_, 5);
v_ngen_761_ = lean_ctor_get(v___x_754_, 6);
v_auxDeclNGen_762_ = lean_ctor_get(v___x_754_, 7);
v_infoState_763_ = lean_ctor_get(v___x_754_, 8);
v_traceState_764_ = lean_ctor_get(v___x_754_, 9);
v_snapshotTasks_765_ = lean_ctor_get(v___x_754_, 10);
v_prevLinterStates_766_ = lean_ctor_get(v___x_754_, 11);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_777_ == 0)
{
v___x_768_ = v___x_754_;
v_isShared_769_ = v_isSharedCheck_777_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_prevLinterStates_766_);
lean_inc(v_snapshotTasks_765_);
lean_inc(v_traceState_764_);
lean_inc(v_infoState_763_);
lean_inc(v_auxDeclNGen_762_);
lean_inc(v_ngen_761_);
lean_inc(v_maxRecDepth_760_);
lean_inc(v_nextMacroScope_759_);
lean_inc(v_usedQuotCtxts_758_);
lean_inc(v_scopes_757_);
lean_inc(v_messages_756_);
lean_inc(v_env_755_);
lean_dec(v___x_754_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_777_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_770_ = l_Lean_Environment_setExporting(v_env_755_, v_isExporting_751_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_770_);
v___x_772_ = v___x_768_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_messages_756_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v_scopes_757_);
lean_ctor_set(v_reuseFailAlloc_776_, 3, v_usedQuotCtxts_758_);
lean_ctor_set(v_reuseFailAlloc_776_, 4, v_nextMacroScope_759_);
lean_ctor_set(v_reuseFailAlloc_776_, 5, v_maxRecDepth_760_);
lean_ctor_set(v_reuseFailAlloc_776_, 6, v_ngen_761_);
lean_ctor_set(v_reuseFailAlloc_776_, 7, v_auxDeclNGen_762_);
lean_ctor_set(v_reuseFailAlloc_776_, 8, v_infoState_763_);
lean_ctor_set(v_reuseFailAlloc_776_, 9, v_traceState_764_);
lean_ctor_set(v_reuseFailAlloc_776_, 10, v_snapshotTasks_765_);
lean_ctor_set(v_reuseFailAlloc_776_, 11, v_prevLinterStates_766_);
v___x_772_ = v_reuseFailAlloc_776_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = lean_st_ref_set(v___y_750_, v___x_772_);
v___x_774_ = lean_box(0);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0___boxed(lean_object* v___y_778_, lean_object* v_isExporting_779_, lean_object* v_a_x3f_780_, lean_object* v___y_781_){
_start:
{
uint8_t v_isExporting_boxed_782_; lean_object* v_res_783_; 
v_isExporting_boxed_782_ = lean_unbox(v_isExporting_779_);
v_res_783_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_778_, v_isExporting_boxed_782_, v_a_x3f_780_);
lean_dec(v_a_x3f_780_);
lean_dec(v___y_778_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(lean_object* v_x_784_, uint8_t v_isExporting_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v___x_789_; lean_object* v_env_790_; uint8_t v_isExporting_791_; lean_object* v___x_792_; uint8_t v_isModule_793_; 
v___x_789_ = lean_st_ref_get(v___y_787_);
v_env_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc_ref(v_env_790_);
lean_dec(v___x_789_);
v_isExporting_791_ = lean_ctor_get_uint8(v_env_790_, sizeof(void*)*8);
v___x_792_ = l_Lean_Environment_header(v_env_790_);
lean_dec_ref(v_env_790_);
v_isModule_793_ = lean_ctor_get_uint8(v___x_792_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_792_);
if (v_isModule_793_ == 0)
{
lean_object* v___x_794_; 
lean_inc(v___y_787_);
lean_inc_ref(v___y_786_);
v___x_794_ = lean_apply_3(v_x_784_, v___y_786_, v___y_787_, lean_box(0));
return v___x_794_;
}
else
{
if (v_isExporting_791_ == 0)
{
if (v_isExporting_785_ == 0)
{
lean_object* v___x_847_; 
lean_inc(v___y_787_);
lean_inc_ref(v___y_786_);
v___x_847_ = lean_apply_3(v_x_784_, v___y_786_, v___y_787_, lean_box(0));
return v___x_847_;
}
else
{
goto v___jp_795_;
}
}
else
{
if (v_isExporting_785_ == 0)
{
goto v___jp_795_;
}
else
{
lean_object* v___x_848_; 
lean_inc(v___y_787_);
lean_inc_ref(v___y_786_);
v___x_848_ = lean_apply_3(v_x_784_, v___y_786_, v___y_787_, lean_box(0));
return v___x_848_;
}
}
v___jp_795_:
{
lean_object* v___x_796_; lean_object* v_env_797_; lean_object* v_messages_798_; lean_object* v_scopes_799_; lean_object* v_usedQuotCtxts_800_; lean_object* v_nextMacroScope_801_; lean_object* v_maxRecDepth_802_; lean_object* v_ngen_803_; lean_object* v_auxDeclNGen_804_; lean_object* v_infoState_805_; lean_object* v_traceState_806_; lean_object* v_snapshotTasks_807_; lean_object* v_prevLinterStates_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_846_; 
v___x_796_ = lean_st_ref_take(v___y_787_);
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
v_prevLinterStates_808_ = lean_ctor_get(v___x_796_, 11);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_846_ == 0)
{
v___x_810_ = v___x_796_;
v_isShared_811_ = v_isSharedCheck_846_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_prevLinterStates_808_);
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
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_846_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_812_ = l_Lean_Environment_setExporting(v_env_797_, v_isExporting_785_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_812_);
v___x_814_ = v___x_810_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_messages_798_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v_scopes_799_);
lean_ctor_set(v_reuseFailAlloc_845_, 3, v_usedQuotCtxts_800_);
lean_ctor_set(v_reuseFailAlloc_845_, 4, v_nextMacroScope_801_);
lean_ctor_set(v_reuseFailAlloc_845_, 5, v_maxRecDepth_802_);
lean_ctor_set(v_reuseFailAlloc_845_, 6, v_ngen_803_);
lean_ctor_set(v_reuseFailAlloc_845_, 7, v_auxDeclNGen_804_);
lean_ctor_set(v_reuseFailAlloc_845_, 8, v_infoState_805_);
lean_ctor_set(v_reuseFailAlloc_845_, 9, v_traceState_806_);
lean_ctor_set(v_reuseFailAlloc_845_, 10, v_snapshotTasks_807_);
lean_ctor_set(v_reuseFailAlloc_845_, 11, v_prevLinterStates_808_);
v___x_814_ = v_reuseFailAlloc_845_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v_r_816_; 
v___x_815_ = lean_st_ref_set(v___y_787_, v___x_814_);
lean_inc(v___y_787_);
lean_inc_ref(v___y_786_);
v_r_816_ = lean_apply_3(v_x_784_, v___y_786_, v___y_787_, lean_box(0));
if (lean_obj_tag(v_r_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_833_; 
v_a_817_ = lean_ctor_get(v_r_816_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v_r_816_);
if (v_isSharedCheck_833_ == 0)
{
v___x_819_ = v_r_816_;
v_isShared_820_ = v_isSharedCheck_833_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v_r_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_833_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
lean_inc(v_a_817_);
if (v_isShared_820_ == 0)
{
lean_ctor_set_tag(v___x_819_, 1);
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_832_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
v___x_823_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_787_, v_isExporting_791_, v___x_822_);
lean_dec_ref(v___x_822_);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; 
v_unused_831_ = lean_ctor_get(v___x_823_, 0);
lean_dec(v_unused_831_);
v___x_825_ = v___x_823_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_dec(v___x_823_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v_a_817_);
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_817_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
v_a_834_ = lean_ctor_get(v_r_816_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v_r_816_, 1);
v___x_835_ = lean_box(0);
v___x_836_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_787_, v_isExporting_791_, v___x_835_);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; 
v_unused_844_ = lean_ctor_get(v___x_836_, 0);
lean_dec(v_unused_844_);
v___x_838_ = v___x_836_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_dec(v___x_836_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 1);
lean_ctor_set(v___x_838_, 0, v_a_834_);
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_834_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___boxed(lean_object* v_x_849_, lean_object* v_isExporting_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
uint8_t v_isExporting_boxed_854_; lean_object* v_res_855_; 
v_isExporting_boxed_854_ = lean_unbox(v_isExporting_850_);
v_res_855_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v_x_849_, v_isExporting_boxed_854_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0(lean_object* v_00_u03b1_856_, lean_object* v_x_857_, uint8_t v_isExporting_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v_x_857_, v_isExporting_858_, v___y_859_, v___y_860_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___boxed(lean_object* v_00_u03b1_863_, lean_object* v_x_864_, lean_object* v_isExporting_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
uint8_t v_isExporting_boxed_869_; lean_object* v_res_870_; 
v_isExporting_boxed_869_ = lean_unbox(v_isExporting_865_);
v_res_870_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0(v_00_u03b1_863_, v_x_864_, v_isExporting_boxed_869_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0(lean_object* v___x_871_, lean_object* v___x_872_, lean_object* v_doc_x3f_873_, lean_object* v_attrs_x3f_874_, lean_object* v_attrKind_875_, lean_object* v_tk_876_, lean_object* v_alts_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_Elab_Command_getRef___redArg(v___y_878_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v_fileName_883_; lean_object* v_fileMap_884_; lean_object* v_currRecDepth_885_; lean_object* v_cmdPos_886_; lean_object* v_macroStack_887_; lean_object* v_quotContext_x3f_888_; lean_object* v_currMacroScope_889_; lean_object* v_snap_x3f_890_; lean_object* v_cancelTk_x3f_891_; uint8_t v_suppressElabErrors_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_911_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
v_fileName_883_ = lean_ctor_get(v___y_878_, 0);
v_fileMap_884_ = lean_ctor_get(v___y_878_, 1);
v_currRecDepth_885_ = lean_ctor_get(v___y_878_, 2);
v_cmdPos_886_ = lean_ctor_get(v___y_878_, 3);
v_macroStack_887_ = lean_ctor_get(v___y_878_, 4);
v_quotContext_x3f_888_ = lean_ctor_get(v___y_878_, 5);
v_currMacroScope_889_ = lean_ctor_get(v___y_878_, 6);
v_snap_x3f_890_ = lean_ctor_get(v___y_878_, 8);
v_cancelTk_x3f_891_ = lean_ctor_get(v___y_878_, 9);
v_suppressElabErrors_892_ = lean_ctor_get_uint8(v___y_878_, sizeof(void*)*10);
v_isSharedCheck_911_ = !lean_is_exclusive(v___y_878_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; 
v_unused_912_ = lean_ctor_get(v___y_878_, 7);
lean_dec(v_unused_912_);
v___x_894_ = v___y_878_;
v_isShared_895_ = v_isSharedCheck_911_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_cancelTk_x3f_891_);
lean_inc(v_snap_x3f_890_);
lean_inc(v_currMacroScope_889_);
lean_inc(v_quotContext_x3f_888_);
lean_inc(v_macroStack_887_);
lean_inc(v_cmdPos_886_);
lean_inc(v_currRecDepth_885_);
lean_inc(v_fileMap_884_);
lean_inc(v_fileName_883_);
lean_dec(v___y_878_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_911_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v_ref_896_; lean_object* v___x_898_; 
v_ref_896_ = l_Lean_replaceRef(v___x_871_, v_a_882_);
lean_dec(v_a_882_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 7, v_ref_896_);
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_fileName_883_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_fileMap_884_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_currRecDepth_885_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_cmdPos_886_);
lean_ctor_set(v_reuseFailAlloc_910_, 4, v_macroStack_887_);
lean_ctor_set(v_reuseFailAlloc_910_, 5, v_quotContext_x3f_888_);
lean_ctor_set(v_reuseFailAlloc_910_, 6, v_currMacroScope_889_);
lean_ctor_set(v_reuseFailAlloc_910_, 7, v_ref_896_);
lean_ctor_set(v_reuseFailAlloc_910_, 8, v_snap_x3f_890_);
lean_ctor_set(v_reuseFailAlloc_910_, 9, v_cancelTk_x3f_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_910_, sizeof(void*)*10, v_suppressElabErrors_892_);
v___x_898_ = v_reuseFailAlloc_910_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_Elab_Command_resolveSyntaxKind(v___x_872_, v___x_898_, v___y_879_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_901_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
v___x_901_ = l_Lean_Elab_Command_elabMacroRulesAux(v_doc_x3f_873_, v_attrs_x3f_874_, v_attrKind_875_, v_tk_876_, v_a_900_, v_alts_877_, v___x_898_, v___y_879_);
lean_dec_ref(v___x_898_);
return v___x_901_;
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec_ref(v___x_898_);
lean_dec_ref(v_alts_877_);
lean_dec(v_attrKind_875_);
lean_dec(v_doc_x3f_873_);
v_a_902_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_899_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_899_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_878_);
lean_dec_ref(v_alts_877_);
lean_dec(v_attrKind_875_);
lean_dec(v_doc_x3f_873_);
lean_dec(v___x_872_);
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0___boxed(lean_object* v___x_913_, lean_object* v___x_914_, lean_object* v_doc_x3f_915_, lean_object* v_attrs_x3f_916_, lean_object* v_attrKind_917_, lean_object* v_tk_918_, lean_object* v_alts_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Elab_Command_elabMacroRules___lam__0(v___x_913_, v___x_914_, v_doc_x3f_915_, v_attrs_x3f_916_, v_attrKind_917_, v_tk_918_, v_alts_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec(v_tk_918_);
lean_dec(v_attrs_x3f_916_);
lean_dec(v___x_913_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5(lean_object* v___x_927_, lean_object* v___x_928_, lean_object* v_attrKind_929_, lean_object* v___x_930_, lean_object* v___x_931_, lean_object* v_attrs_x3f_932_, lean_object* v___x_933_, lean_object* v___x_934_, lean_object* v___x_935_, lean_object* v_doc_x3f_936_, lean_object* v_kind_x3f_937_, lean_object* v_alts_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_Elab_Command_getRef___redArg(v___y_939_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_944_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v___x_942_, 1);
v___x_944_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_939_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_1012_; 
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v___x_944_, 0);
lean_dec(v_unused_1013_);
v___x_946_ = v___x_944_;
v_isShared_947_ = v_isSharedCheck_1012_;
goto v_resetjp_945_;
}
else
{
lean_dec(v___x_944_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_1012_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_quotContext_x3f_948_; uint8_t v___x_949_; lean_object* v___x_950_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; 
v_quotContext_x3f_948_ = lean_ctor_get(v___y_939_, 5);
v___x_949_ = 0;
v___x_950_ = l_Lean_SourceInfo_fromRef(v_a_943_, v___x_949_);
lean_dec(v_a_943_);
if (lean_obj_tag(v_quotContext_x3f_948_) == 0)
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_940_);
lean_dec_ref(v___x_1011_);
goto v___jp_1005_;
}
else
{
goto v___jp_1005_;
}
v___jp_951_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
lean_inc_ref_n(v___y_954_, 2);
v___x_958_ = l_Array_append___redArg(v___y_954_, v___y_957_);
lean_dec_ref(v___y_957_);
lean_inc_n(v___y_956_, 2);
lean_inc_n(v___x_950_, 3);
v___x_959_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_959_, 0, v___x_950_);
lean_ctor_set(v___x_959_, 1, v___y_956_);
lean_ctor_set(v___x_959_, 2, v___x_958_);
v___x_960_ = l_Array_append___redArg(v___y_954_, v_alts_938_);
v___x_961_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_961_, 0, v___x_950_);
lean_ctor_set(v___x_961_, 1, v___y_956_);
lean_ctor_set(v___x_961_, 2, v___x_960_);
v___x_962_ = l_Lean_Syntax_node1(v___x_950_, v___x_927_, v___x_961_);
v___x_963_ = l_Lean_Syntax_node6(v___x_950_, v___x_928_, v___y_955_, v___y_953_, v_attrKind_929_, v___y_952_, v___x_959_, v___x_962_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_963_);
v___x_965_ = v___x_946_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
v___jp_967_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
lean_inc_ref(v___y_968_);
v___x_972_ = l_Array_append___redArg(v___y_968_, v___y_971_);
lean_dec_ref(v___y_971_);
lean_inc(v___y_970_);
lean_inc_n(v___x_950_, 2);
v___x_973_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_973_, 0, v___x_950_);
lean_ctor_set(v___x_973_, 1, v___y_970_);
lean_ctor_set(v___x_973_, 2, v___x_972_);
v___x_974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_950_);
lean_ctor_set(v___x_974_, 1, v___x_930_);
if (lean_obj_tag(v_kind_x3f_937_) == 0)
{
lean_object* v___x_975_; 
v___x_975_ = lean_mk_empty_array_with_capacity(v___x_931_);
v___y_952_ = v___x_974_;
v___y_953_ = v___x_973_;
v___y_954_ = v___y_968_;
v___y_955_ = v___y_969_;
v___y_956_ = v___y_970_;
v___y_957_ = v___x_975_;
goto v___jp_951_;
}
else
{
lean_object* v_val_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_val_976_ = lean_ctor_get(v_kind_x3f_937_, 0);
lean_inc(v_val_976_);
lean_dec_ref_known(v_kind_x3f_937_, 1);
v___x_977_ = l_Lean_mkIdent(v_val_976_);
v___x_978_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0));
lean_inc_n(v___x_950_, 4);
v___x_979_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_950_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1));
v___x_981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_950_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
v___x_983_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_950_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2));
v___x_985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_950_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = l_Array_mkArray5___redArg(v___x_979_, v___x_981_, v___x_983_, v___x_977_, v___x_985_);
v___y_952_ = v___x_974_;
v___y_953_ = v___x_973_;
v___y_954_ = v___y_968_;
v___y_955_ = v___y_969_;
v___y_956_ = v___y_970_;
v___y_957_ = v___x_986_;
goto v___jp_951_;
}
}
v___jp_987_:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
lean_inc_ref(v___y_988_);
v___x_991_ = l_Array_append___redArg(v___y_988_, v___y_990_);
lean_dec_ref(v___y_990_);
lean_inc(v___y_989_);
lean_inc(v___x_950_);
v___x_992_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_992_, 0, v___x_950_);
lean_ctor_set(v___x_992_, 1, v___y_989_);
lean_ctor_set(v___x_992_, 2, v___x_991_);
if (lean_obj_tag(v_attrs_x3f_932_) == 1)
{
lean_object* v_val_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_val_993_ = lean_ctor_get(v_attrs_x3f_932_, 0);
v___x_994_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
v___x_995_ = l_Lean_Name_mkStr4(v___x_933_, v___x_934_, v___x_935_, v___x_994_);
v___x_996_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
lean_inc_n(v___x_950_, 4);
v___x_997_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_950_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
lean_inc_ref(v___y_988_);
v___x_998_ = l_Array_append___redArg(v___y_988_, v_val_993_);
lean_inc(v___y_989_);
v___x_999_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_999_, 0, v___x_950_);
lean_ctor_set(v___x_999_, 1, v___y_989_);
lean_ctor_set(v___x_999_, 2, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
v___x_1001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_950_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_Syntax_node3(v___x_950_, v___x_995_, v___x_997_, v___x_999_, v___x_1001_);
v___x_1003_ = l_Array_mkArray1___redArg(v___x_1002_);
v___y_968_ = v___y_988_;
v___y_969_ = v___x_992_;
v___y_970_ = v___y_989_;
v___y_971_ = v___x_1003_;
goto v___jp_967_;
}
else
{
lean_object* v___x_1004_; 
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_934_);
lean_dec_ref(v___x_933_);
v___x_1004_ = lean_mk_empty_array_with_capacity(v___x_931_);
v___y_968_ = v___y_988_;
v___y_969_ = v___x_992_;
v___y_970_ = v___y_989_;
v___y_971_ = v___x_1004_;
goto v___jp_967_;
}
}
v___jp_1005_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1007_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
if (lean_obj_tag(v_doc_x3f_936_) == 1)
{
lean_object* v_val_1008_; lean_object* v___x_1009_; 
v_val_1008_ = lean_ctor_get(v_doc_x3f_936_, 0);
lean_inc(v_val_1008_);
lean_dec_ref_known(v_doc_x3f_936_, 1);
v___x_1009_ = l_Array_mkArray1___redArg(v_val_1008_);
v___y_988_ = v___x_1007_;
v___y_989_ = v___x_1006_;
v___y_990_ = v___x_1009_;
goto v___jp_987_;
}
else
{
lean_object* v___x_1010_; 
lean_dec(v_doc_x3f_936_);
v___x_1010_ = lean_mk_empty_array_with_capacity(v___x_931_);
v___y_988_ = v___x_1007_;
v___y_989_ = v___x_1006_;
v___y_990_ = v___x_1010_;
goto v___jp_987_;
}
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec(v_a_943_);
lean_dec(v_kind_x3f_937_);
lean_dec(v_doc_x3f_936_);
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_934_);
lean_dec_ref(v___x_933_);
lean_dec_ref(v___x_930_);
lean_dec(v_attrKind_929_);
lean_dec(v___x_928_);
lean_dec(v___x_927_);
v_a_1014_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_944_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_944_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v_kind_x3f_937_);
lean_dec(v_doc_x3f_936_);
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_934_);
lean_dec_ref(v___x_933_);
lean_dec_ref(v___x_930_);
lean_dec(v_attrKind_929_);
lean_dec(v___x_928_);
lean_dec(v___x_927_);
v_a_1022_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_942_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_942_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5___boxed(lean_object* v___x_1030_, lean_object* v___x_1031_, lean_object* v_attrKind_1032_, lean_object* v___x_1033_, lean_object* v___x_1034_, lean_object* v_attrs_x3f_1035_, lean_object* v___x_1036_, lean_object* v___x_1037_, lean_object* v___x_1038_, lean_object* v_doc_x3f_1039_, lean_object* v_kind_x3f_1040_, lean_object* v_alts_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_Elab_Command_elabMacroRules___lam__5(v___x_1030_, v___x_1031_, v_attrKind_1032_, v___x_1033_, v___x_1034_, v_attrs_x3f_1035_, v___x_1036_, v___x_1037_, v___x_1038_, v_doc_x3f_1039_, v_kind_x3f_1040_, v_alts_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec_ref(v_alts_1041_);
lean_dec(v_attrs_x3f_1035_);
lean_dec(v___x_1034_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1(lean_object* v_stx_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
uint8_t v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; uint8_t v___y_1107_; uint8_t v___y_1108_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; 
v___x_1111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4));
v___x_1112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5));
v___x_1113_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0));
v___x_1114_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1));
lean_inc(v_stx_1098_);
v___x_1115_ = l_Lean_Syntax_isOfKind(v_stx_1098_, v___x_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1181_; 
lean_dec(v_stx_1098_);
v___x_1181_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1181_;
}
else
{
lean_object* v___x_1182_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v_a_1195_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; uint8_t v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; uint8_t v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v_attrs_x3f_1270_; lean_object* v_doc_x3f_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1182_ = lean_unsigned_to_nat(0u);
v___x_1491_ = l_Lean_Syntax_getArg(v_stx_1098_, v___x_1182_);
v___x_1492_ = l_Lean_Syntax_isNone(v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1493_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1491_);
v___x_1494_ = l_Lean_Syntax_matchesNull(v___x_1491_, v___x_1493_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; 
lean_dec(v___x_1491_);
lean_dec(v_stx_1098_);
v___x_1495_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1495_;
}
else
{
lean_object* v_doc_x3f_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
v_doc_x3f_1496_ = l_Lean_Syntax_getArg(v___x_1491_, v___x_1182_);
lean_dec(v___x_1491_);
v___x_1497_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17));
lean_inc(v_doc_x3f_1496_);
v___x_1498_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1496_, v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
lean_dec(v_doc_x3f_1496_);
lean_dec(v_stx_1098_);
v___x_1499_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1500_, 0, v_doc_x3f_1496_);
v_doc_x3f_1475_ = v___x_1500_;
v___y_1476_ = v___y_1099_;
v___y_1477_ = v___y_1100_;
goto v___jp_1474_;
}
}
}
else
{
lean_object* v___x_1501_; 
lean_dec(v___x_1491_);
v___x_1501_ = lean_box(0);
v_doc_x3f_1475_ = v___x_1501_;
v___y_1476_ = v___y_1099_;
v___y_1477_ = v___y_1100_;
goto v___jp_1474_;
}
v___jp_1183_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__31));
v___x_1197_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__32));
v___x_1198_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
if (lean_obj_tag(v___y_1188_) == 1)
{
lean_object* v_val_1199_; lean_object* v___x_1200_; 
v_val_1199_ = lean_ctor_get(v___y_1188_, 0);
lean_inc(v_val_1199_);
lean_dec_ref_known(v___y_1188_, 1);
v___x_1200_ = l_Array_mkArray1___redArg(v_val_1199_);
v___y_1117_ = v___x_1198_;
v___y_1118_ = v_a_1195_;
v___y_1119_ = v___y_1185_;
v___y_1120_ = v___y_1187_;
v___y_1121_ = v___y_1189_;
v___y_1122_ = v___y_1191_;
v___y_1123_ = v___y_1190_;
v___y_1124_ = v___x_1197_;
v___y_1125_ = v___x_1196_;
v___y_1126_ = v___y_1184_;
v___y_1127_ = v___y_1186_;
v___y_1128_ = v___y_1193_;
v___y_1129_ = v___y_1192_;
v___y_1130_ = v___y_1194_;
v___y_1131_ = v___x_1200_;
goto v___jp_1116_;
}
else
{
lean_object* v___x_1201_; 
lean_dec(v___y_1188_);
v___x_1201_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__33));
v___y_1117_ = v___x_1198_;
v___y_1118_ = v_a_1195_;
v___y_1119_ = v___y_1185_;
v___y_1120_ = v___y_1187_;
v___y_1121_ = v___y_1189_;
v___y_1122_ = v___y_1191_;
v___y_1123_ = v___y_1190_;
v___y_1124_ = v___x_1197_;
v___y_1125_ = v___x_1196_;
v___y_1126_ = v___y_1184_;
v___y_1127_ = v___y_1186_;
v___y_1128_ = v___y_1193_;
v___y_1129_ = v___y_1192_;
v___y_1130_ = v___y_1194_;
v___y_1131_ = v___x_1201_;
goto v___jp_1116_;
}
}
v___jp_1202_:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_Elab_Command_getRef___redArg(v___y_1208_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1218_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 1);
v___x_1218_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1208_);
lean_dec_ref(v___y_1208_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1218_, 1);
v___x_1220_ = l_Lean_Parser_Command_visibility_ofAttrKind(v___y_1204_);
v___x_1221_ = l_Lean_SourceInfo_fromRef(v_a_1217_, v___y_1206_);
lean_dec(v_a_1217_);
if (lean_obj_tag(v___y_1203_) == 0)
{
lean_object* v___x_1222_; lean_object* v_a_1223_; 
v___x_1222_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_1214_);
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref(v___x_1222_);
v___y_1184_ = v___x_1221_;
v___y_1185_ = v___x_1220_;
v___y_1186_ = v___y_1211_;
v___y_1187_ = v___y_1205_;
v___y_1188_ = v___y_1212_;
v___y_1189_ = v___y_1207_;
v___y_1190_ = v___y_1209_;
v___y_1191_ = v___y_1210_;
v___y_1192_ = v_a_1219_;
v___y_1193_ = v___y_1215_;
v___y_1194_ = v___y_1213_;
v_a_1195_ = v_a_1223_;
goto v___jp_1183_;
}
else
{
lean_object* v_val_1224_; 
v_val_1224_ = lean_ctor_get(v___y_1203_, 0);
lean_inc(v_val_1224_);
v___y_1184_ = v___x_1221_;
v___y_1185_ = v___x_1220_;
v___y_1186_ = v___y_1211_;
v___y_1187_ = v___y_1205_;
v___y_1188_ = v___y_1212_;
v___y_1189_ = v___y_1207_;
v___y_1190_ = v___y_1209_;
v___y_1191_ = v___y_1210_;
v___y_1192_ = v_a_1219_;
v___y_1193_ = v___y_1215_;
v___y_1194_ = v___y_1213_;
v_a_1195_ = v_val_1224_;
goto v___jp_1183_;
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec(v_a_1217_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1205_);
lean_dec(v___y_1204_);
v_a_1225_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1218_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1218_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
else
{
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1205_);
lean_dec(v___y_1204_);
return v___x_1216_;
}
}
v___jp_1233_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1249_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__34));
lean_inc_ref(v___y_1238_);
v___x_1250_ = l_Lean_Name_mkStr4(v___x_1111_, v___x_1112_, v___y_1238_, v___x_1249_);
v___x_1251_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__37));
v___x_1252_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__38));
lean_inc_n(v___y_1243_, 2);
v___x_1253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___y_1243_);
lean_ctor_set(v___x_1253_, 1, v___x_1251_);
lean_inc(v___y_1244_);
v___x_1254_ = l_Lean_Syntax_node2(v___y_1243_, v___x_1252_, v___x_1253_, v___y_1244_);
lean_inc(v___y_1235_);
v___x_1255_ = l_Lean_Syntax_node2(v___y_1243_, v___x_1250_, v___y_1235_, v___x_1254_);
if (lean_obj_tag(v___y_1246_) == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1256_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_1257_ = lean_mk_empty_array_with_capacity(v___y_1242_);
v___x_1258_ = lean_array_push(v___x_1257_, v___x_1255_);
v___x_1259_ = l_Lean_Syntax_SepArray_ofElems(v___x_1256_, v___x_1258_);
lean_dec_ref(v___x_1258_);
v___y_1203_ = v___y_1234_;
v___y_1204_ = v___y_1235_;
v___y_1205_ = v___y_1236_;
v___y_1206_ = v___y_1237_;
v___y_1207_ = v___y_1238_;
v___y_1208_ = v___y_1239_;
v___y_1209_ = v___y_1240_;
v___y_1210_ = v___y_1241_;
v___y_1211_ = v___y_1244_;
v___y_1212_ = v___y_1245_;
v___y_1213_ = v___y_1247_;
v___y_1214_ = v___y_1248_;
v___y_1215_ = v___x_1259_;
goto v___jp_1202_;
}
else
{
lean_object* v_val_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v_val_1260_ = lean_ctor_get(v___y_1246_, 0);
lean_inc(v_val_1260_);
lean_dec_ref_known(v___y_1246_, 1);
v___x_1261_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_1262_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1260_);
lean_dec(v_val_1260_);
v___x_1263_ = lean_array_push(v___x_1262_, v___x_1255_);
v___x_1264_ = l_Lean_Syntax_SepArray_ofElems(v___x_1261_, v___x_1263_);
lean_dec_ref(v___x_1263_);
v___y_1203_ = v___y_1234_;
v___y_1204_ = v___y_1235_;
v___y_1205_ = v___y_1236_;
v___y_1206_ = v___y_1237_;
v___y_1207_ = v___y_1238_;
v___y_1208_ = v___y_1239_;
v___y_1209_ = v___y_1240_;
v___y_1210_ = v___y_1241_;
v___y_1211_ = v___y_1244_;
v___y_1212_ = v___y_1245_;
v___y_1213_ = v___y_1247_;
v___y_1214_ = v___y_1248_;
v___y_1215_ = v___x_1264_;
goto v___jp_1202_;
}
}
v___jp_1265_:
{
lean_object* v___x_1271_; lean_object* v_attrKind_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1271_ = lean_unsigned_to_nat(2u);
v_attrKind_1272_ = l_Lean_Syntax_getArg(v_stx_1098_, v___x_1271_);
v___x_1273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6));
v___x_1274_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9));
lean_inc(v_attrKind_1272_);
v___x_1275_ = l_Lean_Syntax_isOfKind(v_attrKind_1272_, v___x_1274_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; 
lean_dec(v_attrKind_1272_);
lean_dec(v_attrs_x3f_1270_);
lean_dec(v___y_1266_);
lean_dec(v_stx_1098_);
v___x_1276_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; lean_object* v_tk_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1277_ = lean_unsigned_to_nat(3u);
v_tk_1278_ = l_Lean_Syntax_getArg(v_stx_1098_, v___x_1277_);
v___x_1279_ = lean_unsigned_to_nat(4u);
v___x_1280_ = l_Lean_Syntax_getArg(v_stx_1098_, v___x_1279_);
lean_inc(v___x_1280_);
v___x_1281_ = l_Lean_Syntax_matchesNull(v___x_1280_, v___x_1182_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1280_);
v___x_1283_ = l_Lean_Syntax_matchesNull(v___x_1280_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; 
lean_dec(v___x_1280_);
lean_dec(v_tk_1278_);
lean_dec(v_attrKind_1272_);
lean_dec(v_attrs_x3f_1270_);
lean_dec(v___y_1266_);
lean_dec(v_stx_1098_);
v___x_1284_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1284_;
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1285_ = l_Lean_Syntax_getArg(v_stx_1098_, v___x_1282_);
lean_dec(v_stx_1098_);
v___x_1286_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10));
lean_inc(v___x_1285_);
v___x_1287_ = l_Lean_Syntax_isOfKind(v___x_1285_, v___x_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; 
lean_dec(v___x_1285_);
lean_dec(v___x_1280_);
lean_dec(v_tk_1278_);
lean_dec(v_attrKind_1272_);
lean_dec(v_attrs_x3f_1270_);
lean_dec(v___y_1266_);
v___x_1288_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1288_;
}
else
{
lean_object* v_kind_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v_kind_1289_ = l_Lean_Syntax_getArg(v___x_1280_, v___x_1277_);
lean_dec(v___x_1280_);
v___x_1290_ = l_Lean_Syntax_getArg(v___x_1285_, v___x_1182_);
lean_dec(v___x_1285_);
lean_inc(v___x_1290_);
v___x_1291_ = l_Lean_Syntax_matchesNull(v___x_1290_, v___y_1269_);
if (v___x_1291_ == 0)
{
lean_object* v_alts_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___f_1301_; 
v_alts_1292_ = l_Lean_Syntax_getArgs(v___x_1290_);
lean_dec(v___x_1290_);
v___x_1293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1294_ = lean_box(2);
lean_inc_ref(v_alts_1292_);
v___x_1295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v___x_1293_);
lean_ctor_set(v___x_1295_, 2, v_alts_1292_);
v___x_1296_ = lean_mk_empty_array_with_capacity(v___x_1271_);
lean_inc(v_tk_1278_);
v___x_1297_ = lean_array_push(v___x_1296_, v_tk_1278_);
v___x_1298_ = lean_array_push(v___x_1297_, v___x_1295_);
v___x_1299_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1294_);
lean_ctor_set(v___x_1299_, 1, v___x_1293_);
lean_ctor_set(v___x_1299_, 2, v___x_1298_);
v___x_1300_ = l_Lean_TSyntax_getId(v_kind_1289_);
lean_dec(v_kind_1289_);
lean_inc(v_attrKind_1272_);
v___f_1301_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1301_, 0, v___x_1299_);
lean_closure_set(v___f_1301_, 1, v___x_1300_);
lean_closure_set(v___f_1301_, 2, v___y_1266_);
lean_closure_set(v___f_1301_, 3, v_attrs_x3f_1270_);
lean_closure_set(v___f_1301_, 4, v_attrKind_1272_);
lean_closure_set(v___f_1301_, 5, v_tk_1278_);
lean_closure_set(v___f_1301_, 6, v_alts_1292_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1302_; 
lean_dec(v_attrKind_1272_);
v___x_1302_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1301_, v___x_1275_, v___y_1267_, v___y_1268_);
return v___x_1302_;
}
else
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = l_Lean_Syntax_getArg(v_attrKind_1272_, v___x_1182_);
lean_dec(v_attrKind_1272_);
lean_inc(v___x_1303_);
v___x_1304_ = l_Lean_Syntax_matchesNull(v___x_1303_, v___y_1269_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
lean_dec(v___x_1303_);
v___x_1305_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1301_, v___x_1275_, v___y_1267_, v___y_1268_);
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1306_ = l_Lean_Syntax_getArg(v___x_1303_, v___x_1182_);
lean_dec(v___x_1303_);
v___x_1307_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1308_ = l_Lean_Syntax_isOfKind(v___x_1306_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1301_, v___x_1275_, v___y_1267_, v___y_1268_);
return v___x_1309_;
}
else
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1301_, v___x_1291_, v___y_1267_, v___y_1268_);
return v___x_1310_;
}
}
}
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1311_ = l_Lean_Syntax_getArg(v___x_1290_, v___x_1182_);
v___x_1312_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8));
lean_inc(v___x_1311_);
v___x_1313_ = l_Lean_Syntax_isOfKind(v___x_1311_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_object* v_alts_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___f_1323_; 
lean_dec(v___x_1311_);
v_alts_1314_ = l_Lean_Syntax_getArgs(v___x_1290_);
lean_dec(v___x_1290_);
v___x_1315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1316_ = lean_box(2);
lean_inc_ref(v_alts_1314_);
v___x_1317_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
lean_ctor_set(v___x_1317_, 1, v___x_1315_);
lean_ctor_set(v___x_1317_, 2, v_alts_1314_);
v___x_1318_ = lean_mk_empty_array_with_capacity(v___x_1271_);
lean_inc(v_tk_1278_);
v___x_1319_ = lean_array_push(v___x_1318_, v_tk_1278_);
v___x_1320_ = lean_array_push(v___x_1319_, v___x_1317_);
v___x_1321_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1316_);
lean_ctor_set(v___x_1321_, 1, v___x_1315_);
lean_ctor_set(v___x_1321_, 2, v___x_1320_);
v___x_1322_ = l_Lean_TSyntax_getId(v_kind_1289_);
lean_dec(v_kind_1289_);
lean_inc(v_attrKind_1272_);
v___f_1323_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1323_, 0, v___x_1321_);
lean_closure_set(v___f_1323_, 1, v___x_1322_);
lean_closure_set(v___f_1323_, 2, v___y_1266_);
lean_closure_set(v___f_1323_, 3, v_attrs_x3f_1270_);
lean_closure_set(v___f_1323_, 4, v_attrKind_1272_);
lean_closure_set(v___f_1323_, 5, v_tk_1278_);
lean_closure_set(v___f_1323_, 6, v_alts_1314_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1324_; 
lean_dec(v_attrKind_1272_);
v___x_1324_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1323_, v___x_1275_, v___y_1267_, v___y_1268_);
return v___x_1324_;
}
else
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = l_Lean_Syntax_getArg(v_attrKind_1272_, v___x_1182_);
lean_dec(v_attrKind_1272_);
lean_inc(v___x_1325_);
v___x_1326_ = l_Lean_Syntax_matchesNull(v___x_1325_, v___y_1269_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
lean_dec(v___x_1325_);
v___x_1327_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1323_, v___x_1275_, v___y_1267_, v___y_1268_);
return v___x_1327_;
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1328_ = l_Lean_Syntax_getArg(v___x_1325_, v___x_1182_);
lean_dec(v___x_1325_);
v___x_1329_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1330_ = l_Lean_Syntax_isOfKind(v___x_1328_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1323_, v___x_1275_, v___y_1267_, v___y_1268_);
return v___x_1331_;
}
else
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1323_, v___x_1313_, v___y_1267_, v___y_1268_);
return v___x_1332_;
}
}
}
}
else
{
lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1333_ = l_Lean_Syntax_getArg(v___x_1311_, v___y_1269_);
lean_inc(v___x_1333_);
v___x_1334_ = l_Lean_Syntax_matchesNull(v___x_1333_, v___y_1269_);
if (v___x_1334_ == 0)
{
lean_object* v_alts_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___f_1344_; 
lean_dec(v___x_1333_);
lean_dec(v___x_1311_);
v_alts_1335_ = l_Lean_Syntax_getArgs(v___x_1290_);
lean_dec(v___x_1290_);
v___x_1336_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1337_ = lean_box(2);
lean_inc_ref(v_alts_1335_);
v___x_1338_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
lean_ctor_set(v___x_1338_, 1, v___x_1336_);
lean_ctor_set(v___x_1338_, 2, v_alts_1335_);
v___x_1339_ = lean_mk_empty_array_with_capacity(v___x_1271_);
lean_inc(v_tk_1278_);
v___x_1340_ = lean_array_push(v___x_1339_, v_tk_1278_);
v___x_1341_ = lean_array_push(v___x_1340_, v___x_1338_);
v___x_1342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1337_);
lean_ctor_set(v___x_1342_, 1, v___x_1336_);
lean_ctor_set(v___x_1342_, 2, v___x_1341_);
v___x_1343_ = l_Lean_TSyntax_getId(v_kind_1289_);
lean_dec(v_kind_1289_);
lean_inc(v_attrKind_1272_);
v___f_1344_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1344_, 0, v___x_1342_);
lean_closure_set(v___f_1344_, 1, v___x_1343_);
lean_closure_set(v___f_1344_, 2, v___y_1266_);
lean_closure_set(v___f_1344_, 3, v_attrs_x3f_1270_);
lean_closure_set(v___f_1344_, 4, v_attrKind_1272_);
lean_closure_set(v___f_1344_, 5, v_tk_1278_);
lean_closure_set(v___f_1344_, 6, v_alts_1335_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1345_; 
lean_dec(v_attrKind_1272_);
v___x_1345_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1344_, v___x_1275_, v___y_1267_, v___y_1268_);
return v___x_1345_;
}
else
{
lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1346_ = l_Lean_Syntax_getArg(v_attrKind_1272_, v___x_1182_);
lean_dec(v_attrKind_1272_);
lean_inc(v___x_1346_);
v___x_1347_ = l_Lean_Syntax_matchesNull(v___x_1346_, v___y_1269_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; 
lean_dec(v___x_1346_);
v___x_1348_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1344_, v___x_1275_, v___y_1267_, v___y_1268_);
return v___x_1348_;
}
else
{
lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1349_ = l_Lean_Syntax_getArg(v___x_1346_, v___x_1182_);
lean_dec(v___x_1346_);
v___x_1350_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1351_ = l_Lean_Syntax_isOfKind(v___x_1349_, v___x_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1344_, v___x_1275_, v___y_1267_, v___y_1268_);
return v___x_1352_;
}
else
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1344_, v___x_1334_, v___y_1267_, v___y_1268_);
return v___x_1353_;
}
}
}
}
else
{
lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1354_ = l_Lean_Syntax_getArg(v___x_1333_, v___x_1182_);
lean_dec(v___x_1333_);
lean_inc(v___x_1354_);
v___x_1355_ = l_Lean_Syntax_matchesNull(v___x_1354_, v___y_1269_);
if (v___x_1355_ == 0)
{
lean_object* v_alts_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___f_1365_; 
lean_dec(v___x_1354_);
lean_dec(v___x_1311_);
v_alts_1356_ = l_Lean_Syntax_getArgs(v___x_1290_);
lean_dec(v___x_1290_);
v___x_1357_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1358_ = lean_box(2);
lean_inc_ref(v_alts_1356_);
v___x_1359_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
lean_ctor_set(v___x_1359_, 1, v___x_1357_);
lean_ctor_set(v___x_1359_, 2, v_alts_1356_);
v___x_1360_ = lean_mk_empty_array_with_capacity(v___x_1271_);
lean_inc(v_tk_1278_);
v___x_1361_ = lean_array_push(v___x_1360_, v_tk_1278_);
v___x_1362_ = lean_array_push(v___x_1361_, v___x_1359_);
v___x_1363_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1358_);
lean_ctor_set(v___x_1363_, 1, v___x_1357_);
lean_ctor_set(v___x_1363_, 2, v___x_1362_);
v___x_1364_ = l_Lean_TSyntax_getId(v_kind_1289_);
lean_dec(v_kind_1289_);
lean_inc(v_attrKind_1272_);
v___f_1365_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1365_, 0, v___x_1363_);
lean_closure_set(v___f_1365_, 1, v___x_1364_);
lean_closure_set(v___f_1365_, 2, v___y_1266_);
lean_closure_set(v___f_1365_, 3, v_attrs_x3f_1270_);
lean_closure_set(v___f_1365_, 4, v_attrKind_1272_);
lean_closure_set(v___f_1365_, 5, v_tk_1278_);
lean_closure_set(v___f_1365_, 6, v_alts_1356_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1366_; 
lean_dec(v_attrKind_1272_);
v___x_1366_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1365_, v___x_1275_, v___y_1267_, v___y_1268_);
return v___x_1366_;
}
else
{
lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1367_ = l_Lean_Syntax_getArg(v_attrKind_1272_, v___x_1182_);
lean_dec(v_attrKind_1272_);
lean_inc(v___x_1367_);
v___x_1368_ = l_Lean_Syntax_matchesNull(v___x_1367_, v___y_1269_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; 
lean_dec(v___x_1367_);
v___x_1369_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1365_, v___x_1275_, v___y_1267_, v___y_1268_);
return v___x_1369_;
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1370_ = l_Lean_Syntax_getArg(v___x_1367_, v___x_1182_);
lean_dec(v___x_1367_);
v___x_1371_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1372_ = l_Lean_Syntax_isOfKind(v___x_1370_, v___x_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1365_, v___x_1275_, v___y_1267_, v___y_1268_);
return v___x_1373_;
}
else
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1365_, v___x_1355_, v___y_1267_, v___y_1268_);
return v___x_1374_;
}
}
}
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1375_ = l_Lean_Syntax_getArg(v___x_1354_, v___x_1182_);
lean_dec(v___x_1354_);
v___x_1376_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14));
lean_inc(v___x_1375_);
v___x_1377_ = l_Lean_Syntax_isOfKind(v___x_1375_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_object* v_alts_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___f_1387_; 
lean_dec(v___x_1375_);
lean_dec(v___x_1311_);
v_alts_1378_ = l_Lean_Syntax_getArgs(v___x_1290_);
lean_dec(v___x_1290_);
v___x_1379_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1380_ = lean_box(2);
lean_inc_ref(v_alts_1378_);
v___x_1381_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
lean_ctor_set(v___x_1381_, 1, v___x_1379_);
lean_ctor_set(v___x_1381_, 2, v_alts_1378_);
v___x_1382_ = lean_mk_empty_array_with_capacity(v___x_1271_);
lean_inc(v_tk_1278_);
v___x_1383_ = lean_array_push(v___x_1382_, v_tk_1278_);
v___x_1384_ = lean_array_push(v___x_1383_, v___x_1381_);
v___x_1385_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1380_);
lean_ctor_set(v___x_1385_, 1, v___x_1379_);
lean_ctor_set(v___x_1385_, 2, v___x_1384_);
v___x_1386_ = l_Lean_TSyntax_getId(v_kind_1289_);
lean_dec(v_kind_1289_);
lean_inc(v_attrKind_1272_);
v___f_1387_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1387_, 0, v___x_1385_);
lean_closure_set(v___f_1387_, 1, v___x_1386_);
lean_closure_set(v___f_1387_, 2, v___y_1266_);
lean_closure_set(v___f_1387_, 3, v_attrs_x3f_1270_);
lean_closure_set(v___f_1387_, 4, v_attrKind_1272_);
lean_closure_set(v___f_1387_, 5, v_tk_1278_);
lean_closure_set(v___f_1387_, 6, v_alts_1378_);
if (v___x_1275_ == 0)
{
lean_dec(v_attrKind_1272_);
v___y_1103_ = v___x_1377_;
v___y_1104_ = v___y_1267_;
v___y_1105_ = v___f_1387_;
v___y_1106_ = v___y_1268_;
v___y_1107_ = v___x_1355_;
v___y_1108_ = v___x_1377_;
goto v___jp_1102_;
}
else
{
lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1388_ = l_Lean_Syntax_getArg(v_attrKind_1272_, v___x_1182_);
lean_dec(v_attrKind_1272_);
lean_inc(v___x_1388_);
v___x_1389_ = l_Lean_Syntax_matchesNull(v___x_1388_, v___y_1269_);
if (v___x_1389_ == 0)
{
lean_dec(v___x_1388_);
v___y_1103_ = v___x_1377_;
v___y_1104_ = v___y_1267_;
v___y_1105_ = v___f_1387_;
v___y_1106_ = v___y_1268_;
v___y_1107_ = v___x_1355_;
v___y_1108_ = v___x_1377_;
goto v___jp_1102_;
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1390_ = l_Lean_Syntax_getArg(v___x_1388_, v___x_1182_);
lean_dec(v___x_1388_);
v___x_1391_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1392_ = l_Lean_Syntax_isOfKind(v___x_1390_, v___x_1391_);
if (v___x_1392_ == 0)
{
v___y_1103_ = v___x_1377_;
v___y_1104_ = v___y_1267_;
v___y_1105_ = v___f_1387_;
v___y_1106_ = v___y_1268_;
v___y_1107_ = v___x_1355_;
v___y_1108_ = v___x_1377_;
goto v___jp_1102_;
}
else
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1387_, v___x_1377_, v___y_1267_, v___y_1268_);
return v___x_1393_;
}
}
}
}
else
{
lean_object* v___x_1394_; 
lean_dec(v___x_1290_);
v___x_1394_ = l_Lean_Elab_Command_getRef___redArg(v___y_1267_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v_fileName_1396_; lean_object* v_fileMap_1397_; lean_object* v_currRecDepth_1398_; lean_object* v_cmdPos_1399_; lean_object* v_macroStack_1400_; lean_object* v_quotContext_x3f_1401_; lean_object* v_currMacroScope_1402_; lean_object* v_snap_x3f_1403_; lean_object* v_cancelTk_x3f_1404_; uint8_t v_suppressElabErrors_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v_ref_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1394_, 1);
v_fileName_1396_ = lean_ctor_get(v___y_1267_, 0);
v_fileMap_1397_ = lean_ctor_get(v___y_1267_, 1);
v_currRecDepth_1398_ = lean_ctor_get(v___y_1267_, 2);
v_cmdPos_1399_ = lean_ctor_get(v___y_1267_, 3);
v_macroStack_1400_ = lean_ctor_get(v___y_1267_, 4);
v_quotContext_x3f_1401_ = lean_ctor_get(v___y_1267_, 5);
v_currMacroScope_1402_ = lean_ctor_get(v___y_1267_, 6);
v_snap_x3f_1403_ = lean_ctor_get(v___y_1267_, 8);
v_cancelTk_x3f_1404_ = lean_ctor_get(v___y_1267_, 9);
v_suppressElabErrors_1405_ = lean_ctor_get_uint8(v___y_1267_, sizeof(void*)*10);
v___x_1406_ = l_Lean_Syntax_getArg(v___x_1311_, v___x_1277_);
lean_dec(v___x_1311_);
v___x_1407_ = lean_mk_empty_array_with_capacity(v___x_1271_);
lean_inc(v_tk_1278_);
v___x_1408_ = lean_array_push(v___x_1407_, v_tk_1278_);
lean_inc(v___x_1406_);
v___x_1409_ = lean_array_push(v___x_1408_, v___x_1406_);
v___x_1410_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1411_ = lean_box(2);
v___x_1412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
lean_ctor_set(v___x_1412_, 1, v___x_1410_);
lean_ctor_set(v___x_1412_, 2, v___x_1409_);
v_ref_1413_ = l_Lean_replaceRef(v___x_1412_, v_a_1395_);
lean_dec(v_a_1395_);
lean_dec_ref_known(v___x_1412_, 3);
lean_inc(v_cancelTk_x3f_1404_);
lean_inc(v_snap_x3f_1403_);
lean_inc(v_currMacroScope_1402_);
lean_inc(v_quotContext_x3f_1401_);
lean_inc(v_macroStack_1400_);
lean_inc(v_cmdPos_1399_);
lean_inc(v_currRecDepth_1398_);
lean_inc_ref(v_fileMap_1397_);
lean_inc_ref(v_fileName_1396_);
v___x_1414_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1414_, 0, v_fileName_1396_);
lean_ctor_set(v___x_1414_, 1, v_fileMap_1397_);
lean_ctor_set(v___x_1414_, 2, v_currRecDepth_1398_);
lean_ctor_set(v___x_1414_, 3, v_cmdPos_1399_);
lean_ctor_set(v___x_1414_, 4, v_macroStack_1400_);
lean_ctor_set(v___x_1414_, 5, v_quotContext_x3f_1401_);
lean_ctor_set(v___x_1414_, 6, v_currMacroScope_1402_);
lean_ctor_set(v___x_1414_, 7, v_ref_1413_);
lean_ctor_set(v___x_1414_, 8, v_snap_x3f_1403_);
lean_ctor_set(v___x_1414_, 9, v_cancelTk_x3f_1404_);
lean_ctor_set_uint8(v___x_1414_, sizeof(void*)*10, v_suppressElabErrors_1405_);
v___x_1415_ = l_Lean_Elab_Command_getRef___redArg(v___x_1414_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1417_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v___x_1417_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_1414_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v___x_1418_; 
lean_dec_ref_known(v___x_1417_, 1);
v___x_1418_ = l_Lean_SourceInfo_fromRef(v_a_1416_, v___x_1281_);
lean_dec(v_a_1416_);
if (lean_obj_tag(v_quotContext_x3f_1401_) == 0)
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_1268_);
lean_dec_ref(v___x_1419_);
v___y_1234_ = v_quotContext_x3f_1401_;
v___y_1235_ = v_attrKind_1272_;
v___y_1236_ = v_tk_1278_;
v___y_1237_ = v___x_1281_;
v___y_1238_ = v___x_1273_;
v___y_1239_ = v___x_1414_;
v___y_1240_ = v___x_1406_;
v___y_1241_ = v___x_1375_;
v___y_1242_ = v___y_1269_;
v___y_1243_ = v___x_1418_;
v___y_1244_ = v_kind_1289_;
v___y_1245_ = v___y_1266_;
v___y_1246_ = v_attrs_x3f_1270_;
v___y_1247_ = v___x_1410_;
v___y_1248_ = v___y_1268_;
goto v___jp_1233_;
}
else
{
v___y_1234_ = v_quotContext_x3f_1401_;
v___y_1235_ = v_attrKind_1272_;
v___y_1236_ = v_tk_1278_;
v___y_1237_ = v___x_1281_;
v___y_1238_ = v___x_1273_;
v___y_1239_ = v___x_1414_;
v___y_1240_ = v___x_1406_;
v___y_1241_ = v___x_1375_;
v___y_1242_ = v___y_1269_;
v___y_1243_ = v___x_1418_;
v___y_1244_ = v_kind_1289_;
v___y_1245_ = v___y_1266_;
v___y_1246_ = v_attrs_x3f_1270_;
v___y_1247_ = v___x_1410_;
v___y_1248_ = v___y_1268_;
goto v___jp_1233_;
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec(v_a_1416_);
lean_dec_ref_known(v___x_1414_, 10);
lean_dec(v___x_1406_);
lean_dec(v___x_1375_);
lean_dec(v_kind_1289_);
lean_dec(v_tk_1278_);
lean_dec(v_attrKind_1272_);
lean_dec(v_attrs_x3f_1270_);
lean_dec(v___y_1266_);
v_a_1420_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1417_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1417_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1414_, 10);
lean_dec(v___x_1406_);
lean_dec(v___x_1375_);
lean_dec(v_kind_1289_);
lean_dec(v_tk_1278_);
lean_dec(v_attrKind_1272_);
lean_dec(v_attrs_x3f_1270_);
lean_dec(v___y_1266_);
return v___x_1415_;
}
}
else
{
lean_dec(v___x_1375_);
lean_dec(v___x_1311_);
lean_dec(v_kind_1289_);
lean_dec(v_tk_1278_);
lean_dec(v_attrKind_1272_);
lean_dec(v_attrs_x3f_1270_);
lean_dec(v___y_1266_);
return v___x_1394_;
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
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
lean_dec(v___x_1280_);
v___x_1428_ = lean_unsigned_to_nat(5u);
v___x_1429_ = l_Lean_Syntax_getArg(v_stx_1098_, v___x_1428_);
lean_dec(v_stx_1098_);
v___x_1430_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10));
lean_inc(v___x_1429_);
v___x_1431_ = l_Lean_Syntax_isOfKind(v___x_1429_, v___x_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; 
lean_dec(v___x_1429_);
lean_dec(v_tk_1278_);
lean_dec(v_attrKind_1272_);
lean_dec(v_attrs_x3f_1270_);
lean_dec(v___y_1266_);
v___x_1432_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_Elab_Command_getRef___redArg(v___y_1267_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v_fileName_1435_; lean_object* v_fileMap_1436_; lean_object* v_currRecDepth_1437_; lean_object* v_cmdPos_1438_; lean_object* v_macroStack_1439_; lean_object* v_quotContext_x3f_1440_; lean_object* v_currMacroScope_1441_; lean_object* v_snap_x3f_1442_; lean_object* v_cancelTk_x3f_1443_; uint8_t v_suppressElabErrors_1444_; lean_object* v___x_1445_; lean_object* v_alts_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___f_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v_ref_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v_fileName_1435_ = lean_ctor_get(v___y_1267_, 0);
v_fileMap_1436_ = lean_ctor_get(v___y_1267_, 1);
v_currRecDepth_1437_ = lean_ctor_get(v___y_1267_, 2);
v_cmdPos_1438_ = lean_ctor_get(v___y_1267_, 3);
v_macroStack_1439_ = lean_ctor_get(v___y_1267_, 4);
v_quotContext_x3f_1440_ = lean_ctor_get(v___y_1267_, 5);
v_currMacroScope_1441_ = lean_ctor_get(v___y_1267_, 6);
v_snap_x3f_1442_ = lean_ctor_get(v___y_1267_, 8);
v_cancelTk_x3f_1443_ = lean_ctor_get(v___y_1267_, 9);
v_suppressElabErrors_1444_ = lean_ctor_get_uint8(v___y_1267_, sizeof(void*)*10);
v___x_1445_ = l_Lean_Syntax_getArg(v___x_1429_, v___x_1182_);
lean_dec(v___x_1429_);
v_alts_1446_ = l_Lean_Syntax_getArgs(v___x_1445_);
lean_dec(v___x_1445_);
v___x_1447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1448_ = lean_box(2);
lean_inc_ref(v_alts_1446_);
v___x_1449_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
lean_ctor_set(v___x_1449_, 1, v___x_1447_);
lean_ctor_set(v___x_1449_, 2, v_alts_1446_);
v___f_1450_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__5___boxed), 15, 10);
lean_closure_set(v___f_1450_, 0, v___x_1430_);
lean_closure_set(v___f_1450_, 1, v___x_1114_);
lean_closure_set(v___f_1450_, 2, v_attrKind_1272_);
lean_closure_set(v___f_1450_, 3, v___x_1113_);
lean_closure_set(v___f_1450_, 4, v___x_1182_);
lean_closure_set(v___f_1450_, 5, v_attrs_x3f_1270_);
lean_closure_set(v___f_1450_, 6, v___x_1111_);
lean_closure_set(v___f_1450_, 7, v___x_1112_);
lean_closure_set(v___f_1450_, 8, v___x_1273_);
lean_closure_set(v___f_1450_, 9, v___y_1266_);
v___x_1451_ = lean_mk_empty_array_with_capacity(v___x_1271_);
v___x_1452_ = lean_array_push(v___x_1451_, v_tk_1278_);
v___x_1453_ = lean_array_push(v___x_1452_, v___x_1449_);
v___x_1454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1448_);
lean_ctor_set(v___x_1454_, 1, v___x_1447_);
lean_ctor_set(v___x_1454_, 2, v___x_1453_);
v_ref_1455_ = l_Lean_replaceRef(v___x_1454_, v_a_1434_);
lean_dec(v_a_1434_);
lean_dec_ref_known(v___x_1454_, 3);
lean_inc(v_cancelTk_x3f_1443_);
lean_inc(v_snap_x3f_1442_);
lean_inc(v_currMacroScope_1441_);
lean_inc(v_quotContext_x3f_1440_);
lean_inc(v_macroStack_1439_);
lean_inc(v_cmdPos_1438_);
lean_inc(v_currRecDepth_1437_);
lean_inc_ref(v_fileMap_1436_);
lean_inc_ref(v_fileName_1435_);
v___x_1456_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1456_, 0, v_fileName_1435_);
lean_ctor_set(v___x_1456_, 1, v_fileMap_1436_);
lean_ctor_set(v___x_1456_, 2, v_currRecDepth_1437_);
lean_ctor_set(v___x_1456_, 3, v_cmdPos_1438_);
lean_ctor_set(v___x_1456_, 4, v_macroStack_1439_);
lean_ctor_set(v___x_1456_, 5, v_quotContext_x3f_1440_);
lean_ctor_set(v___x_1456_, 6, v_currMacroScope_1441_);
lean_ctor_set(v___x_1456_, 7, v_ref_1455_);
lean_ctor_set(v___x_1456_, 8, v_snap_x3f_1442_);
lean_ctor_set(v___x_1456_, 9, v_cancelTk_x3f_1443_);
lean_ctor_set_uint8(v___x_1456_, sizeof(void*)*10, v_suppressElabErrors_1444_);
v___x_1457_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(v_alts_1446_, v___x_1113_, v___f_1450_, v___x_1456_, v___y_1268_);
lean_dec_ref_known(v___x_1456_, 10);
lean_dec_ref(v_alts_1446_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
v_a_1466_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1457_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1457_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
else
{
lean_dec(v___x_1429_);
lean_dec(v_tk_1278_);
lean_dec(v_attrKind_1272_);
lean_dec(v_attrs_x3f_1270_);
lean_dec(v___y_1266_);
return v___x_1433_;
}
}
}
}
}
v___jp_1474_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1478_ = lean_unsigned_to_nat(1u);
v___x_1479_ = l_Lean_Syntax_getArg(v_stx_1098_, v___x_1478_);
v___x_1480_ = l_Lean_Syntax_isNone(v___x_1479_);
if (v___x_1480_ == 0)
{
uint8_t v___x_1481_; 
lean_inc(v___x_1479_);
v___x_1481_ = l_Lean_Syntax_matchesNull(v___x_1479_, v___x_1478_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; 
lean_dec(v___x_1479_);
lean_dec(v_doc_x3f_1475_);
lean_dec(v_stx_1098_);
v___x_1482_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1482_;
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; 
v___x_1483_ = l_Lean_Syntax_getArg(v___x_1479_, v___x_1182_);
lean_dec(v___x_1479_);
v___x_1484_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15));
lean_inc(v___x_1483_);
v___x_1485_ = l_Lean_Syntax_isOfKind(v___x_1483_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; 
lean_dec(v___x_1483_);
lean_dec(v_doc_x3f_1475_);
lean_dec(v_stx_1098_);
v___x_1486_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1486_;
}
else
{
lean_object* v___x_1487_; lean_object* v_attrs_x3f_1488_; lean_object* v___x_1489_; 
v___x_1487_ = l_Lean_Syntax_getArg(v___x_1483_, v___x_1478_);
lean_dec(v___x_1483_);
v_attrs_x3f_1488_ = l_Lean_Syntax_getArgs(v___x_1487_);
lean_dec(v___x_1487_);
v___x_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1489_, 0, v_attrs_x3f_1488_);
v___y_1266_ = v_doc_x3f_1475_;
v___y_1267_ = v___y_1476_;
v___y_1268_ = v___y_1477_;
v___y_1269_ = v___x_1478_;
v_attrs_x3f_1270_ = v___x_1489_;
goto v___jp_1265_;
}
}
}
else
{
lean_object* v___x_1490_; 
lean_dec(v___x_1479_);
v___x_1490_ = lean_box(0);
v___y_1266_ = v_doc_x3f_1475_;
v___y_1267_ = v___y_1476_;
v___y_1268_ = v___y_1477_;
v___y_1269_ = v___x_1478_;
v_attrs_x3f_1270_ = v___x_1490_;
goto v___jp_1265_;
}
}
}
v___jp_1102_:
{
if (v___y_1108_ == 0)
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1105_, v___y_1107_, v___y_1104_, v___y_1106_);
return v___x_1109_;
}
else
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1105_, v___y_1103_, v___y_1104_, v___y_1106_);
return v___x_1110_;
}
}
v___jp_1116_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_inc_ref_n(v___y_1117_, 3);
v___x_1132_ = l_Array_append___redArg(v___y_1117_, v___y_1131_);
lean_dec_ref(v___y_1131_);
lean_inc_n(v___y_1130_, 6);
lean_inc_n(v___y_1126_, 17);
v___x_1133_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1133_, 0, v___y_1126_);
lean_ctor_set(v___x_1133_, 1, v___y_1130_);
lean_ctor_set(v___x_1133_, 2, v___x_1132_);
v___x_1134_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
lean_inc_ref_n(v___y_1121_, 2);
v___x_1135_ = l_Lean_Name_mkStr4(v___x_1111_, v___x_1112_, v___y_1121_, v___x_1134_);
v___x_1136_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
v___x_1137_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___y_1126_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = l_Array_append___redArg(v___y_1117_, v___y_1128_);
lean_dec_ref(v___y_1128_);
v___x_1139_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1139_, 0, v___y_1126_);
lean_ctor_set(v___x_1139_, 1, v___y_1130_);
lean_ctor_set(v___x_1139_, 2, v___x_1138_);
v___x_1140_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
v___x_1141_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___y_1126_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = l_Lean_Syntax_node3(v___y_1126_, v___x_1135_, v___x_1137_, v___x_1139_, v___x_1141_);
v___x_1143_ = l_Lean_Syntax_node1(v___y_1126_, v___y_1130_, v___x_1142_);
lean_inc_ref(v___y_1125_);
v___x_1144_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___y_1126_);
lean_ctor_set(v___x_1144_, 1, v___y_1125_);
v___x_1145_ = l_Lean_TSyntax_getId(v___y_1127_);
v___x_1146_ = l_Lean_mkIdentFrom(v___y_1120_, v___x_1145_, v___x_1115_);
lean_dec(v___y_1120_);
v___x_1147_ = l_Lean_Syntax_node2(v___y_1126_, v___y_1130_, v___x_1146_, v___y_1127_);
v___x_1148_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__6));
v___x_1149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___y_1126_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__8, &l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8);
v___x_1151_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__9));
v___x_1152_ = l_Lean_addMacroScope(v___y_1118_, v___x_1151_, v___y_1129_);
v___x_1153_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6));
v___x_1154_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1154_, 0, v___y_1126_);
lean_ctor_set(v___x_1154_, 1, v___x_1150_);
lean_ctor_set(v___x_1154_, 2, v___x_1152_);
lean_ctor_set(v___x_1154_, 3, v___x_1153_);
v___x_1155_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
v___x_1156_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___y_1126_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__11));
v___x_1158_ = l_Lean_Name_mkStr4(v___x_1111_, v___x_1112_, v___y_1121_, v___x_1157_);
v___x_1159_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___y_1126_);
lean_ctor_set(v___x_1159_, 1, v___x_1157_);
v___x_1160_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7));
v___x_1161_ = l_Lean_Name_mkStr4(v___x_1111_, v___x_1112_, v___y_1121_, v___x_1160_);
v___x_1162_ = l_Lean_Syntax_node1(v___y_1126_, v___y_1130_, v___y_1122_);
v___x_1163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1163_, 0, v___y_1126_);
lean_ctor_set(v___x_1163_, 1, v___y_1130_);
lean_ctor_set(v___x_1163_, 2, v___y_1117_);
v___x_1164_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13));
v___x_1165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___y_1126_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = l_Lean_Syntax_node4(v___y_1126_, v___x_1161_, v___x_1162_, v___x_1163_, v___x_1165_, v___y_1123_);
v___x_1167_ = l_Lean_Syntax_node2(v___y_1126_, v___x_1158_, v___x_1159_, v___x_1166_);
v___x_1168_ = lean_unsigned_to_nat(9u);
v___x_1169_ = lean_mk_empty_array_with_capacity(v___x_1168_);
v___x_1170_ = lean_array_push(v___x_1169_, v___x_1133_);
v___x_1171_ = lean_array_push(v___x_1170_, v___x_1143_);
v___x_1172_ = lean_array_push(v___x_1171_, v___y_1119_);
v___x_1173_ = lean_array_push(v___x_1172_, v___x_1144_);
v___x_1174_ = lean_array_push(v___x_1173_, v___x_1147_);
v___x_1175_ = lean_array_push(v___x_1174_, v___x_1149_);
v___x_1176_ = lean_array_push(v___x_1175_, v___x_1154_);
v___x_1177_ = lean_array_push(v___x_1176_, v___x_1156_);
v___x_1178_ = lean_array_push(v___x_1177_, v___x_1167_);
lean_inc(v___y_1124_);
v___x_1179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1179_, 0, v___y_1126_);
lean_ctor_set(v___x_1179_, 1, v___y_1124_);
lean_ctor_set(v___x_1179_, 2, v___x_1178_);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___boxed(lean_object* v_stx_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_Elab_Command_elabMacroRules___lam__1(v_stx_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules(lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v___f_1512_; lean_object* v___x_1513_; 
v___f_1512_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___closed__0));
v___x_1513_ = l_Lean_Elab_Command_adaptExpander(v___f_1512_, v_a_1508_, v_a_1509_, v_a_1510_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___boxed(lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_Elab_Command_elabMacroRules(v_a_1514_, v_a_1515_, v_a_1516_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1(){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1526_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1527_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1));
v___x_1528_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1));
v___x_1529_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___boxed), 4, 0);
v___x_1530_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1526_, v___x_1527_, v___x_1528_, v___x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___boxed(lean_object* v_a_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1();
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3(){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1));
v___x_1560_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6));
v___x_1561_ = l_Lean_addBuiltinDeclarationRanges(v___x_1559_, v___x_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___boxed(lean_object* v_a_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3();
return v_res_1563_;
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
