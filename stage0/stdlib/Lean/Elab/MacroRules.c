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
lean_object* lean_mk_syntax_ident(lean_object*);
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
static const lean_string_object l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabMacroRules"};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(122, 95, 207, 180, 64, 53, 80, 160)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(38) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(68) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__0_value),((lean_object*)(((size_t)(38) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__1_value),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(42) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__3_value),((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__4_value),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___boxed(lean_object*);
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
v___x_42_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v___x_41_);
lean_ctor_set(v___x_42_, 2, v___x_41_);
lean_ctor_set(v___x_42_, 3, v___x_40_);
lean_ctor_set(v___x_42_, 4, v___x_40_);
lean_ctor_set(v___x_42_, 5, v___x_40_);
lean_ctor_set(v___x_42_, 6, v___x_40_);
lean_ctor_set(v___x_42_, 7, v___x_40_);
lean_ctor_set(v___x_42_, 8, v___x_40_);
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
lean_dec_ref(v___x_113_);
if (lean_obj_tag(v_val_115_) == 1)
{
uint8_t v_v_116_; 
v_v_116_ = lean_ctor_get_uint8(v_val_115_, 0);
lean_dec_ref(v_val_115_);
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
lean_dec_ref(v___x_167_);
v_macroStack_169_ = lean_ctor_get(v___y_164_, 4);
lean_inc(v_macroStack_169_);
lean_dec_ref(v___y_164_);
v___x_170_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msg_163_, v___y_165_);
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref(v___x_170_);
lean_inc(v_macroStack_169_);
v___x_172_ = l_Lean_Elab_getBetterRef(v_a_168_, v_macroStack_169_);
lean_dec(v_a_168_);
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
lean_dec_ref(v___y_164_);
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
lean_object* v_a_202_; lean_object* v_fileName_203_; lean_object* v_fileMap_204_; lean_object* v_currRecDepth_205_; lean_object* v_cmdPos_206_; lean_object* v_macroStack_207_; lean_object* v_quotContext_x3f_208_; lean_object* v_currMacroScope_209_; lean_object* v_snap_x3f_210_; lean_object* v_cancelTk_x3f_211_; uint8_t v_suppressElabErrors_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_221_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_a_202_);
lean_dec_ref(v___x_201_);
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
v_isSharedCheck_221_ = !lean_is_exclusive(v___y_198_);
if (v_isSharedCheck_221_ == 0)
{
lean_object* v_unused_222_; 
v_unused_222_ = lean_ctor_get(v___y_198_, 7);
lean_dec(v_unused_222_);
v___x_214_ = v___y_198_;
v_isShared_215_ = v_isSharedCheck_221_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_cancelTk_x3f_211_);
lean_inc(v_snap_x3f_210_);
lean_inc(v_currMacroScope_209_);
lean_inc(v_quotContext_x3f_208_);
lean_inc(v_macroStack_207_);
lean_inc(v_cmdPos_206_);
lean_inc(v_currRecDepth_205_);
lean_inc(v_fileMap_204_);
lean_inc(v_fileName_203_);
lean_dec(v___y_198_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_221_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v_ref_216_; lean_object* v___x_218_; 
v_ref_216_ = l_Lean_replaceRef(v_ref_196_, v_a_202_);
lean_dec(v_a_202_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 7, v_ref_216_);
v___x_218_ = v___x_214_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_fileName_203_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_fileMap_204_);
lean_ctor_set(v_reuseFailAlloc_220_, 2, v_currRecDepth_205_);
lean_ctor_set(v_reuseFailAlloc_220_, 3, v_cmdPos_206_);
lean_ctor_set(v_reuseFailAlloc_220_, 4, v_macroStack_207_);
lean_ctor_set(v_reuseFailAlloc_220_, 5, v_quotContext_x3f_208_);
lean_ctor_set(v_reuseFailAlloc_220_, 6, v_currMacroScope_209_);
lean_ctor_set(v_reuseFailAlloc_220_, 7, v_ref_216_);
lean_ctor_set(v_reuseFailAlloc_220_, 8, v_snap_x3f_210_);
lean_ctor_set(v_reuseFailAlloc_220_, 9, v_cancelTk_x3f_211_);
lean_ctor_set_uint8(v_reuseFailAlloc_220_, sizeof(void*)*10, v_suppressElabErrors_212_);
v___x_218_ = v_reuseFailAlloc_220_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_197_, v___x_218_, v___y_199_);
return v___x_219_;
}
}
}
else
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
lean_dec_ref(v___y_198_);
lean_dec_ref(v_msg_197_);
v_a_223_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_201_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_201_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg___boxed(lean_object* v_ref_231_, lean_object* v_msg_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_ref_231_, v_msg_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec(v_ref_231_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(lean_object* v_k_240_, lean_object* v_as_241_, size_t v_sz_242_, size_t v_i_243_, lean_object* v_b_244_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = lean_usize_dec_lt(v_i_243_, v_sz_242_);
if (v___x_245_ == 0)
{
lean_dec(v_k_240_);
return v_b_244_;
}
else
{
lean_object* v___x_246_; lean_object* v_a_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
lean_dec_ref(v_b_244_);
v___x_246_ = lean_box(0);
v_a_247_ = lean_array_uget_borrowed(v_as_241_, v_i_243_);
lean_inc(v_a_247_);
v___x_248_ = l_Lean_Syntax_getKind(v_a_247_);
lean_inc(v_k_240_);
v___x_249_ = l_Lean_Elab_Command_checkRuleKind(v___x_248_, v_k_240_);
lean_dec(v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; size_t v___x_251_; size_t v___x_252_; 
v___x_250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0));
v___x_251_ = ((size_t)1ULL);
v___x_252_ = lean_usize_add(v_i_243_, v___x_251_);
v_i_243_ = v___x_252_;
v_b_244_ = v___x_250_;
goto _start;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec(v_k_240_);
lean_inc(v_a_247_);
v___x_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_254_, 0, v_a_247_);
v___x_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v___x_246_);
return v___x_256_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___boxed(lean_object* v_k_257_, lean_object* v_as_258_, lean_object* v_sz_259_, lean_object* v_i_260_, lean_object* v_b_261_){
_start:
{
size_t v_sz_boxed_262_; size_t v_i_boxed_263_; lean_object* v_res_264_; 
v_sz_boxed_262_ = lean_unbox_usize(v_sz_259_);
lean_dec(v_sz_259_);
v_i_boxed_263_ = lean_unbox_usize(v_i_260_);
lean_dec(v_i_260_);
v_res_264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(v_k_257_, v_as_258_, v_sz_boxed_262_, v_i_boxed_263_, v_b_261_);
lean_dec_ref(v_as_258_);
return v_res_264_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__0));
v___x_267_ = l_Lean_stringToMessageData(v___x_266_);
return v___x_267_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__2));
v___x_270_ = l_Lean_stringToMessageData(v___x_269_);
return v___x_270_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12(void){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Array_mkArray0(lean_box(0));
return v___x_284_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__16));
v___x_291_ = l_Lean_stringToMessageData(v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(lean_object* v_k_292_, size_t v_sz_293_, size_t v_i_294_, lean_object* v_bs_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
uint8_t v___x_299_; 
v___x_299_ = lean_usize_dec_lt(v_i_294_, v_sz_293_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
lean_dec_ref(v___y_296_);
lean_dec(v_k_292_);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v_bs_295_);
return v___x_300_;
}
else
{
lean_object* v_v_301_; lean_object* v___x_302_; lean_object* v_bs_x27_303_; lean_object* v_a_305_; lean_object* v___y_311_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___x_330_; uint8_t v___x_331_; 
v_v_301_ = lean_array_uget(v_bs_295_, v_i_294_);
v___x_302_ = lean_unsigned_to_nat(0u);
v_bs_x27_303_ = lean_array_uset(v_bs_295_, v_i_294_, v___x_302_);
v___x_330_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8));
lean_inc(v_v_301_);
v___x_331_ = l_Lean_Syntax_isOfKind(v_v_301_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; 
lean_dec(v_v_301_);
v___x_332_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
v___y_311_ = v___x_332_;
goto v___jp_310_;
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_333_ = lean_unsigned_to_nat(1u);
v___x_334_ = l_Lean_Syntax_getArg(v_v_301_, v___x_333_);
lean_inc(v___x_334_);
v___x_335_ = l_Lean_Syntax_matchesNull(v___x_334_, v___x_333_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
lean_dec(v___x_334_);
lean_dec(v_v_301_);
v___x_336_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
v___y_311_ = v___x_336_;
goto v___jp_310_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v_pat_355_; lean_object* v___y_357_; lean_object* v___y_358_; uint8_t v___x_410_; 
v___x_337_ = l_Lean_Syntax_getArg(v___x_334_, v___x_302_);
lean_dec(v___x_334_);
v___x_338_ = lean_unsigned_to_nat(3u);
v___x_339_ = l_Lean_Syntax_getArg(v_v_301_, v___x_338_);
v___x_353_ = l_Lean_Syntax_getArgs(v___x_337_);
lean_dec(v___x_337_);
v___x_354_ = lean_box(0);
v_pat_355_ = lean_array_get(v___x_354_, v___x_353_, v___x_302_);
v___x_410_ = l_Lean_Syntax_isQuot(v_pat_355_);
if (v___x_410_ == 0)
{
if (v___x_335_ == 0)
{
lean_inc_ref(v___y_296_);
v___y_357_ = v___y_296_;
v___y_358_ = v___y_297_;
goto v___jp_356_;
}
else
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
if (lean_obj_tag(v___x_411_) == 0)
{
lean_dec_ref(v___x_411_);
lean_inc_ref(v___y_296_);
v___y_357_ = v___y_296_;
v___y_358_ = v___y_297_;
goto v___jp_356_;
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec(v_pat_355_);
lean_dec_ref(v___x_353_);
lean_dec(v___x_339_);
lean_dec_ref(v_bs_x27_303_);
lean_dec(v_v_301_);
lean_dec_ref(v___y_296_);
lean_dec(v_k_292_);
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
else
{
lean_inc_ref(v___y_296_);
v___y_357_ = v___y_296_;
v___y_358_ = v___y_297_;
goto v___jp_356_;
}
v___jp_340_:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9));
lean_inc(v___y_341_);
v___x_344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_344_, 0, v___y_341_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_346_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
v___x_347_ = l_Array_append___redArg(v___x_346_, v___y_342_);
lean_dec_ref(v___y_342_);
lean_inc(v___y_341_);
v___x_348_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_348_, 0, v___y_341_);
lean_ctor_set(v___x_348_, 1, v___x_345_);
lean_ctor_set(v___x_348_, 2, v___x_347_);
lean_inc(v___y_341_);
v___x_349_ = l_Lean_Syntax_node1(v___y_341_, v___x_345_, v___x_348_);
v___x_350_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13));
lean_inc(v___y_341_);
v___x_351_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_351_, 0, v___y_341_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
v___x_352_ = l_Lean_Syntax_node4(v___y_341_, v___x_330_, v___x_344_, v___x_349_, v___x_351_, v___x_339_);
v_a_305_ = v___x_352_;
goto v___jp_304_;
}
v___jp_356_:
{
lean_object* v_quoted_359_; lean_object* v_k_x27_360_; uint8_t v___x_361_; 
lean_inc(v_pat_355_);
v_quoted_359_ = l_Lean_Syntax_getQuotContent(v_pat_355_);
lean_inc(v_quoted_359_);
v_k_x27_360_ = l_Lean_Syntax_getKind(v_quoted_359_);
lean_inc(v_k_292_);
v___x_361_ = l_Lean_Elab_Command_checkRuleKind(v_k_x27_360_, v_k_292_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__15));
v___x_363_ = lean_name_eq(v_k_x27_360_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
lean_dec(v_quoted_359_);
lean_dec(v_pat_355_);
lean_dec_ref(v___x_353_);
lean_dec(v___x_339_);
v___x_364_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17);
v___x_365_ = l_Lean_MessageData_ofName(v_k_x27_360_);
v___x_366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3);
v___x_368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_366_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_v_301_, v___x_368_, v___y_357_, v___y_358_);
lean_dec(v_v_301_);
v___y_311_ = v___x_369_;
goto v___jp_310_;
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; size_t v_sz_372_; size_t v___x_373_; lean_object* v___x_374_; lean_object* v_fst_375_; 
lean_dec(v_k_x27_360_);
v___x_370_ = l_Lean_Syntax_getArgs(v_quoted_359_);
lean_dec(v_quoted_359_);
v___x_371_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0));
v_sz_372_ = lean_array_size(v___x_370_);
v___x_373_ = ((size_t)0ULL);
lean_inc(v_k_292_);
v___x_374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(v_k_292_, v___x_370_, v_sz_372_, v___x_373_, v___x_371_);
lean_dec_ref(v___x_370_);
v_fst_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_fst_375_);
lean_dec_ref(v___x_374_);
if (lean_obj_tag(v_fst_375_) == 0)
{
lean_dec(v_pat_355_);
lean_dec_ref(v___x_353_);
lean_dec(v___x_339_);
v___y_322_ = v___y_358_;
v___y_323_ = v___y_357_;
goto v___jp_321_;
}
else
{
lean_object* v_val_376_; 
v_val_376_ = lean_ctor_get(v_fst_375_, 0);
lean_inc(v_val_376_);
lean_dec_ref(v_fst_375_);
if (lean_obj_tag(v_val_376_) == 0)
{
lean_dec(v_pat_355_);
lean_dec_ref(v___x_353_);
lean_dec(v___x_339_);
v___y_322_ = v___y_358_;
v___y_323_ = v___y_357_;
goto v___jp_321_;
}
else
{
lean_object* v_val_377_; lean_object* v___x_378_; 
lean_dec(v_v_301_);
v_val_377_ = lean_ctor_get(v_val_376_, 0);
lean_inc(v_val_377_);
lean_dec_ref(v_val_376_);
v___x_378_ = l_Lean_Elab_Command_getRef___redArg(v___y_357_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_380_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
lean_dec_ref(v___x_378_);
v___x_380_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_357_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_quotContext_x3f_381_; lean_object* v_pat_382_; lean_object* v_pats_383_; lean_object* v___x_384_; 
lean_dec_ref(v___x_380_);
v_quotContext_x3f_381_ = lean_ctor_get(v___y_357_, 5);
lean_inc(v_quotContext_x3f_381_);
lean_dec_ref(v___y_357_);
v_pat_382_ = l_Lean_Syntax_setArg(v_pat_355_, v___x_333_, v_val_377_);
v_pats_383_ = lean_array_set(v___x_353_, v___x_302_, v_pat_382_);
v___x_384_ = l_Lean_SourceInfo_fromRef(v_a_379_, v___x_361_);
lean_dec(v_a_379_);
if (lean_obj_tag(v_quotContext_x3f_381_) == 0)
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_358_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_dec_ref(v___x_385_);
v___y_341_ = v___x_384_;
v___y_342_ = v_pats_383_;
goto v___jp_340_;
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec(v___x_384_);
lean_dec_ref(v_pats_383_);
lean_dec(v___x_339_);
lean_dec_ref(v_bs_x27_303_);
lean_dec_ref(v___y_296_);
lean_dec(v_k_292_);
v_a_386_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_385_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_385_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
else
{
lean_dec_ref(v_quotContext_x3f_381_);
v___y_341_ = v___x_384_;
v___y_342_ = v_pats_383_;
goto v___jp_340_;
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec(v_a_379_);
lean_dec(v_val_377_);
lean_dec_ref(v___y_357_);
lean_dec(v_pat_355_);
lean_dec_ref(v___x_353_);
lean_dec(v___x_339_);
lean_dec_ref(v_bs_x27_303_);
lean_dec_ref(v___y_296_);
lean_dec(v_k_292_);
v_a_394_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_380_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_380_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec(v_val_377_);
lean_dec_ref(v___y_357_);
lean_dec(v_pat_355_);
lean_dec_ref(v___x_353_);
lean_dec(v___x_339_);
lean_dec_ref(v_bs_x27_303_);
lean_dec_ref(v___y_296_);
lean_dec(v_k_292_);
v_a_402_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_378_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_378_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_x27_360_);
lean_dec(v_quoted_359_);
lean_dec_ref(v___y_357_);
lean_dec(v_pat_355_);
lean_dec_ref(v___x_353_);
lean_dec(v___x_339_);
v_a_305_ = v_v_301_;
goto v___jp_304_;
}
}
}
}
v___jp_304_:
{
size_t v___x_306_; size_t v___x_307_; lean_object* v___x_308_; 
v___x_306_ = ((size_t)1ULL);
v___x_307_ = lean_usize_add(v_i_294_, v___x_306_);
v___x_308_ = lean_array_uset(v_bs_x27_303_, v_i_294_, v_a_305_);
v_i_294_ = v___x_307_;
v_bs_295_ = v___x_308_;
goto _start;
}
v___jp_310_:
{
if (lean_obj_tag(v___y_311_) == 0)
{
lean_object* v_a_312_; 
v_a_312_ = lean_ctor_get(v___y_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref(v___y_311_);
v_a_305_ = v_a_312_;
goto v___jp_304_;
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec_ref(v_bs_x27_303_);
lean_dec_ref(v___y_296_);
lean_dec(v_k_292_);
v_a_313_ = lean_ctor_get(v___y_311_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___y_311_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___y_311_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___y_311_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
v___jp_321_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_324_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1);
lean_inc(v_k_292_);
v___x_325_ = l_Lean_MessageData_ofName(v_k_292_);
v___x_326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_324_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3);
v___x_328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_326_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_v_301_, v___x_328_, v___y_323_, v___y_322_);
lean_dec(v_v_301_);
v___y_311_ = v___x_329_;
goto v___jp_310_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___boxed(lean_object* v_k_420_, lean_object* v_sz_421_, lean_object* v_i_422_, lean_object* v_bs_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
size_t v_sz_boxed_427_; size_t v_i_boxed_428_; lean_object* v_res_429_; 
v_sz_boxed_427_ = lean_unbox_usize(v_sz_421_);
lean_dec(v_sz_421_);
v_i_boxed_428_ = lean_unbox_usize(v_i_422_);
lean_dec(v_i_422_);
v_res_429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(v_k_420_, v_sz_boxed_427_, v_i_boxed_428_, v_bs_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
return v_res_429_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__4(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__3));
v___x_435_ = l_String_toRawSubstring_x27(v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__7));
v___x_441_ = l_String_toRawSubstring_x27(v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__19(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__18));
v___x_454_ = l_String_toRawSubstring_x27(v___x_453_);
return v___x_454_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__26(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__25));
v___x_469_ = l_String_toRawSubstring_x27(v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux(lean_object* v_doc_x3f_496_, lean_object* v_attrs_x3f_497_, lean_object* v_attrKind_498_, lean_object* v_tk_499_, lean_object* v_k_500_, lean_object* v_alts_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
size_t v_sz_505_; size_t v___x_506_; lean_object* v___x_507_; 
v_sz_505_ = lean_array_size(v_alts_501_);
v___x_506_ = ((size_t)0ULL);
lean_inc_ref(v_a_502_);
lean_inc(v_k_500_);
v___x_507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(v_k_500_, v_sz_505_, v___x_506_, v_alts_501_, v_a_502_, v_a_503_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_690_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_690_ == 0)
{
v___x_510_ = v___x_507_;
v_isShared_511_ = v_isSharedCheck_690_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_690_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v_a_629_; lean_object* v___x_638_; 
v___x_638_ = l_Lean_Elab_Command_getRef___redArg(v_a_502_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_640_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref(v___x_638_);
v___x_640_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_502_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_quotContext_x3f_641_; uint8_t v___x_642_; lean_object* v___y_644_; lean_object* v___x_662_; 
lean_dec_ref(v___x_640_);
v_quotContext_x3f_641_ = lean_ctor_get(v_a_502_, 5);
lean_inc(v_quotContext_x3f_641_);
v___x_642_ = 0;
v___x_662_ = l_Lean_SourceInfo_fromRef(v_a_639_, v___x_642_);
lean_dec(v_a_639_);
if (lean_obj_tag(v_quotContext_x3f_641_) == 0)
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v_a_503_);
lean_dec_ref(v___x_681_);
goto v___jp_663_;
}
else
{
goto v___jp_663_;
}
v___jp_643_:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Elab_Command_getRef___redArg(v_a_502_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_647_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref(v___x_645_);
v___x_647_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_502_);
lean_dec_ref(v_a_502_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref(v___x_647_);
v___x_649_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_498_);
v___x_650_ = l_Lean_SourceInfo_fromRef(v_a_646_, v___x_642_);
lean_dec(v_a_646_);
if (lean_obj_tag(v_quotContext_x3f_641_) == 0)
{
lean_object* v___x_651_; lean_object* v_a_652_; 
v___x_651_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v_a_503_);
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref(v___x_651_);
v___y_625_ = v___x_649_;
v___y_626_ = v___y_644_;
v___y_627_ = v_a_648_;
v___y_628_ = v___x_650_;
v_a_629_ = v_a_652_;
goto v___jp_624_;
}
else
{
lean_object* v_val_653_; 
v_val_653_ = lean_ctor_get(v_quotContext_x3f_641_, 0);
lean_inc(v_val_653_);
lean_dec_ref(v_quotContext_x3f_641_);
v___y_625_ = v___x_649_;
v___y_626_ = v___y_644_;
v___y_627_ = v_a_648_;
v___y_628_ = v___x_650_;
v_a_629_ = v_val_653_;
goto v___jp_624_;
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec(v_a_646_);
lean_dec_ref(v___y_644_);
lean_dec(v_quotContext_x3f_641_);
lean_del_object(v___x_510_);
lean_dec(v_a_508_);
lean_dec(v_k_500_);
lean_dec(v_attrKind_498_);
lean_dec(v_doc_x3f_496_);
v_a_654_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_647_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_647_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
else
{
lean_dec_ref(v___y_644_);
lean_dec(v_quotContext_x3f_641_);
lean_del_object(v___x_510_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_502_);
lean_dec(v_k_500_);
lean_dec(v_attrKind_498_);
lean_dec(v_doc_x3f_496_);
return v___x_645_;
}
}
v___jp_663_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_664_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__35));
v___x_665_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__37));
v___x_666_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__38));
lean_inc(v___x_662_);
v___x_667_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_662_);
lean_ctor_set(v___x_667_, 1, v___x_665_);
lean_inc(v_k_500_);
v___x_668_ = lean_mk_syntax_ident(v_k_500_);
lean_inc(v___x_662_);
v___x_669_ = l_Lean_Syntax_node2(v___x_662_, v___x_666_, v___x_667_, v___x_668_);
lean_inc(v_attrKind_498_);
v___x_670_ = l_Lean_Syntax_node2(v___x_662_, v___x_664_, v_attrKind_498_, v___x_669_);
if (lean_obj_tag(v_attrs_x3f_497_) == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_671_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_672_ = lean_unsigned_to_nat(1u);
v___x_673_ = lean_mk_empty_array_with_capacity(v___x_672_);
v___x_674_ = lean_array_push(v___x_673_, v___x_670_);
v___x_675_ = l_Lean_Syntax_SepArray_ofElems(v___x_671_, v___x_674_);
lean_dec_ref(v___x_674_);
v___y_644_ = v___x_675_;
goto v___jp_643_;
}
else
{
lean_object* v_val_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_val_676_ = lean_ctor_get(v_attrs_x3f_497_, 0);
v___x_677_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_678_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_676_);
v___x_679_ = lean_array_push(v___x_678_, v___x_670_);
v___x_680_ = l_Lean_Syntax_SepArray_ofElems(v___x_677_, v___x_679_);
lean_dec_ref(v___x_679_);
v___y_644_ = v___x_680_;
goto v___jp_643_;
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec(v_a_639_);
lean_del_object(v___x_510_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_502_);
lean_dec(v_k_500_);
lean_dec(v_attrKind_498_);
lean_dec(v_doc_x3f_496_);
v_a_682_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_640_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_640_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_del_object(v___x_510_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_502_);
lean_dec(v_k_500_);
lean_dec(v_attrKind_498_);
lean_dec(v_doc_x3f_496_);
return v___x_638_;
}
v___jp_512_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
lean_inc_ref(v___y_518_);
v___x_524_ = l_Array_append___redArg(v___y_518_, v___y_523_);
lean_dec_ref(v___y_523_);
lean_inc(v___y_521_);
lean_inc(v___y_522_);
v___x_525_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_525_, 0, v___y_522_);
lean_ctor_set(v___x_525_, 1, v___y_521_);
lean_ctor_set(v___x_525_, 2, v___x_524_);
v___x_526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5));
v___x_527_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6));
v___x_528_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
lean_inc_ref(v___y_516_);
v___x_529_ = l_Lean_Name_mkStr4(v___y_516_, v___x_526_, v___x_527_, v___x_528_);
v___x_530_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
lean_inc(v___y_522_);
v___x_531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_531_, 0, v___y_522_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
lean_inc_ref(v___y_518_);
v___x_532_ = l_Array_append___redArg(v___y_518_, v___y_520_);
lean_dec_ref(v___y_520_);
lean_inc(v___y_521_);
lean_inc(v___y_522_);
v___x_533_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_533_, 0, v___y_522_);
lean_ctor_set(v___x_533_, 1, v___y_521_);
lean_ctor_set(v___x_533_, 2, v___x_532_);
v___x_534_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
lean_inc(v___y_522_);
v___x_535_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_535_, 0, v___y_522_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
lean_inc(v___y_522_);
v___x_536_ = l_Lean_Syntax_node3(v___y_522_, v___x_529_, v___x_531_, v___x_533_, v___x_535_);
lean_inc(v___y_521_);
lean_inc(v___y_522_);
v___x_537_ = l_Lean_Syntax_node1(v___y_522_, v___y_521_, v___x_536_);
lean_inc(v___y_522_);
v___x_538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_538_, 0, v___y_522_);
lean_ctor_set(v___x_538_, 1, v___y_517_);
v___x_539_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__4, &l_Lean_Elab_Command_elabMacroRulesAux___closed__4_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__4);
v___x_540_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__5));
lean_inc(v___y_519_);
lean_inc(v___y_515_);
v___x_541_ = l_Lean_addMacroScope(v___y_515_, v___x_540_, v___y_519_);
v___x_542_ = lean_box(0);
lean_inc(v___y_522_);
v___x_543_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_543_, 0, v___y_522_);
lean_ctor_set(v___x_543_, 1, v___x_539_);
lean_ctor_set(v___x_543_, 2, v___x_541_);
lean_ctor_set(v___x_543_, 3, v___x_542_);
v___x_544_ = 1;
v___x_545_ = l_Lean_mkIdentFrom(v_tk_499_, v_k_500_, v___x_544_);
lean_inc(v___y_521_);
lean_inc(v___y_522_);
v___x_546_ = l_Lean_Syntax_node2(v___y_522_, v___y_521_, v___x_543_, v___x_545_);
v___x_547_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__6));
lean_inc(v___y_522_);
v___x_548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_548_, 0, v___y_522_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__7));
v___x_550_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__8, &l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8);
v___x_551_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__9));
lean_inc(v___y_519_);
lean_inc(v___y_515_);
v___x_552_ = l_Lean_addMacroScope(v___y_515_, v___x_551_, v___y_519_);
lean_inc_ref(v___y_516_);
v___x_553_ = l_Lean_Name_mkStr2(v___y_516_, v___x_549_);
lean_inc(v___x_553_);
v___x_554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v___x_542_);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
v___x_556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v___x_542_);
v___x_557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_554_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
lean_inc(v___y_522_);
v___x_558_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_558_, 0, v___y_522_);
lean_ctor_set(v___x_558_, 1, v___x_550_);
lean_ctor_set(v___x_558_, 2, v___x_552_);
lean_ctor_set(v___x_558_, 3, v___x_557_);
v___x_559_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
lean_inc(v___y_522_);
v___x_560_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_560_, 0, v___y_522_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__11));
lean_inc_ref(v___y_516_);
v___x_562_ = l_Lean_Name_mkStr4(v___y_516_, v___x_526_, v___x_527_, v___x_561_);
lean_inc(v___y_522_);
v___x_563_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_563_, 0, v___y_522_);
lean_ctor_set(v___x_563_, 1, v___x_561_);
v___x_564_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__12));
lean_inc_ref(v___y_516_);
v___x_565_ = l_Lean_Name_mkStr4(v___y_516_, v___x_526_, v___x_527_, v___x_564_);
v___x_566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7));
lean_inc_ref(v___y_516_);
v___x_567_ = l_Lean_Name_mkStr4(v___y_516_, v___x_526_, v___x_527_, v___x_566_);
v___x_568_ = l_Array_append___redArg(v___y_518_, v_a_508_);
lean_dec(v_a_508_);
v___x_569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9));
lean_inc(v___y_522_);
v___x_570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_570_, 0, v___y_522_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__13));
lean_inc_ref(v___y_516_);
v___x_572_ = l_Lean_Name_mkStr4(v___y_516_, v___x_526_, v___x_527_, v___x_571_);
v___x_573_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__14));
lean_inc(v___y_522_);
v___x_574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_574_, 0, v___y_522_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
lean_inc(v___y_522_);
v___x_575_ = l_Lean_Syntax_node1(v___y_522_, v___x_572_, v___x_574_);
lean_inc(v___y_521_);
lean_inc(v___y_522_);
v___x_576_ = l_Lean_Syntax_node1(v___y_522_, v___y_521_, v___x_575_);
lean_inc(v___y_521_);
lean_inc(v___y_522_);
v___x_577_ = l_Lean_Syntax_node1(v___y_522_, v___y_521_, v___x_576_);
v___x_578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13));
lean_inc(v___y_522_);
v___x_579_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_579_, 0, v___y_522_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__15));
lean_inc_ref(v___y_516_);
v___x_581_ = l_Lean_Name_mkStr4(v___y_516_, v___x_526_, v___x_527_, v___x_580_);
v___x_582_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__16));
lean_inc(v___y_522_);
v___x_583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_583_, 0, v___y_522_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__17));
lean_inc_ref(v___y_516_);
v___x_585_ = l_Lean_Name_mkStr4(v___y_516_, v___x_526_, v___x_527_, v___x_584_);
v___x_586_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__19, &l_Lean_Elab_Command_elabMacroRulesAux___closed__19_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__19);
v___x_587_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__20));
lean_inc(v___y_519_);
lean_inc(v___y_515_);
v___x_588_ = l_Lean_addMacroScope(v___y_515_, v___x_587_, v___y_519_);
v___x_589_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__24));
lean_inc(v___y_522_);
v___x_590_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_590_, 0, v___y_522_);
lean_ctor_set(v___x_590_, 1, v___x_586_);
lean_ctor_set(v___x_590_, 2, v___x_588_);
lean_ctor_set(v___x_590_, 3, v___x_589_);
v___x_591_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__26, &l_Lean_Elab_Command_elabMacroRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__26);
v___x_592_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__27));
v___x_593_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__28));
v___x_594_ = l_Lean_Name_mkStr4(v___y_516_, v___x_549_, v___x_592_, v___x_593_);
lean_inc(v___x_594_);
v___x_595_ = l_Lean_addMacroScope(v___y_515_, v___x_594_, v___y_519_);
lean_inc(v___x_594_);
v___x_596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_542_);
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_594_);
v___x_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set(v___x_598_, 1, v___x_542_);
v___x_599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_596_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
lean_inc(v___y_522_);
v___x_600_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_600_, 0, v___y_522_);
lean_ctor_set(v___x_600_, 1, v___x_591_);
lean_ctor_set(v___x_600_, 2, v___x_595_);
lean_ctor_set(v___x_600_, 3, v___x_599_);
lean_inc(v___y_521_);
lean_inc(v___y_522_);
v___x_601_ = l_Lean_Syntax_node1(v___y_522_, v___y_521_, v___x_600_);
lean_inc(v___y_522_);
v___x_602_ = l_Lean_Syntax_node2(v___y_522_, v___x_585_, v___x_590_, v___x_601_);
lean_inc(v___y_522_);
v___x_603_ = l_Lean_Syntax_node2(v___y_522_, v___x_581_, v___x_583_, v___x_602_);
lean_inc(v___y_522_);
v___x_604_ = l_Lean_Syntax_node4(v___y_522_, v___x_567_, v___x_570_, v___x_577_, v___x_579_, v___x_603_);
v___x_605_ = lean_array_push(v___x_568_, v___x_604_);
lean_inc(v___y_522_);
v___x_606_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_606_, 0, v___y_522_);
lean_ctor_set(v___x_606_, 1, v___y_521_);
lean_ctor_set(v___x_606_, 2, v___x_605_);
lean_inc(v___y_522_);
v___x_607_ = l_Lean_Syntax_node1(v___y_522_, v___x_565_, v___x_606_);
lean_inc(v___y_522_);
v___x_608_ = l_Lean_Syntax_node2(v___y_522_, v___x_562_, v___x_563_, v___x_607_);
v___x_609_ = lean_unsigned_to_nat(9u);
v___x_610_ = lean_mk_empty_array_with_capacity(v___x_609_);
v___x_611_ = lean_array_push(v___x_610_, v___x_525_);
v___x_612_ = lean_array_push(v___x_611_, v___x_537_);
v___x_613_ = lean_array_push(v___x_612_, v___y_514_);
v___x_614_ = lean_array_push(v___x_613_, v___x_538_);
v___x_615_ = lean_array_push(v___x_614_, v___x_546_);
v___x_616_ = lean_array_push(v___x_615_, v___x_548_);
v___x_617_ = lean_array_push(v___x_616_, v___x_558_);
v___x_618_ = lean_array_push(v___x_617_, v___x_560_);
v___x_619_ = lean_array_push(v___x_618_, v___x_608_);
v___x_620_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_620_, 0, v___y_522_);
lean_ctor_set(v___x_620_, 1, v___y_513_);
lean_ctor_set(v___x_620_, 2, v___x_619_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_620_);
v___x_622_ = v___x_510_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
v___jp_624_:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4));
v___x_631_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__31));
v___x_632_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__32));
v___x_633_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_634_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
if (lean_obj_tag(v_doc_x3f_496_) == 1)
{
lean_object* v_val_635_; lean_object* v___x_636_; 
v_val_635_ = lean_ctor_get(v_doc_x3f_496_, 0);
lean_inc(v_val_635_);
lean_dec_ref(v_doc_x3f_496_);
v___x_636_ = l_Array_mkArray1___redArg(v_val_635_);
v___y_513_ = v___x_632_;
v___y_514_ = v___y_625_;
v___y_515_ = v_a_629_;
v___y_516_ = v___x_630_;
v___y_517_ = v___x_631_;
v___y_518_ = v___x_634_;
v___y_519_ = v___y_627_;
v___y_520_ = v___y_626_;
v___y_521_ = v___x_633_;
v___y_522_ = v___y_628_;
v___y_523_ = v___x_636_;
goto v___jp_512_;
}
else
{
lean_object* v___x_637_; 
lean_dec(v_doc_x3f_496_);
v___x_637_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__33));
v___y_513_ = v___x_632_;
v___y_514_ = v___y_625_;
v___y_515_ = v_a_629_;
v___y_516_ = v___x_630_;
v___y_517_ = v___x_631_;
v___y_518_ = v___x_634_;
v___y_519_ = v___y_627_;
v___y_520_ = v___y_626_;
v___y_521_ = v___x_633_;
v___y_522_ = v___y_628_;
v___y_523_ = v___x_637_;
goto v___jp_512_;
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec_ref(v_a_502_);
lean_dec(v_k_500_);
lean_dec(v_attrKind_498_);
lean_dec(v_doc_x3f_496_);
v_a_691_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_507_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_507_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux___boxed(lean_object* v_doc_x3f_699_, lean_object* v_attrs_x3f_700_, lean_object* v_attrKind_701_, lean_object* v_tk_702_, lean_object* v_k_703_, lean_object* v_alts_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Elab_Command_elabMacroRulesAux(v_doc_x3f_699_, v_attrs_x3f_700_, v_attrKind_701_, v_tk_702_, v_k_703_, v_alts_704_, v_a_705_, v_a_706_);
lean_dec(v_a_706_);
lean_dec(v_tk_702_);
lean_dec(v_attrs_x3f_700_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(lean_object* v_00_u03b1_709_, lean_object* v_ref_710_, lean_object* v_msg_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_ref_710_, v_msg_711_, v___y_712_, v___y_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___boxed(lean_object* v_00_u03b1_716_, lean_object* v_ref_717_, lean_object* v_msg_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(v_00_u03b1_716_, v_ref_717_, v_msg_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec(v_ref_717_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3(lean_object* v_msgData_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msgData_723_, v___y_725_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3(v_msgData_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(lean_object* v_00_u03b1_733_, lean_object* v_msg_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_734_, v___y_735_, v___y_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___boxed(lean_object* v_00_u03b1_739_, lean_object* v_msg_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(v_00_u03b1_739_, v_msg_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4(lean_object* v_msgData_745_, lean_object* v_macroStack_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_msgData_745_, v_macroStack_746_, v___y_748_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___boxed(lean_object* v_msgData_751_, lean_object* v_macroStack_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4(v_msgData_751_, v_macroStack_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(lean_object* v___y_757_, uint8_t v_isExporting_758_, lean_object* v_a_x3f_759_){
_start:
{
lean_object* v___x_761_; lean_object* v_env_762_; lean_object* v_messages_763_; lean_object* v_scopes_764_; lean_object* v_usedQuotCtxts_765_; lean_object* v_nextMacroScope_766_; lean_object* v_maxRecDepth_767_; lean_object* v_ngen_768_; lean_object* v_auxDeclNGen_769_; lean_object* v_infoState_770_; lean_object* v_traceState_771_; lean_object* v_snapshotTasks_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_783_; 
v___x_761_ = lean_st_ref_take(v___y_757_);
v_env_762_ = lean_ctor_get(v___x_761_, 0);
v_messages_763_ = lean_ctor_get(v___x_761_, 1);
v_scopes_764_ = lean_ctor_get(v___x_761_, 2);
v_usedQuotCtxts_765_ = lean_ctor_get(v___x_761_, 3);
v_nextMacroScope_766_ = lean_ctor_get(v___x_761_, 4);
v_maxRecDepth_767_ = lean_ctor_get(v___x_761_, 5);
v_ngen_768_ = lean_ctor_get(v___x_761_, 6);
v_auxDeclNGen_769_ = lean_ctor_get(v___x_761_, 7);
v_infoState_770_ = lean_ctor_get(v___x_761_, 8);
v_traceState_771_ = lean_ctor_get(v___x_761_, 9);
v_snapshotTasks_772_ = lean_ctor_get(v___x_761_, 10);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_783_ == 0)
{
v___x_774_ = v___x_761_;
v_isShared_775_ = v_isSharedCheck_783_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_snapshotTasks_772_);
lean_inc(v_traceState_771_);
lean_inc(v_infoState_770_);
lean_inc(v_auxDeclNGen_769_);
lean_inc(v_ngen_768_);
lean_inc(v_maxRecDepth_767_);
lean_inc(v_nextMacroScope_766_);
lean_inc(v_usedQuotCtxts_765_);
lean_inc(v_scopes_764_);
lean_inc(v_messages_763_);
lean_inc(v_env_762_);
lean_dec(v___x_761_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_783_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_776_ = l_Lean_Environment_setExporting(v_env_762_, v_isExporting_758_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_776_);
v___x_778_ = v___x_774_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_messages_763_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_scopes_764_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v_usedQuotCtxts_765_);
lean_ctor_set(v_reuseFailAlloc_782_, 4, v_nextMacroScope_766_);
lean_ctor_set(v_reuseFailAlloc_782_, 5, v_maxRecDepth_767_);
lean_ctor_set(v_reuseFailAlloc_782_, 6, v_ngen_768_);
lean_ctor_set(v_reuseFailAlloc_782_, 7, v_auxDeclNGen_769_);
lean_ctor_set(v_reuseFailAlloc_782_, 8, v_infoState_770_);
lean_ctor_set(v_reuseFailAlloc_782_, 9, v_traceState_771_);
lean_ctor_set(v_reuseFailAlloc_782_, 10, v_snapshotTasks_772_);
v___x_778_ = v_reuseFailAlloc_782_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = lean_st_ref_set(v___y_757_, v___x_778_);
v___x_780_ = lean_box(0);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
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
lean_object* v___x_795_; lean_object* v_env_796_; uint8_t v_isExporting_797_; lean_object* v___x_798_; lean_object* v_env_799_; lean_object* v_messages_800_; lean_object* v_scopes_801_; lean_object* v_usedQuotCtxts_802_; lean_object* v_nextMacroScope_803_; lean_object* v_maxRecDepth_804_; lean_object* v_ngen_805_; lean_object* v_auxDeclNGen_806_; lean_object* v_infoState_807_; lean_object* v_traceState_808_; lean_object* v_snapshotTasks_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_847_; 
v___x_795_ = lean_st_ref_get(v___y_793_);
v_env_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc_ref(v_env_796_);
lean_dec(v___x_795_);
v_isExporting_797_ = lean_ctor_get_uint8(v_env_796_, sizeof(void*)*8);
lean_dec_ref(v_env_796_);
v___x_798_ = lean_st_ref_take(v___y_793_);
v_env_799_ = lean_ctor_get(v___x_798_, 0);
v_messages_800_ = lean_ctor_get(v___x_798_, 1);
v_scopes_801_ = lean_ctor_get(v___x_798_, 2);
v_usedQuotCtxts_802_ = lean_ctor_get(v___x_798_, 3);
v_nextMacroScope_803_ = lean_ctor_get(v___x_798_, 4);
v_maxRecDepth_804_ = lean_ctor_get(v___x_798_, 5);
v_ngen_805_ = lean_ctor_get(v___x_798_, 6);
v_auxDeclNGen_806_ = lean_ctor_get(v___x_798_, 7);
v_infoState_807_ = lean_ctor_get(v___x_798_, 8);
v_traceState_808_ = lean_ctor_get(v___x_798_, 9);
v_snapshotTasks_809_ = lean_ctor_get(v___x_798_, 10);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_847_ == 0)
{
v___x_811_ = v___x_798_;
v_isShared_812_ = v_isSharedCheck_847_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_snapshotTasks_809_);
lean_inc(v_traceState_808_);
lean_inc(v_infoState_807_);
lean_inc(v_auxDeclNGen_806_);
lean_inc(v_ngen_805_);
lean_inc(v_maxRecDepth_804_);
lean_inc(v_nextMacroScope_803_);
lean_inc(v_usedQuotCtxts_802_);
lean_inc(v_scopes_801_);
lean_inc(v_messages_800_);
lean_inc(v_env_799_);
lean_dec(v___x_798_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_847_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = l_Lean_Environment_setExporting(v_env_799_, v_isExporting_791_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_813_);
v___x_815_ = v___x_811_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_messages_800_);
lean_ctor_set(v_reuseFailAlloc_846_, 2, v_scopes_801_);
lean_ctor_set(v_reuseFailAlloc_846_, 3, v_usedQuotCtxts_802_);
lean_ctor_set(v_reuseFailAlloc_846_, 4, v_nextMacroScope_803_);
lean_ctor_set(v_reuseFailAlloc_846_, 5, v_maxRecDepth_804_);
lean_ctor_set(v_reuseFailAlloc_846_, 6, v_ngen_805_);
lean_ctor_set(v_reuseFailAlloc_846_, 7, v_auxDeclNGen_806_);
lean_ctor_set(v_reuseFailAlloc_846_, 8, v_infoState_807_);
lean_ctor_set(v_reuseFailAlloc_846_, 9, v_traceState_808_);
lean_ctor_set(v_reuseFailAlloc_846_, 10, v_snapshotTasks_809_);
v___x_815_ = v_reuseFailAlloc_846_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_816_; lean_object* v_r_817_; 
v___x_816_ = lean_st_ref_set(v___y_793_, v___x_815_);
lean_inc(v___y_793_);
v_r_817_ = lean_apply_3(v_x_790_, v___y_792_, v___y_793_, lean_box(0));
if (lean_obj_tag(v_r_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_834_; 
v_a_818_ = lean_ctor_get(v_r_817_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v_r_817_);
if (v_isSharedCheck_834_ == 0)
{
v___x_820_ = v_r_817_;
v_isShared_821_ = v_isSharedCheck_834_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v_r_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_834_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
lean_inc(v_a_818_);
if (v_isShared_821_ == 0)
{
lean_ctor_set_tag(v___x_820_, 1);
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_833_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
v___x_824_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_793_, v_isExporting_797_, v___x_823_);
lean_dec_ref(v___x_823_);
lean_dec(v___y_793_);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; 
v_unused_832_ = lean_ctor_get(v___x_824_, 0);
lean_dec(v_unused_832_);
v___x_826_ = v___x_824_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_dec(v___x_824_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v_a_818_);
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_818_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
v_a_835_ = lean_ctor_get(v_r_817_, 0);
lean_inc(v_a_835_);
lean_dec_ref(v_r_817_);
v___x_836_ = lean_box(0);
v___x_837_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_793_, v_isExporting_797_, v___x_836_);
lean_dec(v___y_793_);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; 
v_unused_845_ = lean_ctor_get(v___x_837_, 0);
lean_dec(v_unused_845_);
v___x_839_ = v___x_837_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_dec(v___x_837_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
lean_ctor_set_tag(v___x_839_, 1);
lean_ctor_set(v___x_839_, 0, v_a_835_);
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_835_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___boxed(lean_object* v_x_848_, lean_object* v_isExporting_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
uint8_t v_isExporting_boxed_853_; lean_object* v_res_854_; 
v_isExporting_boxed_853_ = lean_unbox(v_isExporting_849_);
v_res_854_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v_x_848_, v_isExporting_boxed_853_, v___y_850_, v___y_851_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0(lean_object* v_00_u03b1_855_, lean_object* v_x_856_, uint8_t v_isExporting_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v_x_856_, v_isExporting_857_, v___y_858_, v___y_859_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___boxed(lean_object* v_00_u03b1_862_, lean_object* v_x_863_, lean_object* v_isExporting_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
uint8_t v_isExporting_boxed_868_; lean_object* v_res_869_; 
v_isExporting_boxed_868_ = lean_unbox(v_isExporting_864_);
v_res_869_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0(v_00_u03b1_862_, v_x_863_, v_isExporting_boxed_868_, v___y_865_, v___y_866_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0(lean_object* v___x_870_, lean_object* v___x_871_, lean_object* v_doc_x3f_872_, lean_object* v_attrs_x3f_873_, lean_object* v_attrKind_874_, lean_object* v_tk_875_, lean_object* v_alts_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_Elab_Command_getRef___redArg(v___y_877_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v_fileName_882_; lean_object* v_fileMap_883_; lean_object* v_currRecDepth_884_; lean_object* v_cmdPos_885_; lean_object* v_macroStack_886_; lean_object* v_quotContext_x3f_887_; lean_object* v_currMacroScope_888_; lean_object* v_snap_x3f_889_; lean_object* v_cancelTk_x3f_890_; uint8_t v_suppressElabErrors_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_910_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref(v___x_880_);
v_fileName_882_ = lean_ctor_get(v___y_877_, 0);
v_fileMap_883_ = lean_ctor_get(v___y_877_, 1);
v_currRecDepth_884_ = lean_ctor_get(v___y_877_, 2);
v_cmdPos_885_ = lean_ctor_get(v___y_877_, 3);
v_macroStack_886_ = lean_ctor_get(v___y_877_, 4);
v_quotContext_x3f_887_ = lean_ctor_get(v___y_877_, 5);
v_currMacroScope_888_ = lean_ctor_get(v___y_877_, 6);
v_snap_x3f_889_ = lean_ctor_get(v___y_877_, 8);
v_cancelTk_x3f_890_ = lean_ctor_get(v___y_877_, 9);
v_suppressElabErrors_891_ = lean_ctor_get_uint8(v___y_877_, sizeof(void*)*10);
v_isSharedCheck_910_ = !lean_is_exclusive(v___y_877_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v___y_877_, 7);
lean_dec(v_unused_911_);
v___x_893_ = v___y_877_;
v_isShared_894_ = v_isSharedCheck_910_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_cancelTk_x3f_890_);
lean_inc(v_snap_x3f_889_);
lean_inc(v_currMacroScope_888_);
lean_inc(v_quotContext_x3f_887_);
lean_inc(v_macroStack_886_);
lean_inc(v_cmdPos_885_);
lean_inc(v_currRecDepth_884_);
lean_inc(v_fileMap_883_);
lean_inc(v_fileName_882_);
lean_dec(v___y_877_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_910_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v_ref_895_; lean_object* v___x_897_; 
v_ref_895_ = l_Lean_replaceRef(v___x_870_, v_a_881_);
lean_dec(v_a_881_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 7, v_ref_895_);
v___x_897_ = v___x_893_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_fileName_882_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_fileMap_883_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v_currRecDepth_884_);
lean_ctor_set(v_reuseFailAlloc_909_, 3, v_cmdPos_885_);
lean_ctor_set(v_reuseFailAlloc_909_, 4, v_macroStack_886_);
lean_ctor_set(v_reuseFailAlloc_909_, 5, v_quotContext_x3f_887_);
lean_ctor_set(v_reuseFailAlloc_909_, 6, v_currMacroScope_888_);
lean_ctor_set(v_reuseFailAlloc_909_, 7, v_ref_895_);
lean_ctor_set(v_reuseFailAlloc_909_, 8, v_snap_x3f_889_);
lean_ctor_set(v_reuseFailAlloc_909_, 9, v_cancelTk_x3f_890_);
lean_ctor_set_uint8(v_reuseFailAlloc_909_, sizeof(void*)*10, v_suppressElabErrors_891_);
v___x_897_ = v_reuseFailAlloc_909_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_898_; 
lean_inc_ref(v___x_897_);
v___x_898_ = l_Lean_Elab_Command_resolveSyntaxKind(v___x_871_, v___x_897_, v___y_878_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_900_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref(v___x_898_);
v___x_900_ = l_Lean_Elab_Command_elabMacroRulesAux(v_doc_x3f_872_, v_attrs_x3f_873_, v_attrKind_874_, v_tk_875_, v_a_899_, v_alts_876_, v___x_897_, v___y_878_);
return v___x_900_;
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec_ref(v___x_897_);
lean_dec_ref(v_alts_876_);
lean_dec(v_attrKind_874_);
lean_dec(v_doc_x3f_872_);
v_a_901_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_898_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_898_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_877_);
lean_dec_ref(v_alts_876_);
lean_dec(v_attrKind_874_);
lean_dec(v_doc_x3f_872_);
lean_dec(v___x_871_);
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0___boxed(lean_object* v___x_912_, lean_object* v___x_913_, lean_object* v_doc_x3f_914_, lean_object* v_attrs_x3f_915_, lean_object* v_attrKind_916_, lean_object* v_tk_917_, lean_object* v_alts_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Elab_Command_elabMacroRules___lam__0(v___x_912_, v___x_913_, v_doc_x3f_914_, v_attrs_x3f_915_, v_attrKind_916_, v_tk_917_, v_alts_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec(v_tk_917_);
lean_dec(v_attrs_x3f_915_);
lean_dec(v___x_912_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5(lean_object* v___x_926_, lean_object* v___x_927_, lean_object* v_attrKind_928_, lean_object* v___x_929_, lean_object* v___x_930_, lean_object* v_attrs_x3f_931_, lean_object* v___x_932_, lean_object* v___x_933_, lean_object* v___x_934_, lean_object* v_doc_x3f_935_, lean_object* v_kind_x3f_936_, lean_object* v_alts_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_Elab_Command_getRef___redArg(v___y_938_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_943_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
lean_dec_ref(v___x_941_);
v___x_943_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_938_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_1011_; 
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; 
v_unused_1012_ = lean_ctor_get(v___x_943_, 0);
lean_dec(v_unused_1012_);
v___x_945_ = v___x_943_;
v_isShared_946_ = v_isSharedCheck_1011_;
goto v_resetjp_944_;
}
else
{
lean_dec(v___x_943_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_1011_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_quotContext_x3f_947_; uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; 
v_quotContext_x3f_947_ = lean_ctor_get(v___y_938_, 5);
v___x_948_ = 0;
v___x_949_ = l_Lean_SourceInfo_fromRef(v_a_942_, v___x_948_);
lean_dec(v_a_942_);
if (lean_obj_tag(v_quotContext_x3f_947_) == 0)
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_939_);
lean_dec_ref(v___x_1010_);
goto v___jp_1004_;
}
else
{
goto v___jp_1004_;
}
v___jp_950_:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
lean_inc_ref(v___y_954_);
v___x_957_ = l_Array_append___redArg(v___y_954_, v___y_956_);
lean_dec_ref(v___y_956_);
lean_inc(v___y_953_);
lean_inc(v___x_949_);
v___x_958_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_958_, 0, v___x_949_);
lean_ctor_set(v___x_958_, 1, v___y_953_);
lean_ctor_set(v___x_958_, 2, v___x_957_);
v___x_959_ = l_Array_append___redArg(v___y_954_, v_alts_937_);
lean_inc(v___x_949_);
v___x_960_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_960_, 0, v___x_949_);
lean_ctor_set(v___x_960_, 1, v___y_953_);
lean_ctor_set(v___x_960_, 2, v___x_959_);
lean_inc(v___x_949_);
v___x_961_ = l_Lean_Syntax_node1(v___x_949_, v___x_926_, v___x_960_);
v___x_962_ = l_Lean_Syntax_node6(v___x_949_, v___x_927_, v___y_955_, v___y_952_, v_attrKind_928_, v___y_951_, v___x_958_, v___x_961_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_962_);
v___x_964_ = v___x_945_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
v___jp_966_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
lean_inc_ref(v___y_968_);
v___x_971_ = l_Array_append___redArg(v___y_968_, v___y_970_);
lean_dec_ref(v___y_970_);
lean_inc(v___y_967_);
lean_inc(v___x_949_);
v___x_972_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_972_, 0, v___x_949_);
lean_ctor_set(v___x_972_, 1, v___y_967_);
lean_ctor_set(v___x_972_, 2, v___x_971_);
lean_inc(v___x_949_);
v___x_973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_949_);
lean_ctor_set(v___x_973_, 1, v___x_929_);
if (lean_obj_tag(v_kind_x3f_936_) == 0)
{
lean_object* v___x_974_; 
v___x_974_ = lean_mk_empty_array_with_capacity(v___x_930_);
v___y_951_ = v___x_973_;
v___y_952_ = v___x_972_;
v___y_953_ = v___y_967_;
v___y_954_ = v___y_968_;
v___y_955_ = v___y_969_;
v___y_956_ = v___x_974_;
goto v___jp_950_;
}
else
{
lean_object* v_val_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_val_975_ = lean_ctor_get(v_kind_x3f_936_, 0);
lean_inc(v_val_975_);
lean_dec_ref(v_kind_x3f_936_);
v___x_976_ = lean_mk_syntax_ident(v_val_975_);
v___x_977_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0));
lean_inc(v___x_949_);
v___x_978_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_949_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1));
lean_inc(v___x_949_);
v___x_980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_949_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
lean_inc(v___x_949_);
v___x_982_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_949_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2));
lean_inc(v___x_949_);
v___x_984_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_949_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = l_Array_mkArray5___redArg(v___x_978_, v___x_980_, v___x_982_, v___x_976_, v___x_984_);
v___y_951_ = v___x_973_;
v___y_952_ = v___x_972_;
v___y_953_ = v___y_967_;
v___y_954_ = v___y_968_;
v___y_955_ = v___y_969_;
v___y_956_ = v___x_985_;
goto v___jp_950_;
}
}
v___jp_986_:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
lean_inc_ref(v___y_988_);
v___x_990_ = l_Array_append___redArg(v___y_988_, v___y_989_);
lean_dec_ref(v___y_989_);
lean_inc(v___y_987_);
lean_inc(v___x_949_);
v___x_991_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_991_, 0, v___x_949_);
lean_ctor_set(v___x_991_, 1, v___y_987_);
lean_ctor_set(v___x_991_, 2, v___x_990_);
if (lean_obj_tag(v_attrs_x3f_931_) == 1)
{
lean_object* v_val_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_val_992_ = lean_ctor_get(v_attrs_x3f_931_, 0);
v___x_993_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
v___x_994_ = l_Lean_Name_mkStr4(v___x_932_, v___x_933_, v___x_934_, v___x_993_);
v___x_995_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
lean_inc(v___x_949_);
v___x_996_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_949_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
lean_inc_ref(v___y_988_);
v___x_997_ = l_Array_append___redArg(v___y_988_, v_val_992_);
lean_inc(v___y_987_);
lean_inc(v___x_949_);
v___x_998_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_998_, 0, v___x_949_);
lean_ctor_set(v___x_998_, 1, v___y_987_);
lean_ctor_set(v___x_998_, 2, v___x_997_);
v___x_999_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
lean_inc(v___x_949_);
v___x_1000_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_949_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
lean_inc(v___x_949_);
v___x_1001_ = l_Lean_Syntax_node3(v___x_949_, v___x_994_, v___x_996_, v___x_998_, v___x_1000_);
v___x_1002_ = l_Array_mkArray1___redArg(v___x_1001_);
v___y_967_ = v___y_987_;
v___y_968_ = v___y_988_;
v___y_969_ = v___x_991_;
v___y_970_ = v___x_1002_;
goto v___jp_966_;
}
else
{
lean_object* v___x_1003_; 
lean_dec_ref(v___x_934_);
lean_dec_ref(v___x_933_);
lean_dec_ref(v___x_932_);
v___x_1003_ = lean_mk_empty_array_with_capacity(v___x_930_);
v___y_967_ = v___y_987_;
v___y_968_ = v___y_988_;
v___y_969_ = v___x_991_;
v___y_970_ = v___x_1003_;
goto v___jp_966_;
}
}
v___jp_1004_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1006_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
if (lean_obj_tag(v_doc_x3f_935_) == 1)
{
lean_object* v_val_1007_; lean_object* v___x_1008_; 
v_val_1007_ = lean_ctor_get(v_doc_x3f_935_, 0);
lean_inc(v_val_1007_);
lean_dec_ref(v_doc_x3f_935_);
v___x_1008_ = l_Array_mkArray1___redArg(v_val_1007_);
v___y_987_ = v___x_1005_;
v___y_988_ = v___x_1006_;
v___y_989_ = v___x_1008_;
goto v___jp_986_;
}
else
{
lean_object* v___x_1009_; 
lean_dec(v_doc_x3f_935_);
v___x_1009_ = lean_mk_empty_array_with_capacity(v___x_930_);
v___y_987_ = v___x_1005_;
v___y_988_ = v___x_1006_;
v___y_989_ = v___x_1009_;
goto v___jp_986_;
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec(v_a_942_);
lean_dec(v_kind_x3f_936_);
lean_dec(v_doc_x3f_935_);
lean_dec_ref(v___x_934_);
lean_dec_ref(v___x_933_);
lean_dec_ref(v___x_932_);
lean_dec_ref(v___x_929_);
lean_dec(v_attrKind_928_);
lean_dec(v___x_927_);
lean_dec(v___x_926_);
v_a_1013_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_943_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_943_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec(v_kind_x3f_936_);
lean_dec(v_doc_x3f_935_);
lean_dec_ref(v___x_934_);
lean_dec_ref(v___x_933_);
lean_dec_ref(v___x_932_);
lean_dec_ref(v___x_929_);
lean_dec(v_attrKind_928_);
lean_dec(v___x_927_);
lean_dec(v___x_926_);
v_a_1021_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_941_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_941_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5___boxed(lean_object* v___x_1029_, lean_object* v___x_1030_, lean_object* v_attrKind_1031_, lean_object* v___x_1032_, lean_object* v___x_1033_, lean_object* v_attrs_x3f_1034_, lean_object* v___x_1035_, lean_object* v___x_1036_, lean_object* v___x_1037_, lean_object* v_doc_x3f_1038_, lean_object* v_kind_x3f_1039_, lean_object* v_alts_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_Elab_Command_elabMacroRules___lam__5(v___x_1029_, v___x_1030_, v_attrKind_1031_, v___x_1032_, v___x_1033_, v_attrs_x3f_1034_, v___x_1035_, v___x_1036_, v___x_1037_, v_doc_x3f_1038_, v_kind_x3f_1039_, v_alts_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec_ref(v_alts_1040_);
lean_dec(v_attrs_x3f_1034_);
lean_dec(v___x_1033_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1(lean_object* v_stx_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___y_1102_; lean_object* v___y_1103_; uint8_t v___y_1104_; lean_object* v___y_1105_; uint8_t v___y_1106_; uint8_t v___y_1107_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; 
v___x_1110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4));
v___x_1111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5));
v___x_1112_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0));
v___x_1113_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1));
lean_inc(v_stx_1097_);
v___x_1114_ = l_Lean_Syntax_isOfKind(v_stx_1097_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1180_; 
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v_stx_1097_);
v___x_1180_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1180_;
}
else
{
lean_object* v___x_1181_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v_a_1194_; lean_object* v___y_1202_; uint8_t v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1233_; uint8_t v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v_attrs_x3f_1269_; lean_object* v_doc_x3f_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___x_1504_; uint8_t v___x_1505_; 
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1504_ = l_Lean_Syntax_getArg(v_stx_1097_, v___x_1181_);
v___x_1505_ = l_Lean_Syntax_isNone(v___x_1504_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1506_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1504_);
v___x_1507_ = l_Lean_Syntax_matchesNull(v___x_1504_, v___x_1506_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; 
lean_dec(v___x_1504_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v_stx_1097_);
v___x_1508_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1508_;
}
else
{
lean_object* v_doc_x3f_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v_doc_x3f_1509_ = l_Lean_Syntax_getArg(v___x_1504_, v___x_1181_);
lean_dec(v___x_1504_);
v___x_1510_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17));
lean_inc(v_doc_x3f_1509_);
v___x_1511_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; 
lean_dec(v_doc_x3f_1509_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v_stx_1097_);
v___x_1512_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1512_;
}
else
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_doc_x3f_1509_);
v_doc_x3f_1488_ = v___x_1513_;
v___y_1489_ = v___y_1098_;
v___y_1490_ = v___y_1099_;
goto v___jp_1487_;
}
}
}
else
{
lean_object* v___x_1514_; 
lean_dec(v___x_1504_);
v___x_1514_ = lean_box(0);
v_doc_x3f_1488_ = v___x_1514_;
v___y_1489_ = v___y_1098_;
v___y_1490_ = v___y_1099_;
goto v___jp_1487_;
}
v___jp_1182_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__31));
v___x_1196_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__32));
v___x_1197_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
if (lean_obj_tag(v___y_1193_) == 1)
{
lean_object* v_val_1198_; lean_object* v___x_1199_; 
v_val_1198_ = lean_ctor_get(v___y_1193_, 0);
lean_inc(v_val_1198_);
lean_dec_ref(v___y_1193_);
v___x_1199_ = l_Array_mkArray1___redArg(v_val_1198_);
v___y_1116_ = v___y_1183_;
v___y_1117_ = v___y_1184_;
v___y_1118_ = v___x_1195_;
v___y_1119_ = v___y_1190_;
v___y_1120_ = v___y_1189_;
v___y_1121_ = v___y_1191_;
v___y_1122_ = v___y_1185_;
v___y_1123_ = v___x_1197_;
v___y_1124_ = v___x_1196_;
v___y_1125_ = v___y_1187_;
v___y_1126_ = v___y_1186_;
v___y_1127_ = v___y_1188_;
v___y_1128_ = v_a_1194_;
v___y_1129_ = v___y_1192_;
v___y_1130_ = v___x_1199_;
goto v___jp_1115_;
}
else
{
lean_object* v___x_1200_; 
lean_dec(v___y_1193_);
v___x_1200_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__33));
v___y_1116_ = v___y_1183_;
v___y_1117_ = v___y_1184_;
v___y_1118_ = v___x_1195_;
v___y_1119_ = v___y_1190_;
v___y_1120_ = v___y_1189_;
v___y_1121_ = v___y_1191_;
v___y_1122_ = v___y_1185_;
v___y_1123_ = v___x_1197_;
v___y_1124_ = v___x_1196_;
v___y_1125_ = v___y_1187_;
v___y_1126_ = v___y_1186_;
v___y_1127_ = v___y_1188_;
v___y_1128_ = v_a_1194_;
v___y_1129_ = v___y_1192_;
v___y_1130_ = v___x_1200_;
goto v___jp_1115_;
}
}
v___jp_1201_:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_Elab_Command_getRef___redArg(v___y_1207_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref(v___x_1215_);
v___x_1217_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1207_);
lean_dec_ref(v___y_1207_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref(v___x_1217_);
v___x_1219_ = l_Lean_Parser_Command_visibility_ofAttrKind(v___y_1211_);
v___x_1220_ = l_Lean_SourceInfo_fromRef(v_a_1216_, v___y_1203_);
lean_dec(v_a_1216_);
if (lean_obj_tag(v___y_1208_) == 0)
{
lean_object* v___x_1221_; lean_object* v_a_1222_; 
v___x_1221_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_1205_);
lean_dec(v___y_1205_);
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec_ref(v___x_1221_);
v___y_1183_ = v___y_1202_;
v___y_1184_ = v___y_1204_;
v___y_1185_ = v___y_1209_;
v___y_1186_ = v___y_1214_;
v___y_1187_ = v___y_1210_;
v___y_1188_ = v___y_1212_;
v___y_1189_ = v___x_1219_;
v___y_1190_ = v___y_1206_;
v___y_1191_ = v_a_1218_;
v___y_1192_ = v___x_1220_;
v___y_1193_ = v___y_1213_;
v_a_1194_ = v_a_1222_;
goto v___jp_1182_;
}
else
{
lean_object* v_val_1223_; 
lean_dec(v___y_1205_);
v_val_1223_ = lean_ctor_get(v___y_1208_, 0);
lean_inc(v_val_1223_);
lean_dec_ref(v___y_1208_);
v___y_1183_ = v___y_1202_;
v___y_1184_ = v___y_1204_;
v___y_1185_ = v___y_1209_;
v___y_1186_ = v___y_1214_;
v___y_1187_ = v___y_1210_;
v___y_1188_ = v___y_1212_;
v___y_1189_ = v___x_1219_;
v___y_1190_ = v___y_1206_;
v___y_1191_ = v_a_1218_;
v___y_1192_ = v___x_1220_;
v___y_1193_ = v___y_1213_;
v_a_1194_ = v_val_1223_;
goto v___jp_1182_;
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec(v_a_1216_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec(v___y_1202_);
v_a_1224_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1217_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1217_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
else
{
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec(v___y_1202_);
return v___x_1215_;
}
}
v___jp_1232_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1248_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__34));
lean_inc_ref(v___y_1241_);
v___x_1249_ = l_Lean_Name_mkStr4(v___x_1110_, v___x_1111_, v___y_1241_, v___x_1248_);
v___x_1250_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__37));
v___x_1251_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__38));
lean_inc(v___y_1242_);
v___x_1252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___y_1242_);
lean_ctor_set(v___x_1252_, 1, v___x_1250_);
lean_inc(v___y_1237_);
lean_inc(v___y_1242_);
v___x_1253_ = l_Lean_Syntax_node2(v___y_1242_, v___x_1251_, v___x_1252_, v___y_1237_);
lean_inc(v___y_1245_);
v___x_1254_ = l_Lean_Syntax_node2(v___y_1242_, v___x_1249_, v___y_1245_, v___x_1253_);
if (lean_obj_tag(v___y_1244_) == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1255_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_1256_ = lean_mk_empty_array_with_capacity(v___y_1240_);
v___x_1257_ = lean_array_push(v___x_1256_, v___x_1254_);
v___x_1258_ = l_Lean_Syntax_SepArray_ofElems(v___x_1255_, v___x_1257_);
lean_dec_ref(v___x_1257_);
v___y_1202_ = v___y_1233_;
v___y_1203_ = v___y_1234_;
v___y_1204_ = v___y_1235_;
v___y_1205_ = v___y_1236_;
v___y_1206_ = v___y_1237_;
v___y_1207_ = v___y_1238_;
v___y_1208_ = v___y_1239_;
v___y_1209_ = v___y_1241_;
v___y_1210_ = v___y_1243_;
v___y_1211_ = v___y_1245_;
v___y_1212_ = v___y_1246_;
v___y_1213_ = v___y_1247_;
v___y_1214_ = v___x_1258_;
goto v___jp_1201_;
}
else
{
lean_object* v_val_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v_val_1259_ = lean_ctor_get(v___y_1244_, 0);
lean_inc(v_val_1259_);
lean_dec_ref(v___y_1244_);
v___x_1260_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_1261_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1259_);
lean_dec(v_val_1259_);
v___x_1262_ = lean_array_push(v___x_1261_, v___x_1254_);
v___x_1263_ = l_Lean_Syntax_SepArray_ofElems(v___x_1260_, v___x_1262_);
lean_dec_ref(v___x_1262_);
v___y_1202_ = v___y_1233_;
v___y_1203_ = v___y_1234_;
v___y_1204_ = v___y_1235_;
v___y_1205_ = v___y_1236_;
v___y_1206_ = v___y_1237_;
v___y_1207_ = v___y_1238_;
v___y_1208_ = v___y_1239_;
v___y_1209_ = v___y_1241_;
v___y_1210_ = v___y_1243_;
v___y_1211_ = v___y_1245_;
v___y_1212_ = v___y_1246_;
v___y_1213_ = v___y_1247_;
v___y_1214_ = v___x_1263_;
goto v___jp_1201_;
}
}
v___jp_1264_:
{
lean_object* v___x_1270_; lean_object* v_attrKind_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1270_ = lean_unsigned_to_nat(2u);
v_attrKind_1271_ = l_Lean_Syntax_getArg(v_stx_1097_, v___x_1270_);
v___x_1272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6));
v___x_1273_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9));
lean_inc(v_attrKind_1271_);
v___x_1274_ = l_Lean_Syntax_isOfKind(v_attrKind_1271_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; 
lean_dec(v_attrKind_1271_);
lean_dec(v_attrs_x3f_1269_);
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v_stx_1097_);
v___x_1275_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1275_;
}
else
{
lean_object* v___x_1276_; lean_object* v_tk_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1276_ = lean_unsigned_to_nat(3u);
v_tk_1277_ = l_Lean_Syntax_getArg(v_stx_1097_, v___x_1276_);
v___x_1278_ = lean_unsigned_to_nat(4u);
v___x_1279_ = l_Lean_Syntax_getArg(v_stx_1097_, v___x_1278_);
lean_inc(v___x_1279_);
v___x_1280_ = l_Lean_Syntax_matchesNull(v___x_1279_, v___x_1181_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1281_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1279_);
v___x_1282_ = l_Lean_Syntax_matchesNull(v___x_1279_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; 
lean_dec(v___x_1279_);
lean_dec(v_tk_1277_);
lean_dec(v_attrKind_1271_);
lean_dec(v_attrs_x3f_1269_);
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v_stx_1097_);
v___x_1283_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1283_;
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1284_ = l_Lean_Syntax_getArg(v_stx_1097_, v___x_1281_);
lean_dec(v_stx_1097_);
v___x_1285_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10));
lean_inc(v___x_1284_);
v___x_1286_ = l_Lean_Syntax_isOfKind(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; 
lean_dec(v___x_1284_);
lean_dec(v___x_1279_);
lean_dec(v_tk_1277_);
lean_dec(v_attrKind_1271_);
lean_dec(v_attrs_x3f_1269_);
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
v___x_1287_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1287_;
}
else
{
lean_object* v_kind_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_kind_1288_ = l_Lean_Syntax_getArg(v___x_1279_, v___x_1276_);
lean_dec(v___x_1279_);
v___x_1289_ = l_Lean_Syntax_getArg(v___x_1284_, v___x_1181_);
lean_dec(v___x_1284_);
lean_inc(v___x_1289_);
v___x_1290_ = l_Lean_Syntax_matchesNull(v___x_1289_, v___y_1268_);
if (v___x_1290_ == 0)
{
lean_object* v_alts_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___f_1300_; 
v_alts_1291_ = l_Lean_Syntax_getArgs(v___x_1289_);
lean_dec(v___x_1289_);
v___x_1292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1293_ = lean_box(2);
lean_inc_ref(v_alts_1291_);
v___x_1294_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
lean_ctor_set(v___x_1294_, 1, v___x_1292_);
lean_ctor_set(v___x_1294_, 2, v_alts_1291_);
v___x_1295_ = lean_mk_empty_array_with_capacity(v___x_1270_);
lean_inc(v_tk_1277_);
v___x_1296_ = lean_array_push(v___x_1295_, v_tk_1277_);
v___x_1297_ = lean_array_push(v___x_1296_, v___x_1294_);
v___x_1298_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1293_);
lean_ctor_set(v___x_1298_, 1, v___x_1292_);
lean_ctor_set(v___x_1298_, 2, v___x_1297_);
v___x_1299_ = l_Lean_TSyntax_getId(v_kind_1288_);
lean_dec(v_kind_1288_);
lean_inc(v_attrKind_1271_);
v___f_1300_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1300_, 0, v___x_1298_);
lean_closure_set(v___f_1300_, 1, v___x_1299_);
lean_closure_set(v___f_1300_, 2, v___y_1266_);
lean_closure_set(v___f_1300_, 3, v_attrs_x3f_1269_);
lean_closure_set(v___f_1300_, 4, v_attrKind_1271_);
lean_closure_set(v___f_1300_, 5, v_tk_1277_);
lean_closure_set(v___f_1300_, 6, v_alts_1291_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1301_; 
lean_dec(v_attrKind_1271_);
v___x_1301_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1300_, v___x_1274_, v___y_1265_, v___y_1267_);
return v___x_1301_;
}
else
{
lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1302_ = l_Lean_Syntax_getArg(v_attrKind_1271_, v___x_1181_);
lean_dec(v_attrKind_1271_);
lean_inc(v___x_1302_);
v___x_1303_ = l_Lean_Syntax_matchesNull(v___x_1302_, v___y_1268_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; 
lean_dec(v___x_1302_);
v___x_1304_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1300_, v___x_1274_, v___y_1265_, v___y_1267_);
return v___x_1304_;
}
else
{
lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1305_ = l_Lean_Syntax_getArg(v___x_1302_, v___x_1181_);
lean_dec(v___x_1302_);
v___x_1306_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1307_ = l_Lean_Syntax_isOfKind(v___x_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1300_, v___x_1274_, v___y_1265_, v___y_1267_);
return v___x_1308_;
}
else
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1300_, v___x_1290_, v___y_1265_, v___y_1267_);
return v___x_1309_;
}
}
}
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v___x_1310_ = l_Lean_Syntax_getArg(v___x_1289_, v___x_1181_);
v___x_1311_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8));
lean_inc(v___x_1310_);
v___x_1312_ = l_Lean_Syntax_isOfKind(v___x_1310_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_object* v_alts_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___f_1322_; 
lean_dec(v___x_1310_);
v_alts_1313_ = l_Lean_Syntax_getArgs(v___x_1289_);
lean_dec(v___x_1289_);
v___x_1314_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1315_ = lean_box(2);
lean_inc_ref(v_alts_1313_);
v___x_1316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
lean_ctor_set(v___x_1316_, 1, v___x_1314_);
lean_ctor_set(v___x_1316_, 2, v_alts_1313_);
v___x_1317_ = lean_mk_empty_array_with_capacity(v___x_1270_);
lean_inc(v_tk_1277_);
v___x_1318_ = lean_array_push(v___x_1317_, v_tk_1277_);
v___x_1319_ = lean_array_push(v___x_1318_, v___x_1316_);
v___x_1320_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1315_);
lean_ctor_set(v___x_1320_, 1, v___x_1314_);
lean_ctor_set(v___x_1320_, 2, v___x_1319_);
v___x_1321_ = l_Lean_TSyntax_getId(v_kind_1288_);
lean_dec(v_kind_1288_);
lean_inc(v_attrKind_1271_);
v___f_1322_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1322_, 0, v___x_1320_);
lean_closure_set(v___f_1322_, 1, v___x_1321_);
lean_closure_set(v___f_1322_, 2, v___y_1266_);
lean_closure_set(v___f_1322_, 3, v_attrs_x3f_1269_);
lean_closure_set(v___f_1322_, 4, v_attrKind_1271_);
lean_closure_set(v___f_1322_, 5, v_tk_1277_);
lean_closure_set(v___f_1322_, 6, v_alts_1313_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1323_; 
lean_dec(v_attrKind_1271_);
v___x_1323_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1322_, v___x_1274_, v___y_1265_, v___y_1267_);
return v___x_1323_;
}
else
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = l_Lean_Syntax_getArg(v_attrKind_1271_, v___x_1181_);
lean_dec(v_attrKind_1271_);
lean_inc(v___x_1324_);
v___x_1325_ = l_Lean_Syntax_matchesNull(v___x_1324_, v___y_1268_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; 
lean_dec(v___x_1324_);
v___x_1326_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1322_, v___x_1274_, v___y_1265_, v___y_1267_);
return v___x_1326_;
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1327_ = l_Lean_Syntax_getArg(v___x_1324_, v___x_1181_);
lean_dec(v___x_1324_);
v___x_1328_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1329_ = l_Lean_Syntax_isOfKind(v___x_1327_, v___x_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1322_, v___x_1274_, v___y_1265_, v___y_1267_);
return v___x_1330_;
}
else
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1322_, v___x_1312_, v___y_1265_, v___y_1267_);
return v___x_1331_;
}
}
}
}
else
{
lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = l_Lean_Syntax_getArg(v___x_1310_, v___y_1268_);
lean_inc(v___x_1332_);
v___x_1333_ = l_Lean_Syntax_matchesNull(v___x_1332_, v___y_1268_);
if (v___x_1333_ == 0)
{
lean_object* v_alts_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___f_1343_; 
lean_dec(v___x_1332_);
lean_dec(v___x_1310_);
v_alts_1334_ = l_Lean_Syntax_getArgs(v___x_1289_);
lean_dec(v___x_1289_);
v___x_1335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1336_ = lean_box(2);
lean_inc_ref(v_alts_1334_);
v___x_1337_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set(v___x_1337_, 1, v___x_1335_);
lean_ctor_set(v___x_1337_, 2, v_alts_1334_);
v___x_1338_ = lean_mk_empty_array_with_capacity(v___x_1270_);
lean_inc(v_tk_1277_);
v___x_1339_ = lean_array_push(v___x_1338_, v_tk_1277_);
v___x_1340_ = lean_array_push(v___x_1339_, v___x_1337_);
v___x_1341_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1336_);
lean_ctor_set(v___x_1341_, 1, v___x_1335_);
lean_ctor_set(v___x_1341_, 2, v___x_1340_);
v___x_1342_ = l_Lean_TSyntax_getId(v_kind_1288_);
lean_dec(v_kind_1288_);
lean_inc(v_attrKind_1271_);
v___f_1343_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1343_, 0, v___x_1341_);
lean_closure_set(v___f_1343_, 1, v___x_1342_);
lean_closure_set(v___f_1343_, 2, v___y_1266_);
lean_closure_set(v___f_1343_, 3, v_attrs_x3f_1269_);
lean_closure_set(v___f_1343_, 4, v_attrKind_1271_);
lean_closure_set(v___f_1343_, 5, v_tk_1277_);
lean_closure_set(v___f_1343_, 6, v_alts_1334_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1344_; 
lean_dec(v_attrKind_1271_);
v___x_1344_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1343_, v___x_1274_, v___y_1265_, v___y_1267_);
return v___x_1344_;
}
else
{
lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1345_ = l_Lean_Syntax_getArg(v_attrKind_1271_, v___x_1181_);
lean_dec(v_attrKind_1271_);
lean_inc(v___x_1345_);
v___x_1346_ = l_Lean_Syntax_matchesNull(v___x_1345_, v___y_1268_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; 
lean_dec(v___x_1345_);
v___x_1347_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1343_, v___x_1274_, v___y_1265_, v___y_1267_);
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1348_ = l_Lean_Syntax_getArg(v___x_1345_, v___x_1181_);
lean_dec(v___x_1345_);
v___x_1349_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1350_ = l_Lean_Syntax_isOfKind(v___x_1348_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1343_, v___x_1274_, v___y_1265_, v___y_1267_);
return v___x_1351_;
}
else
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1343_, v___x_1333_, v___y_1265_, v___y_1267_);
return v___x_1352_;
}
}
}
}
else
{
lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1353_ = l_Lean_Syntax_getArg(v___x_1332_, v___x_1181_);
lean_dec(v___x_1332_);
lean_inc(v___x_1353_);
v___x_1354_ = l_Lean_Syntax_matchesNull(v___x_1353_, v___y_1268_);
if (v___x_1354_ == 0)
{
lean_object* v_alts_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___f_1364_; 
lean_dec(v___x_1353_);
lean_dec(v___x_1310_);
v_alts_1355_ = l_Lean_Syntax_getArgs(v___x_1289_);
lean_dec(v___x_1289_);
v___x_1356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1357_ = lean_box(2);
lean_inc_ref(v_alts_1355_);
v___x_1358_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v___x_1356_);
lean_ctor_set(v___x_1358_, 2, v_alts_1355_);
v___x_1359_ = lean_mk_empty_array_with_capacity(v___x_1270_);
lean_inc(v_tk_1277_);
v___x_1360_ = lean_array_push(v___x_1359_, v_tk_1277_);
v___x_1361_ = lean_array_push(v___x_1360_, v___x_1358_);
v___x_1362_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1357_);
lean_ctor_set(v___x_1362_, 1, v___x_1356_);
lean_ctor_set(v___x_1362_, 2, v___x_1361_);
v___x_1363_ = l_Lean_TSyntax_getId(v_kind_1288_);
lean_dec(v_kind_1288_);
lean_inc(v_attrKind_1271_);
v___f_1364_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1364_, 0, v___x_1362_);
lean_closure_set(v___f_1364_, 1, v___x_1363_);
lean_closure_set(v___f_1364_, 2, v___y_1266_);
lean_closure_set(v___f_1364_, 3, v_attrs_x3f_1269_);
lean_closure_set(v___f_1364_, 4, v_attrKind_1271_);
lean_closure_set(v___f_1364_, 5, v_tk_1277_);
lean_closure_set(v___f_1364_, 6, v_alts_1355_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1365_; 
lean_dec(v_attrKind_1271_);
v___x_1365_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1364_, v___x_1274_, v___y_1265_, v___y_1267_);
return v___x_1365_;
}
else
{
lean_object* v___x_1366_; uint8_t v___x_1367_; 
v___x_1366_ = l_Lean_Syntax_getArg(v_attrKind_1271_, v___x_1181_);
lean_dec(v_attrKind_1271_);
lean_inc(v___x_1366_);
v___x_1367_ = l_Lean_Syntax_matchesNull(v___x_1366_, v___y_1268_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; 
lean_dec(v___x_1366_);
v___x_1368_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1364_, v___x_1274_, v___y_1265_, v___y_1267_);
return v___x_1368_;
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1369_ = l_Lean_Syntax_getArg(v___x_1366_, v___x_1181_);
lean_dec(v___x_1366_);
v___x_1370_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1371_ = l_Lean_Syntax_isOfKind(v___x_1369_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1364_, v___x_1274_, v___y_1265_, v___y_1267_);
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1364_, v___x_1354_, v___y_1265_, v___y_1267_);
return v___x_1373_;
}
}
}
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1374_ = l_Lean_Syntax_getArg(v___x_1353_, v___x_1181_);
lean_dec(v___x_1353_);
v___x_1375_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14));
lean_inc(v___x_1374_);
v___x_1376_ = l_Lean_Syntax_isOfKind(v___x_1374_, v___x_1375_);
if (v___x_1376_ == 0)
{
lean_object* v_alts_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___f_1386_; 
lean_dec(v___x_1374_);
lean_dec(v___x_1310_);
v_alts_1377_ = l_Lean_Syntax_getArgs(v___x_1289_);
lean_dec(v___x_1289_);
v___x_1378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1379_ = lean_box(2);
lean_inc_ref(v_alts_1377_);
v___x_1380_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
lean_ctor_set(v___x_1380_, 1, v___x_1378_);
lean_ctor_set(v___x_1380_, 2, v_alts_1377_);
v___x_1381_ = lean_mk_empty_array_with_capacity(v___x_1270_);
lean_inc(v_tk_1277_);
v___x_1382_ = lean_array_push(v___x_1381_, v_tk_1277_);
v___x_1383_ = lean_array_push(v___x_1382_, v___x_1380_);
v___x_1384_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1379_);
lean_ctor_set(v___x_1384_, 1, v___x_1378_);
lean_ctor_set(v___x_1384_, 2, v___x_1383_);
v___x_1385_ = l_Lean_TSyntax_getId(v_kind_1288_);
lean_dec(v_kind_1288_);
lean_inc(v_attrKind_1271_);
v___f_1386_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1386_, 0, v___x_1384_);
lean_closure_set(v___f_1386_, 1, v___x_1385_);
lean_closure_set(v___f_1386_, 2, v___y_1266_);
lean_closure_set(v___f_1386_, 3, v_attrs_x3f_1269_);
lean_closure_set(v___f_1386_, 4, v_attrKind_1271_);
lean_closure_set(v___f_1386_, 5, v_tk_1277_);
lean_closure_set(v___f_1386_, 6, v_alts_1377_);
if (v___x_1274_ == 0)
{
lean_dec(v_attrKind_1271_);
v___y_1102_ = v___y_1265_;
v___y_1103_ = v___y_1267_;
v___y_1104_ = v___x_1376_;
v___y_1105_ = v___f_1386_;
v___y_1106_ = v___x_1354_;
v___y_1107_ = v___x_1376_;
goto v___jp_1101_;
}
else
{
lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1387_ = l_Lean_Syntax_getArg(v_attrKind_1271_, v___x_1181_);
lean_dec(v_attrKind_1271_);
lean_inc(v___x_1387_);
v___x_1388_ = l_Lean_Syntax_matchesNull(v___x_1387_, v___y_1268_);
if (v___x_1388_ == 0)
{
lean_dec(v___x_1387_);
v___y_1102_ = v___y_1265_;
v___y_1103_ = v___y_1267_;
v___y_1104_ = v___x_1376_;
v___y_1105_ = v___f_1386_;
v___y_1106_ = v___x_1354_;
v___y_1107_ = v___x_1376_;
goto v___jp_1101_;
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1389_ = l_Lean_Syntax_getArg(v___x_1387_, v___x_1181_);
lean_dec(v___x_1387_);
v___x_1390_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1391_ = l_Lean_Syntax_isOfKind(v___x_1389_, v___x_1390_);
if (v___x_1391_ == 0)
{
v___y_1102_ = v___y_1265_;
v___y_1103_ = v___y_1267_;
v___y_1104_ = v___x_1376_;
v___y_1105_ = v___f_1386_;
v___y_1106_ = v___x_1354_;
v___y_1107_ = v___x_1376_;
goto v___jp_1101_;
}
else
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1386_, v___x_1376_, v___y_1265_, v___y_1267_);
return v___x_1392_;
}
}
}
}
else
{
lean_object* v___x_1393_; 
lean_dec(v___x_1289_);
v___x_1393_ = l_Lean_Elab_Command_getRef___redArg(v___y_1265_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v_fileName_1395_; lean_object* v_fileMap_1396_; lean_object* v_currRecDepth_1397_; lean_object* v_cmdPos_1398_; lean_object* v_macroStack_1399_; lean_object* v_quotContext_x3f_1400_; lean_object* v_currMacroScope_1401_; lean_object* v_snap_x3f_1402_; lean_object* v_cancelTk_x3f_1403_; uint8_t v_suppressElabErrors_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1432_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref(v___x_1393_);
v_fileName_1395_ = lean_ctor_get(v___y_1265_, 0);
v_fileMap_1396_ = lean_ctor_get(v___y_1265_, 1);
v_currRecDepth_1397_ = lean_ctor_get(v___y_1265_, 2);
v_cmdPos_1398_ = lean_ctor_get(v___y_1265_, 3);
v_macroStack_1399_ = lean_ctor_get(v___y_1265_, 4);
v_quotContext_x3f_1400_ = lean_ctor_get(v___y_1265_, 5);
v_currMacroScope_1401_ = lean_ctor_get(v___y_1265_, 6);
v_snap_x3f_1402_ = lean_ctor_get(v___y_1265_, 8);
v_cancelTk_x3f_1403_ = lean_ctor_get(v___y_1265_, 9);
v_suppressElabErrors_1404_ = lean_ctor_get_uint8(v___y_1265_, sizeof(void*)*10);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___y_1265_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; 
v_unused_1433_ = lean_ctor_get(v___y_1265_, 7);
lean_dec(v_unused_1433_);
v___x_1406_ = v___y_1265_;
v_isShared_1407_ = v_isSharedCheck_1432_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_cancelTk_x3f_1403_);
lean_inc(v_snap_x3f_1402_);
lean_inc(v_currMacroScope_1401_);
lean_inc(v_quotContext_x3f_1400_);
lean_inc(v_macroStack_1399_);
lean_inc(v_cmdPos_1398_);
lean_inc(v_currRecDepth_1397_);
lean_inc(v_fileMap_1396_);
lean_inc(v_fileName_1395_);
lean_dec(v___y_1265_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1432_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v_ref_1415_; lean_object* v___x_1417_; 
v___x_1408_ = l_Lean_Syntax_getArg(v___x_1310_, v___x_1276_);
lean_dec(v___x_1310_);
v___x_1409_ = lean_mk_empty_array_with_capacity(v___x_1270_);
lean_inc(v_tk_1277_);
v___x_1410_ = lean_array_push(v___x_1409_, v_tk_1277_);
lean_inc(v___x_1408_);
v___x_1411_ = lean_array_push(v___x_1410_, v___x_1408_);
v___x_1412_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1413_ = lean_box(2);
v___x_1414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
lean_ctor_set(v___x_1414_, 1, v___x_1412_);
lean_ctor_set(v___x_1414_, 2, v___x_1411_);
v_ref_1415_ = l_Lean_replaceRef(v___x_1414_, v_a_1394_);
lean_dec(v_a_1394_);
lean_dec_ref(v___x_1414_);
lean_inc(v_quotContext_x3f_1400_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 7, v_ref_1415_);
v___x_1417_ = v___x_1406_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_fileName_1395_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_fileMap_1396_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_currRecDepth_1397_);
lean_ctor_set(v_reuseFailAlloc_1431_, 3, v_cmdPos_1398_);
lean_ctor_set(v_reuseFailAlloc_1431_, 4, v_macroStack_1399_);
lean_ctor_set(v_reuseFailAlloc_1431_, 5, v_quotContext_x3f_1400_);
lean_ctor_set(v_reuseFailAlloc_1431_, 6, v_currMacroScope_1401_);
lean_ctor_set(v_reuseFailAlloc_1431_, 7, v_ref_1415_);
lean_ctor_set(v_reuseFailAlloc_1431_, 8, v_snap_x3f_1402_);
lean_ctor_set(v_reuseFailAlloc_1431_, 9, v_cancelTk_x3f_1403_);
lean_ctor_set_uint8(v_reuseFailAlloc_1431_, sizeof(void*)*10, v_suppressElabErrors_1404_);
v___x_1417_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_Elab_Command_getRef___redArg(v___x_1417_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1420_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref(v___x_1418_);
v___x_1420_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_1417_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v___x_1421_; 
lean_dec_ref(v___x_1420_);
v___x_1421_ = l_Lean_SourceInfo_fromRef(v_a_1419_, v___x_1280_);
lean_dec(v_a_1419_);
if (lean_obj_tag(v_quotContext_x3f_1400_) == 0)
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_1267_);
lean_dec_ref(v___x_1422_);
v___y_1233_ = v___x_1374_;
v___y_1234_ = v___x_1280_;
v___y_1235_ = v___x_1408_;
v___y_1236_ = v___y_1267_;
v___y_1237_ = v_kind_1288_;
v___y_1238_ = v___x_1417_;
v___y_1239_ = v_quotContext_x3f_1400_;
v___y_1240_ = v___y_1268_;
v___y_1241_ = v___x_1272_;
v___y_1242_ = v___x_1421_;
v___y_1243_ = v___x_1412_;
v___y_1244_ = v_attrs_x3f_1269_;
v___y_1245_ = v_attrKind_1271_;
v___y_1246_ = v_tk_1277_;
v___y_1247_ = v___y_1266_;
goto v___jp_1232_;
}
else
{
v___y_1233_ = v___x_1374_;
v___y_1234_ = v___x_1280_;
v___y_1235_ = v___x_1408_;
v___y_1236_ = v___y_1267_;
v___y_1237_ = v_kind_1288_;
v___y_1238_ = v___x_1417_;
v___y_1239_ = v_quotContext_x3f_1400_;
v___y_1240_ = v___y_1268_;
v___y_1241_ = v___x_1272_;
v___y_1242_ = v___x_1421_;
v___y_1243_ = v___x_1412_;
v___y_1244_ = v_attrs_x3f_1269_;
v___y_1245_ = v_attrKind_1271_;
v___y_1246_ = v_tk_1277_;
v___y_1247_ = v___y_1266_;
goto v___jp_1232_;
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec(v_a_1419_);
lean_dec_ref(v___x_1417_);
lean_dec(v___x_1408_);
lean_dec(v_quotContext_x3f_1400_);
lean_dec(v___x_1374_);
lean_dec(v_kind_1288_);
lean_dec(v_tk_1277_);
lean_dec(v_attrKind_1271_);
lean_dec(v_attrs_x3f_1269_);
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
v_a_1423_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1420_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1420_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
else
{
lean_dec_ref(v___x_1417_);
lean_dec(v___x_1408_);
lean_dec(v_quotContext_x3f_1400_);
lean_dec(v___x_1374_);
lean_dec(v_kind_1288_);
lean_dec(v_tk_1277_);
lean_dec(v_attrKind_1271_);
lean_dec(v_attrs_x3f_1269_);
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
return v___x_1418_;
}
}
}
}
else
{
lean_dec(v___x_1374_);
lean_dec(v___x_1310_);
lean_dec(v_kind_1288_);
lean_dec(v_tk_1277_);
lean_dec(v_attrKind_1271_);
lean_dec(v_attrs_x3f_1269_);
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
return v___x_1393_;
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
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
lean_dec(v___x_1279_);
v___x_1434_ = lean_unsigned_to_nat(5u);
v___x_1435_ = l_Lean_Syntax_getArg(v_stx_1097_, v___x_1434_);
lean_dec(v_stx_1097_);
v___x_1436_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10));
lean_inc(v___x_1435_);
v___x_1437_ = l_Lean_Syntax_isOfKind(v___x_1435_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; 
lean_dec(v___x_1435_);
lean_dec(v_tk_1277_);
lean_dec(v_attrKind_1271_);
lean_dec(v_attrs_x3f_1269_);
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
v___x_1438_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1438_;
}
else
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_Elab_Command_getRef___redArg(v___y_1265_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v_fileName_1441_; lean_object* v_fileMap_1442_; lean_object* v_currRecDepth_1443_; lean_object* v_cmdPos_1444_; lean_object* v_macroStack_1445_; lean_object* v_quotContext_x3f_1446_; lean_object* v_currMacroScope_1447_; lean_object* v_snap_x3f_1448_; lean_object* v_cancelTk_x3f_1449_; uint8_t v_suppressElabErrors_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1485_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref(v___x_1439_);
v_fileName_1441_ = lean_ctor_get(v___y_1265_, 0);
v_fileMap_1442_ = lean_ctor_get(v___y_1265_, 1);
v_currRecDepth_1443_ = lean_ctor_get(v___y_1265_, 2);
v_cmdPos_1444_ = lean_ctor_get(v___y_1265_, 3);
v_macroStack_1445_ = lean_ctor_get(v___y_1265_, 4);
v_quotContext_x3f_1446_ = lean_ctor_get(v___y_1265_, 5);
v_currMacroScope_1447_ = lean_ctor_get(v___y_1265_, 6);
v_snap_x3f_1448_ = lean_ctor_get(v___y_1265_, 8);
v_cancelTk_x3f_1449_ = lean_ctor_get(v___y_1265_, 9);
v_suppressElabErrors_1450_ = lean_ctor_get_uint8(v___y_1265_, sizeof(void*)*10);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___y_1265_);
if (v_isSharedCheck_1485_ == 0)
{
lean_object* v_unused_1486_; 
v_unused_1486_ = lean_ctor_get(v___y_1265_, 7);
lean_dec(v_unused_1486_);
v___x_1452_ = v___y_1265_;
v_isShared_1453_ = v_isSharedCheck_1485_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_cancelTk_x3f_1449_);
lean_inc(v_snap_x3f_1448_);
lean_inc(v_currMacroScope_1447_);
lean_inc(v_quotContext_x3f_1446_);
lean_inc(v_macroStack_1445_);
lean_inc(v_cmdPos_1444_);
lean_inc(v_currRecDepth_1443_);
lean_inc(v_fileMap_1442_);
lean_inc(v_fileName_1441_);
lean_dec(v___y_1265_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1485_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; lean_object* v_alts_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___f_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v_ref_1464_; lean_object* v___x_1466_; 
v___x_1454_ = l_Lean_Syntax_getArg(v___x_1435_, v___x_1181_);
lean_dec(v___x_1435_);
v_alts_1455_ = l_Lean_Syntax_getArgs(v___x_1454_);
lean_dec(v___x_1454_);
v___x_1456_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1457_ = lean_box(2);
lean_inc_ref(v_alts_1455_);
v___x_1458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
lean_ctor_set(v___x_1458_, 1, v___x_1456_);
lean_ctor_set(v___x_1458_, 2, v_alts_1455_);
v___f_1459_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__5___boxed), 15, 10);
lean_closure_set(v___f_1459_, 0, v___x_1436_);
lean_closure_set(v___f_1459_, 1, v___x_1113_);
lean_closure_set(v___f_1459_, 2, v_attrKind_1271_);
lean_closure_set(v___f_1459_, 3, v___x_1112_);
lean_closure_set(v___f_1459_, 4, v___x_1181_);
lean_closure_set(v___f_1459_, 5, v_attrs_x3f_1269_);
lean_closure_set(v___f_1459_, 6, v___x_1110_);
lean_closure_set(v___f_1459_, 7, v___x_1111_);
lean_closure_set(v___f_1459_, 8, v___x_1272_);
lean_closure_set(v___f_1459_, 9, v___y_1266_);
v___x_1460_ = lean_mk_empty_array_with_capacity(v___x_1270_);
v___x_1461_ = lean_array_push(v___x_1460_, v_tk_1277_);
v___x_1462_ = lean_array_push(v___x_1461_, v___x_1458_);
v___x_1463_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1457_);
lean_ctor_set(v___x_1463_, 1, v___x_1456_);
lean_ctor_set(v___x_1463_, 2, v___x_1462_);
v_ref_1464_ = l_Lean_replaceRef(v___x_1463_, v_a_1440_);
lean_dec(v_a_1440_);
lean_dec_ref(v___x_1463_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 7, v_ref_1464_);
v___x_1466_ = v___x_1452_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_fileName_1441_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_fileMap_1442_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_currRecDepth_1443_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_cmdPos_1444_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v_macroStack_1445_);
lean_ctor_set(v_reuseFailAlloc_1484_, 5, v_quotContext_x3f_1446_);
lean_ctor_set(v_reuseFailAlloc_1484_, 6, v_currMacroScope_1447_);
lean_ctor_set(v_reuseFailAlloc_1484_, 7, v_ref_1464_);
lean_ctor_set(v_reuseFailAlloc_1484_, 8, v_snap_x3f_1448_);
lean_ctor_set(v_reuseFailAlloc_1484_, 9, v_cancelTk_x3f_1449_);
lean_ctor_set_uint8(v_reuseFailAlloc_1484_, sizeof(void*)*10, v_suppressElabErrors_1450_);
v___x_1466_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(v_alts_1455_, v___x_1112_, v___f_1459_, v___x_1466_, v___y_1267_);
lean_dec_ref(v_alts_1455_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1467_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1467_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
v_a_1476_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1467_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1467_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1435_);
lean_dec(v_tk_1277_);
lean_dec(v_attrKind_1271_);
lean_dec(v_attrs_x3f_1269_);
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
return v___x_1439_;
}
}
}
}
}
v___jp_1487_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; 
v___x_1491_ = lean_unsigned_to_nat(1u);
v___x_1492_ = l_Lean_Syntax_getArg(v_stx_1097_, v___x_1491_);
v___x_1493_ = l_Lean_Syntax_isNone(v___x_1492_);
if (v___x_1493_ == 0)
{
uint8_t v___x_1494_; 
lean_inc(v___x_1492_);
v___x_1494_ = l_Lean_Syntax_matchesNull(v___x_1492_, v___x_1491_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; 
lean_dec(v___x_1492_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v_doc_x3f_1488_);
lean_dec(v_stx_1097_);
v___x_1495_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1495_;
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1496_ = l_Lean_Syntax_getArg(v___x_1492_, v___x_1181_);
lean_dec(v___x_1492_);
v___x_1497_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15));
lean_inc(v___x_1496_);
v___x_1498_ = l_Lean_Syntax_isOfKind(v___x_1496_, v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
lean_dec(v___x_1496_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v_doc_x3f_1488_);
lean_dec(v_stx_1097_);
v___x_1499_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; lean_object* v_attrs_x3f_1501_; lean_object* v___x_1502_; 
v___x_1500_ = l_Lean_Syntax_getArg(v___x_1496_, v___x_1491_);
lean_dec(v___x_1496_);
v_attrs_x3f_1501_ = l_Lean_Syntax_getArgs(v___x_1500_);
lean_dec(v___x_1500_);
v___x_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1502_, 0, v_attrs_x3f_1501_);
v___y_1265_ = v___y_1489_;
v___y_1266_ = v_doc_x3f_1488_;
v___y_1267_ = v___y_1490_;
v___y_1268_ = v___x_1491_;
v_attrs_x3f_1269_ = v___x_1502_;
goto v___jp_1264_;
}
}
}
else
{
lean_object* v___x_1503_; 
lean_dec(v___x_1492_);
v___x_1503_ = lean_box(0);
v___y_1265_ = v___y_1489_;
v___y_1266_ = v_doc_x3f_1488_;
v___y_1267_ = v___y_1490_;
v___y_1268_ = v___x_1491_;
v_attrs_x3f_1269_ = v___x_1503_;
goto v___jp_1264_;
}
}
}
v___jp_1101_:
{
if (v___y_1107_ == 0)
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1105_, v___y_1106_, v___y_1102_, v___y_1103_);
return v___x_1108_;
}
else
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1105_, v___y_1104_, v___y_1102_, v___y_1103_);
return v___x_1109_;
}
}
v___jp_1115_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_inc_ref(v___y_1123_);
v___x_1131_ = l_Array_append___redArg(v___y_1123_, v___y_1130_);
lean_dec_ref(v___y_1130_);
lean_inc(v___y_1125_);
lean_inc(v___y_1129_);
v___x_1132_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1132_, 0, v___y_1129_);
lean_ctor_set(v___x_1132_, 1, v___y_1125_);
lean_ctor_set(v___x_1132_, 2, v___x_1131_);
v___x_1133_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
lean_inc_ref(v___y_1122_);
v___x_1134_ = l_Lean_Name_mkStr4(v___x_1110_, v___x_1111_, v___y_1122_, v___x_1133_);
v___x_1135_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
lean_inc(v___y_1129_);
v___x_1136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___y_1129_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
lean_inc_ref(v___y_1123_);
v___x_1137_ = l_Array_append___redArg(v___y_1123_, v___y_1126_);
lean_dec_ref(v___y_1126_);
lean_inc(v___y_1125_);
lean_inc(v___y_1129_);
v___x_1138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1138_, 0, v___y_1129_);
lean_ctor_set(v___x_1138_, 1, v___y_1125_);
lean_ctor_set(v___x_1138_, 2, v___x_1137_);
v___x_1139_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
lean_inc(v___y_1129_);
v___x_1140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___y_1129_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
lean_inc(v___y_1129_);
v___x_1141_ = l_Lean_Syntax_node3(v___y_1129_, v___x_1134_, v___x_1136_, v___x_1138_, v___x_1140_);
lean_inc(v___y_1125_);
lean_inc(v___y_1129_);
v___x_1142_ = l_Lean_Syntax_node1(v___y_1129_, v___y_1125_, v___x_1141_);
lean_inc(v___y_1129_);
v___x_1143_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___y_1129_);
lean_ctor_set(v___x_1143_, 1, v___y_1118_);
v___x_1144_ = l_Lean_TSyntax_getId(v___y_1119_);
v___x_1145_ = l_Lean_mkIdentFrom(v___y_1127_, v___x_1144_, v___x_1114_);
lean_dec(v___y_1127_);
lean_inc(v___y_1125_);
lean_inc(v___y_1129_);
v___x_1146_ = l_Lean_Syntax_node2(v___y_1129_, v___y_1125_, v___x_1145_, v___y_1119_);
v___x_1147_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__6));
lean_inc(v___y_1129_);
v___x_1148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___y_1129_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__8, &l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8);
v___x_1150_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__9));
v___x_1151_ = l_Lean_addMacroScope(v___y_1128_, v___x_1150_, v___y_1121_);
v___x_1152_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6));
lean_inc(v___y_1129_);
v___x_1153_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1153_, 0, v___y_1129_);
lean_ctor_set(v___x_1153_, 1, v___x_1149_);
lean_ctor_set(v___x_1153_, 2, v___x_1151_);
lean_ctor_set(v___x_1153_, 3, v___x_1152_);
v___x_1154_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
lean_inc(v___y_1129_);
v___x_1155_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___y_1129_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__11));
lean_inc_ref(v___y_1122_);
v___x_1157_ = l_Lean_Name_mkStr4(v___x_1110_, v___x_1111_, v___y_1122_, v___x_1156_);
lean_inc(v___y_1129_);
v___x_1158_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___y_1129_);
lean_ctor_set(v___x_1158_, 1, v___x_1156_);
v___x_1159_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7));
v___x_1160_ = l_Lean_Name_mkStr4(v___x_1110_, v___x_1111_, v___y_1122_, v___x_1159_);
lean_inc(v___y_1125_);
lean_inc(v___y_1129_);
v___x_1161_ = l_Lean_Syntax_node1(v___y_1129_, v___y_1125_, v___y_1116_);
lean_inc(v___y_1129_);
v___x_1162_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1162_, 0, v___y_1129_);
lean_ctor_set(v___x_1162_, 1, v___y_1125_);
lean_ctor_set(v___x_1162_, 2, v___y_1123_);
v___x_1163_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13));
lean_inc(v___y_1129_);
v___x_1164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___y_1129_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
lean_inc(v___y_1129_);
v___x_1165_ = l_Lean_Syntax_node4(v___y_1129_, v___x_1160_, v___x_1161_, v___x_1162_, v___x_1164_, v___y_1117_);
lean_inc(v___y_1129_);
v___x_1166_ = l_Lean_Syntax_node2(v___y_1129_, v___x_1157_, v___x_1158_, v___x_1165_);
v___x_1167_ = lean_unsigned_to_nat(9u);
v___x_1168_ = lean_mk_empty_array_with_capacity(v___x_1167_);
v___x_1169_ = lean_array_push(v___x_1168_, v___x_1132_);
v___x_1170_ = lean_array_push(v___x_1169_, v___x_1142_);
v___x_1171_ = lean_array_push(v___x_1170_, v___y_1120_);
v___x_1172_ = lean_array_push(v___x_1171_, v___x_1143_);
v___x_1173_ = lean_array_push(v___x_1172_, v___x_1146_);
v___x_1174_ = lean_array_push(v___x_1173_, v___x_1148_);
v___x_1175_ = lean_array_push(v___x_1174_, v___x_1153_);
v___x_1176_ = lean_array_push(v___x_1175_, v___x_1155_);
v___x_1177_ = lean_array_push(v___x_1176_, v___x_1166_);
v___x_1178_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1178_, 0, v___y_1129_);
lean_ctor_set(v___x_1178_, 1, v___y_1124_);
lean_ctor_set(v___x_1178_, 2, v___x_1177_);
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___boxed(lean_object* v_stx_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_Elab_Command_elabMacroRules___lam__1(v_stx_1515_, v___y_1516_, v___y_1517_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules(lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v___f_1525_; lean_object* v___x_1526_; 
v___f_1525_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___closed__0));
v___x_1526_ = l_Lean_Elab_Command_adaptExpander(v___f_1525_, v_a_1521_, v_a_1522_, v_a_1523_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___boxed(lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_Elab_Command_elabMacroRules(v_a_1527_, v_a_1528_, v_a_1529_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1(){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1539_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1540_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1));
v___x_1541_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1));
v___x_1542_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___boxed), 4, 0);
v___x_1543_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1539_, v___x_1540_, v___x_1541_, v___x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___boxed(lean_object* v_a_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1();
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3(){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1572_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1));
v___x_1573_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6));
v___x_1574_ = l_Lean_addBuiltinDeclarationRanges(v___x_1572_, v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___boxed(lean_object* v_a_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3();
return v_res_1576_;
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
res = l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3();
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
