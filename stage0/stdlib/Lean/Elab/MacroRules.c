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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_14_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_11_ = stack[1].m_obj;
lean_object* v___y_12_ = stack[2].m_obj;
lean_object* v_res_15_;
v_res_15_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0(lean_box(0), v___y_11_, v___y_12_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___boxed(lean_object* v_00_u03b1_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0(v_00_u03b1_16_, v___y_17_, v___y_18_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_20_;
}
}
lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(lean_object* v___y_21_){
_start:
{
lean_object* v___x_23_; lean_object* v_env_24_; lean_object* v___x_25_; lean_object* v_mainModule_26_; lean_object* v___x_27_; 
v___x_23_ = lean_st_ref_get(v___y_21_);
v_env_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc_ref(v_env_24_);
lean_dec(v___x_23_);
v___x_25_ = l_Lean_Environment_header(v_env_24_);
lean_dec_ref(v_env_24_);
v_mainModule_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc(v_mainModule_26_);
lean_dec_ref(v___x_25_);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v_mainModule_26_);
return v___x_27_;
}
}
LEAN_EXPORT void l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_21_ = stack[0].m_obj;
lean_object* v_res_28_;
v_res_28_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_21_);
stack->m_obj
 = v_res_28_;
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg___boxed(lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_29_);
lean_dec(v___y_29_);
return v_res_31_;
}
}
lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3(lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_33_);
return v___x_35_;
}
}
LEAN_EXPORT void l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_32_ = stack[0].m_obj;
lean_object* v___y_33_ = stack[1].m_obj;
lean_object* v_res_36_;
v_res_36_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3(v___y_32_, v___y_33_);
stack->m_obj
 = v_res_36_;
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___boxed(lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3(v___y_37_, v___y_38_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
return v_res_40_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_41_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_44_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_45_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_46_ = lean_unsigned_to_nat(0u);
v___x_47_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
lean_ctor_set(v___x_47_, 2, v___x_46_);
lean_ctor_set(v___x_47_, 3, v___x_46_);
lean_ctor_set(v___x_47_, 4, v___x_45_);
lean_ctor_set(v___x_47_, 5, v___x_45_);
lean_ctor_set(v___x_47_, 6, v___x_45_);
lean_ctor_set(v___x_47_, 7, v___x_45_);
lean_ctor_set(v___x_47_, 8, v___x_45_);
lean_ctor_set(v___x_47_, 9, v___x_45_);
lean_ctor_set(v___x_47_, 10, v___x_45_);
lean_ctor_set(v___x_47_, 11, v___x_44_);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_unsigned_to_nat(32u);
v___x_49_ = lean_mk_empty_array_with_capacity(v___x_48_);
v___x_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4(void){
_start:
{
size_t v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_51_ = ((size_t)5ULL);
v___x_52_ = lean_unsigned_to_nat(0u);
v___x_53_ = lean_unsigned_to_nat(32u);
v___x_54_ = lean_mk_empty_array_with_capacity(v___x_53_);
v___x_55_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3);
v___x_56_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_54_);
lean_ctor_set(v___x_56_, 2, v___x_52_);
lean_ctor_set(v___x_56_, 3, v___x_52_);
lean_ctor_set_usize(v___x_56_, 4, v___x_51_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = lean_box(1);
v___x_58_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4);
v___x_59_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_60_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___x_58_);
lean_ctor_set(v___x_60_, 2, v___x_57_);
return v___x_60_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(lean_object* v_msgData_61_, lean_object* v___y_62_){
_start:
{
lean_object* v___x_64_; lean_object* v_env_65_; uint8_t v___x_66_; lean_object* v_env_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v_scopes_70_; lean_object* v___x_71_; lean_object* v_opts_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_64_ = lean_st_ref_get(v___y_62_);
v_env_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc_ref(v_env_65_);
lean_dec(v___x_64_);
v___x_66_ = 0;
v_env_67_ = l_Lean_Environment_setRecordingDeps(v_env_65_, v___x_66_);
v___x_68_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_69_ = lean_st_ref_get(v___y_62_);
v_scopes_70_ = lean_ctor_get(v___x_69_, 2);
lean_inc(v_scopes_70_);
lean_dec(v___x_69_);
v___x_71_ = l_List_head_x21___redArg(v___x_68_, v_scopes_70_);
lean_dec(v_scopes_70_);
v_opts_72_ = lean_ctor_get(v___x_71_, 1);
lean_inc_ref(v_opts_72_);
lean_dec(v___x_71_);
v___x_73_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_74_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5);
v___x_75_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_75_, 0, v_env_67_);
lean_ctor_set(v___x_75_, 1, v___x_73_);
lean_ctor_set(v___x_75_, 2, v___x_74_);
lean_ctor_set(v___x_75_, 3, v_opts_72_);
v___x_76_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v_msgData_61_);
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_61_ = stack[0].m_obj;
lean_object* v___y_62_ = stack[1].m_obj;
lean_object* v_res_78_;
v_res_78_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msgData_61_, v___y_62_);
stack->m_obj
 = v_res_78_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msgData_79_, v___y_80_);
lean_dec(v___y_80_);
return v_res_82_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_box(1);
v___x_84_ = l_Lean_MessageData_ofFormat(v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__2));
v___x_89_ = l_Lean_MessageData_ofFormat(v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8(lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
if (lean_obj_tag(v_x_91_) == 0)
{
return v_x_90_;
}
else
{
lean_object* v_head_92_; lean_object* v_tail_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_115_; 
v_head_92_ = lean_ctor_get(v_x_91_, 0);
v_tail_93_ = lean_ctor_get(v_x_91_, 1);
v_isSharedCheck_115_ = !lean_is_exclusive(v_x_91_);
if (v_isSharedCheck_115_ == 0)
{
v___x_95_ = v_x_91_;
v_isShared_96_ = v_isSharedCheck_115_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_tail_93_);
lean_inc(v_head_92_);
lean_dec(v_x_91_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_115_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v_before_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_113_; 
v_before_97_ = lean_ctor_get(v_head_92_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v_head_92_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; 
v_unused_114_ = lean_ctor_get(v_head_92_, 1);
lean_dec(v_unused_114_);
v___x_99_ = v_head_92_;
v_isShared_100_ = v_isSharedCheck_113_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_before_97_);
lean_dec(v_head_92_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_113_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_101_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0);
if (v_isShared_100_ == 0)
{
lean_ctor_set_tag(v___x_99_, 7);
lean_ctor_set(v___x_99_, 1, v___x_101_);
lean_ctor_set(v___x_99_, 0, v_x_90_);
v___x_103_ = v___x_99_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_x_90_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v___x_101_);
v___x_103_ = v_reuseFailAlloc_112_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_104_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3);
if (v_isShared_96_ == 0)
{
lean_ctor_set_tag(v___x_95_, 7);
lean_ctor_set(v___x_95_, 1, v___x_104_);
lean_ctor_set(v___x_95_, 0, v___x_103_);
v___x_106_ = v___x_95_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v___x_104_);
v___x_106_ = v_reuseFailAlloc_111_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = l_Lean_MessageData_ofSyntax(v_before_97_);
v___x_108_ = l_Lean_indentD(v___x_107_);
v___x_109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_106_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v_x_90_ = v___x_109_;
v_x_91_ = v_tail_93_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(lean_object* v_opts_116_, lean_object* v_opt_117_){
_start:
{
lean_object* v_name_118_; lean_object* v_defValue_119_; lean_object* v_map_120_; lean_object* v___x_121_; 
v_name_118_ = lean_ctor_get(v_opt_117_, 0);
v_defValue_119_ = lean_ctor_get(v_opt_117_, 1);
v_map_120_ = lean_ctor_get(v_opts_116_, 0);
v___x_121_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_120_, v_name_118_);
if (lean_obj_tag(v___x_121_) == 0)
{
uint8_t v___x_122_; 
v___x_122_ = lean_unbox(v_defValue_119_);
return v___x_122_;
}
else
{
lean_object* v_val_123_; 
v_val_123_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_val_123_);
lean_dec_ref_known(v___x_121_, 1);
if (lean_obj_tag(v_val_123_) == 1)
{
uint8_t v_v_124_; 
v_v_124_ = lean_ctor_get_uint8(v_val_123_, 0);
lean_dec_ref_known(v_val_123_, 0);
return v_v_124_;
}
else
{
uint8_t v___x_125_; 
lean_dec(v_val_123_);
v___x_125_ = lean_unbox(v_defValue_119_);
return v___x_125_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_116_ = stack[0].m_obj;
lean_object* v_opt_117_ = stack[1].m_obj;
uint8_t v_res_126_;
v_res_126_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(v_opts_116_, v_opt_117_);
stack->m_num = v_res_126_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7___boxed(lean_object* v_opts_127_, lean_object* v_opt_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(v_opts_127_, v_opt_128_);
lean_dec_ref(v_opt_128_);
lean_dec_ref(v_opts_127_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__1));
v___x_135_ = l_Lean_MessageData_ofFormat(v___x_134_);
return v___x_135_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(lean_object* v_msgData_136_, lean_object* v_macroStack_137_, lean_object* v___y_138_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v_scopes_142_; lean_object* v___x_143_; lean_object* v_opts_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_140_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_141_ = lean_st_ref_get(v___y_138_);
v_scopes_142_ = lean_ctor_get(v___x_141_, 2);
lean_inc(v_scopes_142_);
lean_dec(v___x_141_);
v___x_143_ = l_List_head_x21___redArg(v___x_140_, v_scopes_142_);
lean_dec(v_scopes_142_);
v_opts_144_ = lean_ctor_get(v___x_143_, 1);
lean_inc_ref(v_opts_144_);
lean_dec(v___x_143_);
v___x_145_ = l_Lean_Elab_pp_macroStack;
v___x_146_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(v_opts_144_, v___x_145_);
lean_dec_ref(v_opts_144_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; 
lean_dec(v_macroStack_137_);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v_msgData_136_);
return v___x_147_;
}
else
{
if (lean_obj_tag(v_macroStack_137_) == 0)
{
lean_object* v___x_148_; 
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v_msgData_136_);
return v___x_148_;
}
else
{
lean_object* v_head_149_; lean_object* v_after_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_165_; 
v_head_149_ = lean_ctor_get(v_macroStack_137_, 0);
lean_inc(v_head_149_);
v_after_150_ = lean_ctor_get(v_head_149_, 1);
v_isSharedCheck_165_ = !lean_is_exclusive(v_head_149_);
if (v_isSharedCheck_165_ == 0)
{
lean_object* v_unused_166_; 
v_unused_166_ = lean_ctor_get(v_head_149_, 0);
lean_dec(v_unused_166_);
v___x_152_ = v_head_149_;
v_isShared_153_ = v_isSharedCheck_165_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_after_150_);
lean_dec(v_head_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_165_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_154_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0);
if (v_isShared_153_ == 0)
{
lean_ctor_set_tag(v___x_152_, 7);
lean_ctor_set(v___x_152_, 1, v___x_154_);
lean_ctor_set(v___x_152_, 0, v_msgData_136_);
v___x_156_ = v___x_152_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_msgData_136_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v___x_154_);
v___x_156_ = v_reuseFailAlloc_164_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v_msgData_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_157_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2);
v___x_158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_156_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = l_Lean_MessageData_ofSyntax(v_after_150_);
v___x_160_ = l_Lean_indentD(v___x_159_);
v_msgData_161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_161_, 0, v___x_158_);
lean_ctor_set(v_msgData_161_, 1, v___x_160_);
v___x_162_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8(v_msgData_161_, v_macroStack_137_);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_136_ = stack[0].m_obj;
lean_object* v_macroStack_137_ = stack[1].m_obj;
lean_object* v___y_138_ = stack[2].m_obj;
lean_object* v_res_167_;
v_res_167_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_msgData_136_, v_macroStack_137_, v___y_138_);
stack->m_obj
 = v_res_167_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_msgData_168_, lean_object* v_macroStack_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_msgData_168_, v_macroStack_169_, v___y_170_);
lean_dec(v___y_170_);
return v_res_172_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(lean_object* v_msg_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Elab_Command_getRef___redArg(v___y_174_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v_macroStack_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v_a_182_; lean_object* v___x_183_; lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_192_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_177_, 1);
v_macroStack_179_ = lean_ctor_get(v___y_174_, 4);
v___x_180_ = l_Lean_Elab_getBetterRef(v_a_178_, v_macroStack_179_);
lean_dec(v_a_178_);
v___x_181_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msg_173_, v___y_175_);
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref(v___x_181_);
lean_inc(v_macroStack_179_);
v___x_183_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_a_182_, v_macroStack_179_, v___y_175_);
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_192_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_192_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_192_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_180_);
lean_ctor_set(v___x_188_, 1, v_a_184_);
if (v_isShared_187_ == 0)
{
lean_ctor_set_tag(v___x_186_, 1);
lean_ctor_set(v___x_186_, 0, v___x_188_);
v___x_190_ = v___x_186_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec_ref(v_msg_173_);
v_a_193_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_177_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_177_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_173_ = stack[0].m_obj;
lean_object* v___y_174_ = stack[1].m_obj;
lean_object* v___y_175_ = stack[2].m_obj;
lean_object* v_res_201_;
v_res_201_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_173_, v___y_174_, v___y_175_);
stack->m_obj
 = v_res_201_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg___boxed(lean_object* v_msg_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
return v_res_206_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(lean_object* v_ref_207_, lean_object* v_msg_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Elab_Command_getRef___redArg(v___y_209_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v_fileName_214_; lean_object* v_fileMap_215_; lean_object* v_currRecDepth_216_; lean_object* v_cmdPos_217_; lean_object* v_macroStack_218_; lean_object* v_quotContext_x3f_219_; lean_object* v_currMacroScope_220_; lean_object* v_snap_x3f_221_; lean_object* v_cancelTk_x3f_222_; uint8_t v_suppressElabErrors_223_; lean_object* v_ref_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_a_213_);
lean_dec_ref_known(v___x_212_, 1);
v_fileName_214_ = lean_ctor_get(v___y_209_, 0);
v_fileMap_215_ = lean_ctor_get(v___y_209_, 1);
v_currRecDepth_216_ = lean_ctor_get(v___y_209_, 2);
v_cmdPos_217_ = lean_ctor_get(v___y_209_, 3);
v_macroStack_218_ = lean_ctor_get(v___y_209_, 4);
v_quotContext_x3f_219_ = lean_ctor_get(v___y_209_, 5);
v_currMacroScope_220_ = lean_ctor_get(v___y_209_, 6);
v_snap_x3f_221_ = lean_ctor_get(v___y_209_, 8);
v_cancelTk_x3f_222_ = lean_ctor_get(v___y_209_, 9);
v_suppressElabErrors_223_ = lean_ctor_get_uint8(v___y_209_, sizeof(void*)*10);
v_ref_224_ = l_Lean_replaceRef(v_ref_207_, v_a_213_);
lean_dec(v_a_213_);
lean_inc(v_cancelTk_x3f_222_);
lean_inc(v_snap_x3f_221_);
lean_inc(v_currMacroScope_220_);
lean_inc(v_quotContext_x3f_219_);
lean_inc(v_macroStack_218_);
lean_inc(v_cmdPos_217_);
lean_inc(v_currRecDepth_216_);
lean_inc_ref(v_fileMap_215_);
lean_inc_ref(v_fileName_214_);
v___x_225_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_225_, 0, v_fileName_214_);
lean_ctor_set(v___x_225_, 1, v_fileMap_215_);
lean_ctor_set(v___x_225_, 2, v_currRecDepth_216_);
lean_ctor_set(v___x_225_, 3, v_cmdPos_217_);
lean_ctor_set(v___x_225_, 4, v_macroStack_218_);
lean_ctor_set(v___x_225_, 5, v_quotContext_x3f_219_);
lean_ctor_set(v___x_225_, 6, v_currMacroScope_220_);
lean_ctor_set(v___x_225_, 7, v_ref_224_);
lean_ctor_set(v___x_225_, 8, v_snap_x3f_221_);
lean_ctor_set(v___x_225_, 9, v_cancelTk_x3f_222_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*10, v_suppressElabErrors_223_);
v___x_226_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_208_, v___x_225_, v___y_210_);
lean_dec_ref_known(v___x_225_, 10);
return v___x_226_;
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
lean_dec_ref(v_msg_208_);
v_a_227_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_212_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_212_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_207_ = stack[0].m_obj;
lean_object* v_msg_208_ = stack[1].m_obj;
lean_object* v___y_209_ = stack[2].m_obj;
lean_object* v___y_210_ = stack[3].m_obj;
lean_object* v_res_235_;
v_res_235_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_ref_207_, v_msg_208_, v___y_209_, v___y_210_);
stack->m_obj
 = v_res_235_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg___boxed(lean_object* v_ref_236_, lean_object* v_msg_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_ref_236_, v_msg_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v_ref_236_);
return v_res_241_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(lean_object* v_k_245_, lean_object* v_as_246_, size_t v_sz_247_, size_t v_i_248_, lean_object* v_b_249_){
_start:
{
uint8_t v___x_250_; 
v___x_250_ = lean_usize_dec_lt(v_i_248_, v_sz_247_);
if (v___x_250_ == 0)
{
lean_dec(v_k_245_);
lean_inc_ref(v_b_249_);
return v_b_249_;
}
else
{
lean_object* v___x_251_; lean_object* v_a_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_251_ = lean_box(0);
v_a_252_ = lean_array_uget_borrowed(v_as_246_, v_i_248_);
lean_inc(v_a_252_);
v___x_253_ = l_Lean_Syntax_getKind(v_a_252_);
lean_inc(v_k_245_);
v___x_254_ = l_Lean_Elab_Command_checkRuleKind(v___x_253_, v_k_245_);
lean_dec(v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; size_t v___x_256_; size_t v___x_257_; 
v___x_255_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0));
v___x_256_ = ((size_t)1ULL);
v___x_257_ = lean_usize_add(v_i_248_, v___x_256_);
v_i_248_ = v___x_257_;
v_b_249_ = v___x_255_;
goto _start;
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v_k_245_);
lean_inc(v_a_252_);
v___x_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_259_, 0, v_a_252_);
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_251_);
return v___x_261_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_245_ = stack[0].m_obj;
lean_object* v_as_246_ = stack[1].m_obj;
size_t v_sz_247_ = stack[2].m_num;
size_t v_i_248_ = stack[3].m_num;
lean_object* v_b_249_ = stack[4].m_obj;
lean_object* v_res_262_;
v_res_262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(v_k_245_, v_as_246_, v_sz_247_, v_i_248_, v_b_249_);
stack->m_obj
 = v_res_262_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___boxed(lean_object* v_k_263_, lean_object* v_as_264_, lean_object* v_sz_265_, lean_object* v_i_266_, lean_object* v_b_267_){
_start:
{
size_t v_sz_boxed_268_; size_t v_i_boxed_269_; lean_object* v_res_270_; 
v_sz_boxed_268_ = lean_unbox_usize(v_sz_265_);
lean_dec(v_sz_265_);
v_i_boxed_269_ = lean_unbox_usize(v_i_266_);
lean_dec(v_i_266_);
v_res_270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(v_k_263_, v_as_264_, v_sz_boxed_268_, v_i_boxed_269_, v_b_267_);
lean_dec_ref(v_b_267_);
lean_dec_ref(v_as_264_);
return v_res_270_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__0));
v___x_273_ = l_Lean_stringToMessageData(v___x_272_);
return v___x_273_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__2));
v___x_276_ = l_Lean_stringToMessageData(v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12(void){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Array_mkArray0___redArg();
return v___x_290_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__16));
v___x_297_ = l_Lean_stringToMessageData(v___x_296_);
return v___x_297_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(lean_object* v_k_298_, size_t v_sz_299_, size_t v_i_300_, lean_object* v_bs_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
uint8_t v___x_305_; 
v___x_305_ = lean_usize_dec_lt(v_i_300_, v_sz_299_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; 
lean_dec(v_k_298_);
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v_bs_301_);
return v___x_306_;
}
else
{
lean_object* v_v_307_; lean_object* v___x_308_; lean_object* v_bs_x27_309_; lean_object* v_a_311_; lean_object* v___y_317_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___x_336_; uint8_t v___x_337_; 
v_v_307_ = lean_array_uget(v_bs_301_, v_i_300_);
v___x_308_ = lean_unsigned_to_nat(0u);
v_bs_x27_309_ = lean_array_uset(v_bs_301_, v_i_300_, v___x_308_);
v___x_336_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8));
lean_inc(v_v_307_);
v___x_337_ = l_Lean_Syntax_isOfKind(v_v_307_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; 
lean_dec(v_v_307_);
v___x_338_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
v___y_317_ = v___x_338_;
goto v___jp_316_;
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = l_Lean_Syntax_getArg(v_v_307_, v___x_339_);
lean_inc(v___x_340_);
v___x_341_ = l_Lean_Syntax_matchesNull(v___x_340_, v___x_339_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
lean_dec(v___x_340_);
lean_dec(v_v_307_);
v___x_342_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
v___y_317_ = v___x_342_;
goto v___jp_316_;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___x_360_; lean_object* v_pat_361_; lean_object* v___y_363_; lean_object* v___y_364_; uint8_t v___x_416_; 
v___x_343_ = lean_box(0);
v___x_344_ = l_Lean_Syntax_getArg(v___x_340_, v___x_308_);
lean_dec(v___x_340_);
v___x_345_ = lean_unsigned_to_nat(3u);
v___x_346_ = l_Lean_Syntax_getArg(v_v_307_, v___x_345_);
v___x_360_ = l_Lean_Syntax_getArgs(v___x_344_);
lean_dec(v___x_344_);
v_pat_361_ = lean_array_get_borrowed(v___x_343_, v___x_360_, v___x_308_);
v___x_416_ = l_Lean_Syntax_isQuot(v_pat_361_);
if (v___x_416_ == 0)
{
if (v___x_341_ == 0)
{
v___y_363_ = v___y_302_;
v___y_364_ = v___y_303_;
goto v___jp_362_;
}
else
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
if (lean_obj_tag(v___x_417_) == 0)
{
lean_dec_ref_known(v___x_417_, 1);
v___y_363_ = v___y_302_;
v___y_364_ = v___y_303_;
goto v___jp_362_;
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec_ref(v___x_360_);
lean_dec(v___x_346_);
lean_dec_ref(v_bs_x27_309_);
lean_dec(v_v_307_);
lean_dec(v_k_298_);
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
else
{
v___y_363_ = v___y_302_;
v___y_364_ = v___y_303_;
goto v___jp_362_;
}
v___jp_347_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_350_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9));
lean_inc_n(v___y_349_, 4);
v___x_351_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_351_, 0, v___y_349_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
v___x_352_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_353_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
v___x_354_ = l_Array_append___redArg(v___x_353_, v___y_348_);
lean_dec_ref(v___y_348_);
v___x_355_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_355_, 0, v___y_349_);
lean_ctor_set(v___x_355_, 1, v___x_352_);
lean_ctor_set(v___x_355_, 2, v___x_354_);
v___x_356_ = l_Lean_Syntax_node1(v___y_349_, v___x_352_, v___x_355_);
v___x_357_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13));
v___x_358_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_358_, 0, v___y_349_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = l_Lean_Syntax_node4(v___y_349_, v___x_336_, v___x_351_, v___x_356_, v___x_358_, v___x_346_);
v_a_311_ = v___x_359_;
goto v___jp_310_;
}
v___jp_362_:
{
lean_object* v_quoted_365_; lean_object* v_k_x27_366_; uint8_t v___x_367_; 
lean_inc(v_pat_361_);
v_quoted_365_ = l_Lean_Syntax_getQuotContent(v_pat_361_);
lean_inc(v_quoted_365_);
v_k_x27_366_ = l_Lean_Syntax_getKind(v_quoted_365_);
lean_inc(v_k_298_);
v___x_367_ = l_Lean_Elab_Command_checkRuleKind(v_k_x27_366_, v_k_298_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__15));
v___x_369_ = lean_name_eq(v_k_x27_366_, v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
lean_dec(v_quoted_365_);
lean_dec_ref(v___x_360_);
lean_dec(v___x_346_);
v___x_370_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17);
v___x_371_ = l_Lean_MessageData_ofName(v_k_x27_366_);
v___x_372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_370_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
v___x_373_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3);
v___x_374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_v_307_, v___x_374_, v___y_363_, v___y_364_);
lean_dec(v_v_307_);
v___y_317_ = v___x_375_;
goto v___jp_316_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; size_t v_sz_378_; size_t v___x_379_; lean_object* v___x_380_; lean_object* v_fst_381_; 
lean_dec(v_k_x27_366_);
v___x_376_ = l_Lean_Syntax_getArgs(v_quoted_365_);
lean_dec(v_quoted_365_);
v___x_377_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0));
v_sz_378_ = lean_array_size(v___x_376_);
v___x_379_ = ((size_t)0ULL);
lean_inc(v_k_298_);
v___x_380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(v_k_298_, v___x_376_, v_sz_378_, v___x_379_, v___x_377_);
lean_dec_ref(v___x_376_);
v_fst_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_fst_381_);
lean_dec_ref(v___x_380_);
if (lean_obj_tag(v_fst_381_) == 0)
{
lean_dec_ref(v___x_360_);
lean_dec(v___x_346_);
v___y_328_ = v___y_363_;
v___y_329_ = v___y_364_;
goto v___jp_327_;
}
else
{
lean_object* v_val_382_; 
v_val_382_ = lean_ctor_get(v_fst_381_, 0);
lean_inc(v_val_382_);
lean_dec_ref_known(v_fst_381_, 1);
if (lean_obj_tag(v_val_382_) == 0)
{
lean_dec_ref(v___x_360_);
lean_dec(v___x_346_);
v___y_328_ = v___y_363_;
v___y_329_ = v___y_364_;
goto v___jp_327_;
}
else
{
lean_object* v_val_383_; lean_object* v_pat_384_; lean_object* v_pats_385_; lean_object* v___x_386_; 
lean_dec(v_v_307_);
v_val_383_ = lean_ctor_get(v_val_382_, 0);
lean_inc(v_val_383_);
lean_dec_ref_known(v_val_382_, 1);
lean_inc(v_pat_361_);
v_pat_384_ = l_Lean_Syntax_setArg(v_pat_361_, v___x_339_, v_val_383_);
v_pats_385_ = lean_array_set(v___x_360_, v___x_308_, v_pat_384_);
v___x_386_ = l_Lean_Elab_Command_getRef___redArg(v___y_363_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
lean_dec_ref_known(v___x_386_, 1);
v___x_388_ = l_Lean_SourceInfo_fromRef(v_a_387_, v___x_367_);
lean_dec(v_a_387_);
v___x_389_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_363_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_quotContext_x3f_390_; 
lean_dec_ref_known(v___x_389_, 1);
v_quotContext_x3f_390_ = lean_ctor_get(v___y_363_, 5);
if (lean_obj_tag(v_quotContext_x3f_390_) == 0)
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_364_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_dec_ref_known(v___x_391_, 1);
v___y_348_ = v_pats_385_;
v___y_349_ = v___x_388_;
goto v___jp_347_;
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec(v___x_388_);
lean_dec_ref(v_pats_385_);
lean_dec(v___x_346_);
lean_dec_ref(v_bs_x27_309_);
lean_dec(v_k_298_);
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
else
{
v___y_348_ = v_pats_385_;
v___y_349_ = v___x_388_;
goto v___jp_347_;
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec(v___x_388_);
lean_dec_ref(v_pats_385_);
lean_dec(v___x_346_);
lean_dec_ref(v_bs_x27_309_);
lean_dec(v_k_298_);
v_a_400_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_389_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_389_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec_ref(v_pats_385_);
lean_dec(v___x_346_);
lean_dec_ref(v_bs_x27_309_);
lean_dec(v_k_298_);
v_a_408_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_386_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_386_);
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
}
}
else
{
lean_dec(v_k_x27_366_);
lean_dec(v_quoted_365_);
lean_dec_ref(v___x_360_);
lean_dec(v___x_346_);
v_a_311_ = v_v_307_;
goto v___jp_310_;
}
}
}
}
v___jp_310_:
{
size_t v___x_312_; size_t v___x_313_; lean_object* v___x_314_; 
v___x_312_ = ((size_t)1ULL);
v___x_313_ = lean_usize_add(v_i_300_, v___x_312_);
v___x_314_ = lean_array_uset(v_bs_x27_309_, v_i_300_, v_a_311_);
v_i_300_ = v___x_313_;
v_bs_301_ = v___x_314_;
goto _start;
}
v___jp_316_:
{
if (lean_obj_tag(v___y_317_) == 0)
{
lean_object* v_a_318_; 
v_a_318_ = lean_ctor_get(v___y_317_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v___y_317_, 1);
v_a_311_ = v_a_318_;
goto v___jp_310_;
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec_ref(v_bs_x27_309_);
lean_dec(v_k_298_);
v_a_319_ = lean_ctor_get(v___y_317_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___y_317_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___y_317_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___y_317_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
v___jp_327_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_330_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1);
lean_inc(v_k_298_);
v___x_331_ = l_Lean_MessageData_ofName(v_k_298_);
v___x_332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3);
v___x_334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_v_307_, v___x_334_, v___y_328_, v___y_329_);
lean_dec(v_v_307_);
v___y_317_ = v___x_335_;
goto v___jp_316_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_298_ = stack[0].m_obj;
size_t v_sz_299_ = stack[1].m_num;
size_t v_i_300_ = stack[2].m_num;
lean_object* v_bs_301_ = stack[3].m_obj;
lean_object* v___y_302_ = stack[4].m_obj;
lean_object* v___y_303_ = stack[5].m_obj;
lean_object* v_res_426_;
v_res_426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(v_k_298_, v_sz_299_, v_i_300_, v_bs_301_, v___y_302_, v___y_303_);
stack->m_obj
 = v_res_426_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___boxed(lean_object* v_k_427_, lean_object* v_sz_428_, lean_object* v_i_429_, lean_object* v_bs_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
size_t v_sz_boxed_434_; size_t v_i_boxed_435_; lean_object* v_res_436_; 
v_sz_boxed_434_ = lean_unbox_usize(v_sz_428_);
lean_dec(v_sz_428_);
v_i_boxed_435_ = lean_unbox_usize(v_i_429_);
lean_dec(v_i_429_);
v_res_436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(v_k_427_, v_sz_boxed_434_, v_i_boxed_435_, v_bs_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_436_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__4(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__3));
v___x_442_ = l_String_toRawSubstring_x27(v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__7));
v___x_448_ = l_String_toRawSubstring_x27(v___x_447_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__19(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__18));
v___x_461_ = l_String_toRawSubstring_x27(v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__26(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__25));
v___x_476_ = l_String_toRawSubstring_x27(v___x_475_);
return v___x_476_;
}
}
lean_object* l_Lean_Elab_Command_elabMacroRulesAux(lean_object* v_doc_x3f_503_, lean_object* v_attrs_x3f_504_, lean_object* v_attrKind_505_, lean_object* v_tk_506_, lean_object* v_k_507_, lean_object* v_alts_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
size_t v_sz_512_; size_t v___x_513_; lean_object* v___x_514_; 
v_sz_512_ = lean_array_size(v_alts_508_);
v___x_513_ = ((size_t)0ULL);
lean_inc(v_k_507_);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(v_k_507_, v_sz_512_, v___x_513_, v_alts_508_, v_a_509_, v_a_510_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_699_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_699_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_699_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_699_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v_a_636_; lean_object* v___x_645_; 
v___x_645_ = l_Lean_Elab_Command_getRef___redArg(v_a_509_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; uint8_t v___x_647_; lean_object* v___y_649_; lean_object* v___x_669_; lean_object* v___x_688_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref_known(v___x_645_, 1);
v___x_647_ = 0;
v___x_669_ = l_Lean_SourceInfo_fromRef(v_a_646_, v___x_647_);
lean_dec(v_a_646_);
v___x_688_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_509_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_quotContext_x3f_689_; 
lean_dec_ref_known(v___x_688_, 1);
v_quotContext_x3f_689_ = lean_ctor_get(v_a_509_, 5);
if (lean_obj_tag(v_quotContext_x3f_689_) == 0)
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v_a_510_);
lean_dec_ref(v___x_690_);
goto v___jp_670_;
}
else
{
goto v___jp_670_;
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec(v___x_669_);
lean_del_object(v___x_517_);
lean_dec(v_a_515_);
lean_dec(v_k_507_);
lean_dec(v_attrKind_505_);
lean_dec(v_doc_x3f_503_);
v_a_691_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_688_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_688_);
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
v___jp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_505_);
v___x_651_ = l_Lean_Elab_Command_getRef___redArg(v_a_509_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
v___x_653_ = l_Lean_SourceInfo_fromRef(v_a_652_, v___x_647_);
lean_dec(v_a_652_);
v___x_654_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_509_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_quotContext_x3f_655_; 
v_quotContext_x3f_655_ = lean_ctor_get(v_a_509_, 5);
if (lean_obj_tag(v_quotContext_x3f_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_657_; lean_object* v_a_658_; 
v_a_656_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_654_, 1);
v___x_657_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v_a_510_);
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref(v___x_657_);
v___y_632_ = v_a_656_;
v___y_633_ = v___y_649_;
v___y_634_ = v___x_650_;
v___y_635_ = v___x_653_;
v_a_636_ = v_a_658_;
goto v___jp_631_;
}
else
{
lean_object* v_a_659_; lean_object* v_val_660_; 
v_a_659_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_654_, 1);
v_val_660_ = lean_ctor_get(v_quotContext_x3f_655_, 0);
lean_inc(v_val_660_);
v___y_632_ = v_a_659_;
v___y_633_ = v___y_649_;
v___y_634_ = v___x_650_;
v___y_635_ = v___x_653_;
v_a_636_ = v_val_660_;
goto v___jp_631_;
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec(v___x_653_);
lean_dec(v___x_650_);
lean_dec_ref(v___y_649_);
lean_del_object(v___x_517_);
lean_dec(v_a_515_);
lean_dec(v_k_507_);
lean_dec(v_doc_x3f_503_);
v_a_661_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_654_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_654_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
else
{
lean_dec(v___x_650_);
lean_dec_ref(v___y_649_);
lean_del_object(v___x_517_);
lean_dec(v_a_515_);
lean_dec(v_k_507_);
lean_dec(v_doc_x3f_503_);
return v___x_651_;
}
}
v___jp_670_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_671_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__35));
v___x_672_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__37));
v___x_673_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__38));
lean_inc_n(v___x_669_, 2);
v___x_674_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_669_);
lean_ctor_set(v___x_674_, 1, v___x_672_);
lean_inc(v_k_507_);
v___x_675_ = l_Lean_mkIdent(v_k_507_);
v___x_676_ = l_Lean_Syntax_node2(v___x_669_, v___x_673_, v___x_674_, v___x_675_);
lean_inc(v_attrKind_505_);
v___x_677_ = l_Lean_Syntax_node2(v___x_669_, v___x_671_, v_attrKind_505_, v___x_676_);
if (lean_obj_tag(v_attrs_x3f_504_) == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_678_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = lean_mk_empty_array_with_capacity(v___x_679_);
v___x_681_ = lean_array_push(v___x_680_, v___x_677_);
v___x_682_ = l_Lean_Syntax_SepArray_ofElems(v___x_678_, v___x_681_);
lean_dec_ref(v___x_681_);
v___y_649_ = v___x_682_;
goto v___jp_648_;
}
else
{
lean_object* v_val_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_val_683_ = lean_ctor_get(v_attrs_x3f_504_, 0);
v___x_684_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_685_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_683_);
v___x_686_ = lean_array_push(v___x_685_, v___x_677_);
v___x_687_ = l_Lean_Syntax_SepArray_ofElems(v___x_684_, v___x_686_);
lean_dec_ref(v___x_686_);
v___y_649_ = v___x_687_;
goto v___jp_648_;
}
}
}
else
{
lean_del_object(v___x_517_);
lean_dec(v_a_515_);
lean_dec(v_k_507_);
lean_dec(v_attrKind_505_);
lean_dec(v_doc_x3f_503_);
return v___x_645_;
}
v___jp_519_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
lean_inc_ref_n(v___y_521_, 3);
v___x_531_ = l_Array_append___redArg(v___y_521_, v___y_530_);
lean_dec_ref(v___y_530_);
lean_inc_n(v___y_527_, 8);
lean_inc_n(v___y_528_, 29);
v___x_532_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_532_, 0, v___y_528_);
lean_ctor_set(v___x_532_, 1, v___y_527_);
lean_ctor_set(v___x_532_, 2, v___x_531_);
v___x_533_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5));
v___x_534_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6));
v___x_535_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
lean_inc_ref_n(v___y_524_, 9);
v___x_536_ = l_Lean_Name_mkStr4(v___y_524_, v___x_533_, v___x_534_, v___x_535_);
v___x_537_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
v___x_538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_538_, 0, v___y_528_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = l_Array_append___redArg(v___y_521_, v___y_523_);
lean_dec_ref(v___y_523_);
v___x_540_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_540_, 0, v___y_528_);
lean_ctor_set(v___x_540_, 1, v___y_527_);
lean_ctor_set(v___x_540_, 2, v___x_539_);
v___x_541_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
v___x_542_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_542_, 0, v___y_528_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = l_Lean_Syntax_node3(v___y_528_, v___x_536_, v___x_538_, v___x_540_, v___x_542_);
v___x_544_ = l_Lean_Syntax_node1(v___y_528_, v___y_527_, v___x_543_);
lean_inc_ref(v___y_525_);
v___x_545_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_545_, 0, v___y_528_);
lean_ctor_set(v___x_545_, 1, v___y_525_);
v___x_546_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__4, &l_Lean_Elab_Command_elabMacroRulesAux___closed__4_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__4);
v___x_547_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__5));
lean_inc_n(v___y_520_, 3);
lean_inc_n(v___y_522_, 3);
v___x_548_ = l_Lean_addMacroScope(v___y_522_, v___x_547_, v___y_520_);
v___x_549_ = lean_box(0);
v___x_550_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_550_, 0, v___y_528_);
lean_ctor_set(v___x_550_, 1, v___x_546_);
lean_ctor_set(v___x_550_, 2, v___x_548_);
lean_ctor_set(v___x_550_, 3, v___x_549_);
v___x_551_ = 1;
v___x_552_ = l_Lean_mkIdentFrom(v_tk_506_, v_k_507_, v___x_551_);
v___x_553_ = l_Lean_Syntax_node2(v___y_528_, v___y_527_, v___x_550_, v___x_552_);
v___x_554_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__6));
v___x_555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_555_, 0, v___y_528_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__7));
v___x_557_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__8, &l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8);
v___x_558_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__9));
v___x_559_ = l_Lean_addMacroScope(v___y_522_, v___x_558_, v___y_520_);
v___x_560_ = l_Lean_Name_mkStr2(v___y_524_, v___x_556_);
lean_inc(v___x_560_);
v___x_561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set(v___x_561_, 1, v___x_549_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_560_);
v___x_563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v___x_549_);
v___x_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_561_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_565_, 0, v___y_528_);
lean_ctor_set(v___x_565_, 1, v___x_557_);
lean_ctor_set(v___x_565_, 2, v___x_559_);
lean_ctor_set(v___x_565_, 3, v___x_564_);
v___x_566_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
v___x_567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_567_, 0, v___y_528_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__11));
v___x_569_ = l_Lean_Name_mkStr4(v___y_524_, v___x_533_, v___x_534_, v___x_568_);
v___x_570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_570_, 0, v___y_528_);
lean_ctor_set(v___x_570_, 1, v___x_568_);
v___x_571_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__12));
v___x_572_ = l_Lean_Name_mkStr4(v___y_524_, v___x_533_, v___x_534_, v___x_571_);
v___x_573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7));
v___x_574_ = l_Lean_Name_mkStr4(v___y_524_, v___x_533_, v___x_534_, v___x_573_);
v___x_575_ = l_Array_append___redArg(v___y_521_, v_a_515_);
lean_dec(v_a_515_);
v___x_576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9));
v___x_577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_577_, 0, v___y_528_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__13));
v___x_579_ = l_Lean_Name_mkStr4(v___y_524_, v___x_533_, v___x_534_, v___x_578_);
v___x_580_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__14));
v___x_581_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_581_, 0, v___y_528_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = l_Lean_Syntax_node1(v___y_528_, v___x_579_, v___x_581_);
v___x_583_ = l_Lean_Syntax_node1(v___y_528_, v___y_527_, v___x_582_);
v___x_584_ = l_Lean_Syntax_node1(v___y_528_, v___y_527_, v___x_583_);
v___x_585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13));
v___x_586_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_586_, 0, v___y_528_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__15));
v___x_588_ = l_Lean_Name_mkStr4(v___y_524_, v___x_533_, v___x_534_, v___x_587_);
v___x_589_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__16));
v___x_590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_590_, 0, v___y_528_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__17));
v___x_592_ = l_Lean_Name_mkStr4(v___y_524_, v___x_533_, v___x_534_, v___x_591_);
v___x_593_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__19, &l_Lean_Elab_Command_elabMacroRulesAux___closed__19_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__19);
v___x_594_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__20));
v___x_595_ = l_Lean_addMacroScope(v___y_522_, v___x_594_, v___y_520_);
v___x_596_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__24));
v___x_597_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_597_, 0, v___y_528_);
lean_ctor_set(v___x_597_, 1, v___x_593_);
lean_ctor_set(v___x_597_, 2, v___x_595_);
lean_ctor_set(v___x_597_, 3, v___x_596_);
v___x_598_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__26, &l_Lean_Elab_Command_elabMacroRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__26);
v___x_599_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__27));
v___x_600_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__28));
v___x_601_ = l_Lean_Name_mkStr4(v___y_524_, v___x_556_, v___x_599_, v___x_600_);
lean_inc_n(v___x_601_, 2);
v___x_602_ = l_Lean_addMacroScope(v___y_522_, v___x_601_, v___y_520_);
v___x_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_549_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_601_);
v___x_605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___x_549_);
v___x_606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_603_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_607_, 0, v___y_528_);
lean_ctor_set(v___x_607_, 1, v___x_598_);
lean_ctor_set(v___x_607_, 2, v___x_602_);
lean_ctor_set(v___x_607_, 3, v___x_606_);
v___x_608_ = l_Lean_Syntax_node1(v___y_528_, v___y_527_, v___x_607_);
v___x_609_ = l_Lean_Syntax_node2(v___y_528_, v___x_592_, v___x_597_, v___x_608_);
v___x_610_ = l_Lean_Syntax_node2(v___y_528_, v___x_588_, v___x_590_, v___x_609_);
v___x_611_ = l_Lean_Syntax_node4(v___y_528_, v___x_574_, v___x_577_, v___x_584_, v___x_586_, v___x_610_);
v___x_612_ = lean_array_push(v___x_575_, v___x_611_);
v___x_613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_613_, 0, v___y_528_);
lean_ctor_set(v___x_613_, 1, v___y_527_);
lean_ctor_set(v___x_613_, 2, v___x_612_);
v___x_614_ = l_Lean_Syntax_node1(v___y_528_, v___x_572_, v___x_613_);
v___x_615_ = l_Lean_Syntax_node2(v___y_528_, v___x_569_, v___x_570_, v___x_614_);
v___x_616_ = lean_unsigned_to_nat(9u);
v___x_617_ = lean_mk_empty_array_with_capacity(v___x_616_);
v___x_618_ = lean_array_push(v___x_617_, v___x_532_);
v___x_619_ = lean_array_push(v___x_618_, v___x_544_);
v___x_620_ = lean_array_push(v___x_619_, v___y_526_);
v___x_621_ = lean_array_push(v___x_620_, v___x_545_);
v___x_622_ = lean_array_push(v___x_621_, v___x_553_);
v___x_623_ = lean_array_push(v___x_622_, v___x_555_);
v___x_624_ = lean_array_push(v___x_623_, v___x_565_);
v___x_625_ = lean_array_push(v___x_624_, v___x_567_);
v___x_626_ = lean_array_push(v___x_625_, v___x_615_);
lean_inc(v___y_529_);
v___x_627_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_627_, 0, v___y_528_);
lean_ctor_set(v___x_627_, 1, v___y_529_);
lean_ctor_set(v___x_627_, 2, v___x_626_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_627_);
v___x_629_ = v___x_517_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
v___jp_631_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4));
v___x_638_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__31));
v___x_639_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__32));
v___x_640_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_641_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
if (lean_obj_tag(v_doc_x3f_503_) == 1)
{
lean_object* v_val_642_; lean_object* v___x_643_; 
v_val_642_ = lean_ctor_get(v_doc_x3f_503_, 0);
lean_inc(v_val_642_);
lean_dec_ref_known(v_doc_x3f_503_, 1);
v___x_643_ = l_Array_mkArray1___redArg(v_val_642_);
v___y_520_ = v___y_632_;
v___y_521_ = v___x_641_;
v___y_522_ = v_a_636_;
v___y_523_ = v___y_633_;
v___y_524_ = v___x_637_;
v___y_525_ = v___x_638_;
v___y_526_ = v___y_634_;
v___y_527_ = v___x_640_;
v___y_528_ = v___y_635_;
v___y_529_ = v___x_639_;
v___y_530_ = v___x_643_;
goto v___jp_519_;
}
else
{
lean_object* v___x_644_; 
lean_dec(v_doc_x3f_503_);
v___x_644_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__33));
v___y_520_ = v___y_632_;
v___y_521_ = v___x_641_;
v___y_522_ = v_a_636_;
v___y_523_ = v___y_633_;
v___y_524_ = v___x_637_;
v___y_525_ = v___x_638_;
v___y_526_ = v___y_634_;
v___y_527_ = v___x_640_;
v___y_528_ = v___y_635_;
v___y_529_ = v___x_639_;
v___y_530_ = v___x_644_;
goto v___jp_519_;
}
}
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec(v_k_507_);
lean_dec(v_attrKind_505_);
lean_dec(v_doc_x3f_503_);
v_a_700_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_514_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_514_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_elabMacroRulesAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_doc_x3f_503_ = stack[0].m_obj;
lean_object* v_attrs_x3f_504_ = stack[1].m_obj;
lean_object* v_attrKind_505_ = stack[2].m_obj;
lean_object* v_tk_506_ = stack[3].m_obj;
lean_object* v_k_507_ = stack[4].m_obj;
lean_object* v_alts_508_ = stack[5].m_obj;
lean_object* v_a_509_ = stack[6].m_obj;
lean_object* v_a_510_ = stack[7].m_obj;
lean_object* v_res_708_;
v_res_708_ = l_Lean_Elab_Command_elabMacroRulesAux(v_doc_x3f_503_, v_attrs_x3f_504_, v_attrKind_505_, v_tk_506_, v_k_507_, v_alts_508_, v_a_509_, v_a_510_);
stack->m_obj
 = v_res_708_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux___boxed(lean_object* v_doc_x3f_709_, lean_object* v_attrs_x3f_710_, lean_object* v_attrKind_711_, lean_object* v_tk_712_, lean_object* v_k_713_, lean_object* v_alts_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_Elab_Command_elabMacroRulesAux(v_doc_x3f_709_, v_attrs_x3f_710_, v_attrKind_711_, v_tk_712_, v_k_713_, v_alts_714_, v_a_715_, v_a_716_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_tk_712_);
lean_dec(v_attrs_x3f_710_);
return v_res_718_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(lean_object* v_00_u03b1_719_, lean_object* v_ref_720_, lean_object* v_msg_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_ref_720_, v_msg_721_, v___y_722_, v___y_723_);
return v___x_725_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_720_ = stack[1].m_obj;
lean_object* v_msg_721_ = stack[2].m_obj;
lean_object* v___y_722_ = stack[3].m_obj;
lean_object* v___y_723_ = stack[4].m_obj;
lean_object* v_res_726_;
v_res_726_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(lean_box(0), v_ref_720_, v_msg_721_, v___y_722_, v___y_723_);
stack->m_obj
 = v_res_726_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___boxed(lean_object* v_00_u03b1_727_, lean_object* v_ref_728_, lean_object* v_msg_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(v_00_u03b1_727_, v_ref_728_, v_msg_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v_ref_728_);
return v_res_733_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3(lean_object* v_msgData_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msgData_734_, v___y_736_);
return v___x_738_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_734_ = stack[0].m_obj;
lean_object* v___y_735_ = stack[1].m_obj;
lean_object* v___y_736_ = stack[2].m_obj;
lean_object* v_res_739_;
v_res_739_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3(v_msgData_734_, v___y_735_, v___y_736_);
stack->m_obj
 = v_res_739_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3(v_msgData_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
return v_res_744_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(lean_object* v_00_u03b1_745_, lean_object* v_msg_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_746_, v___y_747_, v___y_748_);
return v___x_750_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_746_ = stack[1].m_obj;
lean_object* v___y_747_ = stack[2].m_obj;
lean_object* v___y_748_ = stack[3].m_obj;
lean_object* v_res_751_;
v_res_751_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(lean_box(0), v_msg_746_, v___y_747_, v___y_748_);
stack->m_obj
 = v_res_751_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___boxed(lean_object* v_00_u03b1_752_, lean_object* v_msg_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(v_00_u03b1_752_, v_msg_753_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
return v_res_757_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4(lean_object* v_msgData_758_, lean_object* v_macroStack_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_msgData_758_, v_macroStack_759_, v___y_761_);
return v___x_763_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_758_ = stack[0].m_obj;
lean_object* v_macroStack_759_ = stack[1].m_obj;
lean_object* v___y_760_ = stack[2].m_obj;
lean_object* v___y_761_ = stack[3].m_obj;
lean_object* v_res_764_;
v_res_764_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4(v_msgData_758_, v_macroStack_759_, v___y_760_, v___y_761_);
stack->m_obj
 = v_res_764_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___boxed(lean_object* v_msgData_765_, lean_object* v_macroStack_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4(v_msgData_765_, v_macroStack_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
return v_res_770_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(lean_object* v___y_771_, uint8_t v_isExporting_772_, lean_object* v_a_x3f_773_){
_start:
{
lean_object* v___x_775_; lean_object* v_env_776_; lean_object* v_messages_777_; lean_object* v_scopes_778_; lean_object* v_usedQuotCtxts_779_; lean_object* v_nextMacroScope_780_; lean_object* v_maxRecDepth_781_; lean_object* v_ngen_782_; lean_object* v_auxDeclNGen_783_; lean_object* v_infoState_784_; lean_object* v_traceState_785_; lean_object* v_snapshotTasks_786_; lean_object* v_prevLinterStates_787_; lean_object* v_codeQualityEntryTasks_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_799_; 
v___x_775_ = lean_st_ref_take(v___y_771_);
v_env_776_ = lean_ctor_get(v___x_775_, 0);
v_messages_777_ = lean_ctor_get(v___x_775_, 1);
v_scopes_778_ = lean_ctor_get(v___x_775_, 2);
v_usedQuotCtxts_779_ = lean_ctor_get(v___x_775_, 3);
v_nextMacroScope_780_ = lean_ctor_get(v___x_775_, 4);
v_maxRecDepth_781_ = lean_ctor_get(v___x_775_, 5);
v_ngen_782_ = lean_ctor_get(v___x_775_, 6);
v_auxDeclNGen_783_ = lean_ctor_get(v___x_775_, 7);
v_infoState_784_ = lean_ctor_get(v___x_775_, 8);
v_traceState_785_ = lean_ctor_get(v___x_775_, 9);
v_snapshotTasks_786_ = lean_ctor_get(v___x_775_, 10);
v_prevLinterStates_787_ = lean_ctor_get(v___x_775_, 11);
v_codeQualityEntryTasks_788_ = lean_ctor_get(v___x_775_, 12);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_799_ == 0)
{
v___x_790_ = v___x_775_;
v_isShared_791_ = v_isSharedCheck_799_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_codeQualityEntryTasks_788_);
lean_inc(v_prevLinterStates_787_);
lean_inc(v_snapshotTasks_786_);
lean_inc(v_traceState_785_);
lean_inc(v_infoState_784_);
lean_inc(v_auxDeclNGen_783_);
lean_inc(v_ngen_782_);
lean_inc(v_maxRecDepth_781_);
lean_inc(v_nextMacroScope_780_);
lean_inc(v_usedQuotCtxts_779_);
lean_inc(v_scopes_778_);
lean_inc(v_messages_777_);
lean_inc(v_env_776_);
lean_dec(v___x_775_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_799_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_792_ = lean_box(0);
v___x_793_ = l_Lean_Environment_setExporting(v_env_776_, v_isExporting_772_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_793_);
v___x_795_ = v___x_790_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_messages_777_);
lean_ctor_set(v_reuseFailAlloc_798_, 2, v_scopes_778_);
lean_ctor_set(v_reuseFailAlloc_798_, 3, v_usedQuotCtxts_779_);
lean_ctor_set(v_reuseFailAlloc_798_, 4, v_nextMacroScope_780_);
lean_ctor_set(v_reuseFailAlloc_798_, 5, v_maxRecDepth_781_);
lean_ctor_set(v_reuseFailAlloc_798_, 6, v_ngen_782_);
lean_ctor_set(v_reuseFailAlloc_798_, 7, v_auxDeclNGen_783_);
lean_ctor_set(v_reuseFailAlloc_798_, 8, v_infoState_784_);
lean_ctor_set(v_reuseFailAlloc_798_, 9, v_traceState_785_);
lean_ctor_set(v_reuseFailAlloc_798_, 10, v_snapshotTasks_786_);
lean_ctor_set(v_reuseFailAlloc_798_, 11, v_prevLinterStates_787_);
lean_ctor_set(v_reuseFailAlloc_798_, 12, v_codeQualityEntryTasks_788_);
v___x_795_ = v_reuseFailAlloc_798_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_st_ref_put(v___y_771_, v___x_795_);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_792_);
return v___x_797_;
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_771_ = stack[0].m_obj;
uint8_t v_isExporting_772_ = stack[1].m_num;
lean_object* v_a_x3f_773_ = stack[2].m_obj;
lean_object* v_res_800_;
v_res_800_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_771_, v_isExporting_772_, v_a_x3f_773_);
stack->m_obj
 = v_res_800_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0___boxed(lean_object* v___y_801_, lean_object* v_isExporting_802_, lean_object* v_a_x3f_803_, lean_object* v___y_804_){
_start:
{
uint8_t v_isExporting_boxed_805_; lean_object* v_res_806_; 
v_isExporting_boxed_805_ = lean_unbox(v_isExporting_802_);
v_res_806_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_801_, v_isExporting_boxed_805_, v_a_x3f_803_);
lean_dec(v_a_x3f_803_);
lean_dec(v___y_801_);
return v_res_806_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(lean_object* v_x_807_, uint8_t v_isExporting_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; lean_object* v_env_813_; lean_object* v___x_814_; uint8_t v_isModule_815_; 
v___x_812_ = lean_st_ref_get(v___y_810_);
v_env_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc_ref(v_env_813_);
lean_dec(v___x_812_);
v___x_814_ = l_Lean_Environment_header(v_env_813_);
v_isModule_815_ = lean_ctor_get_uint8(v___x_814_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_814_);
if (v_isModule_815_ == 0)
{
lean_object* v___x_816_; 
lean_dec_ref(v_env_813_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
v___x_816_ = lean_apply_3(v_x_807_, v___y_809_, v___y_810_, lean_box(0));
return v___x_816_;
}
else
{
uint8_t v_isExporting_817_; 
v_isExporting_817_ = lean_ctor_get_uint8(v_env_813_, sizeof(void*)*13);
lean_dec_ref(v_env_813_);
if (v_isExporting_808_ == 0)
{
if (v_isExporting_817_ == 0)
{
lean_object* v___x_871_; 
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
v___x_871_ = lean_apply_3(v_x_807_, v___y_809_, v___y_810_, lean_box(0));
return v___x_871_;
}
else
{
goto v___jp_818_;
}
}
else
{
if (v_isExporting_817_ == 0)
{
goto v___jp_818_;
}
else
{
lean_object* v___x_872_; 
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
v___x_872_ = lean_apply_3(v_x_807_, v___y_809_, v___y_810_, lean_box(0));
return v___x_872_;
}
}
v___jp_818_:
{
lean_object* v___x_819_; lean_object* v_env_820_; lean_object* v_messages_821_; lean_object* v_scopes_822_; lean_object* v_usedQuotCtxts_823_; lean_object* v_nextMacroScope_824_; lean_object* v_maxRecDepth_825_; lean_object* v_ngen_826_; lean_object* v_auxDeclNGen_827_; lean_object* v_infoState_828_; lean_object* v_traceState_829_; lean_object* v_snapshotTasks_830_; lean_object* v_prevLinterStates_831_; lean_object* v_codeQualityEntryTasks_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_870_; 
v___x_819_ = lean_st_ref_take(v___y_810_);
v_env_820_ = lean_ctor_get(v___x_819_, 0);
v_messages_821_ = lean_ctor_get(v___x_819_, 1);
v_scopes_822_ = lean_ctor_get(v___x_819_, 2);
v_usedQuotCtxts_823_ = lean_ctor_get(v___x_819_, 3);
v_nextMacroScope_824_ = lean_ctor_get(v___x_819_, 4);
v_maxRecDepth_825_ = lean_ctor_get(v___x_819_, 5);
v_ngen_826_ = lean_ctor_get(v___x_819_, 6);
v_auxDeclNGen_827_ = lean_ctor_get(v___x_819_, 7);
v_infoState_828_ = lean_ctor_get(v___x_819_, 8);
v_traceState_829_ = lean_ctor_get(v___x_819_, 9);
v_snapshotTasks_830_ = lean_ctor_get(v___x_819_, 10);
v_prevLinterStates_831_ = lean_ctor_get(v___x_819_, 11);
v_codeQualityEntryTasks_832_ = lean_ctor_get(v___x_819_, 12);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_870_ == 0)
{
v___x_834_ = v___x_819_;
v_isShared_835_ = v_isSharedCheck_870_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_codeQualityEntryTasks_832_);
lean_inc(v_prevLinterStates_831_);
lean_inc(v_snapshotTasks_830_);
lean_inc(v_traceState_829_);
lean_inc(v_infoState_828_);
lean_inc(v_auxDeclNGen_827_);
lean_inc(v_ngen_826_);
lean_inc(v_maxRecDepth_825_);
lean_inc(v_nextMacroScope_824_);
lean_inc(v_usedQuotCtxts_823_);
lean_inc(v_scopes_822_);
lean_inc(v_messages_821_);
lean_inc(v_env_820_);
lean_dec(v___x_819_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_870_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = l_Lean_Environment_setExporting(v_env_820_, v_isExporting_808_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_836_);
v___x_838_ = v___x_834_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_messages_821_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_scopes_822_);
lean_ctor_set(v_reuseFailAlloc_869_, 3, v_usedQuotCtxts_823_);
lean_ctor_set(v_reuseFailAlloc_869_, 4, v_nextMacroScope_824_);
lean_ctor_set(v_reuseFailAlloc_869_, 5, v_maxRecDepth_825_);
lean_ctor_set(v_reuseFailAlloc_869_, 6, v_ngen_826_);
lean_ctor_set(v_reuseFailAlloc_869_, 7, v_auxDeclNGen_827_);
lean_ctor_set(v_reuseFailAlloc_869_, 8, v_infoState_828_);
lean_ctor_set(v_reuseFailAlloc_869_, 9, v_traceState_829_);
lean_ctor_set(v_reuseFailAlloc_869_, 10, v_snapshotTasks_830_);
lean_ctor_set(v_reuseFailAlloc_869_, 11, v_prevLinterStates_831_);
lean_ctor_set(v_reuseFailAlloc_869_, 12, v_codeQualityEntryTasks_832_);
v___x_838_ = v_reuseFailAlloc_869_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_839_; lean_object* v_r_840_; 
v___x_839_ = lean_st_ref_put(v___y_810_, v___x_838_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
v_r_840_ = lean_apply_3(v_x_807_, v___y_809_, v___y_810_, lean_box(0));
if (lean_obj_tag(v_r_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_857_; 
v_a_841_ = lean_ctor_get(v_r_840_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v_r_840_);
if (v_isSharedCheck_857_ == 0)
{
v___x_843_ = v_r_840_;
v_isShared_844_ = v_isSharedCheck_857_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v_r_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_857_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
lean_inc(v_a_841_);
if (v_isShared_844_ == 0)
{
lean_ctor_set_tag(v___x_843_, 1);
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_856_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
v___x_847_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_810_, v_isExporting_817_, v___x_846_);
lean_dec_ref(v___x_846_);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; 
v_unused_855_ = lean_ctor_get(v___x_847_, 0);
lean_dec(v_unused_855_);
v___x_849_ = v___x_847_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_dec(v___x_847_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v_a_841_);
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_841_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
v_a_858_ = lean_ctor_get(v_r_840_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v_r_840_, 1);
v___x_859_ = lean_box(0);
v___x_860_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_810_, v_isExporting_817_, v___x_859_);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; 
v_unused_868_ = lean_ctor_get(v___x_860_, 0);
lean_dec(v_unused_868_);
v___x_862_ = v___x_860_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_dec(v___x_860_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set_tag(v___x_862_, 1);
lean_ctor_set(v___x_862_, 0, v_a_858_);
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_858_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_807_ = stack[0].m_obj;
uint8_t v_isExporting_808_ = stack[1].m_num;
lean_object* v___y_809_ = stack[2].m_obj;
lean_object* v___y_810_ = stack[3].m_obj;
lean_object* v_res_873_;
v_res_873_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v_x_807_, v_isExporting_808_, v___y_809_, v___y_810_);
stack->m_obj
 = v_res_873_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___boxed(lean_object* v_x_874_, lean_object* v_isExporting_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
uint8_t v_isExporting_boxed_879_; lean_object* v_res_880_; 
v_isExporting_boxed_879_ = lean_unbox(v_isExporting_875_);
v_res_880_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v_x_874_, v_isExporting_boxed_879_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
return v_res_880_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0(lean_object* v_00_u03b1_881_, lean_object* v_x_882_, uint8_t v_isExporting_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v_x_882_, v_isExporting_883_, v___y_884_, v___y_885_);
return v___x_887_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_882_ = stack[1].m_obj;
uint8_t v_isExporting_883_ = stack[2].m_num;
lean_object* v___y_884_ = stack[3].m_obj;
lean_object* v___y_885_ = stack[4].m_obj;
lean_object* v_res_888_;
v_res_888_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0(lean_box(0), v_x_882_, v_isExporting_883_, v___y_884_, v___y_885_);
stack->m_obj
 = v_res_888_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___boxed(lean_object* v_00_u03b1_889_, lean_object* v_x_890_, lean_object* v_isExporting_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
uint8_t v_isExporting_boxed_895_; lean_object* v_res_896_; 
v_isExporting_boxed_895_ = lean_unbox(v_isExporting_891_);
v_res_896_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0(v_00_u03b1_889_, v_x_890_, v_isExporting_boxed_895_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
return v_res_896_;
}
}
lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0(lean_object* v___x_897_, lean_object* v___x_898_, lean_object* v_doc_x3f_899_, lean_object* v_attrs_x3f_900_, lean_object* v_attrKind_901_, lean_object* v_tk_902_, lean_object* v_alts_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_Elab_Command_getRef___redArg(v___y_904_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v_fileName_909_; lean_object* v_fileMap_910_; lean_object* v_currRecDepth_911_; lean_object* v_cmdPos_912_; lean_object* v_macroStack_913_; lean_object* v_quotContext_x3f_914_; lean_object* v_currMacroScope_915_; lean_object* v_snap_x3f_916_; lean_object* v_cancelTk_x3f_917_; uint8_t v_suppressElabErrors_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_937_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v___x_907_, 1);
v_fileName_909_ = lean_ctor_get(v___y_904_, 0);
v_fileMap_910_ = lean_ctor_get(v___y_904_, 1);
v_currRecDepth_911_ = lean_ctor_get(v___y_904_, 2);
v_cmdPos_912_ = lean_ctor_get(v___y_904_, 3);
v_macroStack_913_ = lean_ctor_get(v___y_904_, 4);
v_quotContext_x3f_914_ = lean_ctor_get(v___y_904_, 5);
v_currMacroScope_915_ = lean_ctor_get(v___y_904_, 6);
v_snap_x3f_916_ = lean_ctor_get(v___y_904_, 8);
v_cancelTk_x3f_917_ = lean_ctor_get(v___y_904_, 9);
v_suppressElabErrors_918_ = lean_ctor_get_uint8(v___y_904_, sizeof(void*)*10);
v_isSharedCheck_937_ = !lean_is_exclusive(v___y_904_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v___y_904_, 7);
lean_dec(v_unused_938_);
v___x_920_ = v___y_904_;
v_isShared_921_ = v_isSharedCheck_937_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_cancelTk_x3f_917_);
lean_inc(v_snap_x3f_916_);
lean_inc(v_currMacroScope_915_);
lean_inc(v_quotContext_x3f_914_);
lean_inc(v_macroStack_913_);
lean_inc(v_cmdPos_912_);
lean_inc(v_currRecDepth_911_);
lean_inc(v_fileMap_910_);
lean_inc(v_fileName_909_);
lean_dec(v___y_904_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_937_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v_ref_922_; lean_object* v___x_924_; 
v_ref_922_ = l_Lean_replaceRef(v___x_897_, v_a_908_);
lean_dec(v_a_908_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 7, v_ref_922_);
v___x_924_ = v___x_920_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_fileName_909_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_fileMap_910_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v_currRecDepth_911_);
lean_ctor_set(v_reuseFailAlloc_936_, 3, v_cmdPos_912_);
lean_ctor_set(v_reuseFailAlloc_936_, 4, v_macroStack_913_);
lean_ctor_set(v_reuseFailAlloc_936_, 5, v_quotContext_x3f_914_);
lean_ctor_set(v_reuseFailAlloc_936_, 6, v_currMacroScope_915_);
lean_ctor_set(v_reuseFailAlloc_936_, 7, v_ref_922_);
lean_ctor_set(v_reuseFailAlloc_936_, 8, v_snap_x3f_916_);
lean_ctor_set(v_reuseFailAlloc_936_, 9, v_cancelTk_x3f_917_);
lean_ctor_set_uint8(v_reuseFailAlloc_936_, sizeof(void*)*10, v_suppressElabErrors_918_);
v___x_924_ = v_reuseFailAlloc_936_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_Elab_Command_resolveSyntaxKind(v___x_898_, v___x_924_, v___y_905_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_927_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
lean_dec_ref_known(v___x_925_, 1);
v___x_927_ = l_Lean_Elab_Command_elabMacroRulesAux(v_doc_x3f_899_, v_attrs_x3f_900_, v_attrKind_901_, v_tk_902_, v_a_926_, v_alts_903_, v___x_924_, v___y_905_);
lean_dec_ref(v___x_924_);
return v___x_927_;
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec_ref(v___x_924_);
lean_dec_ref(v_alts_903_);
lean_dec(v_attrKind_901_);
lean_dec(v_doc_x3f_899_);
v_a_928_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_925_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_925_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_904_);
lean_dec_ref(v_alts_903_);
lean_dec(v_attrKind_901_);
lean_dec(v_doc_x3f_899_);
lean_dec(v___x_898_);
return v___x_907_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_elabMacroRules___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_897_ = stack[0].m_obj;
lean_object* v___x_898_ = stack[1].m_obj;
lean_object* v_doc_x3f_899_ = stack[2].m_obj;
lean_object* v_attrs_x3f_900_ = stack[3].m_obj;
lean_object* v_attrKind_901_ = stack[4].m_obj;
lean_object* v_tk_902_ = stack[5].m_obj;
lean_object* v_alts_903_ = stack[6].m_obj;
lean_object* v___y_904_ = stack[7].m_obj;
lean_object* v___y_905_ = stack[8].m_obj;
lean_object* v_res_939_;
v_res_939_ = l_Lean_Elab_Command_elabMacroRules___lam__0(v___x_897_, v___x_898_, v_doc_x3f_899_, v_attrs_x3f_900_, v_attrKind_901_, v_tk_902_, v_alts_903_, v___y_904_, v___y_905_);
stack->m_obj
 = v_res_939_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0___boxed(lean_object* v___x_940_, lean_object* v___x_941_, lean_object* v_doc_x3f_942_, lean_object* v_attrs_x3f_943_, lean_object* v_attrKind_944_, lean_object* v_tk_945_, lean_object* v_alts_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Elab_Command_elabMacroRules___lam__0(v___x_940_, v___x_941_, v_doc_x3f_942_, v_attrs_x3f_943_, v_attrKind_944_, v_tk_945_, v_alts_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec(v_tk_945_);
lean_dec(v_attrs_x3f_943_);
lean_dec(v___x_940_);
return v_res_950_;
}
}
lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5(lean_object* v___x_954_, lean_object* v___x_955_, lean_object* v_attrKind_956_, lean_object* v___x_957_, lean_object* v___x_958_, lean_object* v_attrs_x3f_959_, lean_object* v___x_960_, lean_object* v___x_961_, lean_object* v___x_962_, lean_object* v_doc_x3f_963_, lean_object* v_kind_x3f_964_, lean_object* v_alts_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_Elab_Command_getRef___redArg(v___y_966_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_1047_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_1047_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_1047_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
uint8_t v___x_974_; lean_object* v___x_975_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___x_1036_; 
v___x_974_ = 0;
v___x_975_ = l_Lean_SourceInfo_fromRef(v_a_970_, v___x_974_);
lean_dec(v_a_970_);
v___x_1036_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_966_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_quotContext_x3f_1037_; 
lean_dec_ref_known(v___x_1036_, 1);
v_quotContext_x3f_1037_ = lean_ctor_get(v___y_966_, 5);
if (lean_obj_tag(v_quotContext_x3f_1037_) == 0)
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_967_);
lean_dec_ref(v___x_1038_);
goto v___jp_1030_;
}
else
{
goto v___jp_1030_;
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec(v___x_975_);
lean_del_object(v___x_972_);
lean_dec(v_kind_x3f_964_);
lean_dec(v_doc_x3f_963_);
lean_dec_ref(v___x_962_);
lean_dec_ref(v___x_961_);
lean_dec_ref(v___x_960_);
lean_dec_ref(v___x_957_);
lean_dec(v_attrKind_956_);
lean_dec(v___x_955_);
lean_dec(v___x_954_);
v_a_1039_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1036_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1036_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
v___jp_976_:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
lean_inc_ref_n(v___y_978_, 2);
v___x_983_ = l_Array_append___redArg(v___y_978_, v___y_982_);
lean_dec_ref(v___y_982_);
lean_inc_n(v___y_981_, 2);
lean_inc_n(v___x_975_, 3);
v___x_984_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_984_, 0, v___x_975_);
lean_ctor_set(v___x_984_, 1, v___y_981_);
lean_ctor_set(v___x_984_, 2, v___x_983_);
v___x_985_ = l_Array_append___redArg(v___y_978_, v_alts_965_);
v___x_986_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_986_, 0, v___x_975_);
lean_ctor_set(v___x_986_, 1, v___y_981_);
lean_ctor_set(v___x_986_, 2, v___x_985_);
v___x_987_ = l_Lean_Syntax_node1(v___x_975_, v___x_954_, v___x_986_);
v___x_988_ = l_Lean_Syntax_node6(v___x_975_, v___x_955_, v___y_979_, v___y_980_, v_attrKind_956_, v___y_977_, v___x_984_, v___x_987_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_988_);
v___x_990_ = v___x_972_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
v___jp_992_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
lean_inc_ref(v___y_993_);
v___x_997_ = l_Array_append___redArg(v___y_993_, v___y_996_);
lean_dec_ref(v___y_996_);
lean_inc(v___y_995_);
lean_inc_n(v___x_975_, 2);
v___x_998_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_998_, 0, v___x_975_);
lean_ctor_set(v___x_998_, 1, v___y_995_);
lean_ctor_set(v___x_998_, 2, v___x_997_);
v___x_999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_975_);
lean_ctor_set(v___x_999_, 1, v___x_957_);
if (lean_obj_tag(v_kind_x3f_964_) == 0)
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_mk_empty_array_with_capacity(v___x_958_);
v___y_977_ = v___x_999_;
v___y_978_ = v___y_993_;
v___y_979_ = v___y_994_;
v___y_980_ = v___x_998_;
v___y_981_ = v___y_995_;
v___y_982_ = v___x_1000_;
goto v___jp_976_;
}
else
{
lean_object* v_val_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_val_1001_ = lean_ctor_get(v_kind_x3f_964_, 0);
lean_inc(v_val_1001_);
lean_dec_ref_known(v_kind_x3f_964_, 1);
v___x_1002_ = l_Lean_mkIdent(v_val_1001_);
v___x_1003_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0));
lean_inc_n(v___x_975_, 4);
v___x_1004_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_975_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1));
v___x_1006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_975_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
v___x_1008_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_975_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2));
v___x_1010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_975_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = l_Array_mkArray5___redArg(v___x_1004_, v___x_1006_, v___x_1008_, v___x_1002_, v___x_1010_);
v___y_977_ = v___x_999_;
v___y_978_ = v___y_993_;
v___y_979_ = v___y_994_;
v___y_980_ = v___x_998_;
v___y_981_ = v___y_995_;
v___y_982_ = v___x_1011_;
goto v___jp_976_;
}
}
v___jp_1012_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_inc_ref(v___y_1013_);
v___x_1016_ = l_Array_append___redArg(v___y_1013_, v___y_1015_);
lean_dec_ref(v___y_1015_);
lean_inc(v___y_1014_);
lean_inc(v___x_975_);
v___x_1017_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1017_, 0, v___x_975_);
lean_ctor_set(v___x_1017_, 1, v___y_1014_);
lean_ctor_set(v___x_1017_, 2, v___x_1016_);
if (lean_obj_tag(v_attrs_x3f_959_) == 1)
{
lean_object* v_val_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_val_1018_ = lean_ctor_get(v_attrs_x3f_959_, 0);
v___x_1019_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
v___x_1020_ = l_Lean_Name_mkStr4(v___x_960_, v___x_961_, v___x_962_, v___x_1019_);
v___x_1021_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
lean_inc_n(v___x_975_, 4);
v___x_1022_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_975_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
lean_inc_ref(v___y_1013_);
v___x_1023_ = l_Array_append___redArg(v___y_1013_, v_val_1018_);
lean_inc(v___y_1014_);
v___x_1024_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1024_, 0, v___x_975_);
lean_ctor_set(v___x_1024_, 1, v___y_1014_);
lean_ctor_set(v___x_1024_, 2, v___x_1023_);
v___x_1025_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
v___x_1026_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_975_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = l_Lean_Syntax_node3(v___x_975_, v___x_1020_, v___x_1022_, v___x_1024_, v___x_1026_);
v___x_1028_ = l_Array_mkArray1___redArg(v___x_1027_);
v___y_993_ = v___y_1013_;
v___y_994_ = v___x_1017_;
v___y_995_ = v___y_1014_;
v___y_996_ = v___x_1028_;
goto v___jp_992_;
}
else
{
lean_object* v___x_1029_; 
lean_dec_ref(v___x_962_);
lean_dec_ref(v___x_961_);
lean_dec_ref(v___x_960_);
v___x_1029_ = lean_mk_empty_array_with_capacity(v___x_958_);
v___y_993_ = v___y_1013_;
v___y_994_ = v___x_1017_;
v___y_995_ = v___y_1014_;
v___y_996_ = v___x_1029_;
goto v___jp_992_;
}
}
v___jp_1030_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1032_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
if (lean_obj_tag(v_doc_x3f_963_) == 1)
{
lean_object* v_val_1033_; lean_object* v___x_1034_; 
v_val_1033_ = lean_ctor_get(v_doc_x3f_963_, 0);
lean_inc(v_val_1033_);
lean_dec_ref_known(v_doc_x3f_963_, 1);
v___x_1034_ = l_Array_mkArray1___redArg(v_val_1033_);
v___y_1013_ = v___x_1032_;
v___y_1014_ = v___x_1031_;
v___y_1015_ = v___x_1034_;
goto v___jp_1012_;
}
else
{
lean_object* v___x_1035_; 
lean_dec(v_doc_x3f_963_);
v___x_1035_ = lean_mk_empty_array_with_capacity(v___x_958_);
v___y_1013_ = v___x_1032_;
v___y_1014_ = v___x_1031_;
v___y_1015_ = v___x_1035_;
goto v___jp_1012_;
}
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec(v_kind_x3f_964_);
lean_dec(v_doc_x3f_963_);
lean_dec_ref(v___x_962_);
lean_dec_ref(v___x_961_);
lean_dec_ref(v___x_960_);
lean_dec_ref(v___x_957_);
lean_dec(v_attrKind_956_);
lean_dec(v___x_955_);
lean_dec(v___x_954_);
v_a_1048_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_969_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_969_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_elabMacroRules___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_954_ = stack[0].m_obj;
lean_object* v___x_955_ = stack[1].m_obj;
lean_object* v_attrKind_956_ = stack[2].m_obj;
lean_object* v___x_957_ = stack[3].m_obj;
lean_object* v___x_958_ = stack[4].m_obj;
lean_object* v_attrs_x3f_959_ = stack[5].m_obj;
lean_object* v___x_960_ = stack[6].m_obj;
lean_object* v___x_961_ = stack[7].m_obj;
lean_object* v___x_962_ = stack[8].m_obj;
lean_object* v_doc_x3f_963_ = stack[9].m_obj;
lean_object* v_kind_x3f_964_ = stack[10].m_obj;
lean_object* v_alts_965_ = stack[11].m_obj;
lean_object* v___y_966_ = stack[12].m_obj;
lean_object* v___y_967_ = stack[13].m_obj;
lean_object* v_res_1056_;
v_res_1056_ = l_Lean_Elab_Command_elabMacroRules___lam__5(v___x_954_, v___x_955_, v_attrKind_956_, v___x_957_, v___x_958_, v_attrs_x3f_959_, v___x_960_, v___x_961_, v___x_962_, v_doc_x3f_963_, v_kind_x3f_964_, v_alts_965_, v___y_966_, v___y_967_);
stack->m_obj
 = v_res_1056_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5___boxed(lean_object* v___x_1057_, lean_object* v___x_1058_, lean_object* v_attrKind_1059_, lean_object* v___x_1060_, lean_object* v___x_1061_, lean_object* v_attrs_x3f_1062_, lean_object* v___x_1063_, lean_object* v___x_1064_, lean_object* v___x_1065_, lean_object* v_doc_x3f_1066_, lean_object* v_kind_x3f_1067_, lean_object* v_alts_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_Elab_Command_elabMacroRules___lam__5(v___x_1057_, v___x_1058_, v_attrKind_1059_, v___x_1060_, v___x_1061_, v_attrs_x3f_1062_, v___x_1063_, v___x_1064_, v___x_1065_, v_doc_x3f_1066_, v_kind_x3f_1067_, v_alts_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec_ref(v_alts_1068_);
lean_dec(v_attrs_x3f_1062_);
lean_dec(v___x_1061_);
return v_res_1072_;
}
}
lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1(lean_object* v_stx_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___y_1130_; lean_object* v___y_1131_; uint8_t v___y_1132_; uint8_t v___y_1133_; lean_object* v___y_1134_; uint8_t v___y_1135_; lean_object* v___y_1139_; lean_object* v___y_1140_; uint8_t v___y_1141_; uint8_t v___y_1142_; lean_object* v___y_1143_; uint8_t v___y_1144_; uint8_t v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; uint8_t v___y_1152_; uint8_t v___y_1153_; lean_object* v___y_1157_; lean_object* v___y_1158_; uint8_t v___y_1159_; lean_object* v___y_1160_; uint8_t v___y_1161_; uint8_t v___y_1162_; lean_object* v___y_1166_; lean_object* v___y_1167_; uint8_t v___y_1168_; uint8_t v___y_1169_; lean_object* v___y_1170_; uint8_t v___y_1171_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; 
v___x_1174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4));
v___x_1175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5));
v___x_1176_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0));
v___x_1177_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1));
lean_inc(v_stx_1125_);
v___x_1178_ = l_Lean_Syntax_isOfKind(v_stx_1125_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1244_; 
lean_dec(v_stx_1125_);
v___x_1244_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1244_;
}
else
{
lean_object* v___x_1245_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v_a_1258_; lean_object* v___y_1266_; lean_object* v___y_1267_; uint8_t v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1298_; lean_object* v___y_1299_; uint8_t v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; uint8_t v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v_attrs_x3f_1383_; lean_object* v_doc_x3f_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v___x_1245_ = lean_unsigned_to_nat(0u);
v___x_1558_ = l_Lean_Syntax_getArg(v_stx_1125_, v___x_1245_);
v___x_1559_ = l_Lean_Syntax_isNone(v___x_1558_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; uint8_t v___x_1561_; 
v___x_1560_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1558_);
v___x_1561_ = l_Lean_Syntax_matchesNull(v___x_1558_, v___x_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; 
lean_dec(v___x_1558_);
lean_dec(v_stx_1125_);
v___x_1562_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1562_;
}
else
{
lean_object* v_doc_x3f_1563_; 
v_doc_x3f_1563_ = l_Lean_Syntax_getArg(v___x_1558_, v___x_1245_);
lean_dec(v___x_1558_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17));
lean_inc(v_doc_x3f_1563_);
v___x_1567_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1563_, v___x_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; 
lean_dec(v_doc_x3f_1563_);
lean_dec(v_stx_1125_);
v___x_1568_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1568_;
}
else
{
goto v___jp_1564_;
}
}
else
{
goto v___jp_1564_;
}
v___jp_1564_:
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1565_, 0, v_doc_x3f_1563_);
v_doc_x3f_1542_ = v___x_1565_;
v___y_1543_ = v___y_1126_;
v___y_1544_ = v___y_1127_;
goto v___jp_1541_;
}
}
}
else
{
lean_object* v___x_1569_; 
lean_dec(v___x_1558_);
v___x_1569_ = lean_box(0);
v_doc_x3f_1542_ = v___x_1569_;
v___y_1543_ = v___y_1126_;
v___y_1544_ = v___y_1127_;
goto v___jp_1541_;
}
v___jp_1246_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__31));
v___x_1260_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__32));
v___x_1261_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
if (lean_obj_tag(v___y_1257_) == 1)
{
lean_object* v_val_1262_; lean_object* v___x_1263_; 
v_val_1262_ = lean_ctor_get(v___y_1257_, 0);
lean_inc(v_val_1262_);
lean_dec_ref_known(v___y_1257_, 1);
v___x_1263_ = l_Array_mkArray1___redArg(v_val_1262_);
v___y_1180_ = v___y_1248_;
v___y_1181_ = v___y_1250_;
v___y_1182_ = v___y_1252_;
v___y_1183_ = v_a_1258_;
v___y_1184_ = v___y_1255_;
v___y_1185_ = v___y_1254_;
v___y_1186_ = v___x_1259_;
v___y_1187_ = v___y_1256_;
v___y_1188_ = v___x_1260_;
v___y_1189_ = v___x_1261_;
v___y_1190_ = v___y_1247_;
v___y_1191_ = v___y_1249_;
v___y_1192_ = v___y_1251_;
v___y_1193_ = v___y_1253_;
v___y_1194_ = v___x_1263_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1264_; 
lean_dec(v___y_1257_);
v___x_1264_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__33));
v___y_1180_ = v___y_1248_;
v___y_1181_ = v___y_1250_;
v___y_1182_ = v___y_1252_;
v___y_1183_ = v_a_1258_;
v___y_1184_ = v___y_1255_;
v___y_1185_ = v___y_1254_;
v___y_1186_ = v___x_1259_;
v___y_1187_ = v___y_1256_;
v___y_1188_ = v___x_1260_;
v___y_1189_ = v___x_1261_;
v___y_1190_ = v___y_1247_;
v___y_1191_ = v___y_1249_;
v___y_1192_ = v___y_1251_;
v___y_1193_ = v___y_1253_;
v___y_1194_ = v___x_1264_;
goto v___jp_1179_;
}
}
v___jp_1265_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = l_Lean_Parser_Command_visibility_ofAttrKind(v___y_1276_);
v___x_1280_ = l_Lean_Elab_Command_getRef___redArg(v___y_1273_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v___x_1282_ = l_Lean_SourceInfo_fromRef(v_a_1281_, v___y_1268_);
lean_dec(v_a_1281_);
v___x_1283_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1273_);
lean_dec_ref(v___y_1273_);
if (lean_obj_tag(v___x_1283_) == 0)
{
if (lean_obj_tag(v___y_1266_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1285_; lean_object* v_a_1286_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 1);
v___x_1285_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_1267_);
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref(v___x_1285_);
v___y_1247_ = v___y_1271_;
v___y_1248_ = v___x_1279_;
v___y_1249_ = v___y_1272_;
v___y_1250_ = v___y_1278_;
v___y_1251_ = v___y_1274_;
v___y_1252_ = v___y_1269_;
v___y_1253_ = v___y_1275_;
v___y_1254_ = v_a_1284_;
v___y_1255_ = v___x_1282_;
v___y_1256_ = v___y_1270_;
v___y_1257_ = v___y_1277_;
v_a_1258_ = v_a_1286_;
goto v___jp_1246_;
}
else
{
lean_object* v_a_1287_; lean_object* v_val_1288_; 
v_a_1287_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1283_, 1);
v_val_1288_ = lean_ctor_get(v___y_1266_, 0);
lean_inc(v_val_1288_);
v___y_1247_ = v___y_1271_;
v___y_1248_ = v___x_1279_;
v___y_1249_ = v___y_1272_;
v___y_1250_ = v___y_1278_;
v___y_1251_ = v___y_1274_;
v___y_1252_ = v___y_1269_;
v___y_1253_ = v___y_1275_;
v___y_1254_ = v_a_1287_;
v___y_1255_ = v___x_1282_;
v___y_1256_ = v___y_1270_;
v___y_1257_ = v___y_1277_;
v_a_1258_ = v_val_1288_;
goto v___jp_1246_;
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec(v___x_1282_);
lean_dec(v___x_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec(v___y_1270_);
v_a_1289_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1283_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1283_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
else
{
lean_dec(v___x_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec(v___y_1270_);
return v___x_1280_;
}
}
v___jp_1297_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1313_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__34));
lean_inc_ref(v___y_1308_);
v___x_1314_ = l_Lean_Name_mkStr4(v___x_1174_, v___x_1175_, v___y_1308_, v___x_1313_);
v___x_1315_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__37));
v___x_1316_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__38));
lean_inc_n(v___y_1306_, 2);
v___x_1317_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___y_1306_);
lean_ctor_set(v___x_1317_, 1, v___x_1315_);
lean_inc(v___y_1303_);
v___x_1318_ = l_Lean_Syntax_node2(v___y_1306_, v___x_1316_, v___x_1317_, v___y_1303_);
lean_inc(v___y_1311_);
v___x_1319_ = l_Lean_Syntax_node2(v___y_1306_, v___x_1314_, v___y_1311_, v___x_1318_);
if (lean_obj_tag(v___y_1301_) == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1320_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_1321_ = lean_mk_empty_array_with_capacity(v___y_1310_);
v___x_1322_ = lean_array_push(v___x_1321_, v___x_1319_);
v___x_1323_ = l_Lean_Syntax_SepArray_ofElems(v___x_1320_, v___x_1322_);
lean_dec_ref(v___x_1322_);
v___y_1266_ = v___y_1298_;
v___y_1267_ = v___y_1299_;
v___y_1268_ = v___y_1300_;
v___y_1269_ = v___y_1302_;
v___y_1270_ = v___y_1303_;
v___y_1271_ = v___y_1304_;
v___y_1272_ = v___y_1305_;
v___y_1273_ = v___y_1307_;
v___y_1274_ = v___y_1308_;
v___y_1275_ = v___y_1309_;
v___y_1276_ = v___y_1311_;
v___y_1277_ = v___y_1312_;
v___y_1278_ = v___x_1323_;
goto v___jp_1265_;
}
else
{
lean_object* v_val_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v_val_1324_ = lean_ctor_get(v___y_1301_, 0);
lean_inc(v_val_1324_);
lean_dec_ref_known(v___y_1301_, 1);
v___x_1325_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__39));
v___x_1326_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_1324_);
lean_dec(v_val_1324_);
v___x_1327_ = lean_array_push(v___x_1326_, v___x_1319_);
v___x_1328_ = l_Lean_Syntax_SepArray_ofElems(v___x_1325_, v___x_1327_);
lean_dec_ref(v___x_1327_);
v___y_1266_ = v___y_1298_;
v___y_1267_ = v___y_1299_;
v___y_1268_ = v___y_1300_;
v___y_1269_ = v___y_1302_;
v___y_1270_ = v___y_1303_;
v___y_1271_ = v___y_1304_;
v___y_1272_ = v___y_1305_;
v___y_1273_ = v___y_1307_;
v___y_1274_ = v___y_1308_;
v___y_1275_ = v___y_1309_;
v___y_1276_ = v___y_1311_;
v___y_1277_ = v___y_1312_;
v___y_1278_ = v___x_1328_;
goto v___jp_1265_;
}
}
v___jp_1329_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1344_ = l_Lean_Syntax_getArg(v___y_1331_, v___y_1335_);
lean_dec(v___y_1331_);
v___x_1345_ = lean_mk_empty_array_with_capacity(v___y_1332_);
lean_inc(v___y_1340_);
v___x_1346_ = lean_array_push(v___x_1345_, v___y_1340_);
lean_inc(v___x_1344_);
v___x_1347_ = lean_array_push(v___x_1346_, v___x_1344_);
v___x_1348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1349_ = lean_box(2);
v___x_1350_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v___x_1348_);
lean_ctor_set(v___x_1350_, 2, v___x_1347_);
v___x_1351_ = l_Lean_Elab_Command_getRef___redArg(v___y_1338_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v_fileName_1353_; lean_object* v_fileMap_1354_; lean_object* v_currRecDepth_1355_; lean_object* v_cmdPos_1356_; lean_object* v_macroStack_1357_; lean_object* v_quotContext_x3f_1358_; lean_object* v_currMacroScope_1359_; lean_object* v_snap_x3f_1360_; lean_object* v_cancelTk_x3f_1361_; uint8_t v_suppressElabErrors_1362_; lean_object* v_ref_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1351_, 1);
v_fileName_1353_ = lean_ctor_get(v___y_1338_, 0);
v_fileMap_1354_ = lean_ctor_get(v___y_1338_, 1);
v_currRecDepth_1355_ = lean_ctor_get(v___y_1338_, 2);
v_cmdPos_1356_ = lean_ctor_get(v___y_1338_, 3);
v_macroStack_1357_ = lean_ctor_get(v___y_1338_, 4);
v_quotContext_x3f_1358_ = lean_ctor_get(v___y_1338_, 5);
v_currMacroScope_1359_ = lean_ctor_get(v___y_1338_, 6);
v_snap_x3f_1360_ = lean_ctor_get(v___y_1338_, 8);
v_cancelTk_x3f_1361_ = lean_ctor_get(v___y_1338_, 9);
v_suppressElabErrors_1362_ = lean_ctor_get_uint8(v___y_1338_, sizeof(void*)*10);
v_ref_1363_ = l_Lean_replaceRef(v___x_1350_, v_a_1352_);
lean_dec(v_a_1352_);
lean_dec_ref_known(v___x_1350_, 3);
lean_inc(v_cancelTk_x3f_1361_);
lean_inc(v_snap_x3f_1360_);
lean_inc(v_currMacroScope_1359_);
lean_inc(v_quotContext_x3f_1358_);
lean_inc(v_macroStack_1357_);
lean_inc(v_cmdPos_1356_);
lean_inc(v_currRecDepth_1355_);
lean_inc_ref(v_fileMap_1354_);
lean_inc_ref(v_fileName_1353_);
v___x_1364_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1364_, 0, v_fileName_1353_);
lean_ctor_set(v___x_1364_, 1, v_fileMap_1354_);
lean_ctor_set(v___x_1364_, 2, v_currRecDepth_1355_);
lean_ctor_set(v___x_1364_, 3, v_cmdPos_1356_);
lean_ctor_set(v___x_1364_, 4, v_macroStack_1357_);
lean_ctor_set(v___x_1364_, 5, v_quotContext_x3f_1358_);
lean_ctor_set(v___x_1364_, 6, v_currMacroScope_1359_);
lean_ctor_set(v___x_1364_, 7, v_ref_1363_);
lean_ctor_set(v___x_1364_, 8, v_snap_x3f_1360_);
lean_ctor_set(v___x_1364_, 9, v_cancelTk_x3f_1361_);
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*10, v_suppressElabErrors_1362_);
v___x_1365_ = l_Lean_Elab_Command_getRef___redArg(v___x_1364_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___x_1365_, 1);
v___x_1367_ = l_Lean_SourceInfo_fromRef(v_a_1366_, v___y_1333_);
lean_dec(v_a_1366_);
v___x_1368_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_1364_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_dec_ref_known(v___x_1368_, 1);
if (lean_obj_tag(v_quotContext_x3f_1358_) == 0)
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_1330_);
lean_dec_ref(v___x_1369_);
v___y_1298_ = v_quotContext_x3f_1358_;
v___y_1299_ = v___y_1330_;
v___y_1300_ = v___y_1333_;
v___y_1301_ = v___y_1334_;
v___y_1302_ = v___x_1348_;
v___y_1303_ = v___y_1336_;
v___y_1304_ = v___y_1337_;
v___y_1305_ = v___x_1344_;
v___y_1306_ = v___x_1367_;
v___y_1307_ = v___x_1364_;
v___y_1308_ = v___y_1339_;
v___y_1309_ = v___y_1340_;
v___y_1310_ = v___y_1341_;
v___y_1311_ = v___y_1343_;
v___y_1312_ = v___y_1342_;
goto v___jp_1297_;
}
else
{
v___y_1298_ = v_quotContext_x3f_1358_;
v___y_1299_ = v___y_1330_;
v___y_1300_ = v___y_1333_;
v___y_1301_ = v___y_1334_;
v___y_1302_ = v___x_1348_;
v___y_1303_ = v___y_1336_;
v___y_1304_ = v___y_1337_;
v___y_1305_ = v___x_1344_;
v___y_1306_ = v___x_1367_;
v___y_1307_ = v___x_1364_;
v___y_1308_ = v___y_1339_;
v___y_1309_ = v___y_1340_;
v___y_1310_ = v___y_1341_;
v___y_1311_ = v___y_1343_;
v___y_1312_ = v___y_1342_;
goto v___jp_1297_;
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v___x_1367_);
lean_dec_ref_known(v___x_1364_, 10);
lean_dec(v___x_1344_);
lean_dec(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v___y_1334_);
v_a_1370_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1368_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1368_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1364_, 10);
lean_dec(v___x_1344_);
lean_dec(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v___y_1334_);
return v___x_1365_;
}
}
else
{
lean_dec_ref_known(v___x_1350_, 3);
lean_dec(v___x_1344_);
lean_dec(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v___y_1334_);
return v___x_1351_;
}
}
v___jp_1378_:
{
lean_object* v___x_1384_; lean_object* v_attrKind_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1384_ = lean_unsigned_to_nat(2u);
v_attrKind_1385_ = l_Lean_Syntax_getArg(v_stx_1125_, v___x_1384_);
v___x_1386_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6));
v___x_1387_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9));
lean_inc(v_attrKind_1385_);
v___x_1388_ = l_Lean_Syntax_isOfKind(v_attrKind_1385_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; 
lean_dec(v_attrKind_1385_);
lean_dec(v_attrs_x3f_1383_);
lean_dec(v___y_1381_);
lean_dec(v_stx_1125_);
v___x_1389_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1389_;
}
else
{
lean_object* v___x_1390_; lean_object* v_tk_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1390_ = lean_unsigned_to_nat(3u);
v_tk_1391_ = l_Lean_Syntax_getArg(v_stx_1125_, v___x_1390_);
v___x_1392_ = lean_unsigned_to_nat(4u);
v___x_1393_ = l_Lean_Syntax_getArg(v_stx_1125_, v___x_1392_);
lean_inc(v___x_1393_);
v___x_1394_ = l_Lean_Syntax_matchesNull(v___x_1393_, v___x_1245_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1395_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_1393_);
v___x_1396_ = l_Lean_Syntax_matchesNull(v___x_1393_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_dec(v___x_1393_);
lean_dec(v_tk_1391_);
lean_dec(v_attrKind_1385_);
lean_dec(v_attrs_x3f_1383_);
lean_dec(v___y_1381_);
lean_dec(v_stx_1125_);
v___x_1397_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1397_;
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1398_ = l_Lean_Syntax_getArg(v_stx_1125_, v___x_1395_);
lean_dec(v_stx_1125_);
v___x_1399_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10));
lean_inc(v___x_1398_);
v___x_1400_ = l_Lean_Syntax_isOfKind(v___x_1398_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
lean_dec(v___x_1398_);
lean_dec(v___x_1393_);
lean_dec(v_tk_1391_);
lean_dec(v_attrKind_1385_);
lean_dec(v_attrs_x3f_1383_);
lean_dec(v___y_1381_);
v___x_1401_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1401_;
}
else
{
lean_object* v_kind_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v_kind_1402_ = l_Lean_Syntax_getArg(v___x_1393_, v___x_1390_);
lean_dec(v___x_1393_);
v___x_1403_ = l_Lean_Syntax_getArg(v___x_1398_, v___x_1245_);
lean_dec(v___x_1398_);
lean_inc(v___x_1403_);
v___x_1404_ = l_Lean_Syntax_matchesNull(v___x_1403_, v___y_1382_);
if (v___x_1404_ == 0)
{
lean_object* v_alts_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___f_1414_; 
v_alts_1405_ = l_Lean_Syntax_getArgs(v___x_1403_);
lean_dec(v___x_1403_);
v___x_1406_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1407_ = lean_box(2);
lean_inc_ref(v_alts_1405_);
v___x_1408_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
lean_ctor_set(v___x_1408_, 1, v___x_1406_);
lean_ctor_set(v___x_1408_, 2, v_alts_1405_);
v___x_1409_ = lean_mk_empty_array_with_capacity(v___x_1384_);
lean_inc(v_tk_1391_);
v___x_1410_ = lean_array_push(v___x_1409_, v_tk_1391_);
v___x_1411_ = lean_array_push(v___x_1410_, v___x_1408_);
v___x_1412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1407_);
lean_ctor_set(v___x_1412_, 1, v___x_1406_);
lean_ctor_set(v___x_1412_, 2, v___x_1411_);
v___x_1413_ = l_Lean_TSyntax_getId(v_kind_1402_);
lean_dec(v_kind_1402_);
lean_inc(v_attrKind_1385_);
v___f_1414_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1414_, 0, v___x_1412_);
lean_closure_set(v___f_1414_, 1, v___x_1413_);
lean_closure_set(v___f_1414_, 2, v___y_1381_);
lean_closure_set(v___f_1414_, 3, v_attrs_x3f_1383_);
lean_closure_set(v___f_1414_, 4, v_attrKind_1385_);
lean_closure_set(v___f_1414_, 5, v_tk_1391_);
lean_closure_set(v___f_1414_, 6, v_alts_1405_);
if (v___x_1388_ == 0)
{
lean_dec(v_attrKind_1385_);
v___y_1148_ = v___x_1404_;
v___y_1149_ = v___y_1380_;
v___y_1150_ = v___y_1379_;
v___y_1151_ = v___f_1414_;
v___y_1152_ = v___x_1400_;
v___y_1153_ = v___x_1388_;
goto v___jp_1147_;
}
else
{
lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1415_ = l_Lean_Syntax_getArg(v_attrKind_1385_, v___x_1245_);
lean_dec(v_attrKind_1385_);
lean_inc(v___x_1415_);
v___x_1416_ = l_Lean_Syntax_matchesNull(v___x_1415_, v___y_1382_);
if (v___x_1416_ == 0)
{
lean_dec(v___x_1415_);
v___y_1148_ = v___x_1404_;
v___y_1149_ = v___y_1380_;
v___y_1150_ = v___y_1379_;
v___y_1151_ = v___f_1414_;
v___y_1152_ = v___x_1400_;
v___y_1153_ = v___x_1416_;
goto v___jp_1147_;
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1417_ = l_Lean_Syntax_getArg(v___x_1415_, v___x_1245_);
lean_dec(v___x_1415_);
v___x_1418_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1419_ = l_Lean_Syntax_isOfKind(v___x_1417_, v___x_1418_);
if (v___x_1419_ == 0)
{
v___y_1148_ = v___x_1404_;
v___y_1149_ = v___y_1380_;
v___y_1150_ = v___y_1379_;
v___y_1151_ = v___f_1414_;
v___y_1152_ = v___x_1400_;
v___y_1153_ = v___x_1419_;
goto v___jp_1147_;
}
else
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1414_, v___x_1404_, v___y_1379_, v___y_1380_);
return v___x_1420_;
}
}
}
}
else
{
lean_object* v___x_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1421_ = l_Lean_Syntax_getArg(v___x_1403_, v___x_1245_);
v___x_1422_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8));
lean_inc(v___x_1421_);
v___x_1423_ = l_Lean_Syntax_isOfKind(v___x_1421_, v___x_1422_);
if (v___x_1423_ == 0)
{
lean_object* v_alts_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___f_1433_; 
lean_dec(v___x_1421_);
v_alts_1424_ = l_Lean_Syntax_getArgs(v___x_1403_);
lean_dec(v___x_1403_);
v___x_1425_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1426_ = lean_box(2);
lean_inc_ref(v_alts_1424_);
v___x_1427_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
lean_ctor_set(v___x_1427_, 1, v___x_1425_);
lean_ctor_set(v___x_1427_, 2, v_alts_1424_);
v___x_1428_ = lean_mk_empty_array_with_capacity(v___x_1384_);
lean_inc(v_tk_1391_);
v___x_1429_ = lean_array_push(v___x_1428_, v_tk_1391_);
v___x_1430_ = lean_array_push(v___x_1429_, v___x_1427_);
v___x_1431_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1426_);
lean_ctor_set(v___x_1431_, 1, v___x_1425_);
lean_ctor_set(v___x_1431_, 2, v___x_1430_);
v___x_1432_ = l_Lean_TSyntax_getId(v_kind_1402_);
lean_dec(v_kind_1402_);
lean_inc(v_attrKind_1385_);
v___f_1433_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1433_, 0, v___x_1431_);
lean_closure_set(v___f_1433_, 1, v___x_1432_);
lean_closure_set(v___f_1433_, 2, v___y_1381_);
lean_closure_set(v___f_1433_, 3, v_attrs_x3f_1383_);
lean_closure_set(v___f_1433_, 4, v_attrKind_1385_);
lean_closure_set(v___f_1433_, 5, v_tk_1391_);
lean_closure_set(v___f_1433_, 6, v_alts_1424_);
if (v___x_1388_ == 0)
{
lean_dec(v_attrKind_1385_);
v___y_1157_ = v___y_1380_;
v___y_1158_ = v___y_1379_;
v___y_1159_ = v___x_1404_;
v___y_1160_ = v___f_1433_;
v___y_1161_ = v___x_1423_;
v___y_1162_ = v___x_1388_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = l_Lean_Syntax_getArg(v_attrKind_1385_, v___x_1245_);
lean_dec(v_attrKind_1385_);
lean_inc(v___x_1434_);
v___x_1435_ = l_Lean_Syntax_matchesNull(v___x_1434_, v___y_1382_);
if (v___x_1435_ == 0)
{
lean_dec(v___x_1434_);
v___y_1157_ = v___y_1380_;
v___y_1158_ = v___y_1379_;
v___y_1159_ = v___x_1404_;
v___y_1160_ = v___f_1433_;
v___y_1161_ = v___x_1423_;
v___y_1162_ = v___x_1435_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1436_ = l_Lean_Syntax_getArg(v___x_1434_, v___x_1245_);
lean_dec(v___x_1434_);
v___x_1437_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1438_ = l_Lean_Syntax_isOfKind(v___x_1436_, v___x_1437_);
if (v___x_1438_ == 0)
{
v___y_1157_ = v___y_1380_;
v___y_1158_ = v___y_1379_;
v___y_1159_ = v___x_1404_;
v___y_1160_ = v___f_1433_;
v___y_1161_ = v___x_1423_;
v___y_1162_ = v___x_1438_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1433_, v___x_1423_, v___y_1379_, v___y_1380_);
return v___x_1439_;
}
}
}
}
else
{
lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1440_ = l_Lean_Syntax_getArg(v___x_1421_, v___y_1382_);
lean_inc(v___x_1440_);
v___x_1441_ = l_Lean_Syntax_matchesNull(v___x_1440_, v___y_1382_);
if (v___x_1441_ == 0)
{
lean_object* v_alts_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___f_1451_; 
lean_dec(v___x_1440_);
lean_dec(v___x_1421_);
v_alts_1442_ = l_Lean_Syntax_getArgs(v___x_1403_);
lean_dec(v___x_1403_);
v___x_1443_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1444_ = lean_box(2);
lean_inc_ref(v_alts_1442_);
v___x_1445_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
lean_ctor_set(v___x_1445_, 1, v___x_1443_);
lean_ctor_set(v___x_1445_, 2, v_alts_1442_);
v___x_1446_ = lean_mk_empty_array_with_capacity(v___x_1384_);
lean_inc(v_tk_1391_);
v___x_1447_ = lean_array_push(v___x_1446_, v_tk_1391_);
v___x_1448_ = lean_array_push(v___x_1447_, v___x_1445_);
v___x_1449_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1444_);
lean_ctor_set(v___x_1449_, 1, v___x_1443_);
lean_ctor_set(v___x_1449_, 2, v___x_1448_);
v___x_1450_ = l_Lean_TSyntax_getId(v_kind_1402_);
lean_dec(v_kind_1402_);
lean_inc(v_attrKind_1385_);
v___f_1451_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1451_, 0, v___x_1449_);
lean_closure_set(v___f_1451_, 1, v___x_1450_);
lean_closure_set(v___f_1451_, 2, v___y_1381_);
lean_closure_set(v___f_1451_, 3, v_attrs_x3f_1383_);
lean_closure_set(v___f_1451_, 4, v_attrKind_1385_);
lean_closure_set(v___f_1451_, 5, v_tk_1391_);
lean_closure_set(v___f_1451_, 6, v_alts_1442_);
if (v___x_1388_ == 0)
{
lean_dec(v_attrKind_1385_);
v___y_1139_ = v___y_1380_;
v___y_1140_ = v___y_1379_;
v___y_1141_ = v___x_1423_;
v___y_1142_ = v___x_1441_;
v___y_1143_ = v___f_1451_;
v___y_1144_ = v___x_1388_;
goto v___jp_1138_;
}
else
{
lean_object* v___x_1452_; uint8_t v___x_1453_; 
v___x_1452_ = l_Lean_Syntax_getArg(v_attrKind_1385_, v___x_1245_);
lean_dec(v_attrKind_1385_);
lean_inc(v___x_1452_);
v___x_1453_ = l_Lean_Syntax_matchesNull(v___x_1452_, v___y_1382_);
if (v___x_1453_ == 0)
{
lean_dec(v___x_1452_);
v___y_1139_ = v___y_1380_;
v___y_1140_ = v___y_1379_;
v___y_1141_ = v___x_1423_;
v___y_1142_ = v___x_1441_;
v___y_1143_ = v___f_1451_;
v___y_1144_ = v___x_1453_;
goto v___jp_1138_;
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v___x_1454_ = l_Lean_Syntax_getArg(v___x_1452_, v___x_1245_);
lean_dec(v___x_1452_);
v___x_1455_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1456_ = l_Lean_Syntax_isOfKind(v___x_1454_, v___x_1455_);
if (v___x_1456_ == 0)
{
v___y_1139_ = v___y_1380_;
v___y_1140_ = v___y_1379_;
v___y_1141_ = v___x_1423_;
v___y_1142_ = v___x_1441_;
v___y_1143_ = v___f_1451_;
v___y_1144_ = v___x_1456_;
goto v___jp_1138_;
}
else
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1451_, v___x_1441_, v___y_1379_, v___y_1380_);
return v___x_1457_;
}
}
}
}
else
{
lean_object* v___x_1458_; uint8_t v___x_1459_; 
v___x_1458_ = l_Lean_Syntax_getArg(v___x_1440_, v___x_1245_);
lean_dec(v___x_1440_);
lean_inc(v___x_1458_);
v___x_1459_ = l_Lean_Syntax_matchesNull(v___x_1458_, v___y_1382_);
if (v___x_1459_ == 0)
{
lean_object* v_alts_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___f_1469_; 
lean_dec(v___x_1458_);
lean_dec(v___x_1421_);
v_alts_1460_ = l_Lean_Syntax_getArgs(v___x_1403_);
lean_dec(v___x_1403_);
v___x_1461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1462_ = lean_box(2);
lean_inc_ref(v_alts_1460_);
v___x_1463_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
lean_ctor_set(v___x_1463_, 1, v___x_1461_);
lean_ctor_set(v___x_1463_, 2, v_alts_1460_);
v___x_1464_ = lean_mk_empty_array_with_capacity(v___x_1384_);
lean_inc(v_tk_1391_);
v___x_1465_ = lean_array_push(v___x_1464_, v_tk_1391_);
v___x_1466_ = lean_array_push(v___x_1465_, v___x_1463_);
v___x_1467_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1462_);
lean_ctor_set(v___x_1467_, 1, v___x_1461_);
lean_ctor_set(v___x_1467_, 2, v___x_1466_);
v___x_1468_ = l_Lean_TSyntax_getId(v_kind_1402_);
lean_dec(v_kind_1402_);
lean_inc(v_attrKind_1385_);
v___f_1469_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1469_, 0, v___x_1467_);
lean_closure_set(v___f_1469_, 1, v___x_1468_);
lean_closure_set(v___f_1469_, 2, v___y_1381_);
lean_closure_set(v___f_1469_, 3, v_attrs_x3f_1383_);
lean_closure_set(v___f_1469_, 4, v_attrKind_1385_);
lean_closure_set(v___f_1469_, 5, v_tk_1391_);
lean_closure_set(v___f_1469_, 6, v_alts_1460_);
if (v___x_1388_ == 0)
{
lean_dec(v_attrKind_1385_);
v___y_1166_ = v___y_1380_;
v___y_1167_ = v___y_1379_;
v___y_1168_ = v___x_1459_;
v___y_1169_ = v___x_1441_;
v___y_1170_ = v___f_1469_;
v___y_1171_ = v___x_1388_;
goto v___jp_1165_;
}
else
{
lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1470_ = l_Lean_Syntax_getArg(v_attrKind_1385_, v___x_1245_);
lean_dec(v_attrKind_1385_);
lean_inc(v___x_1470_);
v___x_1471_ = l_Lean_Syntax_matchesNull(v___x_1470_, v___y_1382_);
if (v___x_1471_ == 0)
{
lean_dec(v___x_1470_);
v___y_1166_ = v___y_1380_;
v___y_1167_ = v___y_1379_;
v___y_1168_ = v___x_1459_;
v___y_1169_ = v___x_1441_;
v___y_1170_ = v___f_1469_;
v___y_1171_ = v___x_1471_;
goto v___jp_1165_;
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1472_ = l_Lean_Syntax_getArg(v___x_1470_, v___x_1245_);
lean_dec(v___x_1470_);
v___x_1473_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1474_ = l_Lean_Syntax_isOfKind(v___x_1472_, v___x_1473_);
if (v___x_1474_ == 0)
{
v___y_1166_ = v___y_1380_;
v___y_1167_ = v___y_1379_;
v___y_1168_ = v___x_1459_;
v___y_1169_ = v___x_1441_;
v___y_1170_ = v___f_1469_;
v___y_1171_ = v___x_1474_;
goto v___jp_1165_;
}
else
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1469_, v___x_1459_, v___y_1379_, v___y_1380_);
return v___x_1475_;
}
}
}
}
else
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_Syntax_getArg(v___x_1458_, v___x_1245_);
lean_dec(v___x_1458_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14));
lean_inc(v___x_1476_);
v___x_1478_ = l_Lean_Syntax_isOfKind(v___x_1476_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_object* v_alts_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___f_1488_; 
lean_dec(v___x_1476_);
lean_dec(v___x_1421_);
v_alts_1479_ = l_Lean_Syntax_getArgs(v___x_1403_);
lean_dec(v___x_1403_);
v___x_1480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1481_ = lean_box(2);
lean_inc_ref(v_alts_1479_);
v___x_1482_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v___x_1480_);
lean_ctor_set(v___x_1482_, 2, v_alts_1479_);
v___x_1483_ = lean_mk_empty_array_with_capacity(v___x_1384_);
lean_inc(v_tk_1391_);
v___x_1484_ = lean_array_push(v___x_1483_, v_tk_1391_);
v___x_1485_ = lean_array_push(v___x_1484_, v___x_1482_);
v___x_1486_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1481_);
lean_ctor_set(v___x_1486_, 1, v___x_1480_);
lean_ctor_set(v___x_1486_, 2, v___x_1485_);
v___x_1487_ = l_Lean_TSyntax_getId(v_kind_1402_);
lean_dec(v_kind_1402_);
lean_inc(v_attrKind_1385_);
v___f_1488_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1488_, 0, v___x_1486_);
lean_closure_set(v___f_1488_, 1, v___x_1487_);
lean_closure_set(v___f_1488_, 2, v___y_1381_);
lean_closure_set(v___f_1488_, 3, v_attrs_x3f_1383_);
lean_closure_set(v___f_1488_, 4, v_attrKind_1385_);
lean_closure_set(v___f_1488_, 5, v_tk_1391_);
lean_closure_set(v___f_1488_, 6, v_alts_1479_);
if (v___x_1388_ == 0)
{
lean_dec(v_attrKind_1385_);
v___y_1130_ = v___y_1380_;
v___y_1131_ = v___y_1379_;
v___y_1132_ = v___x_1459_;
v___y_1133_ = v___x_1394_;
v___y_1134_ = v___f_1488_;
v___y_1135_ = v___x_1388_;
goto v___jp_1129_;
}
else
{
lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1489_ = l_Lean_Syntax_getArg(v_attrKind_1385_, v___x_1245_);
lean_dec(v_attrKind_1385_);
lean_inc(v___x_1489_);
v___x_1490_ = l_Lean_Syntax_matchesNull(v___x_1489_, v___y_1382_);
if (v___x_1490_ == 0)
{
lean_dec(v___x_1489_);
v___y_1130_ = v___y_1380_;
v___y_1131_ = v___y_1379_;
v___y_1132_ = v___x_1459_;
v___y_1133_ = v___x_1394_;
v___y_1134_ = v___f_1488_;
v___y_1135_ = v___x_1490_;
goto v___jp_1129_;
}
else
{
lean_object* v___x_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; 
v___x_1491_ = l_Lean_Syntax_getArg(v___x_1489_, v___x_1245_);
lean_dec(v___x_1489_);
v___x_1492_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
v___x_1493_ = l_Lean_Syntax_isOfKind(v___x_1491_, v___x_1492_);
if (v___x_1493_ == 0)
{
v___y_1130_ = v___y_1380_;
v___y_1131_ = v___y_1379_;
v___y_1132_ = v___x_1459_;
v___y_1133_ = v___x_1394_;
v___y_1134_ = v___f_1488_;
v___y_1135_ = v___x_1493_;
goto v___jp_1129_;
}
else
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_1488_, v___x_1394_, v___y_1379_, v___y_1380_);
return v___x_1494_;
}
}
}
}
else
{
lean_dec(v___x_1403_);
v___y_1330_ = v___y_1380_;
v___y_1331_ = v___x_1421_;
v___y_1332_ = v___x_1384_;
v___y_1333_ = v___x_1394_;
v___y_1334_ = v_attrs_x3f_1383_;
v___y_1335_ = v___x_1390_;
v___y_1336_ = v_kind_1402_;
v___y_1337_ = v___x_1476_;
v___y_1338_ = v___y_1379_;
v___y_1339_ = v___x_1386_;
v___y_1340_ = v_tk_1391_;
v___y_1341_ = v___y_1382_;
v___y_1342_ = v___y_1381_;
v___y_1343_ = v_attrKind_1385_;
goto v___jp_1329_;
}
}
else
{
lean_dec(v___x_1403_);
v___y_1330_ = v___y_1380_;
v___y_1331_ = v___x_1421_;
v___y_1332_ = v___x_1384_;
v___y_1333_ = v___x_1394_;
v___y_1334_ = v_attrs_x3f_1383_;
v___y_1335_ = v___x_1390_;
v___y_1336_ = v_kind_1402_;
v___y_1337_ = v___x_1476_;
v___y_1338_ = v___y_1379_;
v___y_1339_ = v___x_1386_;
v___y_1340_ = v_tk_1391_;
v___y_1341_ = v___y_1382_;
v___y_1342_ = v___y_1381_;
v___y_1343_ = v_attrKind_1385_;
goto v___jp_1329_;
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
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
lean_dec(v___x_1393_);
v___x_1495_ = lean_unsigned_to_nat(5u);
v___x_1496_ = l_Lean_Syntax_getArg(v_stx_1125_, v___x_1495_);
lean_dec(v_stx_1125_);
v___x_1497_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10));
lean_inc(v___x_1496_);
v___x_1498_ = l_Lean_Syntax_isOfKind(v___x_1496_, v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
lean_dec(v___x_1496_);
lean_dec(v_tk_1391_);
lean_dec(v_attrKind_1385_);
lean_dec(v_attrs_x3f_1383_);
lean_dec(v___y_1381_);
v___x_1499_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1499_;
}
else
{
lean_object* v___f_1500_; lean_object* v___x_1501_; lean_object* v_alts_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___f_1500_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__5___boxed), 15, 10);
lean_closure_set(v___f_1500_, 0, v___x_1497_);
lean_closure_set(v___f_1500_, 1, v___x_1177_);
lean_closure_set(v___f_1500_, 2, v_attrKind_1385_);
lean_closure_set(v___f_1500_, 3, v___x_1176_);
lean_closure_set(v___f_1500_, 4, v___x_1245_);
lean_closure_set(v___f_1500_, 5, v_attrs_x3f_1383_);
lean_closure_set(v___f_1500_, 6, v___x_1174_);
lean_closure_set(v___f_1500_, 7, v___x_1175_);
lean_closure_set(v___f_1500_, 8, v___x_1386_);
lean_closure_set(v___f_1500_, 9, v___y_1381_);
v___x_1501_ = l_Lean_Syntax_getArg(v___x_1496_, v___x_1245_);
lean_dec(v___x_1496_);
v_alts_1502_ = l_Lean_Syntax_getArgs(v___x_1501_);
lean_dec(v___x_1501_);
v___x_1503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11));
v___x_1504_ = lean_box(2);
lean_inc_ref(v_alts_1502_);
v___x_1505_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
lean_ctor_set(v___x_1505_, 1, v___x_1503_);
lean_ctor_set(v___x_1505_, 2, v_alts_1502_);
v___x_1506_ = lean_mk_empty_array_with_capacity(v___x_1384_);
v___x_1507_ = lean_array_push(v___x_1506_, v_tk_1391_);
v___x_1508_ = lean_array_push(v___x_1507_, v___x_1505_);
v___x_1509_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1504_);
lean_ctor_set(v___x_1509_, 1, v___x_1503_);
lean_ctor_set(v___x_1509_, 2, v___x_1508_);
v___x_1510_ = l_Lean_Elab_Command_getRef___redArg(v___y_1379_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v_fileName_1512_; lean_object* v_fileMap_1513_; lean_object* v_currRecDepth_1514_; lean_object* v_cmdPos_1515_; lean_object* v_macroStack_1516_; lean_object* v_quotContext_x3f_1517_; lean_object* v_currMacroScope_1518_; lean_object* v_snap_x3f_1519_; lean_object* v_cancelTk_x3f_1520_; uint8_t v_suppressElabErrors_1521_; lean_object* v_ref_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref_known(v___x_1510_, 1);
v_fileName_1512_ = lean_ctor_get(v___y_1379_, 0);
v_fileMap_1513_ = lean_ctor_get(v___y_1379_, 1);
v_currRecDepth_1514_ = lean_ctor_get(v___y_1379_, 2);
v_cmdPos_1515_ = lean_ctor_get(v___y_1379_, 3);
v_macroStack_1516_ = lean_ctor_get(v___y_1379_, 4);
v_quotContext_x3f_1517_ = lean_ctor_get(v___y_1379_, 5);
v_currMacroScope_1518_ = lean_ctor_get(v___y_1379_, 6);
v_snap_x3f_1519_ = lean_ctor_get(v___y_1379_, 8);
v_cancelTk_x3f_1520_ = lean_ctor_get(v___y_1379_, 9);
v_suppressElabErrors_1521_ = lean_ctor_get_uint8(v___y_1379_, sizeof(void*)*10);
v_ref_1522_ = l_Lean_replaceRef(v___x_1509_, v_a_1511_);
lean_dec(v_a_1511_);
lean_dec_ref_known(v___x_1509_, 3);
lean_inc(v_cancelTk_x3f_1520_);
lean_inc(v_snap_x3f_1519_);
lean_inc(v_currMacroScope_1518_);
lean_inc(v_quotContext_x3f_1517_);
lean_inc(v_macroStack_1516_);
lean_inc(v_cmdPos_1515_);
lean_inc(v_currRecDepth_1514_);
lean_inc_ref(v_fileMap_1513_);
lean_inc_ref(v_fileName_1512_);
v___x_1523_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1523_, 0, v_fileName_1512_);
lean_ctor_set(v___x_1523_, 1, v_fileMap_1513_);
lean_ctor_set(v___x_1523_, 2, v_currRecDepth_1514_);
lean_ctor_set(v___x_1523_, 3, v_cmdPos_1515_);
lean_ctor_set(v___x_1523_, 4, v_macroStack_1516_);
lean_ctor_set(v___x_1523_, 5, v_quotContext_x3f_1517_);
lean_ctor_set(v___x_1523_, 6, v_currMacroScope_1518_);
lean_ctor_set(v___x_1523_, 7, v_ref_1522_);
lean_ctor_set(v___x_1523_, 8, v_snap_x3f_1519_);
lean_ctor_set(v___x_1523_, 9, v_cancelTk_x3f_1520_);
lean_ctor_set_uint8(v___x_1523_, sizeof(void*)*10, v_suppressElabErrors_1521_);
v___x_1524_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(v_alts_1502_, v___x_1176_, v___f_1500_, v___x_1523_, v___y_1380_);
lean_dec_ref_known(v___x_1523_, 10);
lean_dec_ref(v_alts_1502_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
v_a_1533_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1524_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1524_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1509_, 3);
lean_dec_ref(v_alts_1502_);
lean_dec_ref(v___f_1500_);
return v___x_1510_;
}
}
}
}
}
v___jp_1541_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v___x_1545_ = lean_unsigned_to_nat(1u);
v___x_1546_ = l_Lean_Syntax_getArg(v_stx_1125_, v___x_1545_);
v___x_1547_ = l_Lean_Syntax_isNone(v___x_1546_);
if (v___x_1547_ == 0)
{
uint8_t v___x_1548_; 
lean_inc(v___x_1546_);
v___x_1548_ = l_Lean_Syntax_matchesNull(v___x_1546_, v___x_1545_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
lean_dec(v___x_1546_);
lean_dec(v_doc_x3f_1542_);
lean_dec(v_stx_1125_);
v___x_1549_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1549_;
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1550_ = l_Lean_Syntax_getArg(v___x_1546_, v___x_1245_);
lean_dec(v___x_1546_);
v___x_1551_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15));
lean_inc(v___x_1550_);
v___x_1552_ = l_Lean_Syntax_isOfKind(v___x_1550_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
lean_dec(v___x_1550_);
lean_dec(v_doc_x3f_1542_);
lean_dec(v_stx_1125_);
v___x_1553_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
return v___x_1553_;
}
else
{
lean_object* v___x_1554_; lean_object* v_attrs_x3f_1555_; lean_object* v___x_1556_; 
v___x_1554_ = l_Lean_Syntax_getArg(v___x_1550_, v___x_1545_);
lean_dec(v___x_1550_);
v_attrs_x3f_1555_ = l_Lean_Syntax_getArgs(v___x_1554_);
lean_dec(v___x_1554_);
v___x_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1556_, 0, v_attrs_x3f_1555_);
v___y_1379_ = v___y_1543_;
v___y_1380_ = v___y_1544_;
v___y_1381_ = v_doc_x3f_1542_;
v___y_1382_ = v___x_1545_;
v_attrs_x3f_1383_ = v___x_1556_;
goto v___jp_1378_;
}
}
}
else
{
lean_object* v___x_1557_; 
lean_dec(v___x_1546_);
v___x_1557_ = lean_box(0);
v___y_1379_ = v___y_1543_;
v___y_1380_ = v___y_1544_;
v___y_1381_ = v_doc_x3f_1542_;
v___y_1382_ = v___x_1545_;
v_attrs_x3f_1383_ = v___x_1557_;
goto v___jp_1378_;
}
}
}
v___jp_1129_:
{
if (v___y_1135_ == 0)
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1134_, v___y_1132_, v___y_1131_, v___y_1130_);
return v___x_1136_;
}
else
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1134_, v___y_1133_, v___y_1131_, v___y_1130_);
return v___x_1137_;
}
}
v___jp_1138_:
{
if (v___y_1144_ == 0)
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1143_, v___y_1141_, v___y_1140_, v___y_1139_);
return v___x_1145_;
}
else
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1143_, v___y_1142_, v___y_1140_, v___y_1139_);
return v___x_1146_;
}
}
v___jp_1147_:
{
if (v___y_1153_ == 0)
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1151_, v___y_1152_, v___y_1150_, v___y_1149_);
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1151_, v___y_1148_, v___y_1150_, v___y_1149_);
return v___x_1155_;
}
}
v___jp_1156_:
{
if (v___y_1162_ == 0)
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1160_, v___y_1159_, v___y_1158_, v___y_1157_);
return v___x_1163_;
}
else
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1160_, v___y_1161_, v___y_1158_, v___y_1157_);
return v___x_1164_;
}
}
v___jp_1165_:
{
if (v___y_1171_ == 0)
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1170_, v___y_1169_, v___y_1167_, v___y_1166_);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_1170_, v___y_1168_, v___y_1167_, v___y_1166_);
return v___x_1173_;
}
}
v___jp_1179_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_inc_ref_n(v___y_1189_, 3);
v___x_1195_ = l_Array_append___redArg(v___y_1189_, v___y_1194_);
lean_dec_ref(v___y_1194_);
lean_inc_n(v___y_1182_, 6);
lean_inc_n(v___y_1184_, 17);
v___x_1196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1196_, 0, v___y_1184_);
lean_ctor_set(v___x_1196_, 1, v___y_1182_);
lean_ctor_set(v___x_1196_, 2, v___x_1195_);
v___x_1197_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
lean_inc_ref_n(v___y_1192_, 2);
v___x_1198_ = l_Lean_Name_mkStr4(v___x_1174_, v___x_1175_, v___y_1192_, v___x_1197_);
v___x_1199_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
v___x_1200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___y_1184_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = l_Array_append___redArg(v___y_1189_, v___y_1181_);
lean_dec_ref(v___y_1181_);
v___x_1202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1202_, 0, v___y_1184_);
lean_ctor_set(v___x_1202_, 1, v___y_1182_);
lean_ctor_set(v___x_1202_, 2, v___x_1201_);
v___x_1203_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
v___x_1204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___y_1184_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = l_Lean_Syntax_node3(v___y_1184_, v___x_1198_, v___x_1200_, v___x_1202_, v___x_1204_);
v___x_1206_ = l_Lean_Syntax_node1(v___y_1184_, v___y_1182_, v___x_1205_);
lean_inc_ref(v___y_1186_);
v___x_1207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___y_1184_);
lean_ctor_set(v___x_1207_, 1, v___y_1186_);
v___x_1208_ = l_Lean_TSyntax_getId(v___y_1187_);
v___x_1209_ = l_Lean_mkIdentFrom(v___y_1193_, v___x_1208_, v___x_1178_);
lean_dec(v___y_1193_);
v___x_1210_ = l_Lean_Syntax_node2(v___y_1184_, v___y_1182_, v___x_1209_, v___y_1187_);
v___x_1211_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__6));
v___x_1212_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___y_1184_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__8, &l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8);
v___x_1214_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__9));
v___x_1215_ = l_Lean_addMacroScope(v___y_1183_, v___x_1214_, v___y_1185_);
v___x_1216_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6));
v___x_1217_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1217_, 0, v___y_1184_);
lean_ctor_set(v___x_1217_, 1, v___x_1213_);
lean_ctor_set(v___x_1217_, 2, v___x_1215_);
lean_ctor_set(v___x_1217_, 3, v___x_1216_);
v___x_1218_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
v___x_1219_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___y_1184_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__11));
v___x_1221_ = l_Lean_Name_mkStr4(v___x_1174_, v___x_1175_, v___y_1192_, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___y_1184_);
lean_ctor_set(v___x_1222_, 1, v___x_1220_);
v___x_1223_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7));
v___x_1224_ = l_Lean_Name_mkStr4(v___x_1174_, v___x_1175_, v___y_1192_, v___x_1223_);
v___x_1225_ = l_Lean_Syntax_node1(v___y_1184_, v___y_1182_, v___y_1190_);
v___x_1226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1226_, 0, v___y_1184_);
lean_ctor_set(v___x_1226_, 1, v___y_1182_);
lean_ctor_set(v___x_1226_, 2, v___y_1189_);
v___x_1227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13));
v___x_1228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___y_1184_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = l_Lean_Syntax_node4(v___y_1184_, v___x_1224_, v___x_1225_, v___x_1226_, v___x_1228_, v___y_1191_);
v___x_1230_ = l_Lean_Syntax_node2(v___y_1184_, v___x_1221_, v___x_1222_, v___x_1229_);
v___x_1231_ = lean_unsigned_to_nat(9u);
v___x_1232_ = lean_mk_empty_array_with_capacity(v___x_1231_);
v___x_1233_ = lean_array_push(v___x_1232_, v___x_1196_);
v___x_1234_ = lean_array_push(v___x_1233_, v___x_1206_);
v___x_1235_ = lean_array_push(v___x_1234_, v___y_1180_);
v___x_1236_ = lean_array_push(v___x_1235_, v___x_1207_);
v___x_1237_ = lean_array_push(v___x_1236_, v___x_1210_);
v___x_1238_ = lean_array_push(v___x_1237_, v___x_1212_);
v___x_1239_ = lean_array_push(v___x_1238_, v___x_1217_);
v___x_1240_ = lean_array_push(v___x_1239_, v___x_1219_);
v___x_1241_ = lean_array_push(v___x_1240_, v___x_1230_);
lean_inc(v___y_1188_);
v___x_1242_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1242_, 0, v___y_1184_);
lean_ctor_set(v___x_1242_, 1, v___y_1188_);
lean_ctor_set(v___x_1242_, 2, v___x_1241_);
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
return v___x_1243_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_elabMacroRules___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1125_ = stack[0].m_obj;
lean_object* v___y_1126_ = stack[1].m_obj;
lean_object* v___y_1127_ = stack[2].m_obj;
lean_object* v_res_1570_;
v_res_1570_ = l_Lean_Elab_Command_elabMacroRules___lam__1(v_stx_1125_, v___y_1126_, v___y_1127_);
stack->m_obj
 = v_res_1570_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___boxed(lean_object* v_stx_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_Elab_Command_elabMacroRules___lam__1(v_stx_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
return v_res_1575_;
}
}
lean_object* l_Lean_Elab_Command_elabMacroRules(lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v___f_1581_; lean_object* v___x_1582_; 
v___f_1581_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___closed__0));
v___x_1582_ = l_Lean_Elab_Command_adaptExpander(v___f_1581_, v_a_1577_, v_a_1578_, v_a_1579_);
return v___x_1582_;
}
}
LEAN_EXPORT void l_Lean_Elab_Command_elabMacroRules_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1577_ = stack[0].m_obj;
lean_object* v_a_1578_ = stack[1].m_obj;
lean_object* v_a_1579_ = stack[2].m_obj;
lean_object* v_res_1583_;
v_res_1583_ = l_Lean_Elab_Command_elabMacroRules(v_a_1577_, v_a_1578_, v_a_1579_);
stack->m_obj
 = v_res_1583_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___boxed(lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_Elab_Command_elabMacroRules(v_a_1584_, v_a_1585_, v_a_1586_);
lean_dec(v_a_1586_);
lean_dec_ref(v_a_1585_);
return v_res_1588_;
}
}
lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1(){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1596_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1597_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1));
v___x_1598_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1));
v___x_1599_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___boxed), 4, 0);
v___x_1600_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1596_, v___x_1597_, v___x_1598_, v___x_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1601_;
v_res_1601_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1();
stack->m_obj
 = v_res_1601_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___boxed(lean_object* v_a_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1();
return v_res_1603_;
}
}
lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3(){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1));
v___x_1631_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6));
v___x_1632_ = l_Lean_addBuiltinDeclarationRanges(v___x_1630_, v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1633_;
v_res_1633_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3();
stack->m_obj
 = v_res_1633_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___boxed(lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3();
return v_res_1635_;
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
