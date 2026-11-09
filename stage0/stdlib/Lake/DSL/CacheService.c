// Lean compiler output
// Module: Lake.DSL.CacheService
// Imports: public import Lake.DSL.Syntax public import Lake.Config.Cache
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withMacroExpansion___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lake_DSL_expandAttrs(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lake_DSL_mkConfigDeclIdent(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_DSL_expandIdentOrStrAsStrLit(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__0 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__0_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__1 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__1_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "cacheServiceCommand"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__2 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__3_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__3_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__2_value),LEAN_SCALAR_PTR_LITERAL(59, 45, 201, 219, 139, 244, 81, 2)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__3 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__3_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "ill-formed cache_service declaration"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__4 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__4_value;
static lean_once_cell_t l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__8 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__8_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__9 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__10_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__10_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__10_value_aux_2),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__9_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__10 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__10_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__11 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__11_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__12 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__12_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__13_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__13_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__11_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__13_value_aux_2),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__12_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__13 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__13_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__14 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__14_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__15 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__15_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__16 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__16_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__17 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__17_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__18 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__18_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__19_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__19_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__19_value_aux_2),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__18_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__19 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__19_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__20 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__20_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__21 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__21_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__22_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__22_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__22_value_aux_2),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__21_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__22 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__22_value;
static const lean_array_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__23 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__23_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__24 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__24_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__25_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__25_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__25_value_aux_2),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__24_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__25 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__25_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__26 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__26_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__27 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__27_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "CacheService"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__28 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__28_value;
static lean_once_cell_t l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__29;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__28_value),LEAN_SCALAR_PTR_LITERAL(28, 12, 24, 204, 101, 230, 51, 208)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__30 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__30_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__31_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__28_value),LEAN_SCALAR_PTR_LITERAL(216, 152, 240, 2, 45, 49, 80, 164)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__31 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__31_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__32 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__32_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__31_value)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__33 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__33_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__34 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__34_value;
static const lean_array_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__35 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__35_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__36 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__36_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__37_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__37_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__37_value_aux_2),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__36_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__37 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__37_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__38 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__38_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__39_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__39_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__39_value_aux_2),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__38_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__39 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__39_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__40 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__40_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__41 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__41_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__42_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__42_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__40_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__42_value_aux_2),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__41_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__42 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__42_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__43 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__43_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__44_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__44_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__40_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__44_value_aux_2),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__43_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__44 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__44_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__45 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__45_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__45_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__46 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__46_value;
static lean_once_cell_t l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__47;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__48 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__48_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__49 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__49_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__50_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__50_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__48_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__50_value_aux_2),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__49_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__50 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__50_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 15, .m_data = "«cache_service»"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__51 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__51_value;
static lean_once_cell_t l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__52;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "cache_service"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__53 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__53_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__53_value),LEAN_SCALAR_PTR_LITERAL(143, 86, 119, 188, 20, 4, 214, 242)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__54 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__54_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__55 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__55_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__56_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__56_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__40_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__56_value_aux_2),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__55_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__56 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__56_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "CacheService.withNameD"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__57 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__57_value;
static lean_once_cell_t l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__58;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "withNameD"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__59 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__59_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__28_value),LEAN_SCALAR_PTR_LITERAL(28, 12, 24, 204, 101, 230, 51, 208)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__60_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__59_value),LEAN_SCALAR_PTR_LITERAL(63, 43, 37, 107, 150, 69, 180, 38)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__60 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__60_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__61_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__28_value),LEAN_SCALAR_PTR_LITERAL(216, 152, 240, 2, 45, 49, 80, 164)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__61_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__59_value),LEAN_SCALAR_PTR_LITERAL(83, 72, 181, 232, 254, 120, 223, 107)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__61 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__61_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__61_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__62 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__62_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__62_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__63 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__63_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__64 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__64_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__65_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__65_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__65_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__65_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__40_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__65_value_aux_2),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__64_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__65 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__65_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__66 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__66_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__67_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__67_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__67_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__40_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__67_value_aux_2),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__66_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__67 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__67_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__68 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__68_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__69 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__69_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__69_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__70 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__70_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__71 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__71_value;
static lean_once_cell_t l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__72;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__73_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__73_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__73 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__73_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__73_value)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__74 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__74_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__75_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__75_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__75_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__75 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__75_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__75_value)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__76 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__76_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__77 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__77_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__78_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__78_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__77_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__78_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__78 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__78_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__78_value)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__79 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__79_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__80_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__80_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__77_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__80 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__80_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__80_value)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__81 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__81_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__82_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__82 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__82_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__82_value)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__83 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__83_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__84 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__84_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__84_value)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__85 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__85_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__85_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__86 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__86_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__83_value),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__86_value)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__87 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__87_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__81_value),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__87_value)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__88 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__88_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__79_value),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__88_value)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__89 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__89_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__76_value),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__89_value)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__90 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__90_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__74_value),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__90_value)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__91 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__91_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "CacheServiceName.ofString"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__92 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__92_value;
static lean_once_cell_t l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__93_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__93;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "CacheServiceName"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__94 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__94_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ofString"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__95 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__95_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__96_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__94_value),LEAN_SCALAR_PTR_LITERAL(140, 66, 71, 95, 7, 209, 111, 51)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__96_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__95_value),LEAN_SCALAR_PTR_LITERAL(168, 247, 6, 228, 210, 173, 161, 194)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__96 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__96_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__97_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__97_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__97_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__94_value),LEAN_SCALAR_PTR_LITERAL(40, 189, 49, 82, 30, 140, 106, 48)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__97_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__95_value),LEAN_SCALAR_PTR_LITERAL(28, 176, 58, 108, 122, 50, 161, 2)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__97 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__97_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__97_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__98 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__98_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__98_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__99 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__99_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__100 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__100_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "whereDecls"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__101 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__101_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__102_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__102_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__102_value_aux_0),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__102_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__102_value_aux_1),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__40_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__102_value_aux_2),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__101_value),LEAN_SCALAR_PTR_LITERAL(51, 156, 180, 247, 37, 30, 126, 62)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__102 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__102_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__1_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__1_value),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 152, 205, 91, 21, 95, 180)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__2 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__2_value),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__1_value),LEAN_SCALAR_PTR_LITERAL(20, 230, 244, 102, 183, 225, 161, 156)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__3 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__3_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__3_value),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__28_value),LEAN_SCALAR_PTR_LITERAL(191, 248, 48, 246, 254, 217, 149, 36)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__4 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(114, 55, 232, 253, 14, 160, 145, 12)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__5 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__5_value),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 51, 108, 110, 232, 224, 18, 38)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__6 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__6_value),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__1_value),LEAN_SCALAR_PTR_LITERAL(33, 199, 185, 237, 202, 227, 9, 147)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__7 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__7_value;
static const lean_string_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "elabCacheServiceCommand"};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__8 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__8_value;
static const lean_ctor_object l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__7_value),((lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 228, 202, 237, 127, 156, 216, 11)}};
static const lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__9 = (const lean_object*)&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__1___redArg(lean_object* v___y_1_){
_start:
{
lean_object* v___x_3_; lean_object* v_env_4_; lean_object* v___x_5_; lean_object* v_mainModule_6_; lean_object* v___x_7_; 
v___x_3_ = lean_st_ref_get(v___y_1_);
v_env_4_ = lean_ctor_get(v___x_3_, 0);
lean_inc_ref(v_env_4_);
lean_dec(v___x_3_);
v___x_5_ = l_Lean_Environment_header(v_env_4_);
lean_dec_ref(v_env_4_);
v_mainModule_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_mainModule_6_);
lean_dec_ref(v___x_5_);
v___x_7_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7_, 0, v_mainModule_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__1___redArg___boxed(lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_getMainModule___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__1___redArg(v___y_8_);
lean_dec(v___y_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__1(lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_getMainModule___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__1___redArg(v___y_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__1___boxed(lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_getMainModule___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__1(v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
return v_res_18_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = lean_box(1);
v___x_20_ = l_Lean_MessageData_ofFormat(v___x_19_);
return v___x_20_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__2));
v___x_25_ = l_Lean_MessageData_ofFormat(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5(lean_object* v_x_26_, lean_object* v_x_27_){
_start:
{
if (lean_obj_tag(v_x_27_) == 0)
{
return v_x_26_;
}
else
{
lean_object* v_head_28_; lean_object* v_tail_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_51_; 
v_head_28_ = lean_ctor_get(v_x_27_, 0);
v_tail_29_ = lean_ctor_get(v_x_27_, 1);
v_isSharedCheck_51_ = !lean_is_exclusive(v_x_27_);
if (v_isSharedCheck_51_ == 0)
{
v___x_31_ = v_x_27_;
v_isShared_32_ = v_isSharedCheck_51_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_tail_29_);
lean_inc(v_head_28_);
lean_dec(v_x_27_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_51_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v_before_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_49_; 
v_before_33_ = lean_ctor_get(v_head_28_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v_head_28_);
if (v_isSharedCheck_49_ == 0)
{
lean_object* v_unused_50_; 
v_unused_50_ = lean_ctor_get(v_head_28_, 1);
lean_dec(v_unused_50_);
v___x_35_ = v_head_28_;
v_isShared_36_ = v_isSharedCheck_49_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_before_33_);
lean_dec(v_head_28_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_49_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_37_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__0);
if (v_isShared_36_ == 0)
{
lean_ctor_set_tag(v___x_35_, 7);
lean_ctor_set(v___x_35_, 1, v___x_37_);
lean_ctor_set(v___x_35_, 0, v_x_26_);
v___x_39_ = v___x_35_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_x_26_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v___x_37_);
v___x_39_ = v_reuseFailAlloc_48_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
lean_object* v___x_40_; lean_object* v___x_42_; 
v___x_40_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__3);
if (v_isShared_32_ == 0)
{
lean_ctor_set_tag(v___x_31_, 7);
lean_ctor_set(v___x_31_, 1, v___x_40_);
lean_ctor_set(v___x_31_, 0, v___x_39_);
v___x_42_ = v___x_31_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v___x_40_);
v___x_42_ = v_reuseFailAlloc_47_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = l_Lean_MessageData_ofSyntax(v_before_33_);
v___x_44_ = l_Lean_indentD(v___x_43_);
v___x_45_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_42_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
v_x_26_ = v___x_45_;
v_x_27_ = v_tail_29_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__4(lean_object* v_opts_52_, lean_object* v_opt_53_){
_start:
{
lean_object* v_name_54_; lean_object* v_defValue_55_; lean_object* v_map_56_; lean_object* v___x_57_; 
v_name_54_ = lean_ctor_get(v_opt_53_, 0);
v_defValue_55_ = lean_ctor_get(v_opt_53_, 1);
v_map_56_ = lean_ctor_get(v_opts_52_, 0);
v___x_57_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_56_, v_name_54_);
if (lean_obj_tag(v___x_57_) == 0)
{
uint8_t v___x_58_; 
v___x_58_ = lean_unbox(v_defValue_55_);
return v___x_58_;
}
else
{
lean_object* v_val_59_; 
v_val_59_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_val_59_);
lean_dec_ref_known(v___x_57_, 1);
if (lean_obj_tag(v_val_59_) == 1)
{
uint8_t v_v_60_; 
v_v_60_ = lean_ctor_get_uint8(v_val_59_, 0);
lean_dec_ref_known(v_val_59_, 0);
return v_v_60_;
}
else
{
uint8_t v___x_61_; 
lean_dec(v_val_59_);
v___x_61_ = lean_unbox(v_defValue_55_);
return v___x_61_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_opts_62_, lean_object* v_opt_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__4(v_opts_62_, v_opt_63_);
lean_dec_ref(v_opt_63_);
lean_dec_ref(v_opts_62_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_70_ = l_Lean_MessageData_ofFormat(v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_71_, lean_object* v_macroStack_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_scopes_77_; lean_object* v___x_78_; lean_object* v_opts_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_75_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_76_ = lean_st_ref_get(v___y_73_);
v_scopes_77_ = lean_ctor_get(v___x_76_, 2);
lean_inc(v_scopes_77_);
lean_dec(v___x_76_);
v___x_78_ = l_List_head_x21___redArg(v___x_75_, v_scopes_77_);
lean_dec(v_scopes_77_);
v_opts_79_ = lean_ctor_get(v___x_78_, 1);
lean_inc_ref(v_opts_79_);
lean_dec(v___x_78_);
v___x_80_ = l_Lean_Elab_pp_macroStack;
v___x_81_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__4(v_opts_79_, v___x_80_);
lean_dec_ref(v_opts_79_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; 
lean_dec(v_macroStack_72_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v_msgData_71_);
return v___x_82_;
}
else
{
if (lean_obj_tag(v_macroStack_72_) == 0)
{
lean_object* v___x_83_; 
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v_msgData_71_);
return v___x_83_;
}
else
{
lean_object* v_head_84_; lean_object* v_after_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_100_; 
v_head_84_ = lean_ctor_get(v_macroStack_72_, 0);
lean_inc(v_head_84_);
v_after_85_ = lean_ctor_get(v_head_84_, 1);
v_isSharedCheck_100_ = !lean_is_exclusive(v_head_84_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v_head_84_, 0);
lean_dec(v_unused_101_);
v___x_87_ = v_head_84_;
v_isShared_88_ = v_isSharedCheck_100_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_after_85_);
lean_dec(v_head_84_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_100_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; lean_object* v___x_91_; 
v___x_89_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5___closed__0);
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 7);
lean_ctor_set(v___x_87_, 1, v___x_89_);
lean_ctor_set(v___x_87_, 0, v_msgData_71_);
v___x_91_ = v___x_87_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_msgData_71_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_89_);
v___x_91_ = v_reuseFailAlloc_99_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v_msgData_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_92_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_93_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = l_Lean_MessageData_ofSyntax(v_after_85_);
v___x_95_ = l_Lean_indentD(v___x_94_);
v_msgData_96_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_96_, 0, v___x_93_);
lean_ctor_set(v_msgData_96_, 1, v___x_95_);
v___x_97_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3_spec__5(v_msgData_96_, v_macroStack_72_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_102_, lean_object* v_macroStack_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg(v_msgData_102_, v_macroStack_103_, v___y_104_);
lean_dec(v___y_104_);
return v_res_106_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_107_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
lean_ctor_set(v___x_112_, 2, v___x_111_);
lean_ctor_set(v___x_112_, 3, v___x_111_);
lean_ctor_set(v___x_112_, 4, v___x_110_);
lean_ctor_set(v___x_112_, 5, v___x_110_);
lean_ctor_set(v___x_112_, 6, v___x_110_);
lean_ctor_set(v___x_112_, 7, v___x_110_);
lean_ctor_set(v___x_112_, 8, v___x_110_);
lean_ctor_set(v___x_112_, 9, v___x_110_);
lean_ctor_set(v___x_112_, 10, v___x_110_);
return v___x_112_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_unsigned_to_nat(32u);
v___x_114_ = lean_mk_empty_array_with_capacity(v___x_113_);
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_116_ = ((size_t)5ULL);
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_unsigned_to_nat(32u);
v___x_119_ = lean_mk_empty_array_with_capacity(v___x_118_);
v___x_120_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_121_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v___x_119_);
lean_ctor_set(v___x_121_, 2, v___x_117_);
lean_ctor_set(v___x_121_, 3, v___x_117_);
lean_ctor_set_usize(v___x_121_, 4, v___x_116_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_122_ = lean_box(1);
v___x_123_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__4);
v___x_124_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v___x_123_);
lean_ctor_set(v___x_125_, 2, v___x_122_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; lean_object* v_env_130_; uint8_t v___x_131_; lean_object* v_env_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v_scopes_135_; lean_object* v___x_136_; lean_object* v_opts_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_129_ = lean_st_ref_get(v___y_127_);
v_env_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc_ref(v_env_130_);
lean_dec(v___x_129_);
v___x_131_ = 0;
v_env_132_ = l_Lean_Environment_setRecordingDeps(v_env_130_, v___x_131_);
v___x_133_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_134_ = lean_st_ref_get(v___y_127_);
v_scopes_135_ = lean_ctor_get(v___x_134_, 2);
lean_inc(v_scopes_135_);
lean_dec(v___x_134_);
v___x_136_ = l_List_head_x21___redArg(v___x_133_, v_scopes_135_);
lean_dec(v_scopes_135_);
v_opts_137_ = lean_ctor_get(v___x_136_, 1);
lean_inc_ref(v_opts_137_);
lean_dec(v___x_136_);
v___x_138_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_139_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___closed__5);
v___x_140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_140_, 0, v_env_132_);
lean_ctor_set(v___x_140_, 1, v___x_138_);
lean_ctor_set(v___x_140_, 2, v___x_139_);
lean_ctor_set(v___x_140_, 3, v_opts_137_);
v___x_141_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v_msgData_126_);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg(v_msgData_143_, v___y_144_);
lean_dec(v___y_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0___redArg(lean_object* v_msg_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Elab_Command_getRef___redArg(v___y_148_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v_macroStack_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v_a_156_; lean_object* v___x_157_; lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_166_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v___x_151_, 1);
v_macroStack_153_ = lean_ctor_get(v___y_148_, 4);
v___x_154_ = l_Lean_Elab_getBetterRef(v_a_152_, v_macroStack_153_);
lean_dec(v_a_152_);
v___x_155_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg(v_msg_147_, v___y_149_);
v_a_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_a_156_);
lean_dec_ref(v___x_155_);
lean_inc(v_macroStack_153_);
v___x_157_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg(v_a_156_, v_macroStack_153_, v___y_149_);
v_a_158_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_166_ == 0)
{
v___x_160_ = v___x_157_;
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_154_);
lean_ctor_set(v___x_162_, 1, v_a_158_);
if (v_isShared_161_ == 0)
{
lean_ctor_set_tag(v___x_160_, 1);
lean_ctor_set(v___x_160_, 0, v___x_162_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
lean_dec_ref(v_msg_147_);
v_a_167_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_151_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_151_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0___redArg___boxed(lean_object* v_msg_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0___redArg(v_msg_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0___redArg(lean_object* v_ref_180_, lean_object* v_msg_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Elab_Command_getRef___redArg(v___y_182_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v_fileName_187_; lean_object* v_fileMap_188_; lean_object* v_currRecDepth_189_; lean_object* v_cmdPos_190_; lean_object* v_macroStack_191_; lean_object* v_quotContext_x3f_192_; lean_object* v_currMacroScope_193_; lean_object* v_snap_x3f_194_; lean_object* v_cancelTk_x3f_195_; uint8_t v_suppressElabErrors_196_; uint8_t v_checkDeprecated_197_; lean_object* v_ref_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 1);
v_fileName_187_ = lean_ctor_get(v___y_182_, 0);
v_fileMap_188_ = lean_ctor_get(v___y_182_, 1);
v_currRecDepth_189_ = lean_ctor_get(v___y_182_, 2);
v_cmdPos_190_ = lean_ctor_get(v___y_182_, 3);
v_macroStack_191_ = lean_ctor_get(v___y_182_, 4);
v_quotContext_x3f_192_ = lean_ctor_get(v___y_182_, 5);
v_currMacroScope_193_ = lean_ctor_get(v___y_182_, 6);
v_snap_x3f_194_ = lean_ctor_get(v___y_182_, 8);
v_cancelTk_x3f_195_ = lean_ctor_get(v___y_182_, 9);
v_suppressElabErrors_196_ = lean_ctor_get_uint8(v___y_182_, sizeof(void*)*10);
v_checkDeprecated_197_ = lean_ctor_get_uint8(v___y_182_, sizeof(void*)*10 + 1);
v_ref_198_ = l_Lean_replaceRef(v_ref_180_, v_a_186_);
lean_dec(v_a_186_);
lean_inc(v_cancelTk_x3f_195_);
lean_inc(v_snap_x3f_194_);
lean_inc(v_currMacroScope_193_);
lean_inc(v_quotContext_x3f_192_);
lean_inc(v_macroStack_191_);
lean_inc(v_cmdPos_190_);
lean_inc(v_currRecDepth_189_);
lean_inc_ref(v_fileMap_188_);
lean_inc_ref(v_fileName_187_);
v___x_199_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_199_, 0, v_fileName_187_);
lean_ctor_set(v___x_199_, 1, v_fileMap_188_);
lean_ctor_set(v___x_199_, 2, v_currRecDepth_189_);
lean_ctor_set(v___x_199_, 3, v_cmdPos_190_);
lean_ctor_set(v___x_199_, 4, v_macroStack_191_);
lean_ctor_set(v___x_199_, 5, v_quotContext_x3f_192_);
lean_ctor_set(v___x_199_, 6, v_currMacroScope_193_);
lean_ctor_set(v___x_199_, 7, v_ref_198_);
lean_ctor_set(v___x_199_, 8, v_snap_x3f_194_);
lean_ctor_set(v___x_199_, 9, v_cancelTk_x3f_195_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*10, v_suppressElabErrors_196_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*10 + 1, v_checkDeprecated_197_);
v___x_200_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0___redArg(v_msg_181_, v___x_199_, v___y_183_);
lean_dec_ref_known(v___x_199_, 10);
return v___x_200_;
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec_ref(v_msg_181_);
v_a_201_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_185_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_185_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0___redArg___boxed(lean_object* v_ref_209_, lean_object* v_msg_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0___redArg(v_ref_209_, v_msg_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v_ref_209_);
return v_res_214_;
}
}
static lean_object* _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__4));
v___x_224_ = l_Lean_stringToMessageData(v___x_223_);
return v___x_224_;
}
}
static lean_object* _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__29(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__28));
v___x_270_ = l_String_toRawSubstring_x27(v___x_269_);
return v___x_270_;
}
}
static lean_object* _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__47(void){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Array_mkArray0___redArg();
return v___x_312_;
}
}
static lean_object* _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__52(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__51));
v___x_322_ = l_String_toRawSubstring_x27(v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__58(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__57));
v___x_334_ = l_String_toRawSubstring_x27(v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__72(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__71));
v___x_367_ = l_String_toRawSubstring_x27(v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__93(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__92));
v___x_420_ = l_String_toRawSubstring_x27(v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand(lean_object* v_stx_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_447_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__3));
lean_inc(v_stx_443_);
v___x_448_ = l_Lean_Syntax_isOfKind(v_stx_443_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_obj_once(&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5, &l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5_once, _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5);
v___x_450_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0___redArg(v_stx_443_, v___x_449_, v_a_444_, v_a_445_);
lean_dec(v_stx_443_);
return v___x_450_;
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; uint8_t v___x_480_; 
v___x_451_ = lean_unsigned_to_nat(4u);
v___x_452_ = l_Lean_Syntax_getArg(v_stx_443_, v___x_451_);
v___x_453_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__6));
v___x_454_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__7));
v___x_455_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__10));
lean_inc(v___x_452_);
v___x_480_ = l_Lean_Syntax_isOfKind(v___x_452_, v___x_455_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec(v___x_452_);
v___x_481_ = lean_obj_once(&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5, &l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5_once, _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5);
v___x_482_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0___redArg(v_stx_443_, v___x_481_, v_a_444_, v_a_445_);
lean_dec(v_stx_443_);
return v___x_482_;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_483_ = lean_unsigned_to_nat(2u);
v___x_484_ = l_Lean_Syntax_getArg(v___x_452_, v___x_483_);
v___x_485_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__13));
lean_inc(v___x_484_);
v___x_486_ = l_Lean_Syntax_isOfKind(v___x_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec(v___x_484_);
lean_dec(v___x_452_);
v___x_487_ = lean_obj_once(&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5, &l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5_once, _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5);
v___x_488_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0___redArg(v_stx_443_, v___x_487_, v_a_444_, v_a_445_);
lean_dec(v_stx_443_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v_a_570_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_489_ = lean_unsigned_to_nat(0u);
v___x_576_ = l_Lean_Syntax_getArg(v___x_484_, v___x_489_);
v___x_577_ = l_Lean_Syntax_matchesNull(v___x_576_, v___x_489_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v___x_484_);
lean_dec(v___x_452_);
v___x_578_ = lean_obj_once(&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5, &l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5_once, _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5);
v___x_579_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0___redArg(v_stx_443_, v___x_578_, v_a_444_, v_a_445_);
lean_dec(v_stx_443_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; lean_object* v___y_582_; uint8_t v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v_a_592_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v_defn_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_673_ = l_Lean_Syntax_getArg(v___x_484_, v___x_580_);
lean_dec(v___x_484_);
v___x_674_ = l_Lean_Syntax_matchesNull(v___x_673_, v___x_489_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v___x_452_);
v___x_675_ = lean_obj_once(&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5, &l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5_once, _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5);
v___x_676_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0___redArg(v_stx_443_, v___x_675_, v_a_444_, v_a_445_);
lean_dec(v_stx_443_);
return v___x_676_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v_kw_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v_defn_682_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v_a_693_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v_wds_x3f_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_677_ = l_Lean_Syntax_getArg(v_stx_443_, v___x_489_);
v___x_678_ = l_Lean_Syntax_getArg(v_stx_443_, v___x_580_);
v_kw_679_ = l_Lean_Syntax_getArg(v_stx_443_, v___x_483_);
v___x_680_ = lean_unsigned_to_nat(3u);
v___x_681_ = l_Lean_Syntax_getArg(v_stx_443_, v___x_680_);
v_defn_682_ = l_Lean_Syntax_getArg(v___x_452_, v___x_580_);
v___x_851_ = l_Lean_Syntax_getArg(v___x_452_, v___x_680_);
lean_dec(v___x_452_);
v___x_852_ = l_Lean_Syntax_isNone(v___x_851_);
if (v___x_852_ == 0)
{
uint8_t v___x_853_; 
lean_inc(v___x_851_);
v___x_853_ = l_Lean_Syntax_matchesNull(v___x_851_, v___x_580_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; 
lean_dec(v___x_851_);
lean_dec(v_defn_682_);
lean_dec(v___x_681_);
lean_dec(v_kw_679_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
v___x_854_ = lean_obj_once(&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5, &l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5_once, _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5);
v___x_855_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0___redArg(v_stx_443_, v___x_854_, v_a_444_, v_a_445_);
lean_dec(v_stx_443_);
return v___x_855_;
}
else
{
lean_object* v_wds_x3f_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v_wds_x3f_856_ = l_Lean_Syntax_getArg(v___x_851_, v___x_489_);
lean_dec(v___x_851_);
v___x_857_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__102));
lean_inc(v_wds_x3f_856_);
v___x_858_ = l_Lean_Syntax_isOfKind(v_wds_x3f_856_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; 
lean_dec(v_wds_x3f_856_);
lean_dec(v_defn_682_);
lean_dec(v___x_681_);
lean_dec(v_kw_679_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
v___x_859_ = lean_obj_once(&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5, &l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5_once, _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__5);
v___x_860_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0___redArg(v_stx_443_, v___x_859_, v_a_444_, v_a_445_);
lean_dec(v_stx_443_);
return v___x_860_;
}
else
{
lean_object* v___x_861_; 
v___x_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_861_, 0, v_wds_x3f_856_);
v_wds_x3f_838_ = v___x_861_;
v___y_839_ = v_a_444_;
v___y_840_ = v_a_445_;
goto v___jp_837_;
}
}
}
else
{
lean_object* v___x_862_; 
lean_dec(v___x_851_);
v___x_862_ = lean_box(0);
v_wds_x3f_838_ = v___x_862_;
v___y_839_ = v_a_444_;
v___y_840_ = v_a_445_;
goto v___jp_837_;
}
v___jp_683_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_694_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__56));
v___x_695_ = lean_obj_once(&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__58, &l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__58_once, _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__58);
v___x_696_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__60));
lean_inc_n(v___y_687_, 2);
lean_inc_n(v_a_693_, 2);
v___x_697_ = l_Lean_addMacroScope(v_a_693_, v___x_696_, v___y_687_);
v___x_698_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__63));
lean_inc_n(v___y_690_, 11);
v___x_699_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_699_, 0, v___y_690_);
lean_ctor_set(v___x_699_, 1, v___x_695_);
lean_ctor_set(v___x_699_, 2, v___x_697_);
lean_ctor_set(v___x_699_, 3, v___x_698_);
v___x_700_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__46));
v___x_701_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__65));
v___x_702_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__67));
v___x_703_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__68));
v___x_704_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_704_, 0, v___y_690_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__70));
v___x_706_ = lean_obj_once(&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__72, &l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__72_once, _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__72);
v___x_707_ = lean_box(0);
v___x_708_ = l_Lean_addMacroScope(v_a_693_, v___x_707_, v___y_687_);
v___x_709_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__91));
v___x_710_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_710_, 0, v___y_690_);
lean_ctor_set(v___x_710_, 1, v___x_706_);
lean_ctor_set(v___x_710_, 2, v___x_708_);
lean_ctor_set(v___x_710_, 3, v___x_709_);
v___x_711_ = l_Lean_Syntax_node1(v___y_690_, v___x_705_, v___x_710_);
v___x_712_ = l_Lean_Syntax_node2(v___y_690_, v___x_702_, v___x_704_, v___x_711_);
v___x_713_ = lean_obj_once(&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__93, &l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__93_once, _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__93);
v___x_714_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__96));
v___x_715_ = l_Lean_addMacroScope(v_a_693_, v___x_714_, v___y_687_);
v___x_716_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__99));
v___x_717_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_717_, 0, v___y_690_);
lean_ctor_set(v___x_717_, 1, v___x_713_);
lean_ctor_set(v___x_717_, 2, v___x_715_);
lean_ctor_set(v___x_717_, 3, v___x_716_);
v___x_718_ = l_Lean_Syntax_node1(v___y_690_, v___x_700_, v___y_686_);
v___x_719_ = l_Lean_Syntax_node2(v___y_690_, v___x_694_, v___x_717_, v___x_718_);
v___x_720_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__100));
v___x_721_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_721_, 0, v___y_690_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = l_Lean_Syntax_node3(v___y_690_, v___x_701_, v___x_712_, v___x_719_, v___x_721_);
v___x_723_ = l_Lean_Syntax_node2(v___y_690_, v___x_700_, v_defn_682_, v___x_722_);
v___x_724_ = l_Lean_Syntax_node2(v___y_690_, v___x_694_, v___x_699_, v___x_723_);
v___y_639_ = v___y_684_;
v___y_640_ = v___y_685_;
v___y_641_ = v___y_689_;
v___y_642_ = v___y_692_;
v_defn_643_ = v___x_724_;
v___y_644_ = v___y_688_;
v___y_645_ = v___y_691_;
goto v___jp_638_;
}
v___jp_725_:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Elab_Command_getRef___redArg(v___y_726_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v_fileName_734_; lean_object* v_fileMap_735_; lean_object* v_currRecDepth_736_; lean_object* v_cmdPos_737_; lean_object* v_macroStack_738_; lean_object* v_quotContext_x3f_739_; lean_object* v_currMacroScope_740_; lean_object* v_snap_x3f_741_; lean_object* v_cancelTk_x3f_742_; uint8_t v_suppressElabErrors_743_; uint8_t v_checkDeprecated_744_; lean_object* v_ref_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___x_732_, 1);
v_fileName_734_ = lean_ctor_get(v___y_726_, 0);
v_fileMap_735_ = lean_ctor_get(v___y_726_, 1);
v_currRecDepth_736_ = lean_ctor_get(v___y_726_, 2);
v_cmdPos_737_ = lean_ctor_get(v___y_726_, 3);
v_macroStack_738_ = lean_ctor_get(v___y_726_, 4);
v_quotContext_x3f_739_ = lean_ctor_get(v___y_726_, 5);
v_currMacroScope_740_ = lean_ctor_get(v___y_726_, 6);
v_snap_x3f_741_ = lean_ctor_get(v___y_726_, 8);
v_cancelTk_x3f_742_ = lean_ctor_get(v___y_726_, 9);
v_suppressElabErrors_743_ = lean_ctor_get_uint8(v___y_726_, sizeof(void*)*10);
v_checkDeprecated_744_ = lean_ctor_get_uint8(v___y_726_, sizeof(void*)*10 + 1);
v_ref_745_ = l_Lean_replaceRef(v_kw_679_, v_a_733_);
lean_dec(v_a_733_);
lean_dec(v_kw_679_);
lean_inc(v_cancelTk_x3f_742_);
lean_inc(v_snap_x3f_741_);
lean_inc(v_currMacroScope_740_);
lean_inc(v_quotContext_x3f_739_);
lean_inc(v_macroStack_738_);
lean_inc(v_cmdPos_737_);
lean_inc(v_currRecDepth_736_);
lean_inc_ref(v_fileMap_735_);
lean_inc_ref(v_fileName_734_);
v___x_746_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_746_, 0, v_fileName_734_);
lean_ctor_set(v___x_746_, 1, v_fileMap_735_);
lean_ctor_set(v___x_746_, 2, v_currRecDepth_736_);
lean_ctor_set(v___x_746_, 3, v_cmdPos_737_);
lean_ctor_set(v___x_746_, 4, v_macroStack_738_);
lean_ctor_set(v___x_746_, 5, v_quotContext_x3f_739_);
lean_ctor_set(v___x_746_, 6, v_currMacroScope_740_);
lean_ctor_set(v___x_746_, 7, v_ref_745_);
lean_ctor_set(v___x_746_, 8, v_snap_x3f_741_);
lean_ctor_set(v___x_746_, 9, v_cancelTk_x3f_742_);
lean_ctor_set_uint8(v___x_746_, sizeof(void*)*10, v_suppressElabErrors_743_);
lean_ctor_set_uint8(v___x_746_, sizeof(void*)*10 + 1, v_checkDeprecated_744_);
lean_inc(v___y_730_);
v___x_747_ = l_Lake_DSL_mkConfigDeclIdent(v___y_730_, v___x_746_, v___y_728_);
if (lean_obj_tag(v___x_747_) == 0)
{
if (lean_obj_tag(v___y_730_) == 1)
{
lean_object* v_a_748_; lean_object* v_val_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
v_val_749_ = lean_ctor_get(v___y_730_, 0);
lean_inc_n(v_val_749_, 2);
lean_dec_ref_known(v___y_730_, 1);
v___x_750_ = l_Lake_DSL_expandIdentOrStrAsStrLit(v_val_749_);
v___x_751_ = l_Lean_Elab_Command_getRef___redArg(v___x_746_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v_ref_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
v_ref_753_ = l_Lean_replaceRef(v_val_749_, v_a_752_);
lean_dec(v_a_752_);
lean_dec(v_val_749_);
lean_inc(v_cancelTk_x3f_742_);
lean_inc(v_snap_x3f_741_);
lean_inc(v_currMacroScope_740_);
lean_inc(v_quotContext_x3f_739_);
lean_inc(v_macroStack_738_);
lean_inc(v_cmdPos_737_);
lean_inc(v_currRecDepth_736_);
lean_inc_ref(v_fileMap_735_);
lean_inc_ref(v_fileName_734_);
v___x_754_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_754_, 0, v_fileName_734_);
lean_ctor_set(v___x_754_, 1, v_fileMap_735_);
lean_ctor_set(v___x_754_, 2, v_currRecDepth_736_);
lean_ctor_set(v___x_754_, 3, v_cmdPos_737_);
lean_ctor_set(v___x_754_, 4, v_macroStack_738_);
lean_ctor_set(v___x_754_, 5, v_quotContext_x3f_739_);
lean_ctor_set(v___x_754_, 6, v_currMacroScope_740_);
lean_ctor_set(v___x_754_, 7, v_ref_753_);
lean_ctor_set(v___x_754_, 8, v_snap_x3f_741_);
lean_ctor_set(v___x_754_, 9, v_cancelTk_x3f_742_);
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*10, v_suppressElabErrors_743_);
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*10 + 1, v_checkDeprecated_744_);
v___x_755_ = l_Lean_Elab_Command_getRef___redArg(v___x_754_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
v___x_757_ = 0;
v___x_758_ = l_Lean_SourceInfo_fromRef(v_a_756_, v___x_757_);
lean_dec(v_a_756_);
v___x_759_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_754_);
lean_dec_ref_known(v___x_754_, 10);
if (lean_obj_tag(v___x_759_) == 0)
{
if (lean_obj_tag(v_quotContext_x3f_739_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_761_; lean_object* v_a_762_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref_known(v___x_759_, 1);
v___x_761_ = l_Lean_getMainModule___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__1___redArg(v___y_728_);
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref(v___x_761_);
v___y_684_ = v___y_731_;
v___y_685_ = v_a_748_;
v___y_686_ = v___x_750_;
v___y_687_ = v_a_760_;
v___y_688_ = v___x_746_;
v___y_689_ = v___y_727_;
v___y_690_ = v___x_758_;
v___y_691_ = v___y_728_;
v___y_692_ = v___y_729_;
v_a_693_ = v_a_762_;
goto v___jp_683_;
}
else
{
lean_object* v_a_763_; lean_object* v_val_764_; 
v_a_763_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v___x_759_, 1);
v_val_764_ = lean_ctor_get(v_quotContext_x3f_739_, 0);
lean_inc(v_val_764_);
v___y_684_ = v___y_731_;
v___y_685_ = v_a_748_;
v___y_686_ = v___x_750_;
v___y_687_ = v_a_763_;
v___y_688_ = v___x_746_;
v___y_689_ = v___y_727_;
v___y_690_ = v___x_758_;
v___y_691_ = v___y_728_;
v___y_692_ = v___y_729_;
v_a_693_ = v_val_764_;
goto v___jp_683_;
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec(v___x_758_);
lean_dec(v___x_750_);
lean_dec(v_a_748_);
lean_dec_ref_known(v___x_746_, 10);
lean_dec(v___y_731_);
lean_dec(v___y_729_);
lean_dec(v___y_727_);
lean_dec(v_defn_682_);
lean_dec(v_stx_443_);
v_a_765_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_759_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_759_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec_ref_known(v___x_754_, 10);
lean_dec(v___x_750_);
lean_dec(v_a_748_);
lean_dec_ref_known(v___x_746_, 10);
lean_dec(v___y_731_);
lean_dec(v___y_729_);
lean_dec(v___y_727_);
lean_dec(v_defn_682_);
lean_dec(v_stx_443_);
v_a_773_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_755_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_755_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec(v___x_750_);
lean_dec(v_val_749_);
lean_dec(v_a_748_);
lean_dec_ref_known(v___x_746_, 10);
lean_dec(v___y_731_);
lean_dec(v___y_729_);
lean_dec(v___y_727_);
lean_dec(v_defn_682_);
lean_dec(v_stx_443_);
v_a_781_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_751_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_751_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_object* v_a_789_; 
lean_dec(v___y_730_);
v_a_789_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_747_, 1);
v___y_639_ = v___y_731_;
v___y_640_ = v_a_789_;
v___y_641_ = v___y_727_;
v___y_642_ = v___y_729_;
v_defn_643_ = v_defn_682_;
v___y_644_ = v___x_746_;
v___y_645_ = v___y_728_;
goto v___jp_638_;
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec_ref_known(v___x_746_, 10);
lean_dec(v___y_731_);
lean_dec(v___y_730_);
lean_dec(v___y_729_);
lean_dec(v___y_727_);
lean_dec(v_defn_682_);
lean_dec(v_stx_443_);
v_a_790_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_747_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_747_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec(v___y_731_);
lean_dec(v___y_730_);
lean_dec(v___y_729_);
lean_dec(v___y_727_);
lean_dec(v_defn_682_);
lean_dec(v_kw_679_);
lean_dec(v_stx_443_);
v_a_798_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_732_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_732_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
v___jp_806_:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_Syntax_getOptional_x3f(v___x_677_);
lean_dec(v___x_677_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v___x_813_; 
v___x_813_ = lean_box(0);
v___y_726_ = v___y_807_;
v___y_727_ = v___y_811_;
v___y_728_ = v___y_808_;
v___y_729_ = v___y_810_;
v___y_730_ = v___y_809_;
v___y_731_ = v___x_813_;
goto v___jp_725_;
}
else
{
lean_object* v_val_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
v_val_814_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_812_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_val_814_);
lean_dec(v___x_812_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_val_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
v___y_726_ = v___y_807_;
v___y_727_ = v___y_811_;
v___y_728_ = v___y_808_;
v___y_729_ = v___y_810_;
v___y_730_ = v___y_809_;
v___y_731_ = v___x_819_;
goto v___jp_725_;
}
}
}
}
v___jp_822_:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Syntax_getOptional_x3f(v___x_678_);
lean_dec(v___x_678_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v___x_828_; 
v___x_828_ = lean_box(0);
v___y_807_ = v___y_823_;
v___y_808_ = v___y_824_;
v___y_809_ = v___y_826_;
v___y_810_ = v___y_825_;
v___y_811_ = v___x_828_;
goto v___jp_806_;
}
else
{
lean_object* v_val_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_val_829_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_827_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_val_829_);
lean_dec(v___x_827_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_val_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
v___y_807_ = v___y_823_;
v___y_808_ = v___y_824_;
v___y_809_ = v___y_826_;
v___y_810_ = v___y_825_;
v___y_811_ = v___x_834_;
goto v___jp_806_;
}
}
}
}
v___jp_837_:
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_Syntax_getOptional_x3f(v___x_681_);
lean_dec(v___x_681_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v___x_842_; 
v___x_842_ = lean_box(0);
v___y_823_ = v___y_839_;
v___y_824_ = v___y_840_;
v___y_825_ = v_wds_x3f_838_;
v___y_826_ = v___x_842_;
goto v___jp_822_;
}
else
{
lean_object* v_val_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
v_val_843_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_841_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_val_843_);
lean_dec(v___x_841_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_val_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
v___y_823_ = v___y_839_;
v___y_824_ = v___y_840_;
v___y_825_ = v_wds_x3f_838_;
v___y_826_ = v___x_848_;
goto v___jp_822_;
}
}
}
}
}
v___jp_581_:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_593_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__40));
v___x_594_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__42));
v___x_595_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__44));
v___x_596_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__46));
v___x_597_ = lean_obj_once(&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__47, &l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__47_once, _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__47);
lean_inc_n(v___y_586_, 4);
v___x_598_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_598_, 0, v___y_586_);
lean_ctor_set(v___x_598_, 1, v___x_596_);
lean_ctor_set(v___x_598_, 2, v___x_597_);
lean_inc_ref(v___x_598_);
v___x_599_ = l_Lean_Syntax_node1(v___y_586_, v___x_595_, v___x_598_);
v___x_600_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__50));
v___x_601_ = lean_obj_once(&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__52, &l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__52_once, _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__52);
v___x_602_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__54));
v___x_603_ = l_Lean_addMacroScope(v_a_592_, v___x_602_, v___y_590_);
v___x_604_ = lean_box(0);
v___x_605_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_605_, 0, v___y_586_);
lean_ctor_set(v___x_605_, 1, v___x_601_);
lean_ctor_set(v___x_605_, 2, v___x_603_);
lean_ctor_set(v___x_605_, 3, v___x_604_);
v___x_606_ = l_Lean_Syntax_node2(v___y_586_, v___x_600_, v___x_605_, v___x_598_);
v___x_607_ = l_Lean_Syntax_node2(v___y_586_, v___x_594_, v___x_599_, v___x_606_);
v___x_608_ = lean_mk_empty_array_with_capacity(v___x_580_);
v___x_609_ = lean_array_push(v___x_608_, v___x_607_);
v___x_610_ = l_Lake_DSL_expandAttrs(v___y_588_);
v___x_611_ = l_Array_append___redArg(v___x_609_, v___x_610_);
lean_dec_ref(v___x_610_);
v___x_612_ = l_Lean_Elab_Command_getRef___redArg(v___y_585_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v___x_612_, 1);
v___x_614_ = l_Lean_SourceInfo_fromRef(v_a_613_, v___y_583_);
lean_dec(v_a_613_);
v___x_615_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_585_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_quotContext_x3f_616_; 
v_quotContext_x3f_616_ = lean_ctor_get(v___y_585_, 5);
if (lean_obj_tag(v_quotContext_x3f_616_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_618_; lean_object* v_a_619_; 
v_a_617_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_617_);
lean_dec_ref_known(v___x_615_, 1);
v___x_618_ = l_Lean_getMainModule___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__1___redArg(v___y_589_);
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref(v___x_618_);
v___y_557_ = v___x_593_;
v___y_558_ = v_a_617_;
v___y_559_ = v___y_584_;
v___y_560_ = v___y_585_;
v___y_561_ = v___x_597_;
v___y_562_ = v___x_604_;
v___y_563_ = v___y_589_;
v___y_564_ = v___x_596_;
v___y_565_ = v___y_582_;
v___y_566_ = v___y_587_;
v___y_567_ = v___x_614_;
v___y_568_ = v___y_591_;
v___y_569_ = v___x_611_;
v_a_570_ = v_a_619_;
goto v___jp_556_;
}
else
{
lean_object* v_a_620_; lean_object* v_val_621_; 
v_a_620_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_620_);
lean_dec_ref_known(v___x_615_, 1);
v_val_621_ = lean_ctor_get(v_quotContext_x3f_616_, 0);
lean_inc(v_val_621_);
v___y_557_ = v___x_593_;
v___y_558_ = v_a_620_;
v___y_559_ = v___y_584_;
v___y_560_ = v___y_585_;
v___y_561_ = v___x_597_;
v___y_562_ = v___x_604_;
v___y_563_ = v___y_589_;
v___y_564_ = v___x_596_;
v___y_565_ = v___y_582_;
v___y_566_ = v___y_587_;
v___y_567_ = v___x_614_;
v___y_568_ = v___y_591_;
v___y_569_ = v___x_611_;
v_a_570_ = v_val_621_;
goto v___jp_556_;
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec(v___x_614_);
lean_dec_ref(v___x_611_);
lean_dec(v___y_591_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec(v___y_582_);
lean_dec(v_stx_443_);
v_a_622_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_615_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_615_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec_ref(v___x_611_);
lean_dec(v___y_591_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec(v___y_582_);
lean_dec(v_stx_443_);
v_a_630_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_612_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_612_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
v___jp_638_:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Elab_Command_getRef___redArg(v___y_644_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; uint8_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v___x_646_, 1);
v___x_648_ = 0;
v___x_649_ = l_Lean_SourceInfo_fromRef(v_a_647_, v___x_648_);
lean_dec(v_a_647_);
v___x_650_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_644_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_quotContext_x3f_651_; 
v_quotContext_x3f_651_ = lean_ctor_get(v___y_644_, 5);
if (lean_obj_tag(v_quotContext_x3f_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; lean_object* v_a_654_; 
v_a_652_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_650_, 1);
v___x_653_ = l_Lean_getMainModule___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__1___redArg(v___y_645_);
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref(v___x_653_);
v___y_582_ = v___y_639_;
v___y_583_ = v___x_648_;
v___y_584_ = v___y_640_;
v___y_585_ = v___y_644_;
v___y_586_ = v___x_649_;
v___y_587_ = v_defn_643_;
v___y_588_ = v___y_641_;
v___y_589_ = v___y_645_;
v___y_590_ = v_a_652_;
v___y_591_ = v___y_642_;
v_a_592_ = v_a_654_;
goto v___jp_581_;
}
else
{
lean_object* v_a_655_; lean_object* v_val_656_; 
v_a_655_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_655_);
lean_dec_ref_known(v___x_650_, 1);
v_val_656_ = lean_ctor_get(v_quotContext_x3f_651_, 0);
lean_inc(v_val_656_);
v___y_582_ = v___y_639_;
v___y_583_ = v___x_648_;
v___y_584_ = v___y_640_;
v___y_585_ = v___y_644_;
v___y_586_ = v___x_649_;
v___y_587_ = v_defn_643_;
v___y_588_ = v___y_641_;
v___y_589_ = v___y_645_;
v___y_590_ = v_a_655_;
v___y_591_ = v___y_642_;
v_a_592_ = v_val_656_;
goto v___jp_581_;
}
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec(v___x_649_);
lean_dec_ref(v___y_644_);
lean_dec(v_defn_643_);
lean_dec(v___y_642_);
lean_dec(v___y_641_);
lean_dec(v___y_640_);
lean_dec(v___y_639_);
lean_dec(v_stx_443_);
v_a_657_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_650_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_650_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref(v___y_644_);
lean_dec(v_defn_643_);
lean_dec(v___y_642_);
lean_dec(v___y_641_);
lean_dec(v___y_640_);
lean_dec(v___y_639_);
lean_dec(v_stx_443_);
v_a_665_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_646_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_646_);
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
v___jp_490_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
lean_inc_ref_n(v___y_496_, 3);
v___x_507_ = l_Array_append___redArg(v___y_496_, v___y_506_);
lean_dec_ref(v___y_506_);
lean_inc_n(v___y_499_, 6);
lean_inc_n(v___y_502_, 16);
v___x_508_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_508_, 0, v___y_502_);
lean_ctor_set(v___x_508_, 1, v___y_499_);
lean_ctor_set(v___x_508_, 2, v___x_507_);
v___x_509_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__14));
lean_inc_ref_n(v___y_491_, 2);
v___x_510_ = l_Lean_Name_mkStr4(v___x_453_, v___x_454_, v___y_491_, v___x_509_);
v___x_511_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__15));
v___x_512_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_512_, 0, v___y_502_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__16));
v___x_514_ = l_Lean_Syntax_SepArray_ofElems(v___x_513_, v___y_505_);
lean_dec_ref(v___y_505_);
v___x_515_ = l_Array_append___redArg(v___y_496_, v___x_514_);
lean_dec_ref(v___x_514_);
v___x_516_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_516_, 0, v___y_502_);
lean_ctor_set(v___x_516_, 1, v___y_499_);
lean_ctor_set(v___x_516_, 2, v___x_515_);
v___x_517_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__17));
v___x_518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_518_, 0, v___y_502_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = l_Lean_Syntax_node3(v___y_502_, v___x_510_, v___x_512_, v___x_516_, v___x_518_);
v___x_520_ = l_Lean_Syntax_node1(v___y_502_, v___y_499_, v___x_519_);
v___x_521_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_521_, 0, v___y_502_);
lean_ctor_set(v___x_521_, 1, v___y_499_);
lean_ctor_set(v___x_521_, 2, v___y_496_);
lean_inc_ref_n(v___x_521_, 8);
lean_inc(v___y_503_);
v___x_522_ = l_Lean_Syntax_node7(v___y_502_, v___y_503_, v___x_508_, v___x_520_, v___x_521_, v___x_521_, v___x_521_, v___x_521_, v___x_521_);
v___x_523_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__19));
v___x_524_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__20));
v___x_525_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_525_, 0, v___y_502_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__22));
v___x_527_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__23));
v___x_528_ = lean_box(2);
v___x_529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v___y_499_);
lean_ctor_set(v___x_529_, 2, v___x_527_);
v___x_530_ = lean_mk_empty_array_with_capacity(v___x_483_);
v___x_531_ = lean_array_push(v___x_530_, v___y_494_);
v___x_532_ = lean_array_push(v___x_531_, v___x_529_);
v___x_533_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_533_, 0, v___x_528_);
lean_ctor_set(v___x_533_, 1, v___x_526_);
lean_ctor_set(v___x_533_, 2, v___x_532_);
v___x_534_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__25));
v___x_535_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__26));
v___x_536_ = l_Lean_Name_mkStr4(v___x_453_, v___x_454_, v___y_491_, v___x_535_);
v___x_537_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__27));
v___x_538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_538_, 0, v___y_502_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = lean_obj_once(&l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__29, &l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__29_once, _init_l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__29);
v___x_540_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__30));
v___x_541_ = l_Lean_addMacroScope(v___y_493_, v___x_540_, v___y_492_);
v___x_542_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__32));
v___x_543_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__33));
lean_inc(v___y_497_);
v___x_544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v___y_497_);
v___x_545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_542_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_546_, 0, v___y_502_);
lean_ctor_set(v___x_546_, 1, v___x_539_);
lean_ctor_set(v___x_546_, 2, v___x_541_);
lean_ctor_set(v___x_546_, 3, v___x_545_);
v___x_547_ = l_Lean_Syntax_node2(v___y_502_, v___x_536_, v___x_538_, v___x_546_);
v___x_548_ = l_Lean_Syntax_node1(v___y_502_, v___y_499_, v___x_547_);
v___x_549_ = l_Lean_Syntax_node2(v___y_502_, v___x_534_, v___x_521_, v___x_548_);
v___x_550_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__34));
v___x_551_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_551_, 0, v___y_502_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = l_Lean_Syntax_node2(v___y_502_, v___x_485_, v___x_521_, v___x_521_);
if (lean_obj_tag(v___y_504_) == 1)
{
lean_object* v_val_553_; lean_object* v___x_554_; 
v_val_553_ = lean_ctor_get(v___y_504_, 0);
lean_inc(v_val_553_);
lean_dec_ref_known(v___y_504_, 1);
v___x_554_ = l_Array_mkArray1___redArg(v_val_553_);
v___y_457_ = v___x_523_;
v___y_458_ = v___x_533_;
v___y_459_ = v___y_495_;
v___y_460_ = v___x_521_;
v___y_461_ = v___y_496_;
v___y_462_ = v___y_498_;
v___y_463_ = v___x_525_;
v___y_464_ = v___x_549_;
v___y_465_ = v___x_522_;
v___y_466_ = v___y_499_;
v___y_467_ = v___x_551_;
v___y_468_ = v___y_500_;
v___y_469_ = v___x_552_;
v___y_470_ = v___y_502_;
v___y_471_ = v___y_501_;
v___y_472_ = v___x_554_;
goto v___jp_456_;
}
else
{
lean_object* v___x_555_; 
lean_dec(v___y_504_);
v___x_555_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__35));
v___y_457_ = v___x_523_;
v___y_458_ = v___x_533_;
v___y_459_ = v___y_495_;
v___y_460_ = v___x_521_;
v___y_461_ = v___y_496_;
v___y_462_ = v___y_498_;
v___y_463_ = v___x_525_;
v___y_464_ = v___x_549_;
v___y_465_ = v___x_522_;
v___y_466_ = v___y_499_;
v___y_467_ = v___x_551_;
v___y_468_ = v___y_500_;
v___y_469_ = v___x_552_;
v___y_470_ = v___y_502_;
v___y_471_ = v___y_501_;
v___y_472_ = v___x_555_;
goto v___jp_456_;
}
}
v___jp_556_:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__37));
v___x_572_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__39));
if (lean_obj_tag(v___y_565_) == 1)
{
lean_object* v_val_573_; lean_object* v___x_574_; 
v_val_573_ = lean_ctor_get(v___y_565_, 0);
lean_inc(v_val_573_);
lean_dec_ref_known(v___y_565_, 1);
v___x_574_ = l_Array_mkArray1___redArg(v_val_573_);
v___y_491_ = v___y_557_;
v___y_492_ = v___y_558_;
v___y_493_ = v_a_570_;
v___y_494_ = v___y_559_;
v___y_495_ = v___y_560_;
v___y_496_ = v___y_561_;
v___y_497_ = v___y_562_;
v___y_498_ = v___y_563_;
v___y_499_ = v___y_564_;
v___y_500_ = v___x_571_;
v___y_501_ = v___y_566_;
v___y_502_ = v___y_567_;
v___y_503_ = v___x_572_;
v___y_504_ = v___y_568_;
v___y_505_ = v___y_569_;
v___y_506_ = v___x_574_;
goto v___jp_490_;
}
else
{
lean_object* v___x_575_; 
lean_dec(v___y_565_);
v___x_575_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__35));
v___y_491_ = v___y_557_;
v___y_492_ = v___y_558_;
v___y_493_ = v_a_570_;
v___y_494_ = v___y_559_;
v___y_495_ = v___y_560_;
v___y_496_ = v___y_561_;
v___y_497_ = v___y_562_;
v___y_498_ = v___y_563_;
v___y_499_ = v___y_564_;
v___y_500_ = v___x_571_;
v___y_501_ = v___y_566_;
v___y_502_ = v___y_567_;
v___y_503_ = v___x_572_;
v___y_504_ = v___y_568_;
v___y_505_ = v___y_569_;
v___y_506_ = v___x_575_;
goto v___jp_490_;
}
}
}
}
v___jp_456_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
lean_inc_ref(v___y_461_);
v___x_473_ = l_Array_append___redArg(v___y_461_, v___y_472_);
lean_dec_ref(v___y_472_);
lean_inc(v___y_466_);
lean_inc_n(v___y_470_, 3);
v___x_474_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_474_, 0, v___y_470_);
lean_ctor_set(v___x_474_, 1, v___y_466_);
lean_ctor_set(v___x_474_, 2, v___x_473_);
v___x_475_ = l_Lean_Syntax_node4(v___y_470_, v___x_455_, v___y_467_, v___y_471_, v___y_469_, v___x_474_);
lean_inc(v___y_457_);
v___x_476_ = l_Lean_Syntax_node5(v___y_470_, v___y_457_, v___y_463_, v___y_458_, v___y_464_, v___x_475_, v___y_460_);
lean_inc(v___y_468_);
v___x_477_ = l_Lean_Syntax_node2(v___y_470_, v___y_468_, v___y_465_, v___x_476_);
lean_inc(v___x_477_);
v___x_478_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_478_, 0, v___x_477_);
v___x_479_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_stx_443_, v___x_477_, v___x_478_, v___y_459_, v___y_462_);
lean_dec_ref(v___y_459_);
return v___x_479_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___boxed(lean_object* v_stx_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand(v_stx_863_, v_a_864_, v_a_865_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0(lean_object* v_00_u03b1_868_, lean_object* v_ref_869_, lean_object* v_msg_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0___redArg(v_ref_869_, v_msg_870_, v___y_871_, v___y_872_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0___boxed(lean_object* v_00_u03b1_875_, lean_object* v_ref_876_, lean_object* v_msg_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0(v_00_u03b1_875_, v_ref_876_, v_msg_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v_ref_876_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2(lean_object* v_msgData_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___redArg(v_msgData_882_, v___y_884_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__2(v_msgData_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0(lean_object* v_00_u03b1_892_, lean_object* v_msg_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0___redArg(v_msg_893_, v___y_894_, v___y_895_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0___boxed(lean_object* v_00_u03b1_898_, lean_object* v_msg_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0(v_00_u03b1_898_, v_msg_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3(lean_object* v_msgData_904_, lean_object* v_macroStack_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___redArg(v_msgData_904_, v_macroStack_905_, v___y_907_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_910_, lean_object* v_macroStack_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand_spec__0_spec__0_spec__3(v_msgData_910_, v_macroStack_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1(){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_943_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_944_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___closed__3));
v___x_945_ = ((lean_object*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___closed__9));
v___x_946_ = lean_alloc_closure((void*)(l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___boxed), 4, 0);
v___x_947_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_943_, v___x_944_, v___x_945_, v___x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1___boxed(lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1();
return v_res_949_;
}
}
lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Cache(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_CacheService(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Cache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand___regBuiltin___private_Lake_DSL_CacheService_0__Lake_DSL_elabCacheServiceCommand__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_DSL_CacheService(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* initialize_Lake_Config_Cache(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_CacheService(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Cache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_CacheService(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_DSL_CacheService(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_DSL_CacheService(builtin);
}
#ifdef __cplusplus
}
#endif
