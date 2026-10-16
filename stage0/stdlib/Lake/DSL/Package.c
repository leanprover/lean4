// Lean compiler output
// Module: Lake.DSL.Package
// Imports: public import Lake.DSL.Syntax import Lake.Config.Package import Lake.DSL.Extensions
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withMacroExpansion___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lake_DSL_expandAttrs(lean_object*);
extern lean_object* l_Lake_DSL_packageDeclName;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkCApp(lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
extern lean_object* l_Lake_PackageConfig_instConfigInfo;
lean_object* l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lake_DSL_mkConfigDeclIdent(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lake_Name_quoteFrom(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lake_nameExt;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_DSL_expandOptSimpleBinder(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3_value;
static lean_once_cell_t l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7_value;
static const lean_array_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "where"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "whereStructInst"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_2),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(164, 171, 248, 18, 201, 160, 43, 108)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(175, 253, 70, 178, 90, 186, 195, 40)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "ill-formed configuration syntax"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23_value;
static lean_once_cell_t l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "declValWhere"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(151, 133, 86, 223, 245, 102, 246, 81)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValStruct"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(133, 214, 189, 204, 150, 4, 239, 13)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "structVal"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(111, 76, 221, 200, 37, 245, 130, 150)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_2),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value;
static const lean_string_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "whereDecls"};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33_value;
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_2),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(51, 156, 180, 247, 37, 30, 126, 62)}};
static const lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34 = (const lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value;
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "deprecated"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__1 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__1_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "\"Use `__name__` instead.\""};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "since"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "\"2025-09-18\""};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "nameConst"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__8 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__8_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_1),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__8_value),LEAN_SCALAR_PTR_LITERAL(97, 173, 245, 76, 54, 29, 98, 170)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "__name__"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "packageCommand"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_1),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11_value),LEAN_SCALAR_PTR_LITERAL(125, 54, 253, 85, 92, 174, 10, 50)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed package declaration"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "abbrev"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "PackageDecl"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20_value),LEAN_SCALAR_PTR_LITERAL(225, 4, 178, 81, 27, 213, 197, 136)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23_value_aux_0),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20_value),LEAN_SCALAR_PTR_LITERAL(253, 117, 189, 141, 218, 132, 90, 198)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23_value)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29_value;
static const lean_array_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "baseName"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35_value),LEAN_SCALAR_PTR_LITERAL(110, 15, 203, 48, 91, 80, 65, 181)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "origName"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41_value),LEAN_SCALAR_PTR_LITERAL(60, 90, 152, 77, 27, 27, 68, 80)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "keyName"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44_value),LEAN_SCALAR_PTR_LITERAL(25, 96, 4, 27, 96, 164, 24, 20)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47_value),LEAN_SCALAR_PTR_LITERAL(207, 146, 87, 28, 198, 178, 209, 199)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 9, .m_data = "«package»"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "package"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58_value),LEAN_SCALAR_PTR_LITERAL(79, 155, 211, 46, 225, 213, 150, 92)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Name"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value_aux_0),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value_aux_1),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value),LEAN_SCALAR_PTR_LITERAL(35, 98, 18, 79, 25, 208, 83, 100)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PackageConfig"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64_value_aux_0),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value),LEAN_SCALAR_PTR_LITERAL(14, 50, 33, 106, 4, 142, 225, 217)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "pkgConfig"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65_value),LEAN_SCALAR_PTR_LITERAL(84, 166, 20, 31, 6, 123, 63, 83)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__67 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__67_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__1_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__1_value),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 152, 205, 91, 21, 95, 180)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2_value),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(20, 230, 244, 102, 183, 225, 161, 156)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Package"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3_value),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 143, 146, 89, 89, 182, 160, 217)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(34, 23, 98, 66, 226, 155, 63, 223)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6_value),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(178, 95, 147, 209, 102, 192, 116, 165)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7_value),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(49, 159, 150, 51, 73, 206, 68, 246)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "elabPackageCommand"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(91, 182, 15, 92, 163, 165, 162, 240)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___boxed(lean_object*);
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "postUpdateDecl"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__0 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_1),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 217, 106, 51, 176, 161, 152, 100)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "ill-formed post_update declaration"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "postUpdateHook"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(245, 119, 73, 252, 84, 37, 44, 204)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "PostUpdateHookDecl"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(9, 155, 11, 76, 182, 116, 206, 79)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value_aux_0),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(197, 83, 199, 129, 62, 183, 64, 19)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pkg"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12_value),LEAN_SCALAR_PTR_LITERAL(72, 34, 106, 28, 91, 254, 136, 225)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "fn"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15_value),LEAN_SCALAR_PTR_LITERAL(187, 167, 219, 45, 179, 169, 243, 14)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 13, .m_data = "«post_update»"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21_value;
static lean_once_cell_t l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "post_update"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23_value),LEAN_SCALAR_PTR_LITERAL(27, 22, 136, 29, 51, 248, 173, 13)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "declValDo"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__25 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__25_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_1),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__25_value),LEAN_SCALAR_PTR_LITERAL(253, 210, 120, 194, 116, 135, 247, 152)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_2),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_1),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_2),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value;
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_0),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_1),((lean_object*)&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_2),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expandPostUpdateDecl"};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 35, 84, 82, 64, 76, 215, 87)}};
static const lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(lean_object* v___y_1_){
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
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg___boxed(lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_8_);
lean_dec(v___y_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2(lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___boxed(lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2(v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Lean_Elab_Command_getRef___redArg(v___y_19_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_32_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_32_ == 0)
{
v___x_25_ = v___x_22_;
v_isShared_26_ = v_isSharedCheck_32_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v___x_22_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_32_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_30_; 
v___x_27_ = 0;
v___x_28_ = l_Lean_SourceInfo_fromRef(v_a_23_, v___x_27_);
lean_dec(v_a_23_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 0, v___x_28_);
v___x_30_ = v___x_25_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___x_28_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
else
{
lean_object* v_a_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_40_; 
v_a_33_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_40_ == 0)
{
v___x_35_ = v___x_22_;
v_isShared_36_ = v_isSharedCheck_40_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_a_33_);
lean_dec(v___x_22_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_40_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_38_; 
if (v_isShared_36_ == 0)
{
v___x_38_ = v___x_35_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_a_33_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0___boxed(lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_41_, v___y_42_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_44_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_45_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_48_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_49_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
lean_ctor_set(v___x_51_, 2, v___x_50_);
lean_ctor_set(v___x_51_, 3, v___x_50_);
lean_ctor_set(v___x_51_, 4, v___x_49_);
lean_ctor_set(v___x_51_, 5, v___x_49_);
lean_ctor_set(v___x_51_, 6, v___x_49_);
lean_ctor_set(v___x_51_, 7, v___x_49_);
lean_ctor_set(v___x_51_, 8, v___x_49_);
lean_ctor_set(v___x_51_, 9, v___x_49_);
lean_ctor_set(v___x_51_, 10, v___x_49_);
lean_ctor_set(v___x_51_, 11, v___x_48_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_unsigned_to_nat(32u);
v___x_53_ = lean_mk_empty_array_with_capacity(v___x_52_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_55_ = ((size_t)5ULL);
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = lean_unsigned_to_nat(32u);
v___x_58_ = lean_mk_empty_array_with_capacity(v___x_57_);
v___x_59_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_60_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___x_58_);
lean_ctor_set(v___x_60_, 2, v___x_56_);
lean_ctor_set(v___x_60_, 3, v___x_56_);
lean_ctor_set_usize(v___x_60_, 4, v___x_55_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_box(1);
v___x_62_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4);
v___x_63_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_64_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
lean_ctor_set(v___x_64_, 2, v___x_61_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; lean_object* v_env_69_; uint8_t v___x_70_; lean_object* v_env_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v_scopes_74_; lean_object* v___x_75_; lean_object* v_opts_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_68_ = lean_st_ref_get(v___y_66_);
v_env_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc_ref(v_env_69_);
lean_dec(v___x_68_);
v___x_70_ = 0;
v_env_71_ = l_Lean_Environment_setRecordingDeps(v_env_69_, v___x_70_);
v___x_72_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_73_ = lean_st_ref_get(v___y_66_);
v_scopes_74_ = lean_ctor_get(v___x_73_, 2);
lean_inc(v_scopes_74_);
lean_dec(v___x_73_);
v___x_75_ = l_List_head_x21___redArg(v___x_72_, v_scopes_74_);
lean_dec(v_scopes_74_);
v_opts_76_ = lean_ctor_get(v___x_75_, 1);
lean_inc_ref(v_opts_76_);
lean_dec(v___x_75_);
v___x_77_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_78_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5);
v___x_79_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_79_, 0, v_env_71_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
lean_ctor_set(v___x_79_, 2, v___x_78_);
lean_ctor_set(v___x_79_, 3, v_opts_76_);
v___x_80_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v_msgData_65_);
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msgData_82_, v___y_83_);
lean_dec(v___y_83_);
return v_res_85_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_box(1);
v___x_87_ = l_Lean_MessageData_ofFormat(v___x_86_);
return v___x_87_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__2));
v___x_92_ = l_Lean_MessageData_ofFormat(v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6(lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
if (lean_obj_tag(v_x_94_) == 0)
{
return v_x_93_;
}
else
{
lean_object* v_head_95_; lean_object* v_tail_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_118_; 
v_head_95_ = lean_ctor_get(v_x_94_, 0);
v_tail_96_ = lean_ctor_get(v_x_94_, 1);
v_isSharedCheck_118_ = !lean_is_exclusive(v_x_94_);
if (v_isSharedCheck_118_ == 0)
{
v___x_98_ = v_x_94_;
v_isShared_99_ = v_isSharedCheck_118_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_tail_96_);
lean_inc(v_head_95_);
lean_dec(v_x_94_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_118_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v_before_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_116_; 
v_before_100_ = lean_ctor_get(v_head_95_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v_head_95_);
if (v_isSharedCheck_116_ == 0)
{
lean_object* v_unused_117_; 
v_unused_117_ = lean_ctor_get(v_head_95_, 1);
lean_dec(v_unused_117_);
v___x_102_ = v_head_95_;
v_isShared_103_ = v_isSharedCheck_116_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_before_100_);
lean_dec(v_head_95_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_116_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_104_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0);
if (v_isShared_103_ == 0)
{
lean_ctor_set_tag(v___x_102_, 7);
lean_ctor_set(v___x_102_, 1, v___x_104_);
lean_ctor_set(v___x_102_, 0, v_x_93_);
v___x_106_ = v___x_102_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_x_93_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v___x_104_);
v___x_106_ = v_reuseFailAlloc_115_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3);
if (v_isShared_99_ == 0)
{
lean_ctor_set_tag(v___x_98_, 7);
lean_ctor_set(v___x_98_, 1, v___x_107_);
lean_ctor_set(v___x_98_, 0, v___x_106_);
v___x_109_ = v___x_98_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_106_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v___x_107_);
v___x_109_ = v_reuseFailAlloc_114_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = l_Lean_MessageData_ofSyntax(v_before_100_);
v___x_111_ = l_Lean_indentD(v___x_110_);
v___x_112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_109_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v_x_93_ = v___x_112_;
v_x_94_ = v_tail_96_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5(lean_object* v_opts_119_, lean_object* v_opt_120_){
_start:
{
lean_object* v_name_121_; lean_object* v_defValue_122_; lean_object* v_map_123_; lean_object* v___x_124_; 
v_name_121_ = lean_ctor_get(v_opt_120_, 0);
v_defValue_122_ = lean_ctor_get(v_opt_120_, 1);
v_map_123_ = lean_ctor_get(v_opts_119_, 0);
v___x_124_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_123_, v_name_121_);
if (lean_obj_tag(v___x_124_) == 0)
{
uint8_t v___x_125_; 
v___x_125_ = lean_unbox(v_defValue_122_);
return v___x_125_;
}
else
{
lean_object* v_val_126_; 
v_val_126_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_val_126_);
lean_dec_ref_known(v___x_124_, 1);
if (lean_obj_tag(v_val_126_) == 1)
{
uint8_t v_v_127_; 
v_v_127_ = lean_ctor_get_uint8(v_val_126_, 0);
lean_dec_ref_known(v_val_126_, 0);
return v_v_127_;
}
else
{
uint8_t v___x_128_; 
lean_dec(v_val_126_);
v___x_128_ = lean_unbox(v_defValue_122_);
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5___boxed(lean_object* v_opts_129_, lean_object* v_opt_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5(v_opts_129_, v_opt_130_);
lean_dec_ref(v_opt_130_);
lean_dec_ref(v_opts_129_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_137_ = l_Lean_MessageData_ofFormat(v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_138_, lean_object* v_macroStack_139_, lean_object* v___y_140_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v_scopes_144_; lean_object* v___x_145_; lean_object* v_opts_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_142_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_143_ = lean_st_ref_get(v___y_140_);
v_scopes_144_ = lean_ctor_get(v___x_143_, 2);
lean_inc(v_scopes_144_);
lean_dec(v___x_143_);
v___x_145_ = l_List_head_x21___redArg(v___x_142_, v_scopes_144_);
lean_dec(v_scopes_144_);
v_opts_146_ = lean_ctor_get(v___x_145_, 1);
lean_inc_ref(v_opts_146_);
lean_dec(v___x_145_);
v___x_147_ = l_Lean_Elab_pp_macroStack;
v___x_148_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5(v_opts_146_, v___x_147_);
lean_dec_ref(v_opts_146_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; 
lean_dec(v_macroStack_139_);
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v_msgData_138_);
return v___x_149_;
}
else
{
if (lean_obj_tag(v_macroStack_139_) == 0)
{
lean_object* v___x_150_; 
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v_msgData_138_);
return v___x_150_;
}
else
{
lean_object* v_head_151_; lean_object* v_after_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_167_; 
v_head_151_ = lean_ctor_get(v_macroStack_139_, 0);
lean_inc(v_head_151_);
v_after_152_ = lean_ctor_get(v_head_151_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v_head_151_);
if (v_isSharedCheck_167_ == 0)
{
lean_object* v_unused_168_; 
v_unused_168_ = lean_ctor_get(v_head_151_, 0);
lean_dec(v_unused_168_);
v___x_154_ = v_head_151_;
v_isShared_155_ = v_isSharedCheck_167_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_after_152_);
lean_dec(v_head_151_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_167_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_156_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0);
if (v_isShared_155_ == 0)
{
lean_ctor_set_tag(v___x_154_, 7);
lean_ctor_set(v___x_154_, 1, v___x_156_);
lean_ctor_set(v___x_154_, 0, v_msgData_138_);
v___x_158_ = v___x_154_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_msgData_138_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v___x_156_);
v___x_158_ = v_reuseFailAlloc_166_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v_msgData_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_159_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_158_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = l_Lean_MessageData_ofSyntax(v_after_152_);
v___x_162_ = l_Lean_indentD(v___x_161_);
v_msgData_163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_163_, 0, v___x_160_);
lean_ctor_set(v_msgData_163_, 1, v___x_162_);
v___x_164_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6(v_msgData_163_, v_macroStack_139_);
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_169_, lean_object* v_macroStack_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_msgData_169_, v_macroStack_170_, v___y_171_);
lean_dec(v___y_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(lean_object* v_msg_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Elab_Command_getRef___redArg(v___y_175_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v_macroStack_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v_a_183_; lean_object* v___x_184_; lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_193_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
v_macroStack_180_ = lean_ctor_get(v___y_175_, 4);
v___x_181_ = l_Lean_Elab_getBetterRef(v_a_179_, v_macroStack_180_);
lean_dec(v_a_179_);
v___x_182_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msg_174_, v___y_176_);
v_a_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_a_183_);
lean_dec_ref(v___x_182_);
lean_inc(v_macroStack_180_);
v___x_184_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_a_183_, v_macroStack_180_, v___y_176_);
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_193_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_181_);
lean_ctor_set(v___x_189_, 1, v_a_185_);
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 1);
lean_ctor_set(v___x_187_, 0, v___x_189_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
else
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
lean_dec_ref(v_msg_174_);
v_a_194_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_178_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_178_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg___boxed(lean_object* v_msg_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(lean_object* v_ref_207_, lean_object* v_msg_208_, lean_object* v___y_209_, lean_object* v___y_210_){
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
v___x_226_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_208_, v___x_225_, v___y_210_);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg___boxed(lean_object* v_ref_235_, lean_object* v_msg_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_ref_235_, v_msg_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v_ref_235_);
return v_res_240_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4(void){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Array_mkArray0___redArg();
return v___x_246_;
}
}
static lean_object* _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23));
v___x_275_ = l_Lean_stringToMessageData(v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(lean_object* v_tyName_303_, lean_object* v_id_304_, lean_object* v_ty_305_, lean_object* v_config_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___x_395_; lean_object* v_whereInfo_397_; lean_object* v_fs_398_; lean_object* v_wds_x3f_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_395_ = l_Lake_PackageConfig_instConfigInfo;
v___x_428_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22));
lean_inc(v_config_306_);
v___x_429_ = l_Lean_Syntax_isOfKind(v_config_306_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_430_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_431_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_430_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = l_Lean_Syntax_getArg(v_config_306_, v___x_432_);
lean_inc(v___x_433_);
v___x_434_ = l_Lean_Syntax_matchesNull(v___x_433_, v___x_432_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_433_);
v___x_436_ = l_Lean_Syntax_matchesNull(v___x_433_, v___x_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec(v___x_433_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_437_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_438_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_437_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_438_;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_439_ = l_Lean_Syntax_getArg(v___x_433_, v___x_432_);
lean_dec(v___x_433_);
v___x_440_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26));
lean_inc(v___x_439_);
v___x_441_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28));
lean_inc(v___x_439_);
v___x_443_ = l_Lean_Syntax_isOfKind(v___x_439_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; 
lean_dec(v___x_439_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_444_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_445_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_444_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_445_;
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_446_ = l_Lean_Syntax_getArg(v___x_439_, v___x_432_);
v___x_447_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30));
lean_inc(v___x_446_);
v___x_448_ = l_Lean_Syntax_isOfKind(v___x_446_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; 
lean_dec(v___x_446_);
lean_dec(v___x_439_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_449_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_450_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_449_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_450_;
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_451_ = l_Lean_Syntax_getArg(v___x_446_, v___x_435_);
v___x_452_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32));
lean_inc(v___x_451_);
v___x_453_ = l_Lean_Syntax_isOfKind(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec(v___x_451_);
lean_dec(v___x_446_);
lean_dec(v___x_439_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_454_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_455_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_454_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_455_;
}
else
{
lean_object* v_tk_456_; lean_object* v___x_457_; lean_object* v_wds_x3f_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___x_465_; uint8_t v___x_466_; 
v_tk_456_ = l_Lean_Syntax_getArg(v___x_446_, v___x_432_);
lean_dec(v___x_446_);
v___x_457_ = l_Lean_Syntax_getArg(v___x_451_, v___x_432_);
lean_dec(v___x_451_);
v___x_465_ = l_Lean_Syntax_getArg(v___x_439_, v___x_435_);
lean_dec(v___x_439_);
v___x_466_ = l_Lean_Syntax_isNone(v___x_465_);
if (v___x_466_ == 0)
{
uint8_t v___x_467_; 
lean_inc(v___x_465_);
v___x_467_ = l_Lean_Syntax_matchesNull(v___x_465_, v___x_435_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec(v___x_465_);
lean_dec(v___x_457_);
lean_dec(v_tk_456_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_468_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_469_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_468_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_469_;
}
else
{
lean_object* v_wds_x3f_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v_wds_x3f_470_ = l_Lean_Syntax_getArg(v___x_465_, v___x_432_);
lean_dec(v___x_465_);
v___x_471_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_470_);
v___x_472_ = l_Lean_Syntax_isOfKind(v_wds_x3f_470_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec(v_wds_x3f_470_);
lean_dec(v___x_457_);
lean_dec(v_tk_456_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_473_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_474_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_473_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_474_;
}
else
{
lean_object* v___x_475_; 
v___x_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_475_, 0, v_wds_x3f_470_);
v_wds_x3f_459_ = v___x_475_;
v___y_460_ = v_a_307_;
v___y_461_ = v_a_308_;
goto v___jp_458_;
}
}
}
else
{
lean_object* v___x_476_; 
lean_dec(v___x_465_);
v___x_476_ = lean_box(0);
v_wds_x3f_459_ = v___x_476_;
v___y_460_ = v_a_307_;
v___y_461_ = v_a_308_;
goto v___jp_458_;
}
v___jp_458_:
{
lean_object* v_fs_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_fs_462_ = l_Lean_Syntax_getArgs(v___x_457_);
lean_dec(v___x_457_);
v___x_463_ = l_Lean_Syntax_getHeadInfo(v_tk_456_);
lean_dec(v_tk_456_);
v___x_464_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_462_);
lean_dec_ref(v_fs_462_);
v_whereInfo_397_ = v___x_463_;
v_fs_398_ = v___x_464_;
v_wds_x3f_399_ = v_wds_x3f_459_;
v___y_400_ = v___y_460_;
v___y_401_ = v___y_461_;
goto v___jp_396_;
}
}
}
}
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_477_ = l_Lean_Syntax_getArg(v___x_439_, v___x_435_);
v___x_478_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32));
lean_inc(v___x_477_);
v___x_479_ = l_Lean_Syntax_isOfKind(v___x_477_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v___x_477_);
lean_dec(v___x_439_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_480_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_481_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_480_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_481_;
}
else
{
lean_object* v_tk_482_; lean_object* v___x_483_; lean_object* v_wds_x3f_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_tk_482_ = l_Lean_Syntax_getArg(v___x_439_, v___x_432_);
v___x_483_ = l_Lean_Syntax_getArg(v___x_477_, v___x_432_);
lean_dec(v___x_477_);
v___x_491_ = lean_unsigned_to_nat(2u);
v___x_492_ = l_Lean_Syntax_getArg(v___x_439_, v___x_491_);
lean_dec(v___x_439_);
v___x_493_ = l_Lean_Syntax_isNone(v___x_492_);
if (v___x_493_ == 0)
{
uint8_t v___x_494_; 
lean_inc(v___x_492_);
v___x_494_ = l_Lean_Syntax_matchesNull(v___x_492_, v___x_435_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; 
lean_dec(v___x_492_);
lean_dec(v___x_483_);
lean_dec(v_tk_482_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_495_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_496_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_495_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_496_;
}
else
{
lean_object* v_wds_x3f_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_wds_x3f_497_ = l_Lean_Syntax_getArg(v___x_492_, v___x_432_);
lean_dec(v___x_492_);
v___x_498_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_497_);
v___x_499_ = l_Lean_Syntax_isOfKind(v_wds_x3f_497_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec(v_wds_x3f_497_);
lean_dec(v___x_483_);
lean_dec(v_tk_482_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_500_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_501_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_500_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_501_;
}
else
{
lean_object* v___x_502_; 
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v_wds_x3f_497_);
v_wds_x3f_485_ = v___x_502_;
v___y_486_ = v_a_307_;
v___y_487_ = v_a_308_;
goto v___jp_484_;
}
}
}
else
{
lean_object* v___x_503_; 
lean_dec(v___x_492_);
v___x_503_ = lean_box(0);
v_wds_x3f_485_ = v___x_503_;
v___y_486_ = v_a_307_;
v___y_487_ = v_a_308_;
goto v___jp_484_;
}
v___jp_484_:
{
lean_object* v_fs_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_fs_488_ = l_Lean_Syntax_getArgs(v___x_483_);
lean_dec(v___x_483_);
v___x_489_ = l_Lean_Syntax_getHeadInfo(v_tk_482_);
lean_dec(v_tk_482_);
v___x_490_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_488_);
lean_dec_ref(v_fs_488_);
v_whereInfo_397_ = v___x_489_;
v_fs_398_ = v___x_490_;
v_wds_x3f_399_ = v_wds_x3f_485_;
v___y_400_ = v___y_486_;
v___y_401_ = v___y_487_;
goto v___jp_396_;
}
}
}
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec(v___x_433_);
v___x_504_ = lean_box(2);
v___x_505_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8));
v___x_506_ = lean_box(0);
v_whereInfo_397_ = v___x_504_;
v_fs_398_ = v___x_505_;
v_wds_x3f_399_ = v___x_506_;
v___y_400_ = v_a_307_;
v___y_401_ = v_a_308_;
goto v___jp_396_;
}
}
v___jp_310_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_319_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0));
lean_inc_ref_n(v___y_313_, 5);
lean_inc_ref_n(v___y_315_, 6);
lean_inc_ref_n(v___y_314_, 6);
v___x_320_ = l_Lean_Name_mkStr4(v___y_314_, v___y_315_, v___y_313_, v___x_319_);
v___x_321_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1));
v___x_322_ = l_Lean_Name_mkStr4(v___y_314_, v___y_315_, v___y_313_, v___x_321_);
v___x_323_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_324_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
lean_inc_n(v___y_311_, 8);
v___x_325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_325_, 0, v___y_311_);
lean_ctor_set(v___x_325_, 1, v___x_323_);
lean_ctor_set(v___x_325_, 2, v___x_324_);
lean_inc_ref_n(v___x_325_, 8);
v___x_326_ = l_Lean_Syntax_node7(v___y_311_, v___x_322_, v___x_325_, v___x_325_, v___x_325_, v___x_325_, v___x_325_, v___x_325_, v___x_325_);
v___x_327_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5));
v___x_328_ = l_Lean_Name_mkStr4(v___y_314_, v___y_315_, v___y_313_, v___x_327_);
v___x_329_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6));
v___x_330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_330_, 0, v___y_311_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7));
v___x_332_ = l_Lean_Name_mkStr4(v___y_314_, v___y_315_, v___y_313_, v___x_331_);
v___x_333_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8));
lean_inc_n(v___y_318_, 2);
v___x_334_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_334_, 0, v___y_318_);
lean_ctor_set(v___x_334_, 1, v___x_323_);
lean_ctor_set(v___x_334_, 2, v___x_333_);
v___x_335_ = lean_unsigned_to_nat(2u);
v___x_336_ = lean_mk_empty_array_with_capacity(v___x_335_);
v___x_337_ = lean_array_push(v___x_336_, v_id_304_);
v___x_338_ = lean_array_push(v___x_337_, v___x_334_);
v___x_339_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_339_, 0, v___y_318_);
lean_ctor_set(v___x_339_, 1, v___x_332_);
lean_ctor_set(v___x_339_, 2, v___x_338_);
v___x_340_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9));
v___x_341_ = l_Lean_Name_mkStr4(v___y_314_, v___y_315_, v___y_313_, v___x_340_);
v___x_342_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10));
v___x_343_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11));
v___x_344_ = l_Lean_Name_mkStr4(v___y_314_, v___y_315_, v___x_342_, v___x_343_);
v___x_345_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12));
v___x_346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_346_, 0, v___y_311_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = l_Lean_Syntax_node2(v___y_311_, v___x_344_, v___x_346_, v_ty_305_);
v___x_348_ = l_Lean_Syntax_node1(v___y_311_, v___x_323_, v___x_347_);
v___x_349_ = l_Lean_Syntax_node2(v___y_311_, v___x_341_, v___x_325_, v___x_348_);
v___x_350_ = l_Lean_Syntax_node5(v___y_311_, v___x_328_, v___x_330_, v___x_339_, v___x_349_, v___y_317_, v___x_325_);
v___x_351_ = l_Lean_Syntax_node2(v___y_311_, v___x_320_, v___x_326_, v___x_350_);
lean_inc(v___x_351_);
v___x_352_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_352_, 0, v___x_351_);
v___x_353_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_config_306_, v___x_351_, v___x_352_, v___y_316_, v___y_312_);
return v___x_353_;
}
v___jp_354_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_364_ = l_Lean_mkOptionalNode(v___y_363_);
v___x_365_ = lean_unsigned_to_nat(3u);
v___x_366_ = lean_mk_empty_array_with_capacity(v___x_365_);
v___x_367_ = lean_array_push(v___x_366_, v___y_358_);
v___x_368_ = lean_array_push(v___x_367_, v___y_355_);
v___x_369_ = lean_array_push(v___x_368_, v___x_364_);
v___x_370_ = lean_box(2);
lean_inc(v___y_360_);
v___x_371_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v___y_360_);
lean_ctor_set(v___x_371_, 2, v___x_369_);
v___x_372_ = l_Lean_Elab_Command_getRef___redArg(v___y_362_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_373_);
lean_dec_ref_known(v___x_372_, 1);
v___x_374_ = 0;
v___x_375_ = l_Lean_SourceInfo_fromRef(v_a_373_, v___x_374_);
lean_dec(v_a_373_);
v___x_376_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_362_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_quotContext_x3f_377_; 
lean_dec_ref_known(v___x_376_, 1);
v_quotContext_x3f_377_ = lean_ctor_get(v___y_362_, 5);
if (lean_obj_tag(v_quotContext_x3f_377_) == 0)
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_357_);
lean_dec_ref(v___x_378_);
v___y_311_ = v___x_375_;
v___y_312_ = v___y_357_;
v___y_313_ = v___y_356_;
v___y_314_ = v___y_359_;
v___y_315_ = v___y_361_;
v___y_316_ = v___y_362_;
v___y_317_ = v___x_371_;
v___y_318_ = v___x_370_;
goto v___jp_310_;
}
else
{
v___y_311_ = v___x_375_;
v___y_312_ = v___y_357_;
v___y_313_ = v___y_356_;
v___y_314_ = v___y_359_;
v___y_315_ = v___y_361_;
v___y_316_ = v___y_362_;
v___y_317_ = v___x_371_;
v___y_318_ = v___x_370_;
goto v___jp_310_;
}
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
lean_dec(v___x_375_);
lean_dec_ref_known(v___x_371_, 3);
lean_dec(v_config_306_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
v_a_379_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_376_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_376_);
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
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec_ref_known(v___x_371_, 3);
lean_dec(v_config_306_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
v_a_387_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_372_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_372_);
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
v___jp_396_:
{
lean_object* v_fieldMap_402_; lean_object* v___x_403_; lean_object* v_whereTk_404_; lean_object* v___x_405_; 
v_fieldMap_402_ = lean_ctor_get(v___x_395_, 1);
v___x_403_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13));
v_whereTk_404_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_whereTk_404_, 0, v_whereInfo_397_);
lean_ctor_set(v_whereTk_404_, 1, v___x_403_);
v___x_405_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(v_tyName_303_, v_fieldMap_402_, v_fs_398_, v___y_400_, v___y_401_);
lean_dec_ref(v_fs_398_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_405_, 1);
v___x_407_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_408_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_409_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_410_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18));
if (lean_obj_tag(v_wds_x3f_399_) == 0)
{
lean_object* v___x_411_; 
v___x_411_ = lean_box(0);
v___y_355_ = v_a_406_;
v___y_356_ = v___x_409_;
v___y_357_ = v___y_401_;
v___y_358_ = v_whereTk_404_;
v___y_359_ = v___x_407_;
v___y_360_ = v___x_410_;
v___y_361_ = v___x_408_;
v___y_362_ = v___y_400_;
v___y_363_ = v___x_411_;
goto v___jp_354_;
}
else
{
lean_object* v_val_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_val_412_ = lean_ctor_get(v_wds_x3f_399_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v_wds_x3f_399_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v_wds_x3f_399_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_val_412_);
lean_dec(v_wds_x3f_399_);
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
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_val_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
v___y_355_ = v_a_406_;
v___y_356_ = v___x_409_;
v___y_357_ = v___y_401_;
v___y_358_ = v_whereTk_404_;
v___y_359_ = v___x_407_;
v___y_360_ = v___x_410_;
v___y_361_ = v___x_408_;
v___y_362_ = v___y_400_;
v___y_363_ = v___x_417_;
goto v___jp_354_;
}
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec_ref_known(v_whereTk_404_, 2);
lean_dec(v_wds_x3f_399_);
lean_dec(v_config_306_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
v_a_420_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_405_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_405_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___boxed(lean_object* v_tyName_507_, lean_object* v_id_508_, lean_object* v_ty_509_, lean_object* v_config_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(v_tyName_507_, v_id_508_, v_ty_509_, v_config_510_, v_a_511_, v_a_512_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
return v_res_514_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13));
v___x_537_ = l_Lean_stringToMessageData(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20));
v___x_547_ = l_String_toRawSubstring_x27(v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35));
v___x_570_ = l_String_toRawSubstring_x27(v___x_569_);
return v___x_570_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41));
v___x_578_ = l_String_toRawSubstring_x27(v___x_577_);
return v___x_578_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44));
v___x_583_ = l_String_toRawSubstring_x27(v___x_582_);
return v___x_583_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47));
v___x_588_ = l_String_toRawSubstring_x27(v___x_587_);
return v___x_588_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56));
v___x_599_ = l_String_toRawSubstring_x27(v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65));
v___x_615_ = l_String_toRawSubstring_x27(v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand(lean_object* v_stx_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_690_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12));
lean_inc(v_stx_618_);
v___x_691_ = l_Lean_Syntax_isOfKind(v_stx_618_, v___x_690_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14);
v___x_693_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_stx_618_, v___x_692_, v_a_619_, v_a_620_);
lean_dec(v_stx_618_);
return v___x_693_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; uint8_t v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; uint8_t v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v_a_829_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; uint8_t v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v_a_862_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; uint8_t v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v_a_961_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; uint8_t v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; uint8_t v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v_a_1074_; lean_object* v_kw_1101_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v_nameStx_x3f_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___x_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = lean_box(0);
v___x_696_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15));
v___x_697_ = l_Lean_Syntax_getArg(v_stx_618_, v___x_694_);
v___x_698_ = lean_unsigned_to_nat(1u);
v___x_699_ = l_Lean_Syntax_getArg(v_stx_618_, v___x_698_);
v___x_700_ = lean_unsigned_to_nat(2u);
v_kw_1101_ = l_Lean_Syntax_getArg(v_stx_618_, v___x_700_);
v___x_1189_ = lean_unsigned_to_nat(3u);
v___x_1190_ = l_Lean_Syntax_getArg(v_stx_618_, v___x_1189_);
v___x_1191_ = l_Lean_Syntax_isNone(v___x_1190_);
if (v___x_1191_ == 0)
{
uint8_t v___x_1192_; 
lean_inc(v___x_1190_);
v___x_1192_ = l_Lean_Syntax_matchesNull(v___x_1190_, v___x_698_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec(v___x_1190_);
lean_dec(v_kw_1101_);
lean_dec(v___x_699_);
lean_dec(v___x_697_);
v___x_1193_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14);
v___x_1194_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_stx_618_, v___x_1193_, v_a_619_, v_a_620_);
lean_dec(v_stx_618_);
return v___x_1194_;
}
else
{
lean_object* v_nameStx_x3f_1195_; lean_object* v___x_1196_; 
v_nameStx_x3f_1195_ = l_Lean_Syntax_getArg(v___x_1190_, v___x_694_);
lean_dec(v___x_1190_);
v___x_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1196_, 0, v_nameStx_x3f_1195_);
v_nameStx_x3f_1174_ = v___x_1196_;
v___y_1175_ = v_a_619_;
v___y_1176_ = v_a_620_;
goto v___jp_1173_;
}
}
else
{
lean_object* v___x_1197_; 
lean_dec(v___x_1190_);
v___x_1197_ = lean_box(0);
v_nameStx_x3f_1174_ = v___x_1197_;
v___y_1175_ = v_a_619_;
v___y_1176_ = v_a_620_;
goto v___jp_1173_;
}
v___jp_701_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
lean_inc_ref_n(v___y_707_, 3);
v___x_728_ = l_Array_append___redArg(v___y_707_, v___y_727_);
lean_dec_ref(v___y_727_);
lean_inc_n(v___y_712_, 6);
lean_inc_n(v___y_709_, 18);
v___x_729_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_729_, 0, v___y_709_);
lean_ctor_set(v___x_729_, 1, v___y_712_);
lean_ctor_set(v___x_729_, 2, v___x_728_);
v___x_730_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16));
lean_inc_ref(v___y_703_);
lean_inc_ref_n(v___y_715_, 6);
lean_inc_ref_n(v___y_713_, 7);
v___x_731_ = l_Lean_Name_mkStr4(v___y_713_, v___y_715_, v___y_703_, v___x_730_);
v___x_732_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17));
v___x_733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_733_, 0, v___y_709_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
lean_inc_ref(v___y_717_);
v___x_734_ = l_Lean_Syntax_SepArray_ofElems(v___y_717_, v___y_719_);
lean_dec_ref(v___y_719_);
v___x_735_ = l_Array_append___redArg(v___y_707_, v___x_734_);
lean_dec_ref(v___x_734_);
v___x_736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_736_, 0, v___y_709_);
lean_ctor_set(v___x_736_, 1, v___y_712_);
lean_ctor_set(v___x_736_, 2, v___x_735_);
v___x_737_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18));
v___x_738_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_738_, 0, v___y_709_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
lean_inc(v___x_731_);
v___x_739_ = l_Lean_Syntax_node3(v___y_709_, v___x_731_, v___x_733_, v___x_736_, v___x_738_);
v___x_740_ = l_Lean_Syntax_node1(v___y_709_, v___y_712_, v___x_739_);
v___x_741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_741_, 0, v___y_709_);
lean_ctor_set(v___x_741_, 1, v___y_712_);
lean_ctor_set(v___x_741_, 2, v___y_707_);
lean_inc_ref_n(v___x_741_, 8);
lean_inc(v___y_711_);
v___x_742_ = l_Lean_Syntax_node7(v___y_709_, v___y_711_, v___x_729_, v___x_740_, v___x_741_, v___x_741_, v___x_741_, v___x_741_, v___x_741_);
v___x_743_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19));
lean_inc_ref_n(v___y_714_, 3);
v___x_744_ = l_Lean_Name_mkStr4(v___y_713_, v___y_715_, v___y_714_, v___x_743_);
v___x_745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_745_, 0, v___y_709_);
lean_ctor_set(v___x_745_, 1, v___x_743_);
v___x_746_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7));
v___x_747_ = l_Lean_Name_mkStr4(v___y_713_, v___y_715_, v___y_714_, v___x_746_);
v___x_748_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8));
lean_inc_n(v___y_721_, 2);
v___x_749_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_749_, 0, v___y_721_);
lean_ctor_set(v___x_749_, 1, v___y_712_);
lean_ctor_set(v___x_749_, 2, v___x_748_);
v___x_750_ = lean_mk_empty_array_with_capacity(v___x_700_);
lean_inc(v___y_710_);
lean_inc_ref(v___x_750_);
v___x_751_ = lean_array_push(v___x_750_, v___y_710_);
lean_inc_ref(v___x_749_);
v___x_752_ = lean_array_push(v___x_751_, v___x_749_);
lean_inc(v___x_747_);
v___x_753_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_753_, 0, v___y_721_);
lean_ctor_set(v___x_753_, 1, v___x_747_);
lean_ctor_set(v___x_753_, 2, v___x_752_);
v___x_754_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9));
v___x_755_ = l_Lean_Name_mkStr4(v___y_713_, v___y_715_, v___y_714_, v___x_754_);
v___x_756_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11));
v___x_757_ = l_Lean_Name_mkStr4(v___y_713_, v___y_715_, v___y_703_, v___x_756_);
v___x_758_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12));
v___x_759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_759_, 0, v___y_709_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21);
v___x_761_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22));
v___x_762_ = l_Lean_addMacroScope(v___y_716_, v___x_761_, v___y_706_);
v___x_763_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24));
v___x_764_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25));
lean_inc(v___y_702_);
v___x_765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___y_702_);
v___x_766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_763_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_767_, 0, v___y_709_);
lean_ctor_set(v___x_767_, 1, v___x_760_);
lean_ctor_set(v___x_767_, 2, v___x_762_);
lean_ctor_set(v___x_767_, 3, v___x_766_);
v___x_768_ = l_Lean_Syntax_node2(v___y_709_, v___x_757_, v___x_759_, v___x_767_);
v___x_769_ = l_Lean_Syntax_node1(v___y_709_, v___y_712_, v___x_768_);
lean_inc(v___x_755_);
v___x_770_ = l_Lean_Syntax_node2(v___y_709_, v___x_755_, v___x_741_, v___x_769_);
v___x_771_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26));
v___x_772_ = l_Lean_Name_mkStr4(v___y_713_, v___y_715_, v___y_714_, v___x_771_);
lean_inc_ref(v___y_720_);
v___x_773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_773_, 0, v___y_709_);
lean_ctor_set(v___x_773_, 1, v___y_720_);
v___x_774_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27));
v___x_775_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___x_776_ = l_Lean_Name_mkStr4(v___y_713_, v___y_715_, v___x_774_, v___x_775_);
lean_inc(v___x_776_);
v___x_777_ = l_Lean_Syntax_node2(v___y_709_, v___x_776_, v___x_741_, v___x_741_);
lean_inc(v___x_772_);
v___x_778_ = l_Lean_Syntax_node4(v___y_709_, v___x_772_, v___x_773_, v___y_704_, v___x_777_, v___x_741_);
lean_inc(v___x_744_);
v___x_779_ = l_Lean_Syntax_node4(v___y_709_, v___x_744_, v___x_745_, v___x_753_, v___x_770_, v___x_778_);
lean_inc(v___y_725_);
v___x_780_ = l_Lean_Syntax_node2(v___y_709_, v___y_725_, v___x_742_, v___x_779_);
lean_inc(v___x_780_);
v___x_781_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_781_, 0, v___x_780_);
v___x_782_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_stx_618_, v___x_780_, v___x_781_, v___y_705_, v___y_718_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
lean_dec_ref_known(v___x_782_, 1);
v___x_783_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29));
v___x_784_ = l_Lean_Name_str___override(v___y_722_, v___x_783_);
v___x_785_ = l_Lean_mkIdentFrom(v___y_710_, v___x_784_, v___y_708_);
lean_dec(v___y_710_);
v___x_786_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_705_, v___y_718_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_788_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_786_, 1);
v___x_788_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_705_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_dec_ref_known(v___x_788_, 1);
if (lean_obj_tag(v___y_724_) == 0)
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_718_);
lean_dec_ref(v___x_789_);
v___y_623_ = v___x_749_;
v___y_624_ = v___y_711_;
v___y_625_ = v___x_747_;
v___y_626_ = v___y_712_;
v___y_627_ = v___x_743_;
v___y_628_ = v___x_732_;
v___y_629_ = v___x_750_;
v___y_630_ = v___y_713_;
v___y_631_ = v___y_705_;
v___y_632_ = v___y_718_;
v___y_633_ = v___y_707_;
v___y_634_ = v___y_720_;
v___y_635_ = v___y_721_;
v___y_636_ = v___x_737_;
v___y_637_ = v___x_744_;
v___y_638_ = v___x_772_;
v___y_639_ = v___y_723_;
v___y_640_ = v_a_787_;
v___y_641_ = v___x_731_;
v___y_642_ = v___x_755_;
v___y_643_ = v___x_785_;
v___y_644_ = v___y_725_;
v___y_645_ = v___y_726_;
v___y_646_ = v___x_776_;
goto v___jp_622_;
}
else
{
lean_dec_ref_known(v___y_724_, 1);
v___y_623_ = v___x_749_;
v___y_624_ = v___y_711_;
v___y_625_ = v___x_747_;
v___y_626_ = v___y_712_;
v___y_627_ = v___x_743_;
v___y_628_ = v___x_732_;
v___y_629_ = v___x_750_;
v___y_630_ = v___y_713_;
v___y_631_ = v___y_705_;
v___y_632_ = v___y_718_;
v___y_633_ = v___y_707_;
v___y_634_ = v___y_720_;
v___y_635_ = v___y_721_;
v___y_636_ = v___x_737_;
v___y_637_ = v___x_744_;
v___y_638_ = v___x_772_;
v___y_639_ = v___y_723_;
v___y_640_ = v_a_787_;
v___y_641_ = v___x_731_;
v___y_642_ = v___x_755_;
v___y_643_ = v___x_785_;
v___y_644_ = v___y_725_;
v___y_645_ = v___y_726_;
v___y_646_ = v___x_776_;
goto v___jp_622_;
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec(v_a_787_);
lean_dec(v___x_785_);
lean_dec(v___x_776_);
lean_dec(v___x_772_);
lean_dec(v___x_755_);
lean_dec_ref(v___x_750_);
lean_dec_ref_known(v___x_749_, 3);
lean_dec(v___x_747_);
lean_dec(v___x_744_);
lean_dec(v___x_731_);
lean_dec(v___y_726_);
lean_dec(v___y_725_);
lean_dec(v___y_724_);
lean_dec(v___y_723_);
lean_dec(v___y_721_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_705_);
v_a_790_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_788_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_788_);
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
lean_dec(v___x_785_);
lean_dec(v___x_776_);
lean_dec(v___x_772_);
lean_dec(v___x_755_);
lean_dec_ref(v___x_750_);
lean_dec_ref_known(v___x_749_, 3);
lean_dec(v___x_747_);
lean_dec(v___x_744_);
lean_dec(v___x_731_);
lean_dec(v___y_726_);
lean_dec(v___y_725_);
lean_dec(v___y_724_);
lean_dec(v___y_723_);
lean_dec(v___y_721_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_705_);
v_a_798_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_786_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_786_);
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
else
{
lean_dec(v___x_776_);
lean_dec(v___x_772_);
lean_dec(v___x_755_);
lean_dec_ref(v___x_750_);
lean_dec_ref_known(v___x_749_, 3);
lean_dec(v___x_747_);
lean_dec(v___x_744_);
lean_dec(v___x_731_);
lean_dec(v___y_726_);
lean_dec(v___y_725_);
lean_dec(v___y_724_);
lean_dec(v___y_723_);
lean_dec(v___y_722_);
lean_dec(v___y_721_);
lean_dec(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_705_);
return v___x_782_;
}
}
v___jp_806_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_830_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_831_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0));
lean_inc_ref_n(v___y_813_, 2);
lean_inc_ref_n(v___y_812_, 2);
v___x_832_ = l_Lean_Name_mkStr4(v___y_812_, v___y_813_, v___x_830_, v___x_831_);
v___x_833_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1));
v___x_834_ = l_Lean_Name_mkStr4(v___y_812_, v___y_813_, v___x_830_, v___x_833_);
if (lean_obj_tag(v___y_807_) == 1)
{
lean_object* v_val_835_; lean_object* v___x_836_; 
v_val_835_ = lean_ctor_get(v___y_807_, 0);
lean_inc(v_val_835_);
lean_dec_ref_known(v___y_807_, 1);
v___x_836_ = l_Array_mkArray1___redArg(v_val_835_);
v___y_702_ = v___y_808_;
v___y_703_ = v___y_809_;
v___y_704_ = v___y_811_;
v___y_705_ = v___y_815_;
v___y_706_ = v___y_817_;
v___y_707_ = v___y_819_;
v___y_708_ = v___y_824_;
v___y_709_ = v___y_826_;
v___y_710_ = v___y_828_;
v___y_711_ = v___x_834_;
v___y_712_ = v___y_810_;
v___y_713_ = v___y_812_;
v___y_714_ = v___x_830_;
v___y_715_ = v___y_813_;
v___y_716_ = v_a_829_;
v___y_717_ = v___y_814_;
v___y_718_ = v___y_816_;
v___y_719_ = v___y_818_;
v___y_720_ = v___y_820_;
v___y_721_ = v___y_822_;
v___y_722_ = v___y_821_;
v___y_723_ = v___y_823_;
v___y_724_ = v___y_825_;
v___y_725_ = v___x_832_;
v___y_726_ = v___y_827_;
v___y_727_ = v___x_836_;
goto v___jp_701_;
}
else
{
lean_object* v___x_837_; 
lean_dec(v___y_807_);
v___x_837_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___y_702_ = v___y_808_;
v___y_703_ = v___y_809_;
v___y_704_ = v___y_811_;
v___y_705_ = v___y_815_;
v___y_706_ = v___y_817_;
v___y_707_ = v___y_819_;
v___y_708_ = v___y_824_;
v___y_709_ = v___y_826_;
v___y_710_ = v___y_828_;
v___y_711_ = v___x_834_;
v___y_712_ = v___y_810_;
v___y_713_ = v___y_812_;
v___y_714_ = v___x_830_;
v___y_715_ = v___y_813_;
v___y_716_ = v_a_829_;
v___y_717_ = v___y_814_;
v___y_718_ = v___y_816_;
v___y_719_ = v___y_818_;
v___y_720_ = v___y_820_;
v___y_721_ = v___y_822_;
v___y_722_ = v___y_821_;
v___y_723_ = v___y_823_;
v___y_724_ = v___y_825_;
v___y_725_ = v___x_832_;
v___y_726_ = v___y_827_;
v___y_727_ = v___x_837_;
goto v___jp_701_;
}
}
v___jp_838_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_863_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31));
lean_inc_ref_n(v___y_843_, 6);
lean_inc_ref_n(v___y_847_, 6);
lean_inc_ref_n(v___y_845_, 6);
v___x_864_ = l_Lean_Name_mkStr4(v___y_845_, v___y_847_, v___y_843_, v___x_863_);
v___x_865_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32));
lean_inc_n(v___y_858_, 28);
v___x_866_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_866_, 0, v___y_858_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
lean_inc_ref(v___y_851_);
lean_inc_n(v___y_844_, 6);
v___x_867_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_867_, 0, v___y_858_);
lean_ctor_set(v___x_867_, 1, v___y_844_);
lean_ctor_set(v___x_867_, 2, v___y_851_);
v___x_868_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31));
v___x_869_ = l_Lean_Name_mkStr4(v___y_845_, v___y_847_, v___y_843_, v___x_868_);
v___x_870_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33));
v___x_871_ = l_Lean_Name_mkStr4(v___y_845_, v___y_847_, v___y_843_, v___x_870_);
v___x_872_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34));
v___x_873_ = l_Lean_Name_mkStr4(v___y_845_, v___y_847_, v___y_843_, v___x_872_);
v___x_874_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36);
v___x_875_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37));
lean_inc_n(v___y_852_, 3);
lean_inc_n(v_a_862_, 3);
v___x_876_ = l_Lean_addMacroScope(v_a_862_, v___x_875_, v___y_852_);
lean_inc_n(v___y_840_, 4);
v___x_877_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_877_, 0, v___y_858_);
lean_ctor_set(v___x_877_, 1, v___x_874_);
lean_ctor_set(v___x_877_, 2, v___x_876_);
lean_ctor_set(v___x_877_, 3, v___y_840_);
lean_inc_ref_n(v___x_867_, 18);
lean_inc_n(v___x_873_, 3);
v___x_878_ = l_Lean_Syntax_node2(v___y_858_, v___x_873_, v___x_877_, v___x_867_);
v___x_879_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38));
v___x_880_ = l_Lean_Name_mkStr4(v___y_845_, v___y_847_, v___y_843_, v___x_879_);
v___x_881_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39));
v___x_882_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_882_, 0, v___y_858_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
lean_inc_ref_n(v___x_882_, 3);
lean_inc_n(v___x_880_, 3);
v___x_883_ = l_Lean_Syntax_node3(v___y_858_, v___x_880_, v___x_882_, v___x_867_, v___y_859_);
v___x_884_ = l_Lean_Syntax_node3(v___y_858_, v___y_844_, v___x_867_, v___x_867_, v___x_883_);
lean_inc_n(v___x_871_, 3);
v___x_885_ = l_Lean_Syntax_node2(v___y_858_, v___x_871_, v___x_878_, v___x_884_);
v___x_886_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40));
v___x_887_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_887_, 0, v___y_858_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42);
v___x_889_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43));
v___x_890_ = l_Lean_addMacroScope(v_a_862_, v___x_889_, v___y_852_);
v___x_891_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_891_, 0, v___y_858_);
lean_ctor_set(v___x_891_, 1, v___x_888_);
lean_ctor_set(v___x_891_, 2, v___x_890_);
lean_ctor_set(v___x_891_, 3, v___y_840_);
v___x_892_ = l_Lean_Syntax_node2(v___y_858_, v___x_873_, v___x_891_, v___x_867_);
v___x_893_ = l_Lean_Syntax_node3(v___y_858_, v___x_880_, v___x_882_, v___x_867_, v___y_846_);
v___x_894_ = l_Lean_Syntax_node3(v___y_858_, v___y_844_, v___x_867_, v___x_867_, v___x_893_);
v___x_895_ = l_Lean_Syntax_node2(v___y_858_, v___x_871_, v___x_892_, v___x_894_);
v___x_896_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45);
v___x_897_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46));
v___x_898_ = l_Lean_addMacroScope(v_a_862_, v___x_897_, v___y_852_);
v___x_899_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_899_, 0, v___y_858_);
lean_ctor_set(v___x_899_, 1, v___x_896_);
lean_ctor_set(v___x_899_, 2, v___x_898_);
lean_ctor_set(v___x_899_, 3, v___y_840_);
v___x_900_ = l_Lean_Syntax_node2(v___y_858_, v___x_873_, v___x_899_, v___x_867_);
v___x_901_ = l_Lean_Syntax_node3(v___y_858_, v___x_880_, v___x_882_, v___x_867_, v___y_841_);
v___x_902_ = l_Lean_Syntax_node3(v___y_858_, v___y_844_, v___x_867_, v___x_867_, v___x_901_);
v___x_903_ = l_Lean_Syntax_node2(v___y_858_, v___x_871_, v___x_900_, v___x_902_);
v___x_904_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48);
v___x_905_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49));
v___x_906_ = l_Lean_addMacroScope(v_a_862_, v___x_905_, v___y_852_);
v___x_907_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_907_, 0, v___y_858_);
lean_ctor_set(v___x_907_, 1, v___x_904_);
lean_ctor_set(v___x_907_, 2, v___x_906_);
lean_ctor_set(v___x_907_, 3, v___y_840_);
v___x_908_ = l_Lean_Syntax_node2(v___y_858_, v___x_873_, v___x_907_, v___x_867_);
v___x_909_ = l_Lean_Syntax_node3(v___y_858_, v___x_880_, v___x_882_, v___x_867_, v___y_842_);
v___x_910_ = l_Lean_Syntax_node3(v___y_858_, v___y_844_, v___x_867_, v___x_867_, v___x_909_);
v___x_911_ = l_Lean_Syntax_node2(v___y_858_, v___x_871_, v___x_908_, v___x_910_);
lean_inc_ref_n(v___x_887_, 2);
v___x_912_ = l_Lean_Syntax_node7(v___y_858_, v___y_844_, v___x_885_, v___x_887_, v___x_895_, v___x_887_, v___x_903_, v___x_887_, v___x_911_);
v___x_913_ = l_Lean_Syntax_node1(v___y_858_, v___x_869_, v___x_912_);
v___x_914_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50));
v___x_915_ = l_Lean_Name_mkStr4(v___y_845_, v___y_847_, v___y_843_, v___x_914_);
v___x_916_ = l_Lean_Syntax_node1(v___y_858_, v___x_915_, v___x_867_);
v___x_917_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51));
v___x_918_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_918_, 0, v___y_858_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = l_Lean_Syntax_node6(v___y_858_, v___x_864_, v___x_866_, v___x_867_, v___x_913_, v___x_916_, v___x_867_, v___x_918_);
v___x_920_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_922_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
v___x_922_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_848_);
if (lean_obj_tag(v___x_922_) == 0)
{
if (lean_obj_tag(v___y_857_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_924_; lean_object* v_a_925_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref_known(v___x_922_, 1);
v___x_924_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_849_);
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref(v___x_924_);
v___y_807_ = v___y_839_;
v___y_808_ = v___y_840_;
v___y_809_ = v___y_843_;
v___y_810_ = v___y_844_;
v___y_811_ = v___x_919_;
v___y_812_ = v___y_845_;
v___y_813_ = v___y_847_;
v___y_814_ = v___x_886_;
v___y_815_ = v___y_848_;
v___y_816_ = v___y_849_;
v___y_817_ = v_a_923_;
v___y_818_ = v___y_850_;
v___y_819_ = v___y_851_;
v___y_820_ = v___x_881_;
v___y_821_ = v___y_854_;
v___y_822_ = v___y_853_;
v___y_823_ = v___y_856_;
v___y_824_ = v___y_855_;
v___y_825_ = v___y_857_;
v___y_826_ = v_a_921_;
v___y_827_ = v___y_860_;
v___y_828_ = v___y_861_;
v_a_829_ = v_a_925_;
goto v___jp_806_;
}
else
{
lean_object* v_a_926_; lean_object* v_val_927_; 
v_a_926_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_926_);
lean_dec_ref_known(v___x_922_, 1);
v_val_927_ = lean_ctor_get(v___y_857_, 0);
lean_inc(v_val_927_);
v___y_807_ = v___y_839_;
v___y_808_ = v___y_840_;
v___y_809_ = v___y_843_;
v___y_810_ = v___y_844_;
v___y_811_ = v___x_919_;
v___y_812_ = v___y_845_;
v___y_813_ = v___y_847_;
v___y_814_ = v___x_886_;
v___y_815_ = v___y_848_;
v___y_816_ = v___y_849_;
v___y_817_ = v_a_926_;
v___y_818_ = v___y_850_;
v___y_819_ = v___y_851_;
v___y_820_ = v___x_881_;
v___y_821_ = v___y_854_;
v___y_822_ = v___y_853_;
v___y_823_ = v___y_856_;
v___y_824_ = v___y_855_;
v___y_825_ = v___y_857_;
v___y_826_ = v_a_921_;
v___y_827_ = v___y_860_;
v___y_828_ = v___y_861_;
v_a_829_ = v_val_927_;
goto v___jp_806_;
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec(v_a_921_);
lean_dec(v___x_919_);
lean_dec(v___y_861_);
lean_dec(v___y_860_);
lean_dec(v___y_857_);
lean_dec(v___y_856_);
lean_dec(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_850_);
lean_dec_ref(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_839_);
lean_dec(v_stx_618_);
v_a_928_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_922_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_922_);
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
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec(v___x_919_);
lean_dec(v___y_861_);
lean_dec(v___y_860_);
lean_dec(v___y_857_);
lean_dec(v___y_856_);
lean_dec(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_850_);
lean_dec_ref(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_839_);
lean_dec(v_stx_618_);
v_a_936_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_920_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_920_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
v___jp_944_:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_962_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_963_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10));
v___x_964_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52));
lean_inc_ref_n(v___y_950_, 3);
v___x_965_ = l_Lean_Name_mkStr4(v___y_950_, v___x_962_, v___x_963_, v___x_964_);
v___x_966_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53));
v___x_967_ = l_Lean_Name_mkStr4(v___y_950_, v___x_962_, v___x_963_, v___x_966_);
v___x_968_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_969_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
lean_inc_n(v___y_958_, 4);
v___x_970_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_970_, 0, v___y_958_);
lean_ctor_set(v___x_970_, 1, v___x_968_);
lean_ctor_set(v___x_970_, 2, v___x_969_);
lean_inc_ref(v___x_970_);
lean_inc(v___x_967_);
v___x_971_ = l_Lean_Syntax_node1(v___y_958_, v___x_967_, v___x_970_);
v___x_972_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54));
v___x_973_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55));
v___x_974_ = l_Lean_Name_mkStr4(v___y_950_, v___x_962_, v___x_972_, v___x_973_);
v___x_975_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57);
v___x_976_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59));
v___x_977_ = l_Lean_addMacroScope(v_a_961_, v___x_976_, v___y_954_);
lean_inc(v___y_946_);
v___x_978_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_978_, 0, v___y_958_);
lean_ctor_set(v___x_978_, 1, v___x_975_);
lean_ctor_set(v___x_978_, 2, v___x_977_);
lean_ctor_set(v___x_978_, 3, v___y_946_);
v___x_979_ = l_Lean_Syntax_node2(v___y_958_, v___x_974_, v___x_978_, v___x_970_);
lean_inc(v___x_965_);
v___x_980_ = l_Lean_Syntax_node2(v___y_958_, v___x_965_, v___x_971_, v___x_979_);
v___x_981_ = lean_mk_empty_array_with_capacity(v___x_698_);
v___x_982_ = lean_array_push(v___x_981_, v___x_980_);
v___x_983_ = l_Lake_DSL_expandAttrs(v___y_960_);
v___x_984_ = l_Array_append___redArg(v___x_982_, v___x_983_);
lean_dec_ref(v___x_983_);
v___x_985_ = l_Lake_DSL_packageDeclName;
v___x_986_ = l_Lean_mkIdentFrom(v___y_949_, v___x_985_, v___y_956_);
lean_dec(v___y_949_);
v___x_987_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_989_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_952_);
if (lean_obj_tag(v___x_989_) == 0)
{
if (lean_obj_tag(v___y_957_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_991_; lean_object* v_a_992_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
v___x_991_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_953_);
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref(v___x_991_);
v___y_839_ = v___y_945_;
v___y_840_ = v___y_946_;
v___y_841_ = v___y_947_;
v___y_842_ = v___y_948_;
v___y_843_ = v___x_963_;
v___y_844_ = v___x_968_;
v___y_845_ = v___y_950_;
v___y_846_ = v___y_951_;
v___y_847_ = v___x_962_;
v___y_848_ = v___y_952_;
v___y_849_ = v___y_953_;
v___y_850_ = v___x_984_;
v___y_851_ = v___x_969_;
v___y_852_ = v_a_990_;
v___y_853_ = v___y_955_;
v___y_854_ = v___x_985_;
v___y_855_ = v___y_956_;
v___y_856_ = v___x_967_;
v___y_857_ = v___y_957_;
v___y_858_ = v_a_988_;
v___y_859_ = v___y_959_;
v___y_860_ = v___x_965_;
v___y_861_ = v___x_986_;
v_a_862_ = v_a_992_;
goto v___jp_838_;
}
else
{
lean_object* v_a_993_; lean_object* v_val_994_; 
v_a_993_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_989_, 1);
v_val_994_ = lean_ctor_get(v___y_957_, 0);
lean_inc(v_val_994_);
v___y_839_ = v___y_945_;
v___y_840_ = v___y_946_;
v___y_841_ = v___y_947_;
v___y_842_ = v___y_948_;
v___y_843_ = v___x_963_;
v___y_844_ = v___x_968_;
v___y_845_ = v___y_950_;
v___y_846_ = v___y_951_;
v___y_847_ = v___x_962_;
v___y_848_ = v___y_952_;
v___y_849_ = v___y_953_;
v___y_850_ = v___x_984_;
v___y_851_ = v___x_969_;
v___y_852_ = v_a_993_;
v___y_853_ = v___y_955_;
v___y_854_ = v___x_985_;
v___y_855_ = v___y_956_;
v___y_856_ = v___x_967_;
v___y_857_ = v___y_957_;
v___y_858_ = v_a_988_;
v___y_859_ = v___y_959_;
v___y_860_ = v___x_965_;
v___y_861_ = v___x_986_;
v_a_862_ = v_val_994_;
goto v___jp_838_;
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec(v_a_988_);
lean_dec(v___x_986_);
lean_dec_ref(v___x_984_);
lean_dec(v___x_967_);
lean_dec(v___x_965_);
lean_dec(v___y_959_);
lean_dec(v___y_957_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec(v___y_948_);
lean_dec(v___y_947_);
lean_dec(v___y_945_);
lean_dec(v_stx_618_);
v_a_995_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_989_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_989_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec(v___x_986_);
lean_dec_ref(v___x_984_);
lean_dec(v___x_967_);
lean_dec(v___x_965_);
lean_dec(v___y_959_);
lean_dec(v___y_957_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec(v___y_948_);
lean_dec(v___y_947_);
lean_dec(v___y_945_);
lean_dec(v_stx_618_);
v_a_1003_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_987_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_987_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
v___jp_1011_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1025_ = l_Nat_reprFast(v___y_1018_);
v___x_1026_ = lean_box(2);
v___x_1027_ = l_Lean_Syntax_mkNumLit(v___x_1025_, v___x_1026_);
v___x_1028_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_1029_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62));
v___x_1030_ = lean_mk_empty_array_with_capacity(v___x_700_);
lean_inc(v___y_1024_);
lean_inc_ref(v___x_1030_);
v___x_1031_ = lean_array_push(v___x_1030_, v___y_1024_);
v___x_1032_ = lean_array_push(v___x_1031_, v___x_1027_);
v___x_1033_ = l_Lean_Syntax_mkCApp(v___x_1029_, v___x_1032_);
v___x_1034_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64));
lean_inc(v___x_1033_);
v___x_1035_ = lean_array_push(v___x_1030_, v___x_1033_);
lean_inc(v___y_1017_);
v___x_1036_ = lean_array_push(v___x_1035_, v___y_1017_);
v___x_1037_ = l_Lean_Syntax_mkCApp(v___x_1034_, v___x_1036_);
lean_inc(v___y_1014_);
v___x_1038_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(v___x_1034_, v___y_1014_, v___x_1037_, v___y_1015_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v___x_1039_; 
lean_dec_ref_known(v___x_1038_, 1);
v___x_1039_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1041_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v___x_1039_, 1);
v___x_1041_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1019_);
if (lean_obj_tag(v___x_1041_) == 0)
{
if (lean_obj_tag(v___y_1022_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1043_; lean_object* v_a_1044_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v___x_1041_, 1);
v___x_1043_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_1020_);
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref(v___x_1043_);
v___y_945_ = v___y_1012_;
v___y_946_ = v___y_1013_;
v___y_947_ = v___x_1033_;
v___y_948_ = v___y_1014_;
v___y_949_ = v___y_1016_;
v___y_950_ = v___x_1028_;
v___y_951_ = v___y_1017_;
v___y_952_ = v___y_1019_;
v___y_953_ = v___y_1020_;
v___y_954_ = v_a_1042_;
v___y_955_ = v___x_1026_;
v___y_956_ = v___y_1021_;
v___y_957_ = v___y_1022_;
v___y_958_ = v_a_1040_;
v___y_959_ = v___y_1024_;
v___y_960_ = v___y_1023_;
v_a_961_ = v_a_1044_;
goto v___jp_944_;
}
else
{
lean_object* v_a_1045_; lean_object* v_val_1046_; 
v_a_1045_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v___x_1041_, 1);
v_val_1046_ = lean_ctor_get(v___y_1022_, 0);
lean_inc(v_val_1046_);
v___y_945_ = v___y_1012_;
v___y_946_ = v___y_1013_;
v___y_947_ = v___x_1033_;
v___y_948_ = v___y_1014_;
v___y_949_ = v___y_1016_;
v___y_950_ = v___x_1028_;
v___y_951_ = v___y_1017_;
v___y_952_ = v___y_1019_;
v___y_953_ = v___y_1020_;
v___y_954_ = v_a_1045_;
v___y_955_ = v___x_1026_;
v___y_956_ = v___y_1021_;
v___y_957_ = v___y_1022_;
v___y_958_ = v_a_1040_;
v___y_959_ = v___y_1024_;
v___y_960_ = v___y_1023_;
v_a_961_ = v_val_1046_;
goto v___jp_944_;
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v_a_1040_);
lean_dec(v___x_1033_);
lean_dec(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec(v___y_1014_);
lean_dec(v___y_1012_);
lean_dec(v_stx_618_);
v_a_1047_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1041_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1041_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec(v___x_1033_);
lean_dec(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec(v___y_1014_);
lean_dec(v___y_1012_);
lean_dec(v_stx_618_);
v_a_1055_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1039_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1039_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_dec(v___x_1033_);
lean_dec(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec(v___y_1014_);
lean_dec(v___y_1012_);
lean_dec(v_stx_618_);
return v___x_1038_;
}
}
v___jp_1063_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1075_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66);
v___x_1076_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__67));
v___x_1077_ = l_Lean_addMacroScope(v_a_1074_, v___x_1076_, v___y_1068_);
v___x_1078_ = lean_box(0);
v___x_1079_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1079_, 0, v___y_1066_);
lean_ctor_set(v___x_1079_, 1, v___x_1075_);
lean_ctor_set(v___x_1079_, 2, v___x_1077_);
lean_ctor_set(v___x_1079_, 3, v___x_1078_);
v___x_1080_ = l_Lake_DSL_mkConfigDeclIdent(v___y_1071_, v___y_1073_, v___y_1065_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v_env_1085_; lean_object* v___x_1086_; lean_object* v_asyncMode_1087_; lean_object* v___x_1088_; lean_object* v_snd_1089_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc_n(v_a_1081_, 2);
lean_dec_ref_known(v___x_1080_, 1);
v___x_1082_ = l_Lean_TSyntax_getId(v_a_1081_);
v___x_1083_ = l_Lake_Name_quoteFrom(v_a_1081_, v___x_1082_, v___y_1069_);
v___x_1084_ = lean_st_ref_get(v___y_1065_);
v_env_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc_ref(v_env_1085_);
lean_dec(v___x_1084_);
v___x_1086_ = l_Lake_nameExt;
v_asyncMode_1087_ = lean_ctor_get(v___x_1086_, 2);
v___x_1088_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_696_, v___x_1086_, v_env_1085_, v_asyncMode_1087_, v___x_695_, v___y_1069_);
v_snd_1089_ = lean_ctor_get(v___x_1088_, 1);
if (lean_obj_tag(v_snd_1089_) == 0)
{
lean_object* v_fst_1090_; 
v_fst_1090_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_fst_1090_);
lean_dec(v___x_1088_);
lean_inc(v___x_1083_);
v___y_1012_ = v___y_1064_;
v___y_1013_ = v___x_1078_;
v___y_1014_ = v___x_1079_;
v___y_1015_ = v___y_1067_;
v___y_1016_ = v_a_1081_;
v___y_1017_ = v___x_1083_;
v___y_1018_ = v_fst_1090_;
v___y_1019_ = v___y_1073_;
v___y_1020_ = v___y_1065_;
v___y_1021_ = v___y_1069_;
v___y_1022_ = v___y_1070_;
v___y_1023_ = v___y_1072_;
v___y_1024_ = v___x_1083_;
goto v___jp_1011_;
}
else
{
lean_object* v_fst_1091_; lean_object* v___x_1092_; 
lean_inc(v_snd_1089_);
v_fst_1091_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_fst_1091_);
lean_dec(v___x_1088_);
lean_inc(v_a_1081_);
v___x_1092_ = l_Lake_Name_quoteFrom(v_a_1081_, v_snd_1089_, v___y_1069_);
v___y_1012_ = v___y_1064_;
v___y_1013_ = v___x_1078_;
v___y_1014_ = v___x_1079_;
v___y_1015_ = v___y_1067_;
v___y_1016_ = v_a_1081_;
v___y_1017_ = v___x_1083_;
v___y_1018_ = v_fst_1091_;
v___y_1019_ = v___y_1073_;
v___y_1020_ = v___y_1065_;
v___y_1021_ = v___y_1069_;
v___y_1022_ = v___y_1070_;
v___y_1023_ = v___y_1072_;
v___y_1024_ = v___x_1092_;
goto v___jp_1011_;
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
lean_dec_ref_known(v___x_1079_, 4);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec(v___y_1070_);
lean_dec(v___y_1067_);
lean_dec(v___y_1064_);
lean_dec(v_stx_618_);
v_a_1093_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1080_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1080_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
v___jp_1102_:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_Elab_Command_getRef___redArg(v___y_1103_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v_fileName_1111_; lean_object* v_fileMap_1112_; lean_object* v_currRecDepth_1113_; lean_object* v_cmdPos_1114_; lean_object* v_macroStack_1115_; lean_object* v_quotContext_x3f_1116_; lean_object* v_currMacroScope_1117_; lean_object* v_snap_x3f_1118_; lean_object* v_cancelTk_x3f_1119_; uint8_t v_suppressElabErrors_1120_; lean_object* v_ref_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v_fileName_1111_ = lean_ctor_get(v___y_1103_, 0);
v_fileMap_1112_ = lean_ctor_get(v___y_1103_, 1);
v_currRecDepth_1113_ = lean_ctor_get(v___y_1103_, 2);
v_cmdPos_1114_ = lean_ctor_get(v___y_1103_, 3);
v_macroStack_1115_ = lean_ctor_get(v___y_1103_, 4);
v_quotContext_x3f_1116_ = lean_ctor_get(v___y_1103_, 5);
v_currMacroScope_1117_ = lean_ctor_get(v___y_1103_, 6);
v_snap_x3f_1118_ = lean_ctor_get(v___y_1103_, 8);
v_cancelTk_x3f_1119_ = lean_ctor_get(v___y_1103_, 9);
v_suppressElabErrors_1120_ = lean_ctor_get_uint8(v___y_1103_, sizeof(void*)*10);
v_ref_1121_ = l_Lean_replaceRef(v_kw_1101_, v_a_1110_);
lean_dec(v_a_1110_);
lean_dec(v_kw_1101_);
lean_inc(v_cancelTk_x3f_1119_);
lean_inc(v_snap_x3f_1118_);
lean_inc(v_currMacroScope_1117_);
lean_inc(v_quotContext_x3f_1116_);
lean_inc(v_macroStack_1115_);
lean_inc(v_cmdPos_1114_);
lean_inc(v_currRecDepth_1113_);
lean_inc_ref(v_fileMap_1112_);
lean_inc_ref(v_fileName_1111_);
v___x_1122_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1122_, 0, v_fileName_1111_);
lean_ctor_set(v___x_1122_, 1, v_fileMap_1112_);
lean_ctor_set(v___x_1122_, 2, v_currRecDepth_1113_);
lean_ctor_set(v___x_1122_, 3, v_cmdPos_1114_);
lean_ctor_set(v___x_1122_, 4, v_macroStack_1115_);
lean_ctor_set(v___x_1122_, 5, v_quotContext_x3f_1116_);
lean_ctor_set(v___x_1122_, 6, v_currMacroScope_1117_);
lean_ctor_set(v___x_1122_, 7, v_ref_1121_);
lean_ctor_set(v___x_1122_, 8, v_snap_x3f_1118_);
lean_ctor_set(v___x_1122_, 9, v_cancelTk_x3f_1119_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*10, v_suppressElabErrors_1120_);
v___x_1123_ = l_Lean_Elab_Command_getRef___redArg(v___x_1122_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; uint8_t v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1123_, 1);
v___x_1125_ = 0;
v___x_1126_ = l_Lean_SourceInfo_fromRef(v_a_1124_, v___x_1125_);
lean_dec(v_a_1124_);
v___x_1127_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_1122_);
if (lean_obj_tag(v___x_1127_) == 0)
{
if (lean_obj_tag(v_quotContext_x3f_1116_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1129_; lean_object* v_a_1130_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1127_, 1);
v___x_1129_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_1104_);
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref(v___x_1129_);
v___y_1064_ = v___y_1108_;
v___y_1065_ = v___y_1104_;
v___y_1066_ = v___x_1126_;
v___y_1067_ = v___y_1105_;
v___y_1068_ = v_a_1128_;
v___y_1069_ = v___x_1125_;
v___y_1070_ = v_quotContext_x3f_1116_;
v___y_1071_ = v___y_1106_;
v___y_1072_ = v___y_1107_;
v___y_1073_ = v___x_1122_;
v_a_1074_ = v_a_1130_;
goto v___jp_1063_;
}
else
{
lean_object* v_a_1131_; lean_object* v_val_1132_; 
v_a_1131_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1127_, 1);
v_val_1132_ = lean_ctor_get(v_quotContext_x3f_1116_, 0);
lean_inc(v_val_1132_);
lean_inc_ref(v_quotContext_x3f_1116_);
v___y_1064_ = v___y_1108_;
v___y_1065_ = v___y_1104_;
v___y_1066_ = v___x_1126_;
v___y_1067_ = v___y_1105_;
v___y_1068_ = v_a_1131_;
v___y_1069_ = v___x_1125_;
v___y_1070_ = v_quotContext_x3f_1116_;
v___y_1071_ = v___y_1106_;
v___y_1072_ = v___y_1107_;
v___y_1073_ = v___x_1122_;
v_a_1074_ = v_val_1132_;
goto v___jp_1063_;
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v___x_1126_);
lean_dec_ref_known(v___x_1122_, 10);
lean_dec(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec(v_stx_618_);
v_a_1133_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1127_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1127_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec_ref_known(v___x_1122_, 10);
lean_dec(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec(v_stx_618_);
v_a_1141_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1123_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1123_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec(v_kw_1101_);
lean_dec(v_stx_618_);
v_a_1149_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1109_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1109_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
v___jp_1157_:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_Syntax_getOptional_x3f(v___x_697_);
lean_dec(v___x_697_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_box(0);
v___y_1103_ = v___y_1158_;
v___y_1104_ = v___y_1159_;
v___y_1105_ = v___y_1160_;
v___y_1106_ = v___y_1161_;
v___y_1107_ = v___y_1162_;
v___y_1108_ = v___x_1164_;
goto v___jp_1102_;
}
else
{
lean_object* v_val_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v_val_1165_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1163_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_val_1165_);
lean_dec(v___x_1163_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_val_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
v___y_1103_ = v___y_1158_;
v___y_1104_ = v___y_1159_;
v___y_1105_ = v___y_1160_;
v___y_1106_ = v___y_1161_;
v___y_1107_ = v___y_1162_;
v___y_1108_ = v___x_1170_;
goto v___jp_1102_;
}
}
}
}
v___jp_1173_:
{
lean_object* v___x_1177_; lean_object* v_cfg_1178_; lean_object* v___x_1179_; 
v___x_1177_ = lean_unsigned_to_nat(4u);
v_cfg_1178_ = l_Lean_Syntax_getArg(v_stx_618_, v___x_1177_);
v___x_1179_ = l_Lean_Syntax_getOptional_x3f(v___x_699_);
lean_dec(v___x_699_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_box(0);
v___y_1158_ = v___y_1175_;
v___y_1159_ = v___y_1176_;
v___y_1160_ = v_cfg_1178_;
v___y_1161_ = v_nameStx_x3f_1174_;
v___y_1162_ = v___x_1180_;
goto v___jp_1157_;
}
else
{
lean_object* v_val_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
v_val_1181_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1179_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_val_1181_);
lean_dec(v___x_1179_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_val_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
v___y_1158_ = v___y_1175_;
v___y_1159_ = v___y_1176_;
v___y_1160_ = v_cfg_1178_;
v___y_1161_ = v_nameStx_x3f_1174_;
v___y_1162_ = v___x_1186_;
goto v___jp_1157_;
}
}
}
}
}
v___jp_622_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
lean_inc_ref(v___y_633_);
lean_inc_n(v___y_626_, 5);
lean_inc_n(v___y_640_, 28);
v___x_647_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_647_, 0, v___y_640_);
lean_ctor_set(v___x_647_, 1, v___y_626_);
lean_ctor_set(v___x_647_, 2, v___y_633_);
lean_inc_ref(v___y_628_);
v___x_648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_648_, 0, v___y_640_);
lean_ctor_set(v___x_648_, 1, v___y_628_);
lean_inc_ref_n(v___x_647_, 13);
v___x_649_ = l_Lean_Syntax_node1(v___y_640_, v___y_639_, v___x_647_);
v___x_650_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0));
lean_inc_ref(v___y_630_);
v___x_651_ = l_Lean_Name_mkStr2(v___y_630_, v___x_650_);
v___x_652_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_652_, 0, v___y_640_);
lean_ctor_set(v___x_652_, 1, v___x_650_);
v___x_653_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2));
v___x_654_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3));
v___x_655_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_655_, 0, v___y_640_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = l_Lean_Syntax_node1(v___y_640_, v___x_653_, v___x_655_);
v___x_657_ = l_Lean_Syntax_node1(v___y_640_, v___y_626_, v___x_656_);
v___x_658_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4));
v___x_659_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_659_, 0, v___y_640_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5));
v___x_661_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_661_, 0, v___y_640_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
lean_inc_ref(v___y_634_);
v___x_662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_662_, 0, v___y_640_);
lean_ctor_set(v___x_662_, 1, v___y_634_);
v___x_663_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6));
v___x_664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_664_, 0, v___y_640_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = l_Lean_Syntax_node1(v___y_640_, v___x_653_, v___x_664_);
v___x_666_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7));
v___x_667_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_667_, 0, v___y_640_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
lean_inc_ref(v___x_662_);
v___x_668_ = l_Lean_Syntax_node5(v___y_640_, v___y_626_, v___x_659_, v___x_661_, v___x_662_, v___x_665_, v___x_667_);
v___x_669_ = l_Lean_Syntax_node5(v___y_640_, v___x_651_, v___x_652_, v___x_647_, v___x_657_, v___x_647_, v___x_668_);
v___x_670_ = l_Lean_Syntax_node2(v___y_640_, v___y_645_, v___x_649_, v___x_669_);
v___x_671_ = l_Lean_Syntax_node1(v___y_640_, v___y_626_, v___x_670_);
lean_inc_ref(v___y_636_);
v___x_672_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_672_, 0, v___y_640_);
lean_ctor_set(v___x_672_, 1, v___y_636_);
v___x_673_ = l_Lean_Syntax_node3(v___y_640_, v___y_641_, v___x_648_, v___x_671_, v___x_672_);
v___x_674_ = l_Lean_Syntax_node1(v___y_640_, v___y_626_, v___x_673_);
v___x_675_ = l_Lean_Syntax_node7(v___y_640_, v___y_624_, v___x_647_, v___x_674_, v___x_647_, v___x_647_, v___x_647_, v___x_647_, v___x_647_);
v___x_676_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_676_, 0, v___y_640_);
lean_ctor_set(v___x_676_, 1, v___y_627_);
v___x_677_ = lean_array_push(v___y_629_, v___y_643_);
v___x_678_ = lean_array_push(v___x_677_, v___y_623_);
v___x_679_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_679_, 0, v___y_635_);
lean_ctor_set(v___x_679_, 1, v___y_625_);
lean_ctor_set(v___x_679_, 2, v___x_678_);
v___x_680_ = l_Lean_Syntax_node2(v___y_640_, v___y_642_, v___x_647_, v___x_647_);
v___x_681_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9));
v___x_682_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10));
v___x_683_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_683_, 0, v___y_640_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = l_Lean_Syntax_node1(v___y_640_, v___x_681_, v___x_683_);
v___x_685_ = l_Lean_Syntax_node2(v___y_640_, v___y_646_, v___x_647_, v___x_647_);
v___x_686_ = l_Lean_Syntax_node4(v___y_640_, v___y_638_, v___x_662_, v___x_684_, v___x_685_, v___x_647_);
v___x_687_ = l_Lean_Syntax_node4(v___y_640_, v___y_637_, v___x_676_, v___x_679_, v___x_680_, v___x_686_);
v___x_688_ = l_Lean_Syntax_node2(v___y_640_, v___y_644_, v___x_675_, v___x_687_);
v___x_689_ = l_Lean_Elab_Command_elabCommand(v___x_688_, v___y_631_, v___y_632_);
lean_dec_ref(v___y_631_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___boxed(lean_object* v_stx_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand(v_stx_1198_, v_a_1199_, v_a_1200_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0(lean_object* v_00_u03b1_1203_, lean_object* v_ref_1204_, lean_object* v_msg_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_ref_1204_, v_msg_1205_, v___y_1206_, v___y_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___boxed(lean_object* v_00_u03b1_1210_, lean_object* v_ref_1211_, lean_object* v_msg_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0(v_00_u03b1_1210_, v_ref_1211_, v_msg_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v_ref_1211_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2(lean_object* v_msgData_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msgData_1217_, v___y_1219_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2(v_msgData_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0(lean_object* v_00_u03b1_1227_, lean_object* v_msg_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_1228_, v___y_1229_, v___y_1230_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1233_, lean_object* v_msg_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0(v_00_u03b1_1233_, v_msg_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3(lean_object* v_msgData_1239_, lean_object* v_macroStack_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_msgData_1239_, v_macroStack_1240_, v___y_1242_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1245_, lean_object* v_macroStack_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3(v_msgData_1245_, v_macroStack_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1(){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1279_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1280_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12));
v___x_1281_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10));
v___x_1282_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___boxed), 4, 0);
v___x_1283_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1279_, v___x_1280_, v___x_1281_, v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___boxed(lean_object* v_a_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1();
return v_res_1285_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3));
v___x_1294_ = l_String_toRawSubstring_x27(v___x_1293_);
return v___x_1294_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6));
v___x_1299_ = l_String_toRawSubstring_x27(v___x_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12));
v___x_1312_ = l_String_toRawSubstring_x27(v___x_1311_);
return v___x_1312_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15));
v___x_1317_ = l_String_toRawSubstring_x27(v___x_1316_);
return v___x_1317_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21));
v___x_1325_ = l_String_toRawSubstring_x27(v___x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl(lean_object* v_stx_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___x_1376_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; uint8_t v___x_1396_; 
v___x_1376_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1));
lean_inc(v_stx_1350_);
v___x_1396_ = l_Lean_Syntax_isOfKind(v_stx_1350_, v___x_1376_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1398_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1350_, v___x_1397_, v_a_1351_, v_a_1352_);
lean_dec(v_stx_1350_);
return v___x_1398_;
}
else
{
lean_object* v___x_1399_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; uint8_t v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v_wds_x3f_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v_wds_x3f_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v_pkg_x3f_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v_attrs_x3f_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v_doc_x3f_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1783_ = l_Lean_Syntax_getArg(v_stx_1350_, v___x_1399_);
v___x_1784_ = l_Lean_Syntax_isNone(v___x_1783_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1785_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1783_);
v___x_1786_ = l_Lean_Syntax_matchesNull(v___x_1783_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
lean_dec(v___x_1783_);
v___x_1787_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1788_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1350_, v___x_1787_, v_a_1351_, v_a_1352_);
lean_dec(v_stx_1350_);
return v___x_1788_;
}
else
{
lean_object* v_doc_x3f_1789_; lean_object* v___x_1790_; 
v_doc_x3f_1789_ = l_Lean_Syntax_getArg(v___x_1783_, v___x_1399_);
lean_dec(v___x_1783_);
v___x_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1790_, 0, v_doc_x3f_1789_);
v_doc_x3f_1771_ = v___x_1790_;
v___y_1772_ = v_a_1351_;
v___y_1773_ = v_a_1352_;
goto v___jp_1770_;
}
}
else
{
lean_object* v___x_1791_; 
lean_dec(v___x_1783_);
v___x_1791_ = lean_box(0);
v_doc_x3f_1771_ = v___x_1791_;
v___y_1772_ = v_a_1351_;
v___y_1773_ = v_a_1352_;
goto v___jp_1770_;
}
v___jp_1400_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_inc_ref_n(v___y_1406_, 2);
v___x_1422_ = l_Array_append___redArg(v___y_1406_, v___y_1421_);
lean_dec_ref(v___y_1421_);
lean_inc_n(v___y_1418_, 8);
lean_inc_n(v___y_1420_, 41);
v___x_1423_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1423_, 0, v___y_1420_);
lean_ctor_set(v___x_1423_, 1, v___y_1418_);
lean_ctor_set(v___x_1423_, 2, v___x_1422_);
v___x_1424_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16));
lean_inc_ref_n(v___y_1414_, 9);
lean_inc_ref_n(v___y_1402_, 13);
lean_inc_ref_n(v___y_1411_, 13);
v___x_1425_ = l_Lean_Name_mkStr4(v___y_1411_, v___y_1402_, v___y_1414_, v___x_1424_);
v___x_1426_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17));
v___x_1427_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___y_1420_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40));
v___x_1429_ = l_Lean_Syntax_SepArray_ofElems(v___x_1428_, v___y_1408_);
lean_dec_ref(v___y_1408_);
v___x_1430_ = l_Array_append___redArg(v___y_1406_, v___x_1429_);
lean_dec_ref(v___x_1429_);
v___x_1431_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1431_, 0, v___y_1420_);
lean_ctor_set(v___x_1431_, 1, v___y_1418_);
lean_ctor_set(v___x_1431_, 2, v___x_1430_);
v___x_1432_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18));
v___x_1433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___y_1420_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = l_Lean_Syntax_node3(v___y_1420_, v___x_1425_, v___x_1427_, v___x_1431_, v___x_1433_);
v___x_1435_ = l_Lean_Syntax_node1(v___y_1420_, v___y_1418_, v___x_1434_);
lean_inc_n(v___y_1407_, 21);
v___x_1436_ = l_Lean_Syntax_node7(v___y_1420_, v___y_1403_, v___x_1423_, v___x_1435_, v___y_1407_, v___y_1407_, v___y_1407_, v___y_1407_, v___y_1407_);
v___x_1437_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5));
lean_inc_ref_n(v___y_1413_, 3);
v___x_1438_ = l_Lean_Name_mkStr4(v___y_1411_, v___y_1402_, v___y_1413_, v___x_1437_);
v___x_1439_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6));
v___x_1440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___y_1420_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
v___x_1441_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7));
v___x_1442_ = l_Lean_Name_mkStr4(v___y_1411_, v___y_1402_, v___y_1413_, v___x_1441_);
v___x_1443_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4);
v___x_1444_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5));
lean_inc_n(v___y_1404_, 3);
lean_inc_n(v___y_1419_, 3);
v___x_1445_ = l_Lean_addMacroScope(v___y_1419_, v___x_1444_, v___y_1404_);
lean_inc_n(v___y_1416_, 4);
v___x_1446_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1446_, 0, v___y_1420_);
lean_ctor_set(v___x_1446_, 1, v___x_1443_);
lean_ctor_set(v___x_1446_, 2, v___x_1445_);
lean_ctor_set(v___x_1446_, 3, v___y_1416_);
v___x_1447_ = l_Lean_Syntax_node2(v___y_1420_, v___x_1442_, v___x_1446_, v___y_1407_);
v___x_1448_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9));
v___x_1449_ = l_Lean_Name_mkStr4(v___y_1411_, v___y_1402_, v___y_1413_, v___x_1448_);
v___x_1450_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11));
v___x_1451_ = l_Lean_Name_mkStr4(v___y_1411_, v___y_1402_, v___y_1414_, v___x_1450_);
v___x_1452_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12));
v___x_1453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___y_1420_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
v___x_1454_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7);
v___x_1455_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8));
v___x_1456_ = l_Lean_addMacroScope(v___y_1419_, v___x_1455_, v___y_1404_);
v___x_1457_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10));
v___x_1458_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11));
v___x_1459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
lean_ctor_set(v___x_1459_, 1, v___y_1416_);
v___x_1460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1457_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1461_, 0, v___y_1420_);
lean_ctor_set(v___x_1461_, 1, v___x_1454_);
lean_ctor_set(v___x_1461_, 2, v___x_1456_);
lean_ctor_set(v___x_1461_, 3, v___x_1460_);
v___x_1462_ = l_Lean_Syntax_node2(v___y_1420_, v___x_1451_, v___x_1453_, v___x_1461_);
v___x_1463_ = l_Lean_Syntax_node1(v___y_1420_, v___y_1418_, v___x_1462_);
v___x_1464_ = l_Lean_Syntax_node2(v___y_1420_, v___x_1449_, v___y_1407_, v___x_1463_);
v___x_1465_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39));
v___x_1466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___y_1420_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31));
v___x_1468_ = l_Lean_Name_mkStr4(v___y_1411_, v___y_1402_, v___y_1414_, v___x_1467_);
v___x_1469_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32));
v___x_1470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___y_1420_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31));
v___x_1472_ = l_Lean_Name_mkStr4(v___y_1411_, v___y_1402_, v___y_1414_, v___x_1471_);
v___x_1473_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33));
v___x_1474_ = l_Lean_Name_mkStr4(v___y_1411_, v___y_1402_, v___y_1414_, v___x_1473_);
v___x_1475_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34));
v___x_1476_ = l_Lean_Name_mkStr4(v___y_1411_, v___y_1402_, v___y_1414_, v___x_1475_);
v___x_1477_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13);
v___x_1478_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14));
v___x_1479_ = l_Lean_addMacroScope(v___y_1419_, v___x_1478_, v___y_1404_);
v___x_1480_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1480_, 0, v___y_1420_);
lean_ctor_set(v___x_1480_, 1, v___x_1477_);
lean_ctor_set(v___x_1480_, 2, v___x_1479_);
lean_ctor_set(v___x_1480_, 3, v___y_1416_);
lean_inc(v___x_1476_);
v___x_1481_ = l_Lean_Syntax_node2(v___y_1420_, v___x_1476_, v___x_1480_, v___y_1407_);
v___x_1482_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38));
v___x_1483_ = l_Lean_Name_mkStr4(v___y_1411_, v___y_1402_, v___y_1414_, v___x_1482_);
v___x_1484_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9));
v___x_1485_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10));
v___x_1486_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___y_1420_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = l_Lean_Syntax_node1(v___y_1420_, v___x_1484_, v___x_1486_);
lean_inc_ref_n(v___x_1466_, 2);
lean_inc(v___x_1483_);
v___x_1488_ = l_Lean_Syntax_node3(v___y_1420_, v___x_1483_, v___x_1466_, v___y_1407_, v___x_1487_);
v___x_1489_ = l_Lean_Syntax_node3(v___y_1420_, v___y_1418_, v___y_1407_, v___y_1407_, v___x_1488_);
lean_inc(v___x_1474_);
v___x_1490_ = l_Lean_Syntax_node2(v___y_1420_, v___x_1474_, v___x_1481_, v___x_1489_);
v___x_1491_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___y_1420_);
lean_ctor_set(v___x_1491_, 1, v___x_1428_);
v___x_1492_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16);
v___x_1493_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17));
v___x_1494_ = l_Lean_addMacroScope(v___y_1419_, v___x_1493_, v___y_1404_);
v___x_1495_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1495_, 0, v___y_1420_);
lean_ctor_set(v___x_1495_, 1, v___x_1492_);
lean_ctor_set(v___x_1495_, 2, v___x_1494_);
lean_ctor_set(v___x_1495_, 3, v___y_1416_);
v___x_1496_ = l_Lean_Syntax_node2(v___y_1420_, v___x_1476_, v___x_1495_, v___y_1407_);
v___x_1497_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18));
v___x_1498_ = l_Lean_Name_mkStr4(v___y_1411_, v___y_1402_, v___y_1414_, v___x_1497_);
v___x_1499_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___y_1420_);
lean_ctor_set(v___x_1499_, 1, v___x_1497_);
v___x_1500_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19));
v___x_1501_ = l_Lean_Name_mkStr4(v___y_1411_, v___y_1402_, v___y_1414_, v___x_1500_);
v___x_1502_ = l_Lean_Syntax_node1(v___y_1420_, v___y_1418_, v___y_1417_);
v___x_1503_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20));
v___x_1504_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___y_1420_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
v___x_1505_ = l_Lean_Syntax_node4(v___y_1420_, v___x_1501_, v___x_1502_, v___y_1407_, v___x_1504_, v___y_1415_);
v___x_1506_ = l_Lean_Syntax_node2(v___y_1420_, v___x_1498_, v___x_1499_, v___x_1505_);
v___x_1507_ = l_Lean_Syntax_node3(v___y_1420_, v___x_1483_, v___x_1466_, v___y_1407_, v___x_1506_);
v___x_1508_ = l_Lean_Syntax_node3(v___y_1420_, v___y_1418_, v___y_1407_, v___y_1407_, v___x_1507_);
v___x_1509_ = l_Lean_Syntax_node2(v___y_1420_, v___x_1474_, v___x_1496_, v___x_1508_);
v___x_1510_ = l_Lean_Syntax_node3(v___y_1420_, v___y_1418_, v___x_1490_, v___x_1491_, v___x_1509_);
v___x_1511_ = l_Lean_Syntax_node1(v___y_1420_, v___x_1472_, v___x_1510_);
v___x_1512_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50));
v___x_1513_ = l_Lean_Name_mkStr4(v___y_1411_, v___y_1402_, v___y_1414_, v___x_1512_);
v___x_1514_ = l_Lean_Syntax_node1(v___y_1420_, v___x_1513_, v___y_1407_);
v___x_1515_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51));
v___x_1516_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___y_1420_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = l_Lean_Syntax_node6(v___y_1420_, v___x_1468_, v___x_1470_, v___y_1407_, v___x_1511_, v___x_1514_, v___y_1407_, v___x_1516_);
lean_inc(v___y_1405_);
v___x_1518_ = l_Lean_Syntax_node2(v___y_1420_, v___y_1405_, v___y_1407_, v___y_1407_);
if (lean_obj_tag(v___y_1410_) == 1)
{
lean_object* v_val_1519_; lean_object* v___x_1520_; 
v_val_1519_ = lean_ctor_get(v___y_1410_, 0);
lean_inc(v_val_1519_);
lean_dec_ref_known(v___y_1410_, 1);
v___x_1520_ = l_Array_mkArray1___redArg(v_val_1519_);
v___y_1354_ = v___y_1401_;
v___y_1355_ = v___x_1518_;
v___y_1356_ = v___x_1447_;
v___y_1357_ = v___x_1438_;
v___y_1358_ = v___x_1464_;
v___y_1359_ = v___x_1436_;
v___y_1360_ = v___y_1406_;
v___y_1361_ = v___x_1466_;
v___y_1362_ = v___y_1407_;
v___y_1363_ = v___y_1409_;
v___y_1364_ = v___x_1517_;
v___y_1365_ = v___y_1412_;
v___y_1366_ = v___x_1440_;
v___y_1367_ = v___y_1418_;
v___y_1368_ = v___y_1420_;
v___y_1369_ = v___x_1520_;
goto v___jp_1353_;
}
else
{
lean_object* v___x_1521_; 
lean_dec(v___y_1410_);
v___x_1521_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___y_1354_ = v___y_1401_;
v___y_1355_ = v___x_1518_;
v___y_1356_ = v___x_1447_;
v___y_1357_ = v___x_1438_;
v___y_1358_ = v___x_1464_;
v___y_1359_ = v___x_1436_;
v___y_1360_ = v___y_1406_;
v___y_1361_ = v___x_1466_;
v___y_1362_ = v___y_1407_;
v___y_1363_ = v___y_1409_;
v___y_1364_ = v___x_1517_;
v___y_1365_ = v___y_1412_;
v___y_1366_ = v___x_1440_;
v___y_1367_ = v___y_1418_;
v___y_1368_ = v___y_1420_;
v___y_1369_ = v___x_1521_;
goto v___jp_1353_;
}
}
v___jp_1522_:
{
lean_object* v_methods_1538_; lean_object* v_quotContext_1539_; lean_object* v_currMacroScope_1540_; lean_object* v_currRecDepth_1541_; lean_object* v_maxRecDepth_1542_; lean_object* v_ref_1543_; lean_object* v_ref_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v_methods_1538_ = lean_ctor_get(v___y_1536_, 0);
v_quotContext_1539_ = lean_ctor_get(v___y_1536_, 1);
v_currMacroScope_1540_ = lean_ctor_get(v___y_1536_, 2);
v_currRecDepth_1541_ = lean_ctor_get(v___y_1536_, 3);
v_maxRecDepth_1542_ = lean_ctor_get(v___y_1536_, 4);
v_ref_1543_ = lean_ctor_get(v___y_1536_, 5);
v_ref_1544_ = l_Lean_replaceRef(v___y_1530_, v_ref_1543_);
lean_dec(v___y_1530_);
lean_inc(v_ref_1544_);
lean_inc(v_maxRecDepth_1542_);
lean_inc(v_currRecDepth_1541_);
lean_inc(v_currMacroScope_1540_);
lean_inc(v_quotContext_1539_);
lean_inc(v_methods_1538_);
v___x_1545_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1545_, 0, v_methods_1538_);
lean_ctor_set(v___x_1545_, 1, v_quotContext_1539_);
lean_ctor_set(v___x_1545_, 2, v_currMacroScope_1540_);
lean_ctor_set(v___x_1545_, 3, v_currRecDepth_1541_);
lean_ctor_set(v___x_1545_, 4, v_maxRecDepth_1542_);
lean_ctor_set(v___x_1545_, 5, v_ref_1544_);
v___x_1546_ = l_Lake_DSL_expandOptSimpleBinder(v___y_1533_, v___x_1545_, v___y_1537_);
lean_dec_ref_known(v___x_1545_, 6);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v_a_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
v_a_1548_ = lean_ctor_get(v___x_1546_, 1);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1546_, 2);
v___x_1549_ = l_Lean_SourceInfo_fromRef(v_ref_1544_, v___y_1529_);
lean_dec(v_ref_1544_);
v___x_1550_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10));
v___x_1551_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52));
lean_inc_ref_n(v___y_1526_, 5);
lean_inc_ref_n(v___y_1523_, 5);
v___x_1552_ = l_Lean_Name_mkStr4(v___y_1523_, v___y_1526_, v___x_1550_, v___x_1551_);
v___x_1553_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53));
v___x_1554_ = l_Lean_Name_mkStr4(v___y_1523_, v___y_1526_, v___x_1550_, v___x_1553_);
v___x_1555_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_1556_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
lean_inc_n(v___x_1549_, 5);
v___x_1557_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1549_);
lean_ctor_set(v___x_1557_, 1, v___x_1555_);
lean_ctor_set(v___x_1557_, 2, v___x_1556_);
lean_inc_ref_n(v___x_1557_, 2);
v___x_1558_ = l_Lean_Syntax_node1(v___x_1549_, v___x_1554_, v___x_1557_);
v___x_1559_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54));
v___x_1560_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55));
v___x_1561_ = l_Lean_Name_mkStr4(v___y_1523_, v___y_1526_, v___x_1559_, v___x_1560_);
v___x_1562_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22);
v___x_1563_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24));
lean_inc(v_currMacroScope_1540_);
lean_inc(v_quotContext_1539_);
v___x_1564_ = l_Lean_addMacroScope(v_quotContext_1539_, v___x_1563_, v_currMacroScope_1540_);
v___x_1565_ = lean_box(0);
v___x_1566_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1549_);
lean_ctor_set(v___x_1566_, 1, v___x_1562_);
lean_ctor_set(v___x_1566_, 2, v___x_1564_);
lean_ctor_set(v___x_1566_, 3, v___x_1565_);
v___x_1567_ = l_Lean_Syntax_node2(v___x_1549_, v___x_1561_, v___x_1566_, v___x_1557_);
v___x_1568_ = l_Lean_Syntax_node2(v___x_1549_, v___x_1552_, v___x_1558_, v___x_1567_);
v___x_1569_ = lean_mk_empty_array_with_capacity(v___y_1532_);
v___x_1570_ = lean_array_push(v___x_1569_, v___x_1568_);
v___x_1571_ = l_Lake_DSL_expandAttrs(v___y_1534_);
v___x_1572_ = l_Array_append___redArg(v___x_1570_, v___x_1571_);
lean_dec_ref(v___x_1571_);
v___x_1573_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0));
lean_inc_ref_n(v___y_1525_, 2);
v___x_1574_ = l_Lean_Name_mkStr4(v___y_1523_, v___y_1526_, v___y_1525_, v___x_1573_);
v___x_1575_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1));
v___x_1576_ = l_Lean_Name_mkStr4(v___y_1523_, v___y_1526_, v___y_1525_, v___x_1575_);
if (lean_obj_tag(v___y_1531_) == 1)
{
lean_object* v_val_1577_; lean_object* v___x_1578_; 
v_val_1577_ = lean_ctor_get(v___y_1531_, 0);
lean_inc(v_val_1577_);
lean_dec_ref_known(v___y_1531_, 1);
v___x_1578_ = l_Array_mkArray1___redArg(v_val_1577_);
lean_inc(v_quotContext_1539_);
lean_inc(v_currMacroScope_1540_);
v___y_1401_ = v___y_1524_;
v___y_1402_ = v___y_1526_;
v___y_1403_ = v___x_1576_;
v___y_1404_ = v_currMacroScope_1540_;
v___y_1405_ = v___y_1528_;
v___y_1406_ = v___x_1556_;
v___y_1407_ = v___x_1557_;
v___y_1408_ = v___x_1572_;
v___y_1409_ = v_a_1548_;
v___y_1410_ = v_wds_x3f_1535_;
v___y_1411_ = v___y_1523_;
v___y_1412_ = v___x_1574_;
v___y_1413_ = v___y_1525_;
v___y_1414_ = v___x_1550_;
v___y_1415_ = v___y_1527_;
v___y_1416_ = v___x_1565_;
v___y_1417_ = v_a_1547_;
v___y_1418_ = v___x_1555_;
v___y_1419_ = v_quotContext_1539_;
v___y_1420_ = v___x_1549_;
v___y_1421_ = v___x_1578_;
goto v___jp_1400_;
}
else
{
lean_object* v___x_1579_; 
lean_dec(v___y_1531_);
v___x_1579_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
lean_inc(v_quotContext_1539_);
lean_inc(v_currMacroScope_1540_);
v___y_1401_ = v___y_1524_;
v___y_1402_ = v___y_1526_;
v___y_1403_ = v___x_1576_;
v___y_1404_ = v_currMacroScope_1540_;
v___y_1405_ = v___y_1528_;
v___y_1406_ = v___x_1556_;
v___y_1407_ = v___x_1557_;
v___y_1408_ = v___x_1572_;
v___y_1409_ = v_a_1548_;
v___y_1410_ = v_wds_x3f_1535_;
v___y_1411_ = v___y_1523_;
v___y_1412_ = v___x_1574_;
v___y_1413_ = v___y_1525_;
v___y_1414_ = v___x_1550_;
v___y_1415_ = v___y_1527_;
v___y_1416_ = v___x_1565_;
v___y_1417_ = v_a_1547_;
v___y_1418_ = v___x_1555_;
v___y_1419_ = v_quotContext_1539_;
v___y_1420_ = v___x_1549_;
v___y_1421_ = v___x_1579_;
goto v___jp_1400_;
}
}
else
{
lean_object* v_a_1580_; lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_ref_1544_);
lean_dec(v_wds_x3f_1535_);
lean_dec(v___y_1534_);
lean_dec(v___y_1531_);
lean_dec(v___y_1527_);
v_a_1580_ = lean_ctor_get(v___x_1546_, 0);
v_a_1581_ = lean_ctor_get(v___x_1546_, 1);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1546_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_inc(v_a_1580_);
lean_dec(v___x_1546_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1580_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
v___jp_1589_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_inc_ref_n(v___y_1602_, 2);
v___x_1604_ = l_Array_append___redArg(v___y_1602_, v___y_1603_);
lean_dec_ref(v___y_1603_);
lean_inc_n(v___y_1593_, 2);
lean_inc_n(v___y_1592_, 6);
v___x_1605_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1605_, 0, v___y_1592_);
lean_ctor_set(v___x_1605_, 1, v___y_1593_);
lean_ctor_set(v___x_1605_, 2, v___x_1604_);
v___x_1606_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_1607_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26));
lean_inc_ref_n(v___y_1600_, 2);
lean_inc_ref_n(v___y_1595_, 2);
v___x_1608_ = l_Lean_Name_mkStr4(v___y_1595_, v___y_1600_, v___x_1606_, v___x_1607_);
v___x_1609_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39));
v___x_1610_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___y_1592_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
lean_inc_ref(v___y_1599_);
v___x_1611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___y_1592_);
lean_ctor_set(v___x_1611_, 1, v___y_1599_);
lean_inc(v___y_1590_);
v___x_1612_ = l_Lean_Syntax_node2(v___y_1592_, v___y_1590_, v___x_1611_, v___y_1596_);
v___x_1613_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27));
v___x_1614_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___x_1615_ = l_Lean_Name_mkStr4(v___y_1595_, v___y_1600_, v___x_1613_, v___x_1614_);
v___x_1616_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1616_, 0, v___y_1592_);
lean_ctor_set(v___x_1616_, 1, v___y_1593_);
lean_ctor_set(v___x_1616_, 2, v___y_1602_);
lean_inc_ref(v___x_1616_);
v___x_1617_ = l_Lean_Syntax_node2(v___y_1592_, v___x_1615_, v___x_1616_, v___x_1616_);
if (lean_obj_tag(v___y_1601_) == 1)
{
lean_object* v_val_1618_; lean_object* v___x_1619_; 
v_val_1618_ = lean_ctor_get(v___y_1601_, 0);
lean_inc(v_val_1618_);
lean_dec_ref_known(v___y_1601_, 1);
v___x_1619_ = l_Array_mkArray1___redArg(v_val_1618_);
v___y_1378_ = v___y_1591_;
v___y_1379_ = v___x_1605_;
v___y_1380_ = v___y_1598_;
v___y_1381_ = v___x_1617_;
v___y_1382_ = v___x_1608_;
v___y_1383_ = v___y_1592_;
v___y_1384_ = v___y_1593_;
v___y_1385_ = v___x_1610_;
v___y_1386_ = v___y_1594_;
v___y_1387_ = v___y_1597_;
v___y_1388_ = v___x_1612_;
v___y_1389_ = v___y_1602_;
v___y_1390_ = v___x_1619_;
goto v___jp_1377_;
}
else
{
lean_object* v___x_1620_; 
lean_dec(v___y_1601_);
v___x_1620_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___y_1378_ = v___y_1591_;
v___y_1379_ = v___x_1605_;
v___y_1380_ = v___y_1598_;
v___y_1381_ = v___x_1617_;
v___y_1382_ = v___x_1608_;
v___y_1383_ = v___y_1592_;
v___y_1384_ = v___y_1593_;
v___y_1385_ = v___x_1610_;
v___y_1386_ = v___y_1594_;
v___y_1387_ = v___y_1597_;
v___y_1388_ = v___x_1612_;
v___y_1389_ = v___y_1602_;
v___y_1390_ = v___x_1620_;
goto v___jp_1377_;
}
}
v___jp_1621_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_inc_ref(v___y_1634_);
v___x_1636_ = l_Array_append___redArg(v___y_1634_, v___y_1635_);
lean_dec_ref(v___y_1635_);
lean_inc(v___y_1624_);
lean_inc(v___y_1623_);
v___x_1637_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1637_, 0, v___y_1623_);
lean_ctor_set(v___x_1637_, 1, v___y_1624_);
lean_ctor_set(v___x_1637_, 2, v___x_1636_);
v___x_1638_ = l_Lean_SourceInfo_fromRef(v___y_1631_, v___x_1396_);
lean_dec(v___y_1631_);
v___x_1639_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23));
v___x_1640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
if (lean_obj_tag(v___y_1628_) == 1)
{
lean_object* v_val_1641_; lean_object* v___x_1642_; 
v_val_1641_ = lean_ctor_get(v___y_1628_, 0);
lean_inc(v_val_1641_);
lean_dec_ref_known(v___y_1628_, 1);
v___x_1642_ = l_Array_mkArray1___redArg(v_val_1641_);
v___y_1590_ = v___y_1622_;
v___y_1591_ = v___x_1640_;
v___y_1592_ = v___y_1623_;
v___y_1593_ = v___y_1624_;
v___y_1594_ = v___y_1625_;
v___y_1595_ = v___y_1626_;
v___y_1596_ = v___y_1627_;
v___y_1597_ = v___x_1637_;
v___y_1598_ = v___y_1629_;
v___y_1599_ = v___y_1630_;
v___y_1600_ = v___y_1632_;
v___y_1601_ = v___y_1633_;
v___y_1602_ = v___y_1634_;
v___y_1603_ = v___x_1642_;
goto v___jp_1589_;
}
else
{
lean_object* v___x_1643_; 
lean_dec(v___y_1628_);
v___x_1643_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___y_1590_ = v___y_1622_;
v___y_1591_ = v___x_1640_;
v___y_1592_ = v___y_1623_;
v___y_1593_ = v___y_1624_;
v___y_1594_ = v___y_1625_;
v___y_1595_ = v___y_1626_;
v___y_1596_ = v___y_1627_;
v___y_1597_ = v___x_1637_;
v___y_1598_ = v___y_1629_;
v___y_1599_ = v___y_1630_;
v___y_1600_ = v___y_1632_;
v___y_1601_ = v___y_1633_;
v___y_1602_ = v___y_1634_;
v___y_1603_ = v___x_1643_;
goto v___jp_1589_;
}
}
v___jp_1644_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
lean_inc_ref(v___y_1657_);
v___x_1659_ = l_Array_append___redArg(v___y_1657_, v___y_1658_);
lean_dec_ref(v___y_1658_);
lean_inc(v___y_1647_);
lean_inc(v___y_1646_);
v___x_1660_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1660_, 0, v___y_1646_);
lean_ctor_set(v___x_1660_, 1, v___y_1647_);
lean_ctor_set(v___x_1660_, 2, v___x_1659_);
if (lean_obj_tag(v___y_1656_) == 1)
{
lean_object* v_val_1661_; lean_object* v___x_1662_; 
v_val_1661_ = lean_ctor_get(v___y_1656_, 0);
lean_inc(v_val_1661_);
lean_dec_ref_known(v___y_1656_, 1);
v___x_1662_ = l_Array_mkArray1___redArg(v_val_1661_);
v___y_1622_ = v___y_1645_;
v___y_1623_ = v___y_1646_;
v___y_1624_ = v___y_1647_;
v___y_1625_ = v___x_1660_;
v___y_1626_ = v___y_1648_;
v___y_1627_ = v___y_1649_;
v___y_1628_ = v___y_1650_;
v___y_1629_ = v___y_1651_;
v___y_1630_ = v___y_1652_;
v___y_1631_ = v___y_1653_;
v___y_1632_ = v___y_1654_;
v___y_1633_ = v___y_1655_;
v___y_1634_ = v___y_1657_;
v___y_1635_ = v___x_1662_;
goto v___jp_1621_;
}
else
{
lean_object* v___x_1663_; 
lean_dec(v___y_1656_);
v___x_1663_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___y_1622_ = v___y_1645_;
v___y_1623_ = v___y_1646_;
v___y_1624_ = v___y_1647_;
v___y_1625_ = v___x_1660_;
v___y_1626_ = v___y_1648_;
v___y_1627_ = v___y_1649_;
v___y_1628_ = v___y_1650_;
v___y_1629_ = v___y_1651_;
v___y_1630_ = v___y_1652_;
v___y_1631_ = v___y_1653_;
v___y_1632_ = v___y_1654_;
v___y_1633_ = v___y_1655_;
v___y_1634_ = v___y_1657_;
v___y_1635_ = v___x_1663_;
goto v___jp_1621_;
}
}
v___jp_1664_:
{
lean_object* v_ref_1677_; uint8_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v_ref_1677_ = lean_ctor_get(v___y_1675_, 5);
v___x_1678_ = 0;
v___x_1679_ = l_Lean_SourceInfo_fromRef(v_ref_1677_, v___x_1678_);
v___x_1680_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_1681_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
if (lean_obj_tag(v___y_1668_) == 1)
{
lean_object* v_val_1682_; lean_object* v___x_1683_; 
v_val_1682_ = lean_ctor_get(v___y_1668_, 0);
lean_inc(v_val_1682_);
lean_dec_ref_known(v___y_1668_, 1);
v___x_1683_ = l_Array_mkArray1___redArg(v_val_1682_);
v___y_1645_ = v___y_1665_;
v___y_1646_ = v___x_1679_;
v___y_1647_ = v___x_1680_;
v___y_1648_ = v___y_1672_;
v___y_1649_ = v___y_1671_;
v___y_1650_ = v___y_1670_;
v___y_1651_ = v___y_1676_;
v___y_1652_ = v___y_1666_;
v___y_1653_ = v___y_1667_;
v___y_1654_ = v___y_1669_;
v___y_1655_ = v_wds_x3f_1674_;
v___y_1656_ = v___y_1673_;
v___y_1657_ = v___x_1681_;
v___y_1658_ = v___x_1683_;
goto v___jp_1644_;
}
else
{
lean_object* v___x_1684_; 
lean_dec(v___y_1668_);
v___x_1684_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___y_1645_ = v___y_1665_;
v___y_1646_ = v___x_1679_;
v___y_1647_ = v___x_1680_;
v___y_1648_ = v___y_1672_;
v___y_1649_ = v___y_1671_;
v___y_1650_ = v___y_1670_;
v___y_1651_ = v___y_1676_;
v___y_1652_ = v___y_1666_;
v___y_1653_ = v___y_1667_;
v___y_1654_ = v___y_1669_;
v___y_1655_ = v_wds_x3f_1674_;
v___y_1656_ = v___y_1673_;
v___y_1657_ = v___x_1681_;
v___y_1658_ = v___x_1684_;
goto v___jp_1644_;
}
}
v___jp_1685_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; uint8_t v___x_1698_; 
v___x_1695_ = lean_unsigned_to_nat(4u);
v___x_1696_ = l_Lean_Syntax_getArg(v_stx_1350_, v___x_1695_);
v___x_1697_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26));
lean_inc(v___x_1696_);
v___x_1698_ = l_Lean_Syntax_isOfKind(v___x_1696_, v___x_1697_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1699_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_1700_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_1701_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_1702_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27));
lean_inc(v___x_1696_);
v___x_1703_ = l_Lean_Syntax_isOfKind(v___x_1696_, v___x_1702_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec(v___x_1696_);
lean_dec(v_pkg_x3f_1692_);
lean_dec(v___y_1691_);
lean_dec(v___y_1688_);
lean_dec(v___y_1687_);
v___x_1704_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1705_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1350_, v___x_1704_, v___y_1693_, v___y_1694_);
lean_dec(v_stx_1350_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; 
v___x_1706_ = l_Lean_Syntax_getArg(v___x_1696_, v___y_1686_);
v___x_1707_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28));
lean_inc(v___x_1706_);
v___x_1708_ = l_Lean_Syntax_isOfKind(v___x_1706_, v___x_1707_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_dec(v___x_1706_);
lean_dec(v___x_1696_);
lean_dec(v_pkg_x3f_1692_);
lean_dec(v___y_1691_);
lean_dec(v___y_1688_);
lean_dec(v___y_1687_);
v___x_1709_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1710_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1350_, v___x_1709_, v___y_1693_, v___y_1694_);
lean_dec(v_stx_1350_);
return v___x_1710_;
}
else
{
lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1711_ = l_Lean_Syntax_getArg(v___x_1706_, v___x_1399_);
v___x_1712_ = l_Lean_Syntax_matchesNull(v___x_1711_, v___x_1399_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec(v___x_1706_);
lean_dec(v___x_1696_);
lean_dec(v_pkg_x3f_1692_);
lean_dec(v___y_1691_);
lean_dec(v___y_1688_);
lean_dec(v___y_1687_);
v___x_1713_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1714_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1350_, v___x_1713_, v___y_1693_, v___y_1694_);
lean_dec(v_stx_1350_);
return v___x_1714_;
}
else
{
lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1715_ = l_Lean_Syntax_getArg(v___x_1706_, v___y_1690_);
lean_dec(v___x_1706_);
v___x_1716_ = l_Lean_Syntax_matchesNull(v___x_1715_, v___x_1399_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_dec(v___x_1696_);
lean_dec(v_pkg_x3f_1692_);
lean_dec(v___y_1691_);
lean_dec(v___y_1688_);
lean_dec(v___y_1687_);
v___x_1717_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1718_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1350_, v___x_1717_, v___y_1693_, v___y_1694_);
lean_dec(v_stx_1350_);
return v___x_1718_;
}
else
{
lean_object* v___x_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; 
v___x_1719_ = l_Lean_Syntax_getArg(v___x_1696_, v___y_1690_);
v___x_1720_ = l_Lean_Syntax_getArg(v___x_1696_, v___y_1689_);
lean_dec(v___x_1696_);
v___x_1721_ = l_Lean_Syntax_isNone(v___x_1720_);
if (v___x_1721_ == 0)
{
uint8_t v___x_1722_; 
lean_inc(v___x_1720_);
v___x_1722_ = l_Lean_Syntax_matchesNull(v___x_1720_, v___y_1690_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_dec(v___x_1720_);
lean_dec(v___x_1719_);
lean_dec(v_pkg_x3f_1692_);
lean_dec(v___y_1691_);
lean_dec(v___y_1688_);
lean_dec(v___y_1687_);
v___x_1723_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1724_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1350_, v___x_1723_, v___y_1693_, v___y_1694_);
lean_dec(v_stx_1350_);
return v___x_1724_;
}
else
{
lean_object* v_wds_x3f_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; 
v_wds_x3f_1725_ = l_Lean_Syntax_getArg(v___x_1720_, v___x_1399_);
lean_dec(v___x_1720_);
v___x_1726_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_1725_);
v___x_1727_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1725_, v___x_1726_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_dec(v_wds_x3f_1725_);
lean_dec(v___x_1719_);
lean_dec(v_pkg_x3f_1692_);
lean_dec(v___y_1691_);
lean_dec(v___y_1688_);
lean_dec(v___y_1687_);
v___x_1728_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1729_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1350_, v___x_1728_, v___y_1693_, v___y_1694_);
lean_dec(v_stx_1350_);
return v___x_1729_;
}
else
{
lean_object* v___x_1730_; 
lean_dec(v_stx_1350_);
v___x_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1730_, 0, v_wds_x3f_1725_);
v___y_1523_ = v___x_1699_;
v___y_1524_ = v___x_1702_;
v___y_1525_ = v___x_1701_;
v___y_1526_ = v___x_1700_;
v___y_1527_ = v___x_1719_;
v___y_1528_ = v___x_1707_;
v___y_1529_ = v___x_1698_;
v___y_1530_ = v___y_1687_;
v___y_1531_ = v___y_1688_;
v___y_1532_ = v___y_1690_;
v___y_1533_ = v_pkg_x3f_1692_;
v___y_1534_ = v___y_1691_;
v_wds_x3f_1535_ = v___x_1730_;
v___y_1536_ = v___y_1693_;
v___y_1537_ = v___y_1694_;
goto v___jp_1522_;
}
}
}
else
{
lean_object* v___x_1731_; 
lean_dec(v___x_1720_);
lean_dec(v_stx_1350_);
v___x_1731_ = lean_box(0);
v___y_1523_ = v___x_1699_;
v___y_1524_ = v___x_1702_;
v___y_1525_ = v___x_1701_;
v___y_1526_ = v___x_1700_;
v___y_1527_ = v___x_1719_;
v___y_1528_ = v___x_1707_;
v___y_1529_ = v___x_1698_;
v___y_1530_ = v___y_1687_;
v___y_1531_ = v___y_1688_;
v___y_1532_ = v___y_1690_;
v___y_1533_ = v_pkg_x3f_1692_;
v___y_1534_ = v___y_1691_;
v_wds_x3f_1535_ = v___x_1731_;
v___y_1536_ = v___y_1693_;
v___y_1537_ = v___y_1694_;
goto v___jp_1522_;
}
}
}
}
}
}
else
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1732_ = l_Lean_Syntax_getArg(v___x_1696_, v___x_1399_);
v___x_1733_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_1734_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_1735_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29));
v___x_1736_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30));
lean_inc(v___x_1732_);
v___x_1737_ = l_Lean_Syntax_isOfKind(v___x_1732_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v___x_1732_);
lean_dec(v___x_1696_);
lean_dec(v_pkg_x3f_1692_);
lean_dec(v___y_1691_);
lean_dec(v___y_1688_);
lean_dec(v___y_1687_);
v___x_1738_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1739_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1350_, v___x_1738_, v___y_1693_, v___y_1694_);
lean_dec(v_stx_1350_);
return v___x_1739_;
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
v___x_1740_ = l_Lean_Syntax_getArg(v___x_1732_, v___y_1690_);
lean_dec(v___x_1732_);
v___x_1741_ = l_Lean_Syntax_getArg(v___x_1696_, v___y_1690_);
lean_dec(v___x_1696_);
v___x_1742_ = l_Lean_Syntax_isNone(v___x_1741_);
if (v___x_1742_ == 0)
{
uint8_t v___x_1743_; 
lean_inc(v___x_1741_);
v___x_1743_ = l_Lean_Syntax_matchesNull(v___x_1741_, v___y_1690_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_dec(v___x_1741_);
lean_dec(v___x_1740_);
lean_dec(v_pkg_x3f_1692_);
lean_dec(v___y_1691_);
lean_dec(v___y_1688_);
lean_dec(v___y_1687_);
v___x_1744_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1745_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1350_, v___x_1744_, v___y_1693_, v___y_1694_);
lean_dec(v_stx_1350_);
return v___x_1745_;
}
else
{
lean_object* v_wds_x3f_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v_wds_x3f_1746_ = l_Lean_Syntax_getArg(v___x_1741_, v___x_1399_);
lean_dec(v___x_1741_);
v___x_1747_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_1746_);
v___x_1748_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1746_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
lean_dec(v_wds_x3f_1746_);
lean_dec(v___x_1740_);
lean_dec(v_pkg_x3f_1692_);
lean_dec(v___y_1691_);
lean_dec(v___y_1688_);
lean_dec(v___y_1687_);
v___x_1749_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1750_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1350_, v___x_1749_, v___y_1693_, v___y_1694_);
lean_dec(v_stx_1350_);
return v___x_1750_;
}
else
{
lean_object* v___x_1751_; 
lean_dec(v_stx_1350_);
v___x_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1751_, 0, v_wds_x3f_1746_);
v___y_1665_ = v___x_1736_;
v___y_1666_ = v___x_1735_;
v___y_1667_ = v___y_1687_;
v___y_1668_ = v___y_1688_;
v___y_1669_ = v___x_1734_;
v___y_1670_ = v_pkg_x3f_1692_;
v___y_1671_ = v___x_1740_;
v___y_1672_ = v___x_1733_;
v___y_1673_ = v___y_1691_;
v_wds_x3f_1674_ = v___x_1751_;
v___y_1675_ = v___y_1693_;
v___y_1676_ = v___y_1694_;
goto v___jp_1664_;
}
}
}
else
{
lean_object* v___x_1752_; 
lean_dec(v___x_1741_);
lean_dec(v_stx_1350_);
v___x_1752_ = lean_box(0);
v___y_1665_ = v___x_1736_;
v___y_1666_ = v___x_1735_;
v___y_1667_ = v___y_1687_;
v___y_1668_ = v___y_1688_;
v___y_1669_ = v___x_1734_;
v___y_1670_ = v_pkg_x3f_1692_;
v___y_1671_ = v___x_1740_;
v___y_1672_ = v___x_1733_;
v___y_1673_ = v___y_1691_;
v_wds_x3f_1674_ = v___x_1752_;
v___y_1675_ = v___y_1693_;
v___y_1676_ = v___y_1694_;
goto v___jp_1664_;
}
}
}
}
v___jp_1753_:
{
lean_object* v___x_1759_; lean_object* v_kw_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1759_ = lean_unsigned_to_nat(2u);
v_kw_1760_ = l_Lean_Syntax_getArg(v_stx_1350_, v___x_1759_);
v___x_1761_ = lean_unsigned_to_nat(3u);
v___x_1762_ = l_Lean_Syntax_getArg(v_stx_1350_, v___x_1761_);
v___x_1763_ = l_Lean_Syntax_isNone(v___x_1762_);
if (v___x_1763_ == 0)
{
uint8_t v___x_1764_; 
lean_inc(v___x_1762_);
v___x_1764_ = l_Lean_Syntax_matchesNull(v___x_1762_, v___y_1755_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_dec(v___x_1762_);
lean_dec(v_kw_1760_);
lean_dec(v_attrs_x3f_1756_);
lean_dec(v___y_1754_);
v___x_1765_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1766_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1350_, v___x_1765_, v___y_1757_, v___y_1758_);
lean_dec(v_stx_1350_);
return v___x_1766_;
}
else
{
lean_object* v_pkg_x3f_1767_; lean_object* v___x_1768_; 
v_pkg_x3f_1767_ = l_Lean_Syntax_getArg(v___x_1762_, v___x_1399_);
lean_dec(v___x_1762_);
v___x_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1768_, 0, v_pkg_x3f_1767_);
v___y_1686_ = v___x_1759_;
v___y_1687_ = v_kw_1760_;
v___y_1688_ = v___y_1754_;
v___y_1689_ = v___x_1761_;
v___y_1690_ = v___y_1755_;
v___y_1691_ = v_attrs_x3f_1756_;
v_pkg_x3f_1692_ = v___x_1768_;
v___y_1693_ = v___y_1757_;
v___y_1694_ = v___y_1758_;
goto v___jp_1685_;
}
}
else
{
lean_object* v___x_1769_; 
lean_dec(v___x_1762_);
v___x_1769_ = lean_box(0);
v___y_1686_ = v___x_1759_;
v___y_1687_ = v_kw_1760_;
v___y_1688_ = v___y_1754_;
v___y_1689_ = v___x_1761_;
v___y_1690_ = v___y_1755_;
v___y_1691_ = v_attrs_x3f_1756_;
v_pkg_x3f_1692_ = v___x_1769_;
v___y_1693_ = v___y_1757_;
v___y_1694_ = v___y_1758_;
goto v___jp_1685_;
}
}
v___jp_1770_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1774_ = lean_unsigned_to_nat(1u);
v___x_1775_ = l_Lean_Syntax_getArg(v_stx_1350_, v___x_1774_);
v___x_1776_ = l_Lean_Syntax_isNone(v___x_1775_);
if (v___x_1776_ == 0)
{
uint8_t v___x_1777_; 
lean_inc(v___x_1775_);
v___x_1777_ = l_Lean_Syntax_matchesNull(v___x_1775_, v___x_1774_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
lean_dec(v___x_1775_);
lean_dec(v_doc_x3f_1771_);
v___x_1778_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1779_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1350_, v___x_1778_, v___y_1772_, v___y_1773_);
lean_dec(v_stx_1350_);
return v___x_1779_;
}
else
{
lean_object* v_attrs_x3f_1780_; lean_object* v___x_1781_; 
v_attrs_x3f_1780_ = l_Lean_Syntax_getArg(v___x_1775_, v___x_1399_);
lean_dec(v___x_1775_);
v___x_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1781_, 0, v_attrs_x3f_1780_);
v___y_1754_ = v_doc_x3f_1771_;
v___y_1755_ = v___x_1774_;
v_attrs_x3f_1756_ = v___x_1781_;
v___y_1757_ = v___y_1772_;
v___y_1758_ = v___y_1773_;
goto v___jp_1753_;
}
}
else
{
lean_object* v___x_1782_; 
lean_dec(v___x_1775_);
v___x_1782_ = lean_box(0);
v___y_1754_ = v_doc_x3f_1771_;
v___y_1755_ = v___x_1774_;
v_attrs_x3f_1756_ = v___x_1782_;
v___y_1757_ = v___y_1772_;
v___y_1758_ = v___y_1773_;
goto v___jp_1753_;
}
}
}
v___jp_1353_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_inc_ref(v___y_1360_);
v___x_1370_ = l_Array_append___redArg(v___y_1360_, v___y_1369_);
lean_dec_ref(v___y_1369_);
lean_inc(v___y_1367_);
lean_inc_n(v___y_1368_, 3);
v___x_1371_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1371_, 0, v___y_1368_);
lean_ctor_set(v___x_1371_, 1, v___y_1367_);
lean_ctor_set(v___x_1371_, 2, v___x_1370_);
lean_inc(v___y_1354_);
v___x_1372_ = l_Lean_Syntax_node4(v___y_1368_, v___y_1354_, v___y_1361_, v___y_1364_, v___y_1355_, v___x_1371_);
v___x_1373_ = l_Lean_Syntax_node5(v___y_1368_, v___y_1357_, v___y_1366_, v___y_1356_, v___y_1358_, v___x_1372_, v___y_1362_);
v___x_1374_ = l_Lean_Syntax_node2(v___y_1368_, v___y_1365_, v___y_1359_, v___x_1373_);
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v___y_1363_);
return v___x_1375_;
}
v___jp_1377_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_inc_ref(v___y_1389_);
v___x_1391_ = l_Array_append___redArg(v___y_1389_, v___y_1390_);
lean_dec_ref(v___y_1390_);
lean_inc(v___y_1384_);
lean_inc_n(v___y_1383_, 2);
v___x_1392_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1392_, 0, v___y_1383_);
lean_ctor_set(v___x_1392_, 1, v___y_1384_);
lean_ctor_set(v___x_1392_, 2, v___x_1391_);
v___x_1393_ = l_Lean_Syntax_node4(v___y_1383_, v___y_1382_, v___y_1385_, v___y_1388_, v___y_1381_, v___x_1392_);
v___x_1394_ = l_Lean_Syntax_node5(v___y_1383_, v___x_1376_, v___y_1386_, v___y_1387_, v___y_1378_, v___y_1379_, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
lean_ctor_set(v___x_1395_, 1, v___y_1380_);
return v___x_1395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___boxed(lean_object* v_stx_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl(v_stx_1792_, v_a_1793_, v_a_1794_);
lean_dec_ref(v_a_1793_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1(){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1801_ = l_Lean_Elab_macroAttribute;
v___x_1802_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1));
v___x_1803_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1));
v___x_1804_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___boxed), 3, 0);
v___x_1805_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1801_, v___x_1802_, v___x_1803_, v___x_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___boxed(lean_object* v_a_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1();
return v_res_1807_;
}
}
lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Extensions(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_Package(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_DSL_Package(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin);
lean_object* initialize_Lake_Config_Package(uint8_t builtin);
lean_object* initialize_Lake_DSL_Extensions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Package(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_DSL_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_DSL_Package(builtin);
}
#ifdef __cplusplus
}
#endif
