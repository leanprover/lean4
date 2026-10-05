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
lean_object* v_wds_x3f_470_; 
v_wds_x3f_470_ = l_Lean_Syntax_getArg(v___x_465_, v___x_432_);
lean_dec(v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_470_);
v___x_474_ = l_Lean_Syntax_isOfKind(v_wds_x3f_470_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec(v_wds_x3f_470_);
lean_dec(v___x_457_);
lean_dec(v_tk_456_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_475_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_476_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_475_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_476_;
}
else
{
goto v___jp_471_;
}
}
else
{
goto v___jp_471_;
}
v___jp_471_:
{
lean_object* v___x_472_; 
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v_wds_x3f_470_);
v_wds_x3f_459_ = v___x_472_;
v___y_460_ = v_a_307_;
v___y_461_ = v_a_308_;
goto v___jp_458_;
}
}
}
else
{
lean_object* v___x_477_; 
lean_dec(v___x_465_);
v___x_477_ = lean_box(0);
v_wds_x3f_459_ = v___x_477_;
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
lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_478_ = l_Lean_Syntax_getArg(v___x_439_, v___x_435_);
v___x_479_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32));
lean_inc(v___x_478_);
v___x_480_ = l_Lean_Syntax_isOfKind(v___x_478_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec(v___x_478_);
lean_dec(v___x_439_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_481_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_482_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_481_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_482_;
}
else
{
lean_object* v_tk_483_; lean_object* v___x_484_; lean_object* v_wds_x3f_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v_tk_483_ = l_Lean_Syntax_getArg(v___x_439_, v___x_432_);
v___x_484_ = l_Lean_Syntax_getArg(v___x_478_, v___x_432_);
lean_dec(v___x_478_);
v___x_492_ = lean_unsigned_to_nat(2u);
v___x_493_ = l_Lean_Syntax_getArg(v___x_439_, v___x_492_);
lean_dec(v___x_439_);
v___x_494_ = l_Lean_Syntax_isNone(v___x_493_);
if (v___x_494_ == 0)
{
uint8_t v___x_495_; 
lean_inc(v___x_493_);
v___x_495_ = l_Lean_Syntax_matchesNull(v___x_493_, v___x_435_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec(v___x_493_);
lean_dec(v___x_484_);
lean_dec(v_tk_483_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_496_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_497_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_496_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_497_;
}
else
{
lean_object* v_wds_x3f_498_; 
v_wds_x3f_498_ = l_Lean_Syntax_getArg(v___x_493_, v___x_432_);
lean_dec(v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_498_);
v___x_502_ = l_Lean_Syntax_isOfKind(v_wds_x3f_498_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec(v_wds_x3f_498_);
lean_dec(v___x_484_);
lean_dec(v_tk_483_);
lean_dec(v_ty_305_);
lean_dec(v_id_304_);
lean_dec(v_tyName_303_);
v___x_503_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
v___x_504_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_306_, v___x_503_, v_a_307_, v_a_308_);
lean_dec(v_config_306_);
return v___x_504_;
}
else
{
goto v___jp_499_;
}
}
else
{
goto v___jp_499_;
}
v___jp_499_:
{
lean_object* v___x_500_; 
v___x_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_500_, 0, v_wds_x3f_498_);
v_wds_x3f_486_ = v___x_500_;
v___y_487_ = v_a_307_;
v___y_488_ = v_a_308_;
goto v___jp_485_;
}
}
}
else
{
lean_object* v___x_505_; 
lean_dec(v___x_493_);
v___x_505_ = lean_box(0);
v_wds_x3f_486_ = v___x_505_;
v___y_487_ = v_a_307_;
v___y_488_ = v_a_308_;
goto v___jp_485_;
}
v___jp_485_:
{
lean_object* v_fs_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_fs_489_ = l_Lean_Syntax_getArgs(v___x_484_);
lean_dec(v___x_484_);
v___x_490_ = l_Lean_Syntax_getHeadInfo(v_tk_483_);
lean_dec(v_tk_483_);
v___x_491_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_489_);
lean_dec_ref(v_fs_489_);
v_whereInfo_397_ = v___x_490_;
v_fs_398_ = v___x_491_;
v_wds_x3f_399_ = v_wds_x3f_486_;
v___y_400_ = v___y_487_;
v___y_401_ = v___y_488_;
goto v___jp_396_;
}
}
}
}
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec(v___x_433_);
v___x_506_ = lean_box(2);
v___x_507_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8));
v___x_508_ = lean_box(0);
v_whereInfo_397_ = v___x_506_;
v_fs_398_ = v___x_507_;
v_wds_x3f_399_ = v___x_508_;
v___y_400_ = v_a_307_;
v___y_401_ = v_a_308_;
goto v___jp_396_;
}
}
v___jp_310_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_319_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0));
lean_inc_ref_n(v___y_316_, 5);
lean_inc_ref_n(v___y_314_, 6);
lean_inc_ref_n(v___y_317_, 6);
v___x_320_ = l_Lean_Name_mkStr4(v___y_317_, v___y_314_, v___y_316_, v___x_319_);
v___x_321_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1));
v___x_322_ = l_Lean_Name_mkStr4(v___y_317_, v___y_314_, v___y_316_, v___x_321_);
v___x_323_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_324_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
lean_inc_n(v___y_313_, 8);
v___x_325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_325_, 0, v___y_313_);
lean_ctor_set(v___x_325_, 1, v___x_323_);
lean_ctor_set(v___x_325_, 2, v___x_324_);
lean_inc_ref_n(v___x_325_, 8);
v___x_326_ = l_Lean_Syntax_node7(v___y_313_, v___x_322_, v___x_325_, v___x_325_, v___x_325_, v___x_325_, v___x_325_, v___x_325_, v___x_325_);
v___x_327_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5));
v___x_328_ = l_Lean_Name_mkStr4(v___y_317_, v___y_314_, v___y_316_, v___x_327_);
v___x_329_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6));
v___x_330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_330_, 0, v___y_313_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7));
v___x_332_ = l_Lean_Name_mkStr4(v___y_317_, v___y_314_, v___y_316_, v___x_331_);
v___x_333_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8));
lean_inc_n(v___y_315_, 2);
v___x_334_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_334_, 0, v___y_315_);
lean_ctor_set(v___x_334_, 1, v___x_323_);
lean_ctor_set(v___x_334_, 2, v___x_333_);
v___x_335_ = lean_unsigned_to_nat(2u);
v___x_336_ = lean_mk_empty_array_with_capacity(v___x_335_);
v___x_337_ = lean_array_push(v___x_336_, v_id_304_);
v___x_338_ = lean_array_push(v___x_337_, v___x_334_);
v___x_339_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_339_, 0, v___y_315_);
lean_ctor_set(v___x_339_, 1, v___x_332_);
lean_ctor_set(v___x_339_, 2, v___x_338_);
v___x_340_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9));
v___x_341_ = l_Lean_Name_mkStr4(v___y_317_, v___y_314_, v___y_316_, v___x_340_);
v___x_342_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10));
v___x_343_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11));
v___x_344_ = l_Lean_Name_mkStr4(v___y_317_, v___y_314_, v___x_342_, v___x_343_);
v___x_345_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12));
v___x_346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_346_, 0, v___y_313_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = l_Lean_Syntax_node2(v___y_313_, v___x_344_, v___x_346_, v_ty_305_);
v___x_348_ = l_Lean_Syntax_node1(v___y_313_, v___x_323_, v___x_347_);
v___x_349_ = l_Lean_Syntax_node2(v___y_313_, v___x_341_, v___x_325_, v___x_348_);
v___x_350_ = l_Lean_Syntax_node5(v___y_313_, v___x_328_, v___x_330_, v___x_339_, v___x_349_, v___y_312_, v___x_325_);
v___x_351_ = l_Lean_Syntax_node2(v___y_313_, v___x_320_, v___x_326_, v___x_350_);
lean_inc(v___x_351_);
v___x_352_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_352_, 0, v___x_351_);
v___x_353_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_config_306_, v___x_351_, v___x_352_, v___y_318_, v___y_311_);
return v___x_353_;
}
v___jp_354_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_364_ = l_Lean_mkOptionalNode(v___y_363_);
v___x_365_ = lean_unsigned_to_nat(3u);
v___x_366_ = lean_mk_empty_array_with_capacity(v___x_365_);
v___x_367_ = lean_array_push(v___x_366_, v___y_355_);
v___x_368_ = lean_array_push(v___x_367_, v___y_359_);
v___x_369_ = lean_array_push(v___x_368_, v___x_364_);
v___x_370_ = lean_box(2);
lean_inc(v___y_362_);
v___x_371_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v___y_362_);
lean_ctor_set(v___x_371_, 2, v___x_369_);
v___x_372_ = l_Lean_Elab_Command_getRef___redArg(v___y_361_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_373_);
lean_dec_ref_known(v___x_372_, 1);
v___x_374_ = 0;
v___x_375_ = l_Lean_SourceInfo_fromRef(v_a_373_, v___x_374_);
lean_dec(v_a_373_);
v___x_376_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_361_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_quotContext_x3f_377_; 
lean_dec_ref_known(v___x_376_, 1);
v_quotContext_x3f_377_ = lean_ctor_get(v___y_361_, 5);
if (lean_obj_tag(v_quotContext_x3f_377_) == 0)
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_356_);
lean_dec_ref(v___x_378_);
v___y_311_ = v___y_356_;
v___y_312_ = v___x_371_;
v___y_313_ = v___x_375_;
v___y_314_ = v___y_357_;
v___y_315_ = v___x_370_;
v___y_316_ = v___y_358_;
v___y_317_ = v___y_360_;
v___y_318_ = v___y_361_;
goto v___jp_310_;
}
else
{
v___y_311_ = v___y_356_;
v___y_312_ = v___x_371_;
v___y_313_ = v___x_375_;
v___y_314_ = v___y_357_;
v___y_315_ = v___x_370_;
v___y_316_ = v___y_358_;
v___y_317_ = v___y_360_;
v___y_318_ = v___y_361_;
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
v___y_355_ = v_whereTk_404_;
v___y_356_ = v___y_401_;
v___y_357_ = v___x_408_;
v___y_358_ = v___x_409_;
v___y_359_ = v_a_406_;
v___y_360_ = v___x_407_;
v___y_361_ = v___y_400_;
v___y_362_ = v___x_410_;
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
v___y_355_ = v_whereTk_404_;
v___y_356_ = v___y_401_;
v___y_357_ = v___x_408_;
v___y_358_ = v___x_409_;
v___y_359_ = v_a_406_;
v___y_360_ = v___x_407_;
v___y_361_ = v___y_400_;
v___y_362_ = v___x_410_;
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
LEAN_EXPORT lean_object* l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___boxed(lean_object* v_tyName_509_, lean_object* v_id_510_, lean_object* v_ty_511_, lean_object* v_config_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(v_tyName_509_, v_id_510_, v_ty_511_, v_config_512_, v_a_513_, v_a_514_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
return v_res_516_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13));
v___x_539_ = l_Lean_stringToMessageData(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20));
v___x_549_ = l_String_toRawSubstring_x27(v___x_548_);
return v___x_549_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35));
v___x_572_ = l_String_toRawSubstring_x27(v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41));
v___x_580_ = l_String_toRawSubstring_x27(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44));
v___x_585_ = l_String_toRawSubstring_x27(v___x_584_);
return v___x_585_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47));
v___x_590_ = l_String_toRawSubstring_x27(v___x_589_);
return v___x_590_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56));
v___x_601_ = l_String_toRawSubstring_x27(v___x_600_);
return v___x_601_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65));
v___x_617_ = l_String_toRawSubstring_x27(v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand(lean_object* v_stx_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12));
lean_inc(v_stx_620_);
v___x_693_ = l_Lean_Syntax_isOfKind(v_stx_620_, v___x_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14);
v___x_695_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_stx_620_, v___x_694_, v_a_621_, v_a_622_);
lean_dec(v_stx_620_);
return v___x_695_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; uint8_t v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; uint8_t v___y_829_; lean_object* v___y_830_; lean_object* v_a_831_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; uint8_t v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v_a_864_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; uint8_t v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v_a_963_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; uint8_t v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; uint8_t v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v_a_1076_; lean_object* v_kw_1103_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v_nameStx_x3f_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = lean_box(0);
v___x_698_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15));
v___x_699_ = l_Lean_Syntax_getArg(v_stx_620_, v___x_696_);
v___x_700_ = lean_unsigned_to_nat(1u);
v___x_701_ = l_Lean_Syntax_getArg(v_stx_620_, v___x_700_);
v___x_702_ = lean_unsigned_to_nat(2u);
v_kw_1103_ = l_Lean_Syntax_getArg(v_stx_620_, v___x_702_);
v___x_1191_ = lean_unsigned_to_nat(3u);
v___x_1192_ = l_Lean_Syntax_getArg(v_stx_620_, v___x_1191_);
v___x_1193_ = l_Lean_Syntax_isNone(v___x_1192_);
if (v___x_1193_ == 0)
{
uint8_t v___x_1194_; 
lean_inc(v___x_1192_);
v___x_1194_ = l_Lean_Syntax_matchesNull(v___x_1192_, v___x_700_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec(v___x_1192_);
lean_dec(v_kw_1103_);
lean_dec(v___x_701_);
lean_dec(v___x_699_);
v___x_1195_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14);
v___x_1196_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_stx_620_, v___x_1195_, v_a_621_, v_a_622_);
lean_dec(v_stx_620_);
return v___x_1196_;
}
else
{
lean_object* v_nameStx_x3f_1197_; lean_object* v___x_1198_; 
v_nameStx_x3f_1197_ = l_Lean_Syntax_getArg(v___x_1192_, v___x_696_);
lean_dec(v___x_1192_);
v___x_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1198_, 0, v_nameStx_x3f_1197_);
v_nameStx_x3f_1176_ = v___x_1198_;
v___y_1177_ = v_a_621_;
v___y_1178_ = v_a_622_;
goto v___jp_1175_;
}
}
else
{
lean_object* v___x_1199_; 
lean_dec(v___x_1192_);
v___x_1199_ = lean_box(0);
v_nameStx_x3f_1176_ = v___x_1199_;
v___y_1177_ = v_a_621_;
v___y_1178_ = v_a_622_;
goto v___jp_1175_;
}
v___jp_703_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
lean_inc_ref_n(v___y_713_, 3);
v___x_730_ = l_Array_append___redArg(v___y_713_, v___y_729_);
lean_dec_ref(v___y_729_);
lean_inc_n(v___y_723_, 6);
lean_inc_n(v___y_706_, 18);
v___x_731_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_731_, 0, v___y_706_);
lean_ctor_set(v___x_731_, 1, v___y_723_);
lean_ctor_set(v___x_731_, 2, v___x_730_);
v___x_732_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16));
lean_inc_ref(v___y_725_);
lean_inc_ref_n(v___y_705_, 6);
lean_inc_ref_n(v___y_722_, 7);
v___x_733_ = l_Lean_Name_mkStr4(v___y_722_, v___y_705_, v___y_725_, v___x_732_);
v___x_734_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17));
v___x_735_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_735_, 0, v___y_706_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
lean_inc_ref(v___y_721_);
v___x_736_ = l_Lean_Syntax_SepArray_ofElems(v___y_721_, v___y_712_);
lean_dec_ref(v___y_712_);
v___x_737_ = l_Array_append___redArg(v___y_713_, v___x_736_);
lean_dec_ref(v___x_736_);
v___x_738_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_738_, 0, v___y_706_);
lean_ctor_set(v___x_738_, 1, v___y_723_);
lean_ctor_set(v___x_738_, 2, v___x_737_);
v___x_739_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18));
v___x_740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_740_, 0, v___y_706_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
lean_inc(v___x_733_);
v___x_741_ = l_Lean_Syntax_node3(v___y_706_, v___x_733_, v___x_735_, v___x_738_, v___x_740_);
v___x_742_ = l_Lean_Syntax_node1(v___y_706_, v___y_723_, v___x_741_);
v___x_743_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_743_, 0, v___y_706_);
lean_ctor_set(v___x_743_, 1, v___y_723_);
lean_ctor_set(v___x_743_, 2, v___y_713_);
lean_inc_ref_n(v___x_743_, 8);
lean_inc(v___y_728_);
v___x_744_ = l_Lean_Syntax_node7(v___y_706_, v___y_728_, v___x_731_, v___x_742_, v___x_743_, v___x_743_, v___x_743_, v___x_743_, v___x_743_);
v___x_745_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19));
lean_inc_ref_n(v___y_711_, 3);
v___x_746_ = l_Lean_Name_mkStr4(v___y_722_, v___y_705_, v___y_711_, v___x_745_);
v___x_747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_747_, 0, v___y_706_);
lean_ctor_set(v___x_747_, 1, v___x_745_);
v___x_748_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7));
v___x_749_ = l_Lean_Name_mkStr4(v___y_722_, v___y_705_, v___y_711_, v___x_748_);
v___x_750_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8));
lean_inc_n(v___y_704_, 2);
v___x_751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_751_, 0, v___y_704_);
lean_ctor_set(v___x_751_, 1, v___y_723_);
lean_ctor_set(v___x_751_, 2, v___x_750_);
v___x_752_ = lean_mk_empty_array_with_capacity(v___x_702_);
lean_inc(v___y_708_);
lean_inc_ref(v___x_752_);
v___x_753_ = lean_array_push(v___x_752_, v___y_708_);
lean_inc_ref(v___x_751_);
v___x_754_ = lean_array_push(v___x_753_, v___x_751_);
lean_inc(v___x_749_);
v___x_755_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_755_, 0, v___y_704_);
lean_ctor_set(v___x_755_, 1, v___x_749_);
lean_ctor_set(v___x_755_, 2, v___x_754_);
v___x_756_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9));
v___x_757_ = l_Lean_Name_mkStr4(v___y_722_, v___y_705_, v___y_711_, v___x_756_);
v___x_758_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11));
v___x_759_ = l_Lean_Name_mkStr4(v___y_722_, v___y_705_, v___y_725_, v___x_758_);
v___x_760_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12));
v___x_761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_761_, 0, v___y_706_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21);
v___x_763_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22));
v___x_764_ = l_Lean_addMacroScope(v___y_727_, v___x_763_, v___y_710_);
v___x_765_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24));
v___x_766_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25));
lean_inc(v___y_718_);
v___x_767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v___y_718_);
v___x_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_765_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_769_, 0, v___y_706_);
lean_ctor_set(v___x_769_, 1, v___x_762_);
lean_ctor_set(v___x_769_, 2, v___x_764_);
lean_ctor_set(v___x_769_, 3, v___x_768_);
v___x_770_ = l_Lean_Syntax_node2(v___y_706_, v___x_759_, v___x_761_, v___x_769_);
v___x_771_ = l_Lean_Syntax_node1(v___y_706_, v___y_723_, v___x_770_);
lean_inc(v___x_757_);
v___x_772_ = l_Lean_Syntax_node2(v___y_706_, v___x_757_, v___x_743_, v___x_771_);
v___x_773_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26));
v___x_774_ = l_Lean_Name_mkStr4(v___y_722_, v___y_705_, v___y_711_, v___x_773_);
lean_inc_ref(v___y_719_);
v___x_775_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_775_, 0, v___y_706_);
lean_ctor_set(v___x_775_, 1, v___y_719_);
v___x_776_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27));
v___x_777_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___x_778_ = l_Lean_Name_mkStr4(v___y_722_, v___y_705_, v___x_776_, v___x_777_);
lean_inc(v___x_778_);
v___x_779_ = l_Lean_Syntax_node2(v___y_706_, v___x_778_, v___x_743_, v___x_743_);
lean_inc(v___x_774_);
v___x_780_ = l_Lean_Syntax_node4(v___y_706_, v___x_774_, v___x_775_, v___y_724_, v___x_779_, v___x_743_);
lean_inc(v___x_746_);
v___x_781_ = l_Lean_Syntax_node4(v___y_706_, v___x_746_, v___x_747_, v___x_755_, v___x_772_, v___x_780_);
lean_inc(v___y_714_);
v___x_782_ = l_Lean_Syntax_node2(v___y_706_, v___y_714_, v___x_744_, v___x_781_);
lean_inc(v___x_782_);
v___x_783_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(v___x_783_, 0, v___x_782_);
v___x_784_ = l_Lean_Elab_Command_withMacroExpansion___redArg(v_stx_620_, v___x_782_, v___x_783_, v___y_709_, v___y_707_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec_ref_known(v___x_784_, 1);
v___x_785_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29));
v___x_786_ = l_Lean_Name_str___override(v___y_720_, v___x_785_);
v___x_787_ = l_Lean_mkIdentFrom(v___y_708_, v___x_786_, v___y_715_);
lean_dec(v___y_708_);
v___x_788_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_709_, v___y_707_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_790_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
v___x_790_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_709_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_dec_ref_known(v___x_790_, 1);
if (lean_obj_tag(v___y_717_) == 0)
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_707_);
lean_dec_ref(v___x_791_);
v___y_625_ = v___y_704_;
v___y_626_ = v___x_739_;
v___y_627_ = v___x_774_;
v___y_628_ = v___y_716_;
v___y_629_ = v___y_707_;
v___y_630_ = v___x_734_;
v___y_631_ = v___y_719_;
v___y_632_ = v___y_709_;
v___y_633_ = v___x_746_;
v___y_634_ = v___x_787_;
v___y_635_ = v___x_749_;
v___y_636_ = v___y_723_;
v___y_637_ = v___y_722_;
v___y_638_ = v___x_733_;
v___y_639_ = v___x_751_;
v___y_640_ = v___x_752_;
v___y_641_ = v___y_713_;
v___y_642_ = v___y_714_;
v___y_643_ = v___x_757_;
v___y_644_ = v___y_726_;
v___y_645_ = v_a_789_;
v___y_646_ = v___y_728_;
v___y_647_ = v___x_778_;
v___y_648_ = v___x_745_;
goto v___jp_624_;
}
else
{
lean_dec_ref_known(v___y_717_, 1);
v___y_625_ = v___y_704_;
v___y_626_ = v___x_739_;
v___y_627_ = v___x_774_;
v___y_628_ = v___y_716_;
v___y_629_ = v___y_707_;
v___y_630_ = v___x_734_;
v___y_631_ = v___y_719_;
v___y_632_ = v___y_709_;
v___y_633_ = v___x_746_;
v___y_634_ = v___x_787_;
v___y_635_ = v___x_749_;
v___y_636_ = v___y_723_;
v___y_637_ = v___y_722_;
v___y_638_ = v___x_733_;
v___y_639_ = v___x_751_;
v___y_640_ = v___x_752_;
v___y_641_ = v___y_713_;
v___y_642_ = v___y_714_;
v___y_643_ = v___x_757_;
v___y_644_ = v___y_726_;
v___y_645_ = v_a_789_;
v___y_646_ = v___y_728_;
v___y_647_ = v___x_778_;
v___y_648_ = v___x_745_;
goto v___jp_624_;
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec(v_a_789_);
lean_dec(v___x_787_);
lean_dec(v___x_778_);
lean_dec(v___x_774_);
lean_dec(v___x_757_);
lean_dec_ref(v___x_752_);
lean_dec_ref_known(v___x_751_, 3);
lean_dec(v___x_749_);
lean_dec(v___x_746_);
lean_dec(v___x_733_);
lean_dec(v___y_728_);
lean_dec(v___y_726_);
lean_dec(v___y_717_);
lean_dec(v___y_716_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_704_);
v_a_792_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_790_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_790_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec(v___x_787_);
lean_dec(v___x_778_);
lean_dec(v___x_774_);
lean_dec(v___x_757_);
lean_dec_ref(v___x_752_);
lean_dec_ref_known(v___x_751_, 3);
lean_dec(v___x_749_);
lean_dec(v___x_746_);
lean_dec(v___x_733_);
lean_dec(v___y_728_);
lean_dec(v___y_726_);
lean_dec(v___y_717_);
lean_dec(v___y_716_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_704_);
v_a_800_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_788_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_788_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
else
{
lean_dec(v___x_778_);
lean_dec(v___x_774_);
lean_dec(v___x_757_);
lean_dec_ref(v___x_752_);
lean_dec_ref_known(v___x_751_, 3);
lean_dec(v___x_749_);
lean_dec(v___x_746_);
lean_dec(v___x_733_);
lean_dec(v___y_728_);
lean_dec(v___y_726_);
lean_dec(v___y_720_);
lean_dec(v___y_717_);
lean_dec(v___y_716_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec(v___y_704_);
return v___x_784_;
}
}
v___jp_808_:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_832_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_833_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0));
lean_inc_ref_n(v___y_809_, 2);
lean_inc_ref_n(v___y_823_, 2);
v___x_834_ = l_Lean_Name_mkStr4(v___y_823_, v___y_809_, v___x_832_, v___x_833_);
v___x_835_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1));
v___x_836_ = l_Lean_Name_mkStr4(v___y_823_, v___y_809_, v___x_832_, v___x_835_);
if (lean_obj_tag(v___y_830_) == 1)
{
lean_object* v_val_837_; lean_object* v___x_838_; 
v_val_837_ = lean_ctor_get(v___y_830_, 0);
lean_inc(v_val_837_);
lean_dec_ref_known(v___y_830_, 1);
v___x_838_ = l_Array_mkArray1___redArg(v_val_837_);
v___y_704_ = v___y_810_;
v___y_705_ = v___y_809_;
v___y_706_ = v___y_812_;
v___y_707_ = v___y_813_;
v___y_708_ = v___y_816_;
v___y_709_ = v___y_818_;
v___y_710_ = v___y_821_;
v___y_711_ = v___x_832_;
v___y_712_ = v___y_826_;
v___y_713_ = v___y_827_;
v___y_714_ = v___x_834_;
v___y_715_ = v___y_829_;
v___y_716_ = v___y_811_;
v___y_717_ = v___y_815_;
v___y_718_ = v___y_814_;
v___y_719_ = v___y_817_;
v___y_720_ = v___y_819_;
v___y_721_ = v___y_820_;
v___y_722_ = v___y_823_;
v___y_723_ = v___y_822_;
v___y_724_ = v___y_824_;
v___y_725_ = v___y_825_;
v___y_726_ = v___y_828_;
v___y_727_ = v_a_831_;
v___y_728_ = v___x_836_;
v___y_729_ = v___x_838_;
goto v___jp_703_;
}
else
{
lean_object* v___x_839_; 
lean_dec(v___y_830_);
v___x_839_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___y_704_ = v___y_810_;
v___y_705_ = v___y_809_;
v___y_706_ = v___y_812_;
v___y_707_ = v___y_813_;
v___y_708_ = v___y_816_;
v___y_709_ = v___y_818_;
v___y_710_ = v___y_821_;
v___y_711_ = v___x_832_;
v___y_712_ = v___y_826_;
v___y_713_ = v___y_827_;
v___y_714_ = v___x_834_;
v___y_715_ = v___y_829_;
v___y_716_ = v___y_811_;
v___y_717_ = v___y_815_;
v___y_718_ = v___y_814_;
v___y_719_ = v___y_817_;
v___y_720_ = v___y_819_;
v___y_721_ = v___y_820_;
v___y_722_ = v___y_823_;
v___y_723_ = v___y_822_;
v___y_724_ = v___y_824_;
v___y_725_ = v___y_825_;
v___y_726_ = v___y_828_;
v___y_727_ = v_a_831_;
v___y_728_ = v___x_836_;
v___y_729_ = v___x_839_;
goto v___jp_703_;
}
}
v___jp_840_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_865_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31));
lean_inc_ref_n(v___y_855_, 6);
lean_inc_ref_n(v___y_842_, 6);
lean_inc_ref_n(v___y_852_, 6);
v___x_866_ = l_Lean_Name_mkStr4(v___y_852_, v___y_842_, v___y_855_, v___x_865_);
v___x_867_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32));
lean_inc_n(v___y_851_, 28);
v___x_868_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_868_, 0, v___y_851_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
lean_inc_ref(v___y_857_);
lean_inc_n(v___y_853_, 6);
v___x_869_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_869_, 0, v___y_851_);
lean_ctor_set(v___x_869_, 1, v___y_853_);
lean_ctor_set(v___x_869_, 2, v___y_857_);
v___x_870_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31));
v___x_871_ = l_Lean_Name_mkStr4(v___y_852_, v___y_842_, v___y_855_, v___x_870_);
v___x_872_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33));
v___x_873_ = l_Lean_Name_mkStr4(v___y_852_, v___y_842_, v___y_855_, v___x_872_);
v___x_874_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34));
v___x_875_ = l_Lean_Name_mkStr4(v___y_852_, v___y_842_, v___y_855_, v___x_874_);
v___x_876_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36);
v___x_877_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37));
lean_inc_n(v___y_859_, 3);
lean_inc_n(v_a_864_, 3);
v___x_878_ = l_Lean_addMacroScope(v_a_864_, v___x_877_, v___y_859_);
lean_inc_n(v___y_846_, 4);
v___x_879_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_879_, 0, v___y_851_);
lean_ctor_set(v___x_879_, 1, v___x_876_);
lean_ctor_set(v___x_879_, 2, v___x_878_);
lean_ctor_set(v___x_879_, 3, v___y_846_);
lean_inc_ref_n(v___x_869_, 18);
lean_inc_n(v___x_875_, 3);
v___x_880_ = l_Lean_Syntax_node2(v___y_851_, v___x_875_, v___x_879_, v___x_869_);
v___x_881_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38));
v___x_882_ = l_Lean_Name_mkStr4(v___y_852_, v___y_842_, v___y_855_, v___x_881_);
v___x_883_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39));
v___x_884_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_884_, 0, v___y_851_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
lean_inc_ref_n(v___x_884_, 3);
lean_inc_n(v___x_882_, 3);
v___x_885_ = l_Lean_Syntax_node3(v___y_851_, v___x_882_, v___x_884_, v___x_869_, v___y_848_);
v___x_886_ = l_Lean_Syntax_node3(v___y_851_, v___y_853_, v___x_869_, v___x_869_, v___x_885_);
lean_inc_n(v___x_873_, 3);
v___x_887_ = l_Lean_Syntax_node2(v___y_851_, v___x_873_, v___x_880_, v___x_886_);
v___x_888_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40));
v___x_889_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_889_, 0, v___y_851_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42);
v___x_891_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43));
v___x_892_ = l_Lean_addMacroScope(v_a_864_, v___x_891_, v___y_859_);
v___x_893_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_893_, 0, v___y_851_);
lean_ctor_set(v___x_893_, 1, v___x_890_);
lean_ctor_set(v___x_893_, 2, v___x_892_);
lean_ctor_set(v___x_893_, 3, v___y_846_);
v___x_894_ = l_Lean_Syntax_node2(v___y_851_, v___x_875_, v___x_893_, v___x_869_);
v___x_895_ = l_Lean_Syntax_node3(v___y_851_, v___x_882_, v___x_884_, v___x_869_, v___y_858_);
v___x_896_ = l_Lean_Syntax_node3(v___y_851_, v___y_853_, v___x_869_, v___x_869_, v___x_895_);
v___x_897_ = l_Lean_Syntax_node2(v___y_851_, v___x_873_, v___x_894_, v___x_896_);
v___x_898_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45);
v___x_899_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46));
v___x_900_ = l_Lean_addMacroScope(v_a_864_, v___x_899_, v___y_859_);
v___x_901_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_901_, 0, v___y_851_);
lean_ctor_set(v___x_901_, 1, v___x_898_);
lean_ctor_set(v___x_901_, 2, v___x_900_);
lean_ctor_set(v___x_901_, 3, v___y_846_);
v___x_902_ = l_Lean_Syntax_node2(v___y_851_, v___x_875_, v___x_901_, v___x_869_);
v___x_903_ = l_Lean_Syntax_node3(v___y_851_, v___x_882_, v___x_884_, v___x_869_, v___y_863_);
v___x_904_ = l_Lean_Syntax_node3(v___y_851_, v___y_853_, v___x_869_, v___x_869_, v___x_903_);
v___x_905_ = l_Lean_Syntax_node2(v___y_851_, v___x_873_, v___x_902_, v___x_904_);
v___x_906_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48);
v___x_907_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49));
v___x_908_ = l_Lean_addMacroScope(v_a_864_, v___x_907_, v___y_859_);
v___x_909_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_909_, 0, v___y_851_);
lean_ctor_set(v___x_909_, 1, v___x_906_);
lean_ctor_set(v___x_909_, 2, v___x_908_);
lean_ctor_set(v___x_909_, 3, v___y_846_);
v___x_910_ = l_Lean_Syntax_node2(v___y_851_, v___x_875_, v___x_909_, v___x_869_);
v___x_911_ = l_Lean_Syntax_node3(v___y_851_, v___x_882_, v___x_884_, v___x_869_, v___y_854_);
v___x_912_ = l_Lean_Syntax_node3(v___y_851_, v___y_853_, v___x_869_, v___x_869_, v___x_911_);
v___x_913_ = l_Lean_Syntax_node2(v___y_851_, v___x_873_, v___x_910_, v___x_912_);
lean_inc_ref_n(v___x_889_, 2);
v___x_914_ = l_Lean_Syntax_node7(v___y_851_, v___y_853_, v___x_887_, v___x_889_, v___x_897_, v___x_889_, v___x_905_, v___x_889_, v___x_913_);
v___x_915_ = l_Lean_Syntax_node1(v___y_851_, v___x_871_, v___x_914_);
v___x_916_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50));
v___x_917_ = l_Lean_Name_mkStr4(v___y_852_, v___y_842_, v___y_855_, v___x_916_);
v___x_918_ = l_Lean_Syntax_node1(v___y_851_, v___x_917_, v___x_869_);
v___x_919_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51));
v___x_920_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_920_, 0, v___y_851_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = l_Lean_Syntax_node6(v___y_851_, v___x_866_, v___x_868_, v___x_869_, v___x_915_, v___x_918_, v___x_869_, v___x_920_);
v___x_922_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_849_, v___y_844_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_924_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref_known(v___x_922_, 1);
v___x_924_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_849_);
if (lean_obj_tag(v___x_924_) == 0)
{
if (lean_obj_tag(v___y_845_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_926_; lean_object* v_a_927_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref_known(v___x_924_, 1);
v___x_926_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_844_);
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref(v___x_926_);
v___y_809_ = v___y_842_;
v___y_810_ = v___y_841_;
v___y_811_ = v___y_843_;
v___y_812_ = v_a_923_;
v___y_813_ = v___y_844_;
v___y_814_ = v___y_846_;
v___y_815_ = v___y_845_;
v___y_816_ = v___y_847_;
v___y_817_ = v___x_883_;
v___y_818_ = v___y_849_;
v___y_819_ = v___y_850_;
v___y_820_ = v___x_888_;
v___y_821_ = v_a_925_;
v___y_822_ = v___y_853_;
v___y_823_ = v___y_852_;
v___y_824_ = v___x_921_;
v___y_825_ = v___y_855_;
v___y_826_ = v___y_856_;
v___y_827_ = v___y_857_;
v___y_828_ = v___y_861_;
v___y_829_ = v___y_860_;
v___y_830_ = v___y_862_;
v_a_831_ = v_a_927_;
goto v___jp_808_;
}
else
{
lean_object* v_a_928_; lean_object* v_val_929_; 
v_a_928_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_924_, 1);
v_val_929_ = lean_ctor_get(v___y_845_, 0);
lean_inc(v_val_929_);
v___y_809_ = v___y_842_;
v___y_810_ = v___y_841_;
v___y_811_ = v___y_843_;
v___y_812_ = v_a_923_;
v___y_813_ = v___y_844_;
v___y_814_ = v___y_846_;
v___y_815_ = v___y_845_;
v___y_816_ = v___y_847_;
v___y_817_ = v___x_883_;
v___y_818_ = v___y_849_;
v___y_819_ = v___y_850_;
v___y_820_ = v___x_888_;
v___y_821_ = v_a_928_;
v___y_822_ = v___y_853_;
v___y_823_ = v___y_852_;
v___y_824_ = v___x_921_;
v___y_825_ = v___y_855_;
v___y_826_ = v___y_856_;
v___y_827_ = v___y_857_;
v___y_828_ = v___y_861_;
v___y_829_ = v___y_860_;
v___y_830_ = v___y_862_;
v_a_831_ = v_val_929_;
goto v___jp_808_;
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_a_923_);
lean_dec(v___x_921_);
lean_dec(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_847_);
lean_dec(v___y_845_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec(v_stx_620_);
v_a_930_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_924_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_924_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec(v___x_921_);
lean_dec(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_847_);
lean_dec(v___y_845_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec(v_stx_620_);
v_a_938_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_922_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_922_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
v___jp_946_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_964_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_965_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10));
v___x_966_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52));
lean_inc_ref_n(v___y_955_, 3);
v___x_967_ = l_Lean_Name_mkStr4(v___y_955_, v___x_964_, v___x_965_, v___x_966_);
v___x_968_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53));
v___x_969_ = l_Lean_Name_mkStr4(v___y_955_, v___x_964_, v___x_965_, v___x_968_);
v___x_970_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_971_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
lean_inc_n(v___y_960_, 4);
v___x_972_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_972_, 0, v___y_960_);
lean_ctor_set(v___x_972_, 1, v___x_970_);
lean_ctor_set(v___x_972_, 2, v___x_971_);
lean_inc_ref(v___x_972_);
lean_inc(v___x_969_);
v___x_973_ = l_Lean_Syntax_node1(v___y_960_, v___x_969_, v___x_972_);
v___x_974_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54));
v___x_975_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55));
v___x_976_ = l_Lean_Name_mkStr4(v___y_955_, v___x_964_, v___x_974_, v___x_975_);
v___x_977_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57);
v___x_978_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59));
v___x_979_ = l_Lean_addMacroScope(v_a_963_, v___x_978_, v___y_954_);
lean_inc(v___y_950_);
v___x_980_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_980_, 0, v___y_960_);
lean_ctor_set(v___x_980_, 1, v___x_977_);
lean_ctor_set(v___x_980_, 2, v___x_979_);
lean_ctor_set(v___x_980_, 3, v___y_950_);
v___x_981_ = l_Lean_Syntax_node2(v___y_960_, v___x_976_, v___x_980_, v___x_972_);
lean_inc(v___x_967_);
v___x_982_ = l_Lean_Syntax_node2(v___y_960_, v___x_967_, v___x_973_, v___x_981_);
v___x_983_ = lean_mk_empty_array_with_capacity(v___x_700_);
v___x_984_ = lean_array_push(v___x_983_, v___x_982_);
v___x_985_ = l_Lake_DSL_expandAttrs(v___y_958_);
v___x_986_ = l_Array_append___redArg(v___x_984_, v___x_985_);
lean_dec_ref(v___x_985_);
v___x_987_ = l_Lake_DSL_packageDeclName;
v___x_988_ = l_Lean_mkIdentFrom(v___y_948_, v___x_987_, v___y_959_);
lean_dec(v___y_948_);
v___x_989_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_953_, v___y_949_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_991_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
v___x_991_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_953_);
if (lean_obj_tag(v___x_991_) == 0)
{
if (lean_obj_tag(v___y_951_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_993_; lean_object* v_a_994_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_991_, 1);
v___x_993_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_949_);
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref(v___x_993_);
v___y_841_ = v___y_947_;
v___y_842_ = v___x_964_;
v___y_843_ = v___x_967_;
v___y_844_ = v___y_949_;
v___y_845_ = v___y_951_;
v___y_846_ = v___y_950_;
v___y_847_ = v___x_988_;
v___y_848_ = v___y_952_;
v___y_849_ = v___y_953_;
v___y_850_ = v___x_987_;
v___y_851_ = v_a_990_;
v___y_852_ = v___y_955_;
v___y_853_ = v___x_970_;
v___y_854_ = v___y_956_;
v___y_855_ = v___x_965_;
v___y_856_ = v___x_986_;
v___y_857_ = v___x_971_;
v___y_858_ = v___y_957_;
v___y_859_ = v_a_992_;
v___y_860_ = v___y_959_;
v___y_861_ = v___x_969_;
v___y_862_ = v___y_962_;
v___y_863_ = v___y_961_;
v_a_864_ = v_a_994_;
goto v___jp_840_;
}
else
{
lean_object* v_a_995_; lean_object* v_val_996_; 
v_a_995_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_991_, 1);
v_val_996_ = lean_ctor_get(v___y_951_, 0);
lean_inc(v_val_996_);
v___y_841_ = v___y_947_;
v___y_842_ = v___x_964_;
v___y_843_ = v___x_967_;
v___y_844_ = v___y_949_;
v___y_845_ = v___y_951_;
v___y_846_ = v___y_950_;
v___y_847_ = v___x_988_;
v___y_848_ = v___y_952_;
v___y_849_ = v___y_953_;
v___y_850_ = v___x_987_;
v___y_851_ = v_a_990_;
v___y_852_ = v___y_955_;
v___y_853_ = v___x_970_;
v___y_854_ = v___y_956_;
v___y_855_ = v___x_965_;
v___y_856_ = v___x_986_;
v___y_857_ = v___x_971_;
v___y_858_ = v___y_957_;
v___y_859_ = v_a_995_;
v___y_860_ = v___y_959_;
v___y_861_ = v___x_969_;
v___y_862_ = v___y_962_;
v___y_863_ = v___y_961_;
v_a_864_ = v_val_996_;
goto v___jp_840_;
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v_a_990_);
lean_dec(v___x_988_);
lean_dec_ref(v___x_986_);
lean_dec(v___x_969_);
lean_dec(v___x_967_);
lean_dec(v___y_962_);
lean_dec(v___y_961_);
lean_dec(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec(v___y_951_);
lean_dec(v___y_947_);
lean_dec(v_stx_620_);
v_a_997_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_991_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_991_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
lean_dec(v___x_988_);
lean_dec_ref(v___x_986_);
lean_dec(v___x_969_);
lean_dec(v___x_967_);
lean_dec(v___y_962_);
lean_dec(v___y_961_);
lean_dec(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec(v___y_951_);
lean_dec(v___y_947_);
lean_dec(v_stx_620_);
v_a_1005_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_989_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_989_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
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
v___jp_1013_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1027_ = l_Nat_reprFast(v___y_1014_);
v___x_1028_ = lean_box(2);
v___x_1029_ = l_Lean_Syntax_mkNumLit(v___x_1027_, v___x_1028_);
v___x_1030_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_1031_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62));
v___x_1032_ = lean_mk_empty_array_with_capacity(v___x_702_);
lean_inc(v___y_1026_);
lean_inc_ref(v___x_1032_);
v___x_1033_ = lean_array_push(v___x_1032_, v___y_1026_);
v___x_1034_ = lean_array_push(v___x_1033_, v___x_1029_);
v___x_1035_ = l_Lean_Syntax_mkCApp(v___x_1031_, v___x_1034_);
v___x_1036_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64));
lean_inc(v___x_1035_);
v___x_1037_ = lean_array_push(v___x_1032_, v___x_1035_);
lean_inc(v___y_1022_);
v___x_1038_ = lean_array_push(v___x_1037_, v___y_1022_);
v___x_1039_ = l_Lean_Syntax_mkCApp(v___x_1036_, v___x_1038_);
lean_inc(v___y_1021_);
v___x_1040_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(v___x_1036_, v___y_1021_, v___x_1039_, v___y_1020_, v___y_1019_, v___y_1016_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v___x_1041_; 
lean_dec_ref_known(v___x_1040_, 1);
v___x_1041_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(v___y_1019_, v___y_1016_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1043_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v___x_1041_, 1);
v___x_1043_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1019_);
if (lean_obj_tag(v___x_1043_) == 0)
{
if (lean_obj_tag(v___y_1018_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1045_; lean_object* v_a_1046_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 1);
v___x_1045_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_1016_);
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref(v___x_1045_);
v___y_947_ = v___x_1028_;
v___y_948_ = v___y_1015_;
v___y_949_ = v___y_1016_;
v___y_950_ = v___y_1017_;
v___y_951_ = v___y_1018_;
v___y_952_ = v___y_1026_;
v___y_953_ = v___y_1019_;
v___y_954_ = v_a_1044_;
v___y_955_ = v___x_1030_;
v___y_956_ = v___y_1021_;
v___y_957_ = v___y_1022_;
v___y_958_ = v___y_1023_;
v___y_959_ = v___y_1024_;
v___y_960_ = v_a_1042_;
v___y_961_ = v___x_1035_;
v___y_962_ = v___y_1025_;
v_a_963_ = v_a_1046_;
goto v___jp_946_;
}
else
{
lean_object* v_a_1047_; lean_object* v_val_1048_; 
v_a_1047_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1043_, 1);
v_val_1048_ = lean_ctor_get(v___y_1018_, 0);
lean_inc(v_val_1048_);
v___y_947_ = v___x_1028_;
v___y_948_ = v___y_1015_;
v___y_949_ = v___y_1016_;
v___y_950_ = v___y_1017_;
v___y_951_ = v___y_1018_;
v___y_952_ = v___y_1026_;
v___y_953_ = v___y_1019_;
v___y_954_ = v_a_1047_;
v___y_955_ = v___x_1030_;
v___y_956_ = v___y_1021_;
v___y_957_ = v___y_1022_;
v___y_958_ = v___y_1023_;
v___y_959_ = v___y_1024_;
v___y_960_ = v_a_1042_;
v___y_961_ = v___x_1035_;
v___y_962_ = v___y_1025_;
v_a_963_ = v_val_1048_;
goto v___jp_946_;
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec(v_a_1042_);
lean_dec(v___x_1035_);
lean_dec(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec(v___y_1015_);
lean_dec(v_stx_620_);
v_a_1049_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1043_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1043_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec(v___x_1035_);
lean_dec(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec(v___y_1015_);
lean_dec(v_stx_620_);
v_a_1057_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1041_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1041_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_dec(v___x_1035_);
lean_dec(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec(v___y_1015_);
lean_dec(v_stx_620_);
return v___x_1040_;
}
}
v___jp_1065_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1077_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66, &l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66);
v___x_1078_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__67));
v___x_1079_ = l_Lean_addMacroScope(v_a_1076_, v___x_1078_, v___y_1074_);
v___x_1080_ = lean_box(0);
v___x_1081_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1081_, 0, v___y_1068_);
lean_ctor_set(v___x_1081_, 1, v___x_1077_);
lean_ctor_set(v___x_1081_, 2, v___x_1079_);
lean_ctor_set(v___x_1081_, 3, v___x_1080_);
v___x_1082_ = l_Lake_DSL_mkConfigDeclIdent(v___y_1066_, v___y_1070_, v___y_1067_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v_env_1087_; lean_object* v___x_1088_; lean_object* v_asyncMode_1089_; lean_object* v___x_1090_; lean_object* v_snd_1091_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc_n(v_a_1083_, 2);
lean_dec_ref_known(v___x_1082_, 1);
v___x_1084_ = l_Lean_TSyntax_getId(v_a_1083_);
v___x_1085_ = l_Lake_Name_quoteFrom(v_a_1083_, v___x_1084_, v___y_1073_);
v___x_1086_ = lean_st_ref_get(v___y_1067_);
v_env_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc_ref(v_env_1087_);
lean_dec(v___x_1086_);
v___x_1088_ = l_Lake_nameExt;
v_asyncMode_1089_ = lean_ctor_get(v___x_1088_, 2);
v___x_1090_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_698_, v___x_1088_, v_env_1087_, v_asyncMode_1089_, v___x_697_, v___y_1073_);
v_snd_1091_ = lean_ctor_get(v___x_1090_, 1);
if (lean_obj_tag(v_snd_1091_) == 0)
{
lean_object* v_fst_1092_; 
v_fst_1092_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_fst_1092_);
lean_dec(v___x_1090_);
lean_inc(v___x_1085_);
v___y_1014_ = v_fst_1092_;
v___y_1015_ = v_a_1083_;
v___y_1016_ = v___y_1067_;
v___y_1017_ = v___x_1080_;
v___y_1018_ = v___y_1069_;
v___y_1019_ = v___y_1070_;
v___y_1020_ = v___y_1072_;
v___y_1021_ = v___x_1081_;
v___y_1022_ = v___x_1085_;
v___y_1023_ = v___y_1071_;
v___y_1024_ = v___y_1073_;
v___y_1025_ = v___y_1075_;
v___y_1026_ = v___x_1085_;
goto v___jp_1013_;
}
else
{
lean_object* v_fst_1093_; lean_object* v___x_1094_; 
lean_inc(v_snd_1091_);
v_fst_1093_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_fst_1093_);
lean_dec(v___x_1090_);
lean_inc(v_a_1083_);
v___x_1094_ = l_Lake_Name_quoteFrom(v_a_1083_, v_snd_1091_, v___y_1073_);
v___y_1014_ = v_fst_1093_;
v___y_1015_ = v_a_1083_;
v___y_1016_ = v___y_1067_;
v___y_1017_ = v___x_1080_;
v___y_1018_ = v___y_1069_;
v___y_1019_ = v___y_1070_;
v___y_1020_ = v___y_1072_;
v___y_1021_ = v___x_1081_;
v___y_1022_ = v___x_1085_;
v___y_1023_ = v___y_1071_;
v___y_1024_ = v___y_1073_;
v___y_1025_ = v___y_1075_;
v___y_1026_ = v___x_1094_;
goto v___jp_1013_;
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec_ref_known(v___x_1081_, 4);
lean_dec(v___y_1075_);
lean_dec(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec(v_stx_620_);
v_a_1095_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1082_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1082_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
v___jp_1104_:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_Elab_Command_getRef___redArg(v___y_1107_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v_fileName_1113_; lean_object* v_fileMap_1114_; lean_object* v_currRecDepth_1115_; lean_object* v_cmdPos_1116_; lean_object* v_macroStack_1117_; lean_object* v_quotContext_x3f_1118_; lean_object* v_currMacroScope_1119_; lean_object* v_snap_x3f_1120_; lean_object* v_cancelTk_x3f_1121_; uint8_t v_suppressElabErrors_1122_; lean_object* v_ref_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1111_, 1);
v_fileName_1113_ = lean_ctor_get(v___y_1107_, 0);
v_fileMap_1114_ = lean_ctor_get(v___y_1107_, 1);
v_currRecDepth_1115_ = lean_ctor_get(v___y_1107_, 2);
v_cmdPos_1116_ = lean_ctor_get(v___y_1107_, 3);
v_macroStack_1117_ = lean_ctor_get(v___y_1107_, 4);
v_quotContext_x3f_1118_ = lean_ctor_get(v___y_1107_, 5);
v_currMacroScope_1119_ = lean_ctor_get(v___y_1107_, 6);
v_snap_x3f_1120_ = lean_ctor_get(v___y_1107_, 8);
v_cancelTk_x3f_1121_ = lean_ctor_get(v___y_1107_, 9);
v_suppressElabErrors_1122_ = lean_ctor_get_uint8(v___y_1107_, sizeof(void*)*10);
v_ref_1123_ = l_Lean_replaceRef(v_kw_1103_, v_a_1112_);
lean_dec(v_a_1112_);
lean_dec(v_kw_1103_);
lean_inc(v_cancelTk_x3f_1121_);
lean_inc(v_snap_x3f_1120_);
lean_inc(v_currMacroScope_1119_);
lean_inc(v_quotContext_x3f_1118_);
lean_inc(v_macroStack_1117_);
lean_inc(v_cmdPos_1116_);
lean_inc(v_currRecDepth_1115_);
lean_inc_ref(v_fileMap_1114_);
lean_inc_ref(v_fileName_1113_);
v___x_1124_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1124_, 0, v_fileName_1113_);
lean_ctor_set(v___x_1124_, 1, v_fileMap_1114_);
lean_ctor_set(v___x_1124_, 2, v_currRecDepth_1115_);
lean_ctor_set(v___x_1124_, 3, v_cmdPos_1116_);
lean_ctor_set(v___x_1124_, 4, v_macroStack_1117_);
lean_ctor_set(v___x_1124_, 5, v_quotContext_x3f_1118_);
lean_ctor_set(v___x_1124_, 6, v_currMacroScope_1119_);
lean_ctor_set(v___x_1124_, 7, v_ref_1123_);
lean_ctor_set(v___x_1124_, 8, v_snap_x3f_1120_);
lean_ctor_set(v___x_1124_, 9, v_cancelTk_x3f_1121_);
lean_ctor_set_uint8(v___x_1124_, sizeof(void*)*10, v_suppressElabErrors_1122_);
v___x_1125_ = l_Lean_Elab_Command_getRef___redArg(v___x_1124_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; uint8_t v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1125_, 1);
v___x_1127_ = 0;
v___x_1128_ = l_Lean_SourceInfo_fromRef(v_a_1126_, v___x_1127_);
lean_dec(v_a_1126_);
v___x_1129_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_1124_);
if (lean_obj_tag(v___x_1129_) == 0)
{
if (lean_obj_tag(v_quotContext_x3f_1118_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1131_; lean_object* v_a_1132_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1129_, 1);
v___x_1131_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_1106_);
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref(v___x_1131_);
v___y_1066_ = v___y_1105_;
v___y_1067_ = v___y_1106_;
v___y_1068_ = v___x_1128_;
v___y_1069_ = v_quotContext_x3f_1118_;
v___y_1070_ = v___x_1124_;
v___y_1071_ = v___y_1109_;
v___y_1072_ = v___y_1108_;
v___y_1073_ = v___x_1127_;
v___y_1074_ = v_a_1130_;
v___y_1075_ = v___y_1110_;
v_a_1076_ = v_a_1132_;
goto v___jp_1065_;
}
else
{
lean_object* v_a_1133_; lean_object* v_val_1134_; 
v_a_1133_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1133_);
lean_dec_ref_known(v___x_1129_, 1);
v_val_1134_ = lean_ctor_get(v_quotContext_x3f_1118_, 0);
lean_inc(v_val_1134_);
lean_inc_ref(v_quotContext_x3f_1118_);
v___y_1066_ = v___y_1105_;
v___y_1067_ = v___y_1106_;
v___y_1068_ = v___x_1128_;
v___y_1069_ = v_quotContext_x3f_1118_;
v___y_1070_ = v___x_1124_;
v___y_1071_ = v___y_1109_;
v___y_1072_ = v___y_1108_;
v___y_1073_ = v___x_1127_;
v___y_1074_ = v_a_1133_;
v___y_1075_ = v___y_1110_;
v_a_1076_ = v_val_1134_;
goto v___jp_1065_;
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec(v___x_1128_);
lean_dec_ref_known(v___x_1124_, 10);
lean_dec(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec(v___y_1105_);
lean_dec(v_stx_620_);
v_a_1135_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1129_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1129_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec_ref_known(v___x_1124_, 10);
lean_dec(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec(v___y_1105_);
lean_dec(v_stx_620_);
v_a_1143_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1125_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1125_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec(v___y_1105_);
lean_dec(v_kw_1103_);
lean_dec(v_stx_620_);
v_a_1151_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1111_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1111_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
v___jp_1159_:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_Syntax_getOptional_x3f(v___x_699_);
lean_dec(v___x_699_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_box(0);
v___y_1105_ = v___y_1160_;
v___y_1106_ = v___y_1161_;
v___y_1107_ = v___y_1162_;
v___y_1108_ = v___y_1163_;
v___y_1109_ = v___y_1164_;
v___y_1110_ = v___x_1166_;
goto v___jp_1104_;
}
else
{
lean_object* v_val_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
v_val_1167_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1165_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_val_1167_);
lean_dec(v___x_1165_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_val_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
v___y_1105_ = v___y_1160_;
v___y_1106_ = v___y_1161_;
v___y_1107_ = v___y_1162_;
v___y_1108_ = v___y_1163_;
v___y_1109_ = v___y_1164_;
v___y_1110_ = v___x_1172_;
goto v___jp_1104_;
}
}
}
}
v___jp_1175_:
{
lean_object* v___x_1179_; lean_object* v_cfg_1180_; lean_object* v___x_1181_; 
v___x_1179_ = lean_unsigned_to_nat(4u);
v_cfg_1180_ = l_Lean_Syntax_getArg(v_stx_620_, v___x_1179_);
v___x_1181_ = l_Lean_Syntax_getOptional_x3f(v___x_701_);
lean_dec(v___x_701_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_box(0);
v___y_1160_ = v_nameStx_x3f_1176_;
v___y_1161_ = v___y_1178_;
v___y_1162_ = v___y_1177_;
v___y_1163_ = v_cfg_1180_;
v___y_1164_ = v___x_1182_;
goto v___jp_1159_;
}
else
{
lean_object* v_val_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
v_val_1183_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1181_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_val_1183_);
lean_dec(v___x_1181_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_val_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
v___y_1160_ = v_nameStx_x3f_1176_;
v___y_1161_ = v___y_1178_;
v___y_1162_ = v___y_1177_;
v___y_1163_ = v_cfg_1180_;
v___y_1164_ = v___x_1188_;
goto v___jp_1159_;
}
}
}
}
}
v___jp_624_:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
lean_inc_ref(v___y_641_);
lean_inc_n(v___y_636_, 5);
lean_inc_n(v___y_645_, 28);
v___x_649_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_649_, 0, v___y_645_);
lean_ctor_set(v___x_649_, 1, v___y_636_);
lean_ctor_set(v___x_649_, 2, v___y_641_);
lean_inc_ref(v___y_630_);
v___x_650_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_650_, 0, v___y_645_);
lean_ctor_set(v___x_650_, 1, v___y_630_);
lean_inc_ref_n(v___x_649_, 13);
v___x_651_ = l_Lean_Syntax_node1(v___y_645_, v___y_644_, v___x_649_);
v___x_652_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0));
lean_inc_ref(v___y_637_);
v___x_653_ = l_Lean_Name_mkStr2(v___y_637_, v___x_652_);
v___x_654_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_654_, 0, v___y_645_);
lean_ctor_set(v___x_654_, 1, v___x_652_);
v___x_655_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2));
v___x_656_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3));
v___x_657_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_657_, 0, v___y_645_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = l_Lean_Syntax_node1(v___y_645_, v___x_655_, v___x_657_);
v___x_659_ = l_Lean_Syntax_node1(v___y_645_, v___y_636_, v___x_658_);
v___x_660_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4));
v___x_661_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_661_, 0, v___y_645_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5));
v___x_663_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_663_, 0, v___y_645_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
lean_inc_ref(v___y_631_);
v___x_664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_664_, 0, v___y_645_);
lean_ctor_set(v___x_664_, 1, v___y_631_);
v___x_665_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6));
v___x_666_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_666_, 0, v___y_645_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = l_Lean_Syntax_node1(v___y_645_, v___x_655_, v___x_666_);
v___x_668_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7));
v___x_669_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_669_, 0, v___y_645_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
lean_inc_ref(v___x_664_);
v___x_670_ = l_Lean_Syntax_node5(v___y_645_, v___y_636_, v___x_661_, v___x_663_, v___x_664_, v___x_667_, v___x_669_);
v___x_671_ = l_Lean_Syntax_node5(v___y_645_, v___x_653_, v___x_654_, v___x_649_, v___x_659_, v___x_649_, v___x_670_);
v___x_672_ = l_Lean_Syntax_node2(v___y_645_, v___y_628_, v___x_651_, v___x_671_);
v___x_673_ = l_Lean_Syntax_node1(v___y_645_, v___y_636_, v___x_672_);
lean_inc_ref(v___y_626_);
v___x_674_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_674_, 0, v___y_645_);
lean_ctor_set(v___x_674_, 1, v___y_626_);
v___x_675_ = l_Lean_Syntax_node3(v___y_645_, v___y_638_, v___x_650_, v___x_673_, v___x_674_);
v___x_676_ = l_Lean_Syntax_node1(v___y_645_, v___y_636_, v___x_675_);
v___x_677_ = l_Lean_Syntax_node7(v___y_645_, v___y_646_, v___x_649_, v___x_676_, v___x_649_, v___x_649_, v___x_649_, v___x_649_, v___x_649_);
v___x_678_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_678_, 0, v___y_645_);
lean_ctor_set(v___x_678_, 1, v___y_648_);
v___x_679_ = lean_array_push(v___y_640_, v___y_634_);
v___x_680_ = lean_array_push(v___x_679_, v___y_639_);
v___x_681_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_681_, 0, v___y_625_);
lean_ctor_set(v___x_681_, 1, v___y_635_);
lean_ctor_set(v___x_681_, 2, v___x_680_);
v___x_682_ = l_Lean_Syntax_node2(v___y_645_, v___y_643_, v___x_649_, v___x_649_);
v___x_683_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9));
v___x_684_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10));
v___x_685_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_685_, 0, v___y_645_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = l_Lean_Syntax_node1(v___y_645_, v___x_683_, v___x_685_);
v___x_687_ = l_Lean_Syntax_node2(v___y_645_, v___y_647_, v___x_649_, v___x_649_);
v___x_688_ = l_Lean_Syntax_node4(v___y_645_, v___y_627_, v___x_664_, v___x_686_, v___x_687_, v___x_649_);
v___x_689_ = l_Lean_Syntax_node4(v___y_645_, v___y_633_, v___x_678_, v___x_681_, v___x_682_, v___x_688_);
v___x_690_ = l_Lean_Syntax_node2(v___y_645_, v___y_642_, v___x_677_, v___x_689_);
v___x_691_ = l_Lean_Elab_Command_elabCommand(v___x_690_, v___y_632_, v___y_629_);
lean_dec_ref(v___y_632_);
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___boxed(lean_object* v_stx_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand(v_stx_1200_, v_a_1201_, v_a_1202_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0(lean_object* v_00_u03b1_1205_, lean_object* v_ref_1206_, lean_object* v_msg_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_ref_1206_, v_msg_1207_, v___y_1208_, v___y_1209_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___boxed(lean_object* v_00_u03b1_1212_, lean_object* v_ref_1213_, lean_object* v_msg_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0(v_00_u03b1_1212_, v_ref_1213_, v_msg_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v_ref_1213_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2(lean_object* v_msgData_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msgData_1219_, v___y_1221_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2(v_msgData_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0(lean_object* v_00_u03b1_1229_, lean_object* v_msg_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_1230_, v___y_1231_, v___y_1232_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1235_, lean_object* v_msg_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0(v_00_u03b1_1235_, v_msg_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3(lean_object* v_msgData_1241_, lean_object* v_macroStack_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_msgData_1241_, v_macroStack_1242_, v___y_1244_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1247_, lean_object* v_macroStack_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3(v_msgData_1247_, v_macroStack_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1(){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1281_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1282_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12));
v___x_1283_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10));
v___x_1284_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___boxed), 4, 0);
v___x_1285_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1281_, v___x_1282_, v___x_1283_, v___x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___boxed(lean_object* v_a_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1();
return v_res_1287_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3));
v___x_1296_ = l_String_toRawSubstring_x27(v___x_1295_);
return v___x_1296_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6));
v___x_1301_ = l_String_toRawSubstring_x27(v___x_1300_);
return v___x_1301_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12));
v___x_1314_ = l_String_toRawSubstring_x27(v___x_1313_);
return v___x_1314_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15));
v___x_1319_ = l_String_toRawSubstring_x27(v___x_1318_);
return v___x_1319_;
}
}
static lean_object* _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21));
v___x_1327_ = l_String_toRawSubstring_x27(v___x_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl(lean_object* v_stx_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___x_1378_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; uint8_t v___x_1398_; 
v___x_1378_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1));
lean_inc(v_stx_1352_);
v___x_1398_ = l_Lean_Syntax_isOfKind(v_stx_1352_, v___x_1378_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1400_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1352_, v___x_1399_, v_a_1353_, v_a_1354_);
lean_dec(v_stx_1352_);
return v___x_1400_;
}
else
{
lean_object* v___x_1401_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; uint8_t v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v_wds_x3f_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; uint8_t v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v_wds_x3f_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v_pkg_x3f_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v_attrs_x3f_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v_doc_x3f_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1814_ = l_Lean_Syntax_getArg(v_stx_1352_, v___x_1401_);
v___x_1815_ = l_Lean_Syntax_isNone(v___x_1814_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1814_);
v___x_1817_ = l_Lean_Syntax_matchesNull(v___x_1814_, v___x_1816_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_dec(v___x_1814_);
v___x_1818_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1819_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1352_, v___x_1818_, v_a_1353_, v_a_1354_);
lean_dec(v_stx_1352_);
return v___x_1819_;
}
else
{
lean_object* v_doc_x3f_1820_; lean_object* v___x_1821_; 
v_doc_x3f_1820_ = l_Lean_Syntax_getArg(v___x_1814_, v___x_1401_);
lean_dec(v___x_1814_);
v___x_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1821_, 0, v_doc_x3f_1820_);
v_doc_x3f_1802_ = v___x_1821_;
v___y_1803_ = v_a_1353_;
v___y_1804_ = v_a_1354_;
goto v___jp_1801_;
}
}
else
{
lean_object* v___x_1822_; 
lean_dec(v___x_1814_);
v___x_1822_ = lean_box(0);
v_doc_x3f_1802_ = v___x_1822_;
v___y_1803_ = v_a_1353_;
v___y_1804_ = v_a_1354_;
goto v___jp_1801_;
}
v___jp_1402_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_inc_ref_n(v___y_1403_, 2);
v___x_1424_ = l_Array_append___redArg(v___y_1403_, v___y_1423_);
lean_dec_ref(v___y_1423_);
lean_inc_n(v___y_1410_, 8);
lean_inc_n(v___y_1404_, 41);
v___x_1425_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1425_, 0, v___y_1404_);
lean_ctor_set(v___x_1425_, 1, v___y_1410_);
lean_ctor_set(v___x_1425_, 2, v___x_1424_);
v___x_1426_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16));
lean_inc_ref_n(v___y_1405_, 9);
lean_inc_ref_n(v___y_1413_, 13);
lean_inc_ref_n(v___y_1420_, 13);
v___x_1427_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1413_, v___y_1405_, v___x_1426_);
v___x_1428_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17));
v___x_1429_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___y_1404_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v___x_1430_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40));
v___x_1431_ = l_Lean_Syntax_SepArray_ofElems(v___x_1430_, v___y_1419_);
lean_dec_ref(v___y_1419_);
v___x_1432_ = l_Array_append___redArg(v___y_1403_, v___x_1431_);
lean_dec_ref(v___x_1431_);
v___x_1433_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1433_, 0, v___y_1404_);
lean_ctor_set(v___x_1433_, 1, v___y_1410_);
lean_ctor_set(v___x_1433_, 2, v___x_1432_);
v___x_1434_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18));
v___x_1435_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___y_1404_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = l_Lean_Syntax_node3(v___y_1404_, v___x_1427_, v___x_1429_, v___x_1433_, v___x_1435_);
v___x_1437_ = l_Lean_Syntax_node1(v___y_1404_, v___y_1410_, v___x_1436_);
lean_inc_n(v___y_1418_, 21);
v___x_1438_ = l_Lean_Syntax_node7(v___y_1404_, v___y_1422_, v___x_1425_, v___x_1437_, v___y_1418_, v___y_1418_, v___y_1418_, v___y_1418_, v___y_1418_);
v___x_1439_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5));
lean_inc_ref_n(v___y_1414_, 3);
v___x_1440_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1413_, v___y_1414_, v___x_1439_);
v___x_1441_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6));
v___x_1442_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___y_1404_);
lean_ctor_set(v___x_1442_, 1, v___x_1441_);
v___x_1443_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7));
v___x_1444_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1413_, v___y_1414_, v___x_1443_);
v___x_1445_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4);
v___x_1446_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5));
lean_inc_n(v___y_1411_, 3);
lean_inc_n(v___y_1406_, 3);
v___x_1447_ = l_Lean_addMacroScope(v___y_1406_, v___x_1446_, v___y_1411_);
lean_inc_n(v___y_1409_, 4);
v___x_1448_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1448_, 0, v___y_1404_);
lean_ctor_set(v___x_1448_, 1, v___x_1445_);
lean_ctor_set(v___x_1448_, 2, v___x_1447_);
lean_ctor_set(v___x_1448_, 3, v___y_1409_);
v___x_1449_ = l_Lean_Syntax_node2(v___y_1404_, v___x_1444_, v___x_1448_, v___y_1418_);
v___x_1450_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9));
v___x_1451_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1413_, v___y_1414_, v___x_1450_);
v___x_1452_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11));
v___x_1453_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1413_, v___y_1405_, v___x_1452_);
v___x_1454_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12));
v___x_1455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___y_1404_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7);
v___x_1457_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8));
v___x_1458_ = l_Lean_addMacroScope(v___y_1406_, v___x_1457_, v___y_1411_);
v___x_1459_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10));
v___x_1460_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11));
v___x_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
lean_ctor_set(v___x_1461_, 1, v___y_1409_);
v___x_1462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1459_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
v___x_1463_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1463_, 0, v___y_1404_);
lean_ctor_set(v___x_1463_, 1, v___x_1456_);
lean_ctor_set(v___x_1463_, 2, v___x_1458_);
lean_ctor_set(v___x_1463_, 3, v___x_1462_);
v___x_1464_ = l_Lean_Syntax_node2(v___y_1404_, v___x_1453_, v___x_1455_, v___x_1463_);
v___x_1465_ = l_Lean_Syntax_node1(v___y_1404_, v___y_1410_, v___x_1464_);
v___x_1466_ = l_Lean_Syntax_node2(v___y_1404_, v___x_1451_, v___y_1418_, v___x_1465_);
v___x_1467_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39));
v___x_1468_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___y_1404_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31));
v___x_1470_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1413_, v___y_1405_, v___x_1469_);
v___x_1471_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32));
v___x_1472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___y_1404_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
v___x_1473_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31));
v___x_1474_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1413_, v___y_1405_, v___x_1473_);
v___x_1475_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33));
v___x_1476_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1413_, v___y_1405_, v___x_1475_);
v___x_1477_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34));
v___x_1478_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1413_, v___y_1405_, v___x_1477_);
v___x_1479_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13);
v___x_1480_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14));
v___x_1481_ = l_Lean_addMacroScope(v___y_1406_, v___x_1480_, v___y_1411_);
v___x_1482_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1482_, 0, v___y_1404_);
lean_ctor_set(v___x_1482_, 1, v___x_1479_);
lean_ctor_set(v___x_1482_, 2, v___x_1481_);
lean_ctor_set(v___x_1482_, 3, v___y_1409_);
lean_inc(v___x_1478_);
v___x_1483_ = l_Lean_Syntax_node2(v___y_1404_, v___x_1478_, v___x_1482_, v___y_1418_);
v___x_1484_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38));
v___x_1485_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1413_, v___y_1405_, v___x_1484_);
v___x_1486_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9));
v___x_1487_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10));
v___x_1488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___y_1404_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = l_Lean_Syntax_node1(v___y_1404_, v___x_1486_, v___x_1488_);
lean_inc_ref_n(v___x_1468_, 2);
lean_inc(v___x_1485_);
v___x_1490_ = l_Lean_Syntax_node3(v___y_1404_, v___x_1485_, v___x_1468_, v___y_1418_, v___x_1489_);
v___x_1491_ = l_Lean_Syntax_node3(v___y_1404_, v___y_1410_, v___y_1418_, v___y_1418_, v___x_1490_);
lean_inc(v___x_1476_);
v___x_1492_ = l_Lean_Syntax_node2(v___y_1404_, v___x_1476_, v___x_1483_, v___x_1491_);
v___x_1493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___y_1404_);
lean_ctor_set(v___x_1493_, 1, v___x_1430_);
v___x_1494_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16);
v___x_1495_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17));
v___x_1496_ = l_Lean_addMacroScope(v___y_1406_, v___x_1495_, v___y_1411_);
v___x_1497_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1497_, 0, v___y_1404_);
lean_ctor_set(v___x_1497_, 1, v___x_1494_);
lean_ctor_set(v___x_1497_, 2, v___x_1496_);
lean_ctor_set(v___x_1497_, 3, v___y_1409_);
v___x_1498_ = l_Lean_Syntax_node2(v___y_1404_, v___x_1478_, v___x_1497_, v___y_1418_);
v___x_1499_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18));
v___x_1500_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1413_, v___y_1405_, v___x_1499_);
v___x_1501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___y_1404_);
lean_ctor_set(v___x_1501_, 1, v___x_1499_);
v___x_1502_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19));
v___x_1503_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1413_, v___y_1405_, v___x_1502_);
v___x_1504_ = l_Lean_Syntax_node1(v___y_1404_, v___y_1410_, v___y_1421_);
v___x_1505_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20));
v___x_1506_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___y_1404_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = l_Lean_Syntax_node4(v___y_1404_, v___x_1503_, v___x_1504_, v___y_1418_, v___x_1506_, v___y_1407_);
v___x_1508_ = l_Lean_Syntax_node2(v___y_1404_, v___x_1500_, v___x_1501_, v___x_1507_);
v___x_1509_ = l_Lean_Syntax_node3(v___y_1404_, v___x_1485_, v___x_1468_, v___y_1418_, v___x_1508_);
v___x_1510_ = l_Lean_Syntax_node3(v___y_1404_, v___y_1410_, v___y_1418_, v___y_1418_, v___x_1509_);
v___x_1511_ = l_Lean_Syntax_node2(v___y_1404_, v___x_1476_, v___x_1498_, v___x_1510_);
v___x_1512_ = l_Lean_Syntax_node3(v___y_1404_, v___y_1410_, v___x_1492_, v___x_1493_, v___x_1511_);
v___x_1513_ = l_Lean_Syntax_node1(v___y_1404_, v___x_1474_, v___x_1512_);
v___x_1514_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50));
v___x_1515_ = l_Lean_Name_mkStr4(v___y_1420_, v___y_1413_, v___y_1405_, v___x_1514_);
v___x_1516_ = l_Lean_Syntax_node1(v___y_1404_, v___x_1515_, v___y_1418_);
v___x_1517_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51));
v___x_1518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___y_1404_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
v___x_1519_ = l_Lean_Syntax_node6(v___y_1404_, v___x_1470_, v___x_1472_, v___y_1418_, v___x_1513_, v___x_1516_, v___y_1418_, v___x_1518_);
lean_inc(v___y_1415_);
v___x_1520_ = l_Lean_Syntax_node2(v___y_1404_, v___y_1415_, v___y_1418_, v___y_1418_);
if (lean_obj_tag(v___y_1416_) == 1)
{
lean_object* v_val_1521_; lean_object* v___x_1522_; 
v_val_1521_ = lean_ctor_get(v___y_1416_, 0);
lean_inc(v_val_1521_);
lean_dec_ref_known(v___y_1416_, 1);
v___x_1522_ = l_Array_mkArray1___redArg(v_val_1521_);
v___y_1356_ = v___x_1519_;
v___y_1357_ = v___x_1520_;
v___y_1358_ = v___y_1403_;
v___y_1359_ = v___y_1404_;
v___y_1360_ = v___x_1468_;
v___y_1361_ = v___y_1408_;
v___y_1362_ = v___x_1438_;
v___y_1363_ = v___y_1410_;
v___y_1364_ = v___y_1412_;
v___y_1365_ = v___x_1442_;
v___y_1366_ = v___y_1417_;
v___y_1367_ = v___y_1418_;
v___y_1368_ = v___x_1449_;
v___y_1369_ = v___x_1466_;
v___y_1370_ = v___x_1440_;
v___y_1371_ = v___x_1522_;
goto v___jp_1355_;
}
else
{
lean_object* v___x_1523_; 
lean_dec(v___y_1416_);
v___x_1523_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___y_1356_ = v___x_1519_;
v___y_1357_ = v___x_1520_;
v___y_1358_ = v___y_1403_;
v___y_1359_ = v___y_1404_;
v___y_1360_ = v___x_1468_;
v___y_1361_ = v___y_1408_;
v___y_1362_ = v___x_1438_;
v___y_1363_ = v___y_1410_;
v___y_1364_ = v___y_1412_;
v___y_1365_ = v___x_1442_;
v___y_1366_ = v___y_1417_;
v___y_1367_ = v___y_1418_;
v___y_1368_ = v___x_1449_;
v___y_1369_ = v___x_1466_;
v___y_1370_ = v___x_1440_;
v___y_1371_ = v___x_1523_;
goto v___jp_1355_;
}
}
v___jp_1524_:
{
lean_object* v_methods_1540_; lean_object* v_quotContext_1541_; lean_object* v_currMacroScope_1542_; lean_object* v_currRecDepth_1543_; lean_object* v_maxRecDepth_1544_; lean_object* v_ref_1545_; lean_object* v_ref_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_methods_1540_ = lean_ctor_get(v___y_1538_, 0);
v_quotContext_1541_ = lean_ctor_get(v___y_1538_, 1);
v_currMacroScope_1542_ = lean_ctor_get(v___y_1538_, 2);
v_currRecDepth_1543_ = lean_ctor_get(v___y_1538_, 3);
v_maxRecDepth_1544_ = lean_ctor_get(v___y_1538_, 4);
v_ref_1545_ = lean_ctor_get(v___y_1538_, 5);
v_ref_1546_ = l_Lean_replaceRef(v___y_1528_, v_ref_1545_);
lean_dec(v___y_1528_);
lean_inc(v_ref_1546_);
lean_inc(v_maxRecDepth_1544_);
lean_inc(v_currRecDepth_1543_);
lean_inc(v_currMacroScope_1542_);
lean_inc(v_quotContext_1541_);
lean_inc(v_methods_1540_);
v___x_1547_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1547_, 0, v_methods_1540_);
lean_ctor_set(v___x_1547_, 1, v_quotContext_1541_);
lean_ctor_set(v___x_1547_, 2, v_currMacroScope_1542_);
lean_ctor_set(v___x_1547_, 3, v_currRecDepth_1543_);
lean_ctor_set(v___x_1547_, 4, v_maxRecDepth_1544_);
lean_ctor_set(v___x_1547_, 5, v_ref_1546_);
v___x_1548_ = l_Lake_DSL_expandOptSimpleBinder(v___y_1531_, v___x_1547_, v___y_1539_);
lean_dec_ref_known(v___x_1547_, 6);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v_a_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
v_a_1550_ = lean_ctor_get(v___x_1548_, 1);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1548_, 2);
v___x_1551_ = l_Lean_SourceInfo_fromRef(v_ref_1546_, v___y_1530_);
lean_dec(v_ref_1546_);
v___x_1552_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10));
v___x_1553_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52));
lean_inc_ref_n(v___y_1527_, 5);
lean_inc_ref_n(v___y_1536_, 5);
v___x_1554_ = l_Lean_Name_mkStr4(v___y_1536_, v___y_1527_, v___x_1552_, v___x_1553_);
v___x_1555_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53));
v___x_1556_ = l_Lean_Name_mkStr4(v___y_1536_, v___y_1527_, v___x_1552_, v___x_1555_);
v___x_1557_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_1558_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
lean_inc_n(v___x_1551_, 5);
v___x_1559_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1551_);
lean_ctor_set(v___x_1559_, 1, v___x_1557_);
lean_ctor_set(v___x_1559_, 2, v___x_1558_);
lean_inc_ref_n(v___x_1559_, 2);
v___x_1560_ = l_Lean_Syntax_node1(v___x_1551_, v___x_1556_, v___x_1559_);
v___x_1561_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54));
v___x_1562_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55));
v___x_1563_ = l_Lean_Name_mkStr4(v___y_1536_, v___y_1527_, v___x_1561_, v___x_1562_);
v___x_1564_ = lean_obj_once(&l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22, &l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22_once, _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22);
v___x_1565_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24));
lean_inc(v_currMacroScope_1542_);
lean_inc(v_quotContext_1541_);
v___x_1566_ = l_Lean_addMacroScope(v_quotContext_1541_, v___x_1565_, v_currMacroScope_1542_);
v___x_1567_ = lean_box(0);
v___x_1568_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1551_);
lean_ctor_set(v___x_1568_, 1, v___x_1564_);
lean_ctor_set(v___x_1568_, 2, v___x_1566_);
lean_ctor_set(v___x_1568_, 3, v___x_1567_);
v___x_1569_ = l_Lean_Syntax_node2(v___x_1551_, v___x_1563_, v___x_1568_, v___x_1559_);
v___x_1570_ = l_Lean_Syntax_node2(v___x_1551_, v___x_1554_, v___x_1560_, v___x_1569_);
v___x_1571_ = lean_mk_empty_array_with_capacity(v___y_1532_);
v___x_1572_ = lean_array_push(v___x_1571_, v___x_1570_);
v___x_1573_ = l_Lake_DSL_expandAttrs(v___y_1533_);
v___x_1574_ = l_Array_append___redArg(v___x_1572_, v___x_1573_);
lean_dec_ref(v___x_1573_);
v___x_1575_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0));
lean_inc_ref_n(v___y_1526_, 2);
v___x_1576_ = l_Lean_Name_mkStr4(v___y_1536_, v___y_1527_, v___y_1526_, v___x_1575_);
v___x_1577_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1));
v___x_1578_ = l_Lean_Name_mkStr4(v___y_1536_, v___y_1527_, v___y_1526_, v___x_1577_);
if (lean_obj_tag(v___y_1535_) == 1)
{
lean_object* v_val_1579_; lean_object* v___x_1580_; 
v_val_1579_ = lean_ctor_get(v___y_1535_, 0);
lean_inc(v_val_1579_);
lean_dec_ref_known(v___y_1535_, 1);
v___x_1580_ = l_Array_mkArray1___redArg(v_val_1579_);
lean_inc(v_currMacroScope_1542_);
lean_inc(v_quotContext_1541_);
v___y_1403_ = v___x_1558_;
v___y_1404_ = v___x_1551_;
v___y_1405_ = v___x_1552_;
v___y_1406_ = v_quotContext_1541_;
v___y_1407_ = v___y_1534_;
v___y_1408_ = v_a_1550_;
v___y_1409_ = v___x_1567_;
v___y_1410_ = v___x_1557_;
v___y_1411_ = v_currMacroScope_1542_;
v___y_1412_ = v___y_1525_;
v___y_1413_ = v___y_1527_;
v___y_1414_ = v___y_1526_;
v___y_1415_ = v___y_1529_;
v___y_1416_ = v_wds_x3f_1537_;
v___y_1417_ = v___x_1576_;
v___y_1418_ = v___x_1559_;
v___y_1419_ = v___x_1574_;
v___y_1420_ = v___y_1536_;
v___y_1421_ = v_a_1549_;
v___y_1422_ = v___x_1578_;
v___y_1423_ = v___x_1580_;
goto v___jp_1402_;
}
else
{
lean_object* v___x_1581_; 
lean_dec(v___y_1535_);
v___x_1581_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
lean_inc(v_currMacroScope_1542_);
lean_inc(v_quotContext_1541_);
v___y_1403_ = v___x_1558_;
v___y_1404_ = v___x_1551_;
v___y_1405_ = v___x_1552_;
v___y_1406_ = v_quotContext_1541_;
v___y_1407_ = v___y_1534_;
v___y_1408_ = v_a_1550_;
v___y_1409_ = v___x_1567_;
v___y_1410_ = v___x_1557_;
v___y_1411_ = v_currMacroScope_1542_;
v___y_1412_ = v___y_1525_;
v___y_1413_ = v___y_1527_;
v___y_1414_ = v___y_1526_;
v___y_1415_ = v___y_1529_;
v___y_1416_ = v_wds_x3f_1537_;
v___y_1417_ = v___x_1576_;
v___y_1418_ = v___x_1559_;
v___y_1419_ = v___x_1574_;
v___y_1420_ = v___y_1536_;
v___y_1421_ = v_a_1549_;
v___y_1422_ = v___x_1578_;
v___y_1423_ = v___x_1581_;
goto v___jp_1402_;
}
}
else
{
lean_object* v_a_1582_; lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec(v_ref_1546_);
lean_dec(v_wds_x3f_1537_);
lean_dec(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec(v___y_1533_);
v_a_1582_ = lean_ctor_get(v___x_1548_, 0);
v_a_1583_ = lean_ctor_get(v___x_1548_, 1);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1548_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_inc(v_a_1582_);
lean_dec(v___x_1548_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1582_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
v___jp_1591_:
{
lean_object* v___x_1607_; 
v___x_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1607_, 0, v___y_1594_);
v___y_1525_ = v___y_1597_;
v___y_1526_ = v___y_1598_;
v___y_1527_ = v___y_1599_;
v___y_1528_ = v___y_1600_;
v___y_1529_ = v___y_1601_;
v___y_1530_ = v___y_1602_;
v___y_1531_ = v___y_1603_;
v___y_1532_ = v___y_1592_;
v___y_1533_ = v___y_1593_;
v___y_1534_ = v___y_1595_;
v___y_1535_ = v___y_1606_;
v___y_1536_ = v___y_1605_;
v_wds_x3f_1537_ = v___x_1607_;
v___y_1538_ = v___y_1596_;
v___y_1539_ = v___y_1604_;
goto v___jp_1524_;
}
v___jp_1608_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_inc_ref_n(v___y_1616_, 2);
v___x_1623_ = l_Array_append___redArg(v___y_1616_, v___y_1622_);
lean_dec_ref(v___y_1622_);
lean_inc_n(v___y_1617_, 2);
lean_inc_n(v___y_1611_, 6);
v___x_1624_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1624_, 0, v___y_1611_);
lean_ctor_set(v___x_1624_, 1, v___y_1617_);
lean_ctor_set(v___x_1624_, 2, v___x_1623_);
v___x_1625_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_1626_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26));
lean_inc_ref_n(v___y_1614_, 2);
lean_inc_ref_n(v___y_1620_, 2);
v___x_1627_ = l_Lean_Name_mkStr4(v___y_1620_, v___y_1614_, v___x_1625_, v___x_1626_);
v___x_1628_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39));
v___x_1629_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___y_1611_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
lean_inc_ref(v___y_1609_);
v___x_1630_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___y_1611_);
lean_ctor_set(v___x_1630_, 1, v___y_1609_);
lean_inc(v___y_1612_);
v___x_1631_ = l_Lean_Syntax_node2(v___y_1611_, v___y_1612_, v___x_1630_, v___y_1618_);
v___x_1632_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27));
v___x_1633_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28));
v___x_1634_ = l_Lean_Name_mkStr4(v___y_1620_, v___y_1614_, v___x_1632_, v___x_1633_);
v___x_1635_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1635_, 0, v___y_1611_);
lean_ctor_set(v___x_1635_, 1, v___y_1617_);
lean_ctor_set(v___x_1635_, 2, v___y_1616_);
lean_inc_ref(v___x_1635_);
v___x_1636_ = l_Lean_Syntax_node2(v___y_1611_, v___x_1634_, v___x_1635_, v___x_1635_);
if (lean_obj_tag(v___y_1615_) == 1)
{
lean_object* v_val_1637_; lean_object* v___x_1638_; 
v_val_1637_ = lean_ctor_get(v___y_1615_, 0);
lean_inc(v_val_1637_);
lean_dec_ref_known(v___y_1615_, 1);
v___x_1638_ = l_Array_mkArray1___redArg(v_val_1637_);
v___y_1380_ = v___y_1617_;
v___y_1381_ = v___x_1629_;
v___y_1382_ = v___x_1627_;
v___y_1383_ = v___y_1610_;
v___y_1384_ = v___x_1636_;
v___y_1385_ = v___y_1611_;
v___y_1386_ = v___y_1613_;
v___y_1387_ = v___x_1631_;
v___y_1388_ = v___y_1619_;
v___y_1389_ = v___x_1624_;
v___y_1390_ = v___y_1621_;
v___y_1391_ = v___y_1616_;
v___y_1392_ = v___x_1638_;
goto v___jp_1379_;
}
else
{
lean_object* v___x_1639_; 
lean_dec(v___y_1615_);
v___x_1639_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___y_1380_ = v___y_1617_;
v___y_1381_ = v___x_1629_;
v___y_1382_ = v___x_1627_;
v___y_1383_ = v___y_1610_;
v___y_1384_ = v___x_1636_;
v___y_1385_ = v___y_1611_;
v___y_1386_ = v___y_1613_;
v___y_1387_ = v___x_1631_;
v___y_1388_ = v___y_1619_;
v___y_1389_ = v___x_1624_;
v___y_1390_ = v___y_1621_;
v___y_1391_ = v___y_1616_;
v___y_1392_ = v___x_1639_;
goto v___jp_1379_;
}
}
v___jp_1640_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_inc_ref(v___y_1647_);
v___x_1655_ = l_Array_append___redArg(v___y_1647_, v___y_1654_);
lean_dec_ref(v___y_1654_);
lean_inc(v___y_1648_);
lean_inc(v___y_1643_);
v___x_1656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1656_, 0, v___y_1643_);
lean_ctor_set(v___x_1656_, 1, v___y_1648_);
lean_ctor_set(v___x_1656_, 2, v___x_1655_);
v___x_1657_ = l_Lean_SourceInfo_fromRef(v___y_1649_, v___x_1398_);
lean_dec(v___y_1649_);
v___x_1658_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23));
v___x_1659_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1657_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
if (lean_obj_tag(v___y_1651_) == 1)
{
lean_object* v_val_1660_; lean_object* v___x_1661_; 
v_val_1660_ = lean_ctor_get(v___y_1651_, 0);
lean_inc(v_val_1660_);
lean_dec_ref_known(v___y_1651_, 1);
v___x_1661_ = l_Array_mkArray1___redArg(v_val_1660_);
v___y_1609_ = v___y_1641_;
v___y_1610_ = v___y_1642_;
v___y_1611_ = v___y_1643_;
v___y_1612_ = v___y_1644_;
v___y_1613_ = v___x_1659_;
v___y_1614_ = v___y_1645_;
v___y_1615_ = v___y_1646_;
v___y_1616_ = v___y_1647_;
v___y_1617_ = v___y_1648_;
v___y_1618_ = v___y_1650_;
v___y_1619_ = v___x_1656_;
v___y_1620_ = v___y_1652_;
v___y_1621_ = v___y_1653_;
v___y_1622_ = v___x_1661_;
goto v___jp_1608_;
}
else
{
lean_object* v___x_1662_; 
lean_dec(v___y_1651_);
v___x_1662_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___y_1609_ = v___y_1641_;
v___y_1610_ = v___y_1642_;
v___y_1611_ = v___y_1643_;
v___y_1612_ = v___y_1644_;
v___y_1613_ = v___x_1659_;
v___y_1614_ = v___y_1645_;
v___y_1615_ = v___y_1646_;
v___y_1616_ = v___y_1647_;
v___y_1617_ = v___y_1648_;
v___y_1618_ = v___y_1650_;
v___y_1619_ = v___x_1656_;
v___y_1620_ = v___y_1652_;
v___y_1621_ = v___y_1653_;
v___y_1622_ = v___x_1662_;
goto v___jp_1608_;
}
}
v___jp_1663_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_inc_ref(v___y_1670_);
v___x_1678_ = l_Array_append___redArg(v___y_1670_, v___y_1677_);
lean_dec_ref(v___y_1677_);
lean_inc(v___y_1671_);
lean_inc(v___y_1665_);
v___x_1679_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1679_, 0, v___y_1665_);
lean_ctor_set(v___x_1679_, 1, v___y_1671_);
lean_ctor_set(v___x_1679_, 2, v___x_1678_);
if (lean_obj_tag(v___y_1667_) == 1)
{
lean_object* v_val_1680_; lean_object* v___x_1681_; 
v_val_1680_ = lean_ctor_get(v___y_1667_, 0);
lean_inc(v_val_1680_);
lean_dec_ref_known(v___y_1667_, 1);
v___x_1681_ = l_Array_mkArray1___redArg(v_val_1680_);
v___y_1641_ = v___y_1664_;
v___y_1642_ = v___x_1679_;
v___y_1643_ = v___y_1665_;
v___y_1644_ = v___y_1666_;
v___y_1645_ = v___y_1668_;
v___y_1646_ = v___y_1669_;
v___y_1647_ = v___y_1670_;
v___y_1648_ = v___y_1671_;
v___y_1649_ = v___y_1672_;
v___y_1650_ = v___y_1673_;
v___y_1651_ = v___y_1674_;
v___y_1652_ = v___y_1675_;
v___y_1653_ = v___y_1676_;
v___y_1654_ = v___x_1681_;
goto v___jp_1640_;
}
else
{
lean_object* v___x_1682_; 
lean_dec(v___y_1667_);
v___x_1682_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___y_1641_ = v___y_1664_;
v___y_1642_ = v___x_1679_;
v___y_1643_ = v___y_1665_;
v___y_1644_ = v___y_1666_;
v___y_1645_ = v___y_1668_;
v___y_1646_ = v___y_1669_;
v___y_1647_ = v___y_1670_;
v___y_1648_ = v___y_1671_;
v___y_1649_ = v___y_1672_;
v___y_1650_ = v___y_1673_;
v___y_1651_ = v___y_1674_;
v___y_1652_ = v___y_1675_;
v___y_1653_ = v___y_1676_;
v___y_1654_ = v___x_1682_;
goto v___jp_1640_;
}
}
v___jp_1683_:
{
lean_object* v_ref_1696_; uint8_t v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v_ref_1696_ = lean_ctor_get(v___y_1694_, 5);
v___x_1697_ = 0;
v___x_1698_ = l_Lean_SourceInfo_fromRef(v_ref_1696_, v___x_1697_);
v___x_1699_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3));
v___x_1700_ = lean_obj_once(&l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4, &l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once, _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
if (lean_obj_tag(v___y_1690_) == 1)
{
lean_object* v_val_1701_; lean_object* v___x_1702_; 
v_val_1701_ = lean_ctor_get(v___y_1690_, 0);
lean_inc(v_val_1701_);
lean_dec_ref_known(v___y_1690_, 1);
v___x_1702_ = l_Array_mkArray1___redArg(v_val_1701_);
v___y_1664_ = v___y_1685_;
v___y_1665_ = v___x_1698_;
v___y_1666_ = v___y_1689_;
v___y_1667_ = v___y_1688_;
v___y_1668_ = v___y_1692_;
v___y_1669_ = v_wds_x3f_1693_;
v___y_1670_ = v___x_1700_;
v___y_1671_ = v___x_1699_;
v___y_1672_ = v___y_1684_;
v___y_1673_ = v___y_1687_;
v___y_1674_ = v___y_1686_;
v___y_1675_ = v___y_1691_;
v___y_1676_ = v___y_1695_;
v___y_1677_ = v___x_1702_;
goto v___jp_1663_;
}
else
{
lean_object* v___x_1703_; 
lean_dec(v___y_1690_);
v___x_1703_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30));
v___y_1664_ = v___y_1685_;
v___y_1665_ = v___x_1698_;
v___y_1666_ = v___y_1689_;
v___y_1667_ = v___y_1688_;
v___y_1668_ = v___y_1692_;
v___y_1669_ = v_wds_x3f_1693_;
v___y_1670_ = v___x_1700_;
v___y_1671_ = v___x_1699_;
v___y_1672_ = v___y_1684_;
v___y_1673_ = v___y_1687_;
v___y_1674_ = v___y_1686_;
v___y_1675_ = v___y_1691_;
v___y_1676_ = v___y_1695_;
v___y_1677_ = v___x_1703_;
goto v___jp_1663_;
}
}
v___jp_1704_:
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1717_, 0, v___y_1712_);
v___y_1684_ = v___y_1706_;
v___y_1685_ = v___y_1705_;
v___y_1686_ = v___y_1708_;
v___y_1687_ = v___y_1707_;
v___y_1688_ = v___y_1710_;
v___y_1689_ = v___y_1709_;
v___y_1690_ = v___y_1714_;
v___y_1691_ = v___y_1713_;
v___y_1692_ = v___y_1715_;
v_wds_x3f_1693_ = v___x_1717_;
v___y_1694_ = v___y_1716_;
v___y_1695_ = v___y_1711_;
goto v___jp_1683_;
}
v___jp_1718_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1728_ = lean_unsigned_to_nat(4u);
v___x_1729_ = l_Lean_Syntax_getArg(v_stx_1352_, v___x_1728_);
v___x_1730_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26));
lean_inc(v___x_1729_);
v___x_1731_ = l_Lean_Syntax_isOfKind(v___x_1729_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1732_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_1733_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_1734_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16));
v___x_1735_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27));
lean_inc(v___x_1729_);
v___x_1736_ = l_Lean_Syntax_isOfKind(v___x_1729_, v___x_1735_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec(v___x_1729_);
lean_dec(v_pkg_x3f_1725_);
lean_dec(v___y_1724_);
lean_dec(v___y_1722_);
lean_dec(v___y_1720_);
v___x_1737_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1738_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1352_, v___x_1737_, v___y_1726_, v___y_1727_);
lean_dec(v_stx_1352_);
return v___x_1738_;
}
else
{
lean_object* v___x_1739_; lean_object* v___x_1740_; uint8_t v___x_1741_; 
v___x_1739_ = l_Lean_Syntax_getArg(v___x_1729_, v___y_1723_);
v___x_1740_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28));
lean_inc(v___x_1739_);
v___x_1741_ = l_Lean_Syntax_isOfKind(v___x_1739_, v___x_1740_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_dec(v___x_1739_);
lean_dec(v___x_1729_);
lean_dec(v_pkg_x3f_1725_);
lean_dec(v___y_1724_);
lean_dec(v___y_1722_);
lean_dec(v___y_1720_);
v___x_1742_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1743_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1352_, v___x_1742_, v___y_1726_, v___y_1727_);
lean_dec(v_stx_1352_);
return v___x_1743_;
}
else
{
lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1744_ = l_Lean_Syntax_getArg(v___x_1739_, v___x_1401_);
v___x_1745_ = l_Lean_Syntax_matchesNull(v___x_1744_, v___x_1401_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec(v___x_1739_);
lean_dec(v___x_1729_);
lean_dec(v_pkg_x3f_1725_);
lean_dec(v___y_1724_);
lean_dec(v___y_1722_);
lean_dec(v___y_1720_);
v___x_1746_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1747_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1352_, v___x_1746_, v___y_1726_, v___y_1727_);
lean_dec(v_stx_1352_);
return v___x_1747_;
}
else
{
lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1748_ = l_Lean_Syntax_getArg(v___x_1739_, v___y_1721_);
lean_dec(v___x_1739_);
v___x_1749_ = l_Lean_Syntax_matchesNull(v___x_1748_, v___x_1401_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec(v___x_1729_);
lean_dec(v_pkg_x3f_1725_);
lean_dec(v___y_1724_);
lean_dec(v___y_1722_);
lean_dec(v___y_1720_);
v___x_1750_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1751_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1352_, v___x_1750_, v___y_1726_, v___y_1727_);
lean_dec(v_stx_1352_);
return v___x_1751_;
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1752_ = l_Lean_Syntax_getArg(v___x_1729_, v___y_1721_);
v___x_1753_ = l_Lean_Syntax_getArg(v___x_1729_, v___y_1719_);
lean_dec(v___x_1729_);
v___x_1754_ = l_Lean_Syntax_isNone(v___x_1753_);
if (v___x_1754_ == 0)
{
uint8_t v___x_1755_; 
lean_inc(v___x_1753_);
v___x_1755_ = l_Lean_Syntax_matchesNull(v___x_1753_, v___y_1721_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec(v___x_1753_);
lean_dec(v___x_1752_);
lean_dec(v_pkg_x3f_1725_);
lean_dec(v___y_1724_);
lean_dec(v___y_1722_);
lean_dec(v___y_1720_);
v___x_1756_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1757_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1352_, v___x_1756_, v___y_1726_, v___y_1727_);
lean_dec(v_stx_1352_);
return v___x_1757_;
}
else
{
lean_object* v_wds_x3f_1758_; 
v_wds_x3f_1758_ = l_Lean_Syntax_getArg(v___x_1753_, v___x_1401_);
lean_dec(v___x_1753_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_1758_);
v___x_1760_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1758_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
lean_dec(v_wds_x3f_1758_);
lean_dec(v___x_1752_);
lean_dec(v_pkg_x3f_1725_);
lean_dec(v___y_1724_);
lean_dec(v___y_1722_);
lean_dec(v___y_1720_);
v___x_1761_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1762_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1352_, v___x_1761_, v___y_1726_, v___y_1727_);
lean_dec(v_stx_1352_);
return v___x_1762_;
}
else
{
lean_dec(v_stx_1352_);
v___y_1592_ = v___y_1721_;
v___y_1593_ = v___y_1722_;
v___y_1594_ = v_wds_x3f_1758_;
v___y_1595_ = v___x_1752_;
v___y_1596_ = v___y_1726_;
v___y_1597_ = v___x_1735_;
v___y_1598_ = v___x_1734_;
v___y_1599_ = v___x_1733_;
v___y_1600_ = v___y_1720_;
v___y_1601_ = v___x_1740_;
v___y_1602_ = v___x_1731_;
v___y_1603_ = v_pkg_x3f_1725_;
v___y_1604_ = v___y_1727_;
v___y_1605_ = v___x_1732_;
v___y_1606_ = v___y_1724_;
goto v___jp_1591_;
}
}
else
{
lean_dec(v_stx_1352_);
v___y_1592_ = v___y_1721_;
v___y_1593_ = v___y_1722_;
v___y_1594_ = v_wds_x3f_1758_;
v___y_1595_ = v___x_1752_;
v___y_1596_ = v___y_1726_;
v___y_1597_ = v___x_1735_;
v___y_1598_ = v___x_1734_;
v___y_1599_ = v___x_1733_;
v___y_1600_ = v___y_1720_;
v___y_1601_ = v___x_1740_;
v___y_1602_ = v___x_1731_;
v___y_1603_ = v_pkg_x3f_1725_;
v___y_1604_ = v___y_1727_;
v___y_1605_ = v___x_1732_;
v___y_1606_ = v___y_1724_;
goto v___jp_1591_;
}
}
}
else
{
lean_object* v___x_1763_; 
lean_dec(v___x_1753_);
lean_dec(v_stx_1352_);
v___x_1763_ = lean_box(0);
v___y_1525_ = v___x_1735_;
v___y_1526_ = v___x_1734_;
v___y_1527_ = v___x_1733_;
v___y_1528_ = v___y_1720_;
v___y_1529_ = v___x_1740_;
v___y_1530_ = v___x_1731_;
v___y_1531_ = v_pkg_x3f_1725_;
v___y_1532_ = v___y_1721_;
v___y_1533_ = v___y_1722_;
v___y_1534_ = v___x_1752_;
v___y_1535_ = v___y_1724_;
v___y_1536_ = v___x_1732_;
v_wds_x3f_1537_ = v___x_1763_;
v___y_1538_ = v___y_1726_;
v___y_1539_ = v___y_1727_;
goto v___jp_1524_;
}
}
}
}
}
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1764_ = l_Lean_Syntax_getArg(v___x_1729_, v___x_1401_);
v___x_1765_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14));
v___x_1766_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15));
v___x_1767_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29));
v___x_1768_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30));
lean_inc(v___x_1764_);
v___x_1769_ = l_Lean_Syntax_isOfKind(v___x_1764_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec(v___x_1764_);
lean_dec(v___x_1729_);
lean_dec(v_pkg_x3f_1725_);
lean_dec(v___y_1724_);
lean_dec(v___y_1722_);
lean_dec(v___y_1720_);
v___x_1770_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1771_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1352_, v___x_1770_, v___y_1726_, v___y_1727_);
lean_dec(v_stx_1352_);
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1772_ = l_Lean_Syntax_getArg(v___x_1764_, v___y_1721_);
lean_dec(v___x_1764_);
v___x_1773_ = l_Lean_Syntax_getArg(v___x_1729_, v___y_1721_);
lean_dec(v___x_1729_);
v___x_1774_ = l_Lean_Syntax_isNone(v___x_1773_);
if (v___x_1774_ == 0)
{
uint8_t v___x_1775_; 
lean_inc(v___x_1773_);
v___x_1775_ = l_Lean_Syntax_matchesNull(v___x_1773_, v___y_1721_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_dec(v___x_1773_);
lean_dec(v___x_1772_);
lean_dec(v_pkg_x3f_1725_);
lean_dec(v___y_1724_);
lean_dec(v___y_1722_);
lean_dec(v___y_1720_);
v___x_1776_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1777_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1352_, v___x_1776_, v___y_1726_, v___y_1727_);
lean_dec(v_stx_1352_);
return v___x_1777_;
}
else
{
lean_object* v_wds_x3f_1778_; 
v_wds_x3f_1778_ = l_Lean_Syntax_getArg(v___x_1773_, v___x_1401_);
lean_dec(v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1779_ = ((lean_object*)(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34));
lean_inc(v_wds_x3f_1778_);
v___x_1780_ = l_Lean_Syntax_isOfKind(v_wds_x3f_1778_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_dec(v_wds_x3f_1778_);
lean_dec(v___x_1772_);
lean_dec(v_pkg_x3f_1725_);
lean_dec(v___y_1724_);
lean_dec(v___y_1722_);
lean_dec(v___y_1720_);
v___x_1781_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1782_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1352_, v___x_1781_, v___y_1726_, v___y_1727_);
lean_dec(v_stx_1352_);
return v___x_1782_;
}
else
{
lean_dec(v_stx_1352_);
v___y_1705_ = v___x_1767_;
v___y_1706_ = v___y_1720_;
v___y_1707_ = v___x_1772_;
v___y_1708_ = v_pkg_x3f_1725_;
v___y_1709_ = v___x_1768_;
v___y_1710_ = v___y_1722_;
v___y_1711_ = v___y_1727_;
v___y_1712_ = v_wds_x3f_1778_;
v___y_1713_ = v___x_1765_;
v___y_1714_ = v___y_1724_;
v___y_1715_ = v___x_1766_;
v___y_1716_ = v___y_1726_;
goto v___jp_1704_;
}
}
else
{
lean_dec(v_stx_1352_);
v___y_1705_ = v___x_1767_;
v___y_1706_ = v___y_1720_;
v___y_1707_ = v___x_1772_;
v___y_1708_ = v_pkg_x3f_1725_;
v___y_1709_ = v___x_1768_;
v___y_1710_ = v___y_1722_;
v___y_1711_ = v___y_1727_;
v___y_1712_ = v_wds_x3f_1778_;
v___y_1713_ = v___x_1765_;
v___y_1714_ = v___y_1724_;
v___y_1715_ = v___x_1766_;
v___y_1716_ = v___y_1726_;
goto v___jp_1704_;
}
}
}
else
{
lean_object* v___x_1783_; 
lean_dec(v___x_1773_);
lean_dec(v_stx_1352_);
v___x_1783_ = lean_box(0);
v___y_1684_ = v___y_1720_;
v___y_1685_ = v___x_1767_;
v___y_1686_ = v_pkg_x3f_1725_;
v___y_1687_ = v___x_1772_;
v___y_1688_ = v___y_1722_;
v___y_1689_ = v___x_1768_;
v___y_1690_ = v___y_1724_;
v___y_1691_ = v___x_1765_;
v___y_1692_ = v___x_1766_;
v_wds_x3f_1693_ = v___x_1783_;
v___y_1694_ = v___y_1726_;
v___y_1695_ = v___y_1727_;
goto v___jp_1683_;
}
}
}
}
v___jp_1784_:
{
lean_object* v___x_1790_; lean_object* v_kw_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v___x_1790_ = lean_unsigned_to_nat(2u);
v_kw_1791_ = l_Lean_Syntax_getArg(v_stx_1352_, v___x_1790_);
v___x_1792_ = lean_unsigned_to_nat(3u);
v___x_1793_ = l_Lean_Syntax_getArg(v_stx_1352_, v___x_1792_);
v___x_1794_ = l_Lean_Syntax_isNone(v___x_1793_);
if (v___x_1794_ == 0)
{
uint8_t v___x_1795_; 
lean_inc(v___x_1793_);
v___x_1795_ = l_Lean_Syntax_matchesNull(v___x_1793_, v___y_1785_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec(v___x_1793_);
lean_dec(v_kw_1791_);
lean_dec(v_attrs_x3f_1787_);
lean_dec(v___y_1786_);
v___x_1796_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1797_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1352_, v___x_1796_, v___y_1788_, v___y_1789_);
lean_dec(v_stx_1352_);
return v___x_1797_;
}
else
{
lean_object* v_pkg_x3f_1798_; lean_object* v___x_1799_; 
v_pkg_x3f_1798_ = l_Lean_Syntax_getArg(v___x_1793_, v___x_1401_);
lean_dec(v___x_1793_);
v___x_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1799_, 0, v_pkg_x3f_1798_);
v___y_1719_ = v___x_1792_;
v___y_1720_ = v_kw_1791_;
v___y_1721_ = v___y_1785_;
v___y_1722_ = v_attrs_x3f_1787_;
v___y_1723_ = v___x_1790_;
v___y_1724_ = v___y_1786_;
v_pkg_x3f_1725_ = v___x_1799_;
v___y_1726_ = v___y_1788_;
v___y_1727_ = v___y_1789_;
goto v___jp_1718_;
}
}
else
{
lean_object* v___x_1800_; 
lean_dec(v___x_1793_);
v___x_1800_ = lean_box(0);
v___y_1719_ = v___x_1792_;
v___y_1720_ = v_kw_1791_;
v___y_1721_ = v___y_1785_;
v___y_1722_ = v_attrs_x3f_1787_;
v___y_1723_ = v___x_1790_;
v___y_1724_ = v___y_1786_;
v_pkg_x3f_1725_ = v___x_1800_;
v___y_1726_ = v___y_1788_;
v___y_1727_ = v___y_1789_;
goto v___jp_1718_;
}
}
v___jp_1801_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1805_ = lean_unsigned_to_nat(1u);
v___x_1806_ = l_Lean_Syntax_getArg(v_stx_1352_, v___x_1805_);
v___x_1807_ = l_Lean_Syntax_isNone(v___x_1806_);
if (v___x_1807_ == 0)
{
uint8_t v___x_1808_; 
lean_inc(v___x_1806_);
v___x_1808_ = l_Lean_Syntax_matchesNull(v___x_1806_, v___x_1805_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_dec(v___x_1806_);
lean_dec(v_doc_x3f_1802_);
v___x_1809_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2));
v___x_1810_ = l_Lean_Macro_throwErrorAt___redArg(v_stx_1352_, v___x_1809_, v___y_1803_, v___y_1804_);
lean_dec(v_stx_1352_);
return v___x_1810_;
}
else
{
lean_object* v_attrs_x3f_1811_; lean_object* v___x_1812_; 
v_attrs_x3f_1811_ = l_Lean_Syntax_getArg(v___x_1806_, v___x_1401_);
lean_dec(v___x_1806_);
v___x_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1812_, 0, v_attrs_x3f_1811_);
v___y_1785_ = v___x_1805_;
v___y_1786_ = v_doc_x3f_1802_;
v_attrs_x3f_1787_ = v___x_1812_;
v___y_1788_ = v___y_1803_;
v___y_1789_ = v___y_1804_;
goto v___jp_1784_;
}
}
else
{
lean_object* v___x_1813_; 
lean_dec(v___x_1806_);
v___x_1813_ = lean_box(0);
v___y_1785_ = v___x_1805_;
v___y_1786_ = v_doc_x3f_1802_;
v_attrs_x3f_1787_ = v___x_1813_;
v___y_1788_ = v___y_1803_;
v___y_1789_ = v___y_1804_;
goto v___jp_1784_;
}
}
}
v___jp_1355_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_inc_ref(v___y_1358_);
v___x_1372_ = l_Array_append___redArg(v___y_1358_, v___y_1371_);
lean_dec_ref(v___y_1371_);
lean_inc(v___y_1363_);
lean_inc_n(v___y_1359_, 3);
v___x_1373_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1373_, 0, v___y_1359_);
lean_ctor_set(v___x_1373_, 1, v___y_1363_);
lean_ctor_set(v___x_1373_, 2, v___x_1372_);
lean_inc(v___y_1364_);
v___x_1374_ = l_Lean_Syntax_node4(v___y_1359_, v___y_1364_, v___y_1360_, v___y_1356_, v___y_1357_, v___x_1373_);
v___x_1375_ = l_Lean_Syntax_node5(v___y_1359_, v___y_1370_, v___y_1365_, v___y_1368_, v___y_1369_, v___x_1374_, v___y_1367_);
v___x_1376_ = l_Lean_Syntax_node2(v___y_1359_, v___y_1366_, v___y_1362_, v___x_1375_);
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
lean_ctor_set(v___x_1377_, 1, v___y_1361_);
return v___x_1377_;
}
v___jp_1379_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
lean_inc_ref(v___y_1391_);
v___x_1393_ = l_Array_append___redArg(v___y_1391_, v___y_1392_);
lean_dec_ref(v___y_1392_);
lean_inc(v___y_1380_);
lean_inc_n(v___y_1385_, 2);
v___x_1394_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1394_, 0, v___y_1385_);
lean_ctor_set(v___x_1394_, 1, v___y_1380_);
lean_ctor_set(v___x_1394_, 2, v___x_1393_);
v___x_1395_ = l_Lean_Syntax_node4(v___y_1385_, v___y_1382_, v___y_1381_, v___y_1387_, v___y_1384_, v___x_1394_);
v___x_1396_ = l_Lean_Syntax_node5(v___y_1385_, v___x_1378_, v___y_1383_, v___y_1388_, v___y_1386_, v___y_1389_, v___x_1395_);
v___x_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
lean_ctor_set(v___x_1397_, 1, v___y_1390_);
return v___x_1397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___boxed(lean_object* v_stx_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl(v_stx_1823_, v_a_1824_, v_a_1825_);
lean_dec_ref(v_a_1824_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1(){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1832_ = l_Lean_Elab_macroAttribute;
v___x_1833_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1));
v___x_1834_ = ((lean_object*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1));
v___x_1835_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___boxed), 3, 0);
v___x_1836_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1832_, v___x_1833_, v___x_1834_, v___x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___boxed(lean_object* v_a_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1();
return v_res_1838_;
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
