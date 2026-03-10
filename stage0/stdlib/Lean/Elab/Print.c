// Lean compiler output
// Module: Lean.Elab.Print
// Imports: public import Lean.Meta.Eqns public import Lean.Elab.Command import Lean.PrettyPrinter.Delaborator.Builtins
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
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__3;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___closed__2;
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Unknown identifier `"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__0 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__1;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__2 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__0_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__2;
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__0 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__1 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__2;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".{"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__4;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__5 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__6 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__0 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__2 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "meta "};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__5 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "protected "};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__8 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "private "};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__11 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unsafe "};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__13 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__13_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__14 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__15;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "partial "};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__16 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__16_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__17 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__17_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__18;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__20 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__20_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__21 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__21_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__22;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__23;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "] "};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__24 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__24_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__25 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__25_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__26;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "defeq"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__27 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__27_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__28;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "expose"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__29 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__29_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__30;
static const lean_array_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__31 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__31_value;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducible"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__32 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__32_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__33;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__34;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "irreducible"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__35 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__35_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__36;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__37;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "implicit_reducible"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__38 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__38_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__39;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__40;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
uint8_t l_Lean_isProtected(lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
extern lean_object* l_Lean_defeqAttr;
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_isDefinition(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkOmittedMsg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "<not imported>"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkOmittedMsg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkOmittedMsg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkOmittedMsg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkOmittedMsg___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkOmittedMsg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkOmittedMsg___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkOmittedMsg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkOmittedMsg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkOmittedMsg(lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1___lam__0___closed__0_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " :="};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__0 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Quotient primitive"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___closed__0 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__2_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___redArg___closed__1;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "inductive"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__0 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "number of parameters: "};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "constructors:"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__5 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__6;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "for "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ("};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__3;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " fields): "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__4_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rules:"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__0 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__1 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__2;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "recursor"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__3 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__4;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "number of indices: "};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__5 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__6;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "number of motives: "};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__7 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__8;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "number of minors: "};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__9 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__10;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "supports k-like reduction"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__11 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "no such field "};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__0 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__1;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__2 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__3;
lean_object* l_Lean_getStructureParentInfo(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getFieldInfo_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_findField_x3f(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Options_set___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__3___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__3___closed__0_value;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__3(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__12___closed__0;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delabCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__18___closed__0 = (const lean_object*)&l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__18___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__18___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__18___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 78, 141, 85, 50, 255, 216, 83)}};
static const lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__18___closed__1 = (const lean_object*)&l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__18___closed__1_value;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__19___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__19___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__19___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__19___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__2_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__4_value;
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__5 = (const lean_object*)&l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__5_value;
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__6 = (const lean_object*)&l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__6_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__17___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__17___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__17___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__17___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__17(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__55_spec__61___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__55_spec__61___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__55(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__55___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__56___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__56___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Meta.Structure"};
static const lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__0 = (const lean_object*)&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__0_value;
static const lean_string_object l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Meta.instantiateStructDefaultValueFn\?"};
static const lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__1 = (const lean_object*)&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__1_value;
static const lean_string_object l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "assertion violation: us.length == cinfo.levelParams.length\n  "};
static const lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__2 = (const lean_object*)&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__3;
lean_object* l_Lean_Meta_mkFreshLevelMVarsFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Data.DTreeMap.Internal.Queries"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.DTreeMap.Internal.Impl.Const.get!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Key is not present in map"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___closed__3;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " := by"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " := <error>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.Elab.Print"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "_private.Lean.Elab.Print.0.Lean.Elab.Command.printStructure"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "missing structure field info"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__8;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_getEffectiveDefaultFnForField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___boxed(lean_object**);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__57_spec__59___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__57___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58___redArg___closed__0;
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___closed__2;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__2;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__3;
extern lean_object* l_Lean_structureResolutionExt;
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__32_spec__42(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__32_spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__32(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__32___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__35(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__35___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__31_spec__40(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__31_spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__31(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__29(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__30___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__30___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__30___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__30(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__33_spec__44(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__33_spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__33(lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__33___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__28(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__37(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_lt___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__36___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_lt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__36___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__36___redArg___closed__0_value;
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__36___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__36___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__32_spec__35(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__32_spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__32(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__33_spec__37(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__33_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__33(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__0;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__1_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__1_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__2_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34___redArg___lam__0___boxed, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__2_value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__35___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__35___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__34(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__38___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__38___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__38___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__38(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8___closed__0 = (const lean_object*)&l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__26(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__14___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__1;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "constructor:"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__4;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "field notation resolution order:"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__5 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__7;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "fields:"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__8_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__9 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__10;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fields: (none)"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__11 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__11_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__12 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__13;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "parents:"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__14 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__14_value)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__15 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__15_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__16;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_pp_proofs;
extern lean_object* l_Lean_diagnostics;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabConstWithSignature___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormatWithInfosM(lean_object*);
lean_object* l_Lean_MessageData_signature(lean_object*);
lean_object* l_Lean_getStructureCtor(lean_object*, lean_object*);
lean_object* l_Lean_mkFlatCtorOfStructCtorName(lean_object*);
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16_spec__25___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16_spec__25___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16_spec__25___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "self"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 226, 111, 209, 39, 160, 197, 219)}};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__3___boxed(lean_object**);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__2(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "structure"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__0 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "class"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__1 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__1_value;
uint8_t lean_is_class(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__14(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16_spec__25(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__19(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__55_spec__61(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__55_spec__61___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__56(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__56___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__57(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__57_spec__59(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "axiom"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__0 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__1 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "theorem"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__2 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "opaque"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__3 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "constructor"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__4 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__4_value;
lean_object* l_Lean_getOriginalConstKind_x3f(lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__2;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstWithInfos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Command_elabPrint_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Command_elabPrint_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabPrint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Command_elabPrint___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabPrint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Command_elabPrint___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabPrint___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_elabPrint___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabPrint___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "print"};
static const lean_object* l_Lean_Elab_Command_elabPrint___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_elabPrint___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrint___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrint___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrint___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__3_value),LEAN_SCALAR_PTR_LITERAL(125, 118, 167, 37, 251, 50, 94, 42)}};
static const lean_object* l_Lean_Elab_Command_elabPrint___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_elabPrint___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid #print command"};
static const lean_object* l_Lean_Elab_Command_elabPrint___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Command_elabPrint___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__6;
static const lean_string_object l_Lean_Elab_Command_elabPrint___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Command_elabPrint___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrint___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__7_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Command_elabPrint___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___closed__8_value;
static const lean_string_object l_Lean_Elab_Command_elabPrint___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Elab_Command_elabPrint___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrint___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__9_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Elab_Command_elabPrint___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___closed__10_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrint(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrint___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabPrint"};
static const lean_object* l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 141, 99, 217, 211, 33, 65, 211)}};
static const lean_object* l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1_value;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(118) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(121) << 1) | 1)),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__0_value),((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__1_value),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(118) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(118) << 1) | 1)),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__3_value),((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__4_value),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__6_value;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printIdSig_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printIdSig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdSig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdSig___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintSig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintSig___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "printSig"};
static const lean_object* l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 120, 207, 188, 237, 203, 170, 123)}};
static const lean_object* l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabPrintSig"};
static const lean_object* l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__3_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(58, 199, 28, 47, 243, 81, 244, 44)}};
static const lean_object* l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0___redArg___closed__0;
lean_object* l_Lean_CollectAxioms_collect(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__2(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__0 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "' depends on axioms: "};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "' does not depend on any axioms"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__5;
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabPrintAxioms_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabPrintAxioms_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabPrintAxioms_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabPrintAxioms_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabPrintAxioms_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabPrintAxioms_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Command_elabPrintAxioms_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Command_elabPrintAxioms_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabPrintAxioms___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "printAxioms"};
static const lean_object* l_Lean_Elab_Command_elabPrintAxioms___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrintAxioms___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrintAxioms___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrintAxioms___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrintAxioms___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 183, 89, 85, 6, 216, 148, 104)}};
static const lean_object* l_Lean_Elab_Command_elabPrintAxioms___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabPrintAxioms___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 134, .m_capacity = 134, .m_length = 133, .m_data = "cannot use `#print axioms` in a `module`; consider temporarily removing the `module` header or placing the command in a separate file"};
static const lean_object* l_Lean_Elab_Command_elabPrintAxioms___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Command_elabPrintAxioms___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabPrintAxioms___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintAxioms(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintAxioms___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "elabPrintAxioms"};
static const lean_object* l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 215, 137, 142, 229, 71, 238, 75)}};
static const lean_object* l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(158) << 1) | 1)),((lean_object*)(((size_t)(38) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(162) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__0_value),((lean_object*)(((size_t)(38) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(158) << 1) | 1)),((lean_object*)(((size_t)(42) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(158) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__3_value),((lean_object*)(((size_t)(42) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__4_value),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___boxed(lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "equations:"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__0 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__1;
static const lean_string_object l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "' does not have equations"};
static const lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__2 = (const lean_object*)&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Command_elabPrintEqns_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Command_elabPrintEqns_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintEqns(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintEqns___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "printEqns"};
static const lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 233, 115, 120, 161, 167, 27, 177)}};
static const lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "elabPrintEqns"};
static const lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__3_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabPrint___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(223, 16, 211, 26, 47, 5, 228, 242)}};
static const lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(173) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(176) << 1) | 1)),((lean_object*)(((size_t)(21) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__0_value),((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__1_value),((lean_object*)(((size_t)(21) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(173) << 1) | 1)),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(173) << 1) | 1)),((lean_object*)(((size_t)(53) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__3_value),((lean_object*)(((size_t)(40) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__4_value),((lean_object*)(((size_t)(53) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___boxed(lean_object*);
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_26; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_5 = x_2;
x_6 = x_26;
goto block_25;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_23; 
x_7 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_3, 1);
lean_dec(x_24);
x_8 = x_3;
x_9 = x_23;
goto block_22;
}
else
{
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0);
if (x_9 == 0)
{
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_10);
lean_ctor_set(x_8, 0, x_1);
x_11 = x_8;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_10);
x_11 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__3);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_12);
lean_ctor_set(x_5, 0, x_11);
x_13 = x_5;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_12);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_MessageData_ofSyntax(x_7);
x_15 = l_Lean_indentD(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_1 = x_16;
x_2 = x_4;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__2(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Elab_Command_instInhabitedScope_default;
x_8 = l_List_head_x21___redArg(x_7, x_6);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = l_Lean_Elab_pp_macroStack;
x_11 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__2(x_9, x_10);
lean_dec_ref(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_30; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_14, 0);
lean_dec(x_31);
x_16 = x_14;
x_17 = x_30;
goto block_29;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_18);
lean_ctor_set(x_16, 0, x_1);
x_19 = x_16;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_18);
x_19 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___closed__2);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_MessageData_ofSyntax(x_15);
x_23 = l_Lean_indentD(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3(x_24, x_2);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__4(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__3);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__4);
x_3 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Command_instInhabitedScope_default;
x_9 = l_List_head_x21___redArg(x_8, x_7);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__2);
x_12 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__5);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_10);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg(x_1, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_7);
x_10 = l_Lean_Elab_getBetterRef(x_6, x_7);
lean_dec(x_6);
x_11 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg(x_9, x_7, x_3);
x_12 = lean_ctor_get(x_11, 0);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
x_13 = x_11;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_12);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_5, 0);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
x_22 = x_5;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_5);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__1, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__1_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__1);
x_6 = 0;
x_7 = l_Lean_MessageData_ofConstName(x_1, x_6);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0___redArg(x_10, x_2, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_15; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
x_5 = x_1;
x_6 = x_15;
goto block_14;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__2);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_7);
lean_ctor_set(x_5, 0, x_2);
x_8 = x_5;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_7);
x_8 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_MessageData_ofName(x_3);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_1 = x_4;
x_2 = x_10;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__6));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__2, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__2_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_16; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
x_5 = x_1;
x_6 = x_16;
goto block_15;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__4, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__4_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__4);
x_8 = l_Lean_MessageData_ofName(x_3);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_8);
lean_ctor_set(x_5, 0, x_7);
x_9 = x_5;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
x_9 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg(x_4, x_9);
x_11 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__7, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__7_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__7);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_get_reducibility_status(x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getReducibilityStatus___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getReducibilityStatus___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_spec__0___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getReducibilityStatus___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__5));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__8));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__11));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__14));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__17));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__21));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__22, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__22_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__22);
x_2 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__25));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__28(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__27));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__30(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__29));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__33(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__32));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__34(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__33, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__33_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__33);
x_2 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__31));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__36(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__35));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__37(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__36, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__36_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__36);
x_2 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__31));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__39(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__38));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__40(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__39, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__39_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__39);
x_2 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__31));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_47; lean_object* x_48; lean_object* x_54; lean_object* x_55; lean_object* x_61; lean_object* x_62; lean_object* x_75; lean_object* x_76; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_100; uint8_t x_101; 
lean_inc(x_2);
x_84 = l_Lean_getReducibilityStatus___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_spec__0___redArg(x_2, x_8);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_100 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__31));
x_101 = lean_unbox(x_85);
lean_dec(x_85);
switch (x_101) {
case 0:
{
lean_object* x_102; 
x_102 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__34, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__34_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__34);
x_86 = x_102;
x_87 = x_8;
goto block_99;
}
case 1:
{
x_86 = x_100;
x_87 = x_8;
goto block_99;
}
case 2:
{
lean_object* x_103; 
x_103 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__37, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__37_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__37);
x_86 = x_103;
x_87 = x_8;
goto block_99;
}
default: 
{
lean_object* x_104; 
x_104 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__40, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__40_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__40);
x_86 = x_104;
x_87 = x_8;
goto block_99;
}
}
block_28:
{
if (x_6 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec(x_3);
x_12 = l_Lean_stringToMessageData(x_1);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = l_Lean_stringToMessageData(x_1);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_MessageData_ofName(x_10);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_MessageData_ofExpr(x_4);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
block_37:
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_st_ref_get(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
lean_dec(x_32);
x_34 = l_Lean_isMarkedMeta(x_33, x_2);
if (x_34 == 0)
{
x_10 = x_29;
x_11 = x_30;
goto block_28;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
x_10 = x_29;
x_11 = x_36;
goto block_28;
}
}
block_46:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_st_ref_get(x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_42);
lean_dec(x_41);
lean_inc(x_2);
x_43 = l_Lean_isProtected(x_42, x_2);
if (x_43 == 0)
{
x_29 = x_38;
x_30 = x_39;
x_31 = x_40;
goto block_37;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_44);
x_29 = x_38;
x_30 = x_45;
x_31 = x_40;
goto block_37;
}
}
block_53:
{
lean_object* x_49; 
lean_inc(x_2);
x_49 = lean_private_to_user_name(x_2);
if (lean_obj_tag(x_49) == 0)
{
lean_inc(x_2);
x_38 = x_2;
x_39 = x_47;
x_40 = x_48;
goto block_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
x_38 = x_50;
x_39 = x_52;
x_40 = x_48;
goto block_46;
}
}
block_60:
{
switch (x_5) {
case 0:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__15, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__15_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__15);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_47 = x_57;
x_48 = x_55;
goto block_53;
}
case 1:
{
x_47 = x_54;
x_48 = x_55;
goto block_53;
}
default: 
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__18, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__18_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__18);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
x_47 = x_59;
x_48 = x_55;
goto block_53;
}
}
}
block_74:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19);
x_64 = lean_array_get_size(x_61);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_dec_eq(x_64, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__23, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__23_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__23);
x_68 = lean_array_to_list(x_61);
x_69 = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__2);
x_70 = l_Lean_MessageData_joinSep(x_68, x_69);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__26, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__26_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__26);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_54 = x_73;
x_55 = x_62;
goto block_60;
}
else
{
lean_dec_ref(x_61);
x_54 = x_63;
x_55 = x_62;
goto block_60;
}
}
block_83:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_st_ref_get(x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc_ref(x_78);
lean_dec(x_77);
x_79 = l_Lean_defeqAttr;
lean_inc(x_2);
x_80 = l_Lean_TagAttribute_hasTag(x_79, x_78, x_2);
if (x_80 == 0)
{
x_61 = x_75;
x_62 = x_76;
goto block_74;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__28, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__28_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__28);
x_82 = lean_array_push(x_75, x_81);
x_61 = x_82;
x_62 = x_76;
goto block_74;
}
}
block_99:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_st_ref_get(x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc_ref(x_89);
lean_dec(x_88);
x_90 = l_Lean_Environment_header(x_89);
x_91 = lean_ctor_get_uint8(x_90, sizeof(void*)*7 + 4);
lean_dec_ref(x_90);
if (x_91 == 0)
{
lean_dec_ref(x_89);
x_75 = x_86;
x_76 = x_87;
goto block_83;
}
else
{
lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_92 = l_Lean_Environment_setExporting(x_89, x_91);
x_93 = 0;
lean_inc(x_2);
x_94 = l_Lean_Environment_find_x3f(x_92, x_2, x_93);
if (lean_obj_tag(x_94) == 0)
{
x_75 = x_86;
x_76 = x_87;
goto block_83;
}
else
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
x_96 = l_Lean_ConstantInfo_isDefinition(x_95);
lean_dec(x_95);
if (x_96 == 0)
{
x_75 = x_86;
x_76 = x_87;
goto block_83;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__30, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__30_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__30);
x_98 = lean_array_push(x_86, x_97);
x_75 = x_98;
x_76 = x_87;
goto block_83;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_5);
x_11 = lean_unbox(x_6);
x_12 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkOmittedMsg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkOmittedMsg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkOmittedMsg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkOmittedMsg___closed__2, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkOmittedMsg___closed__2_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkOmittedMsg___closed__2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_MessageData_ofExpr(x_3);
return x_4;
}
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1___lam__0___closed__0));
x_7 = lean_string_dec_eq(x_5, x_6);
if (x_7 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
else
{
return x_1;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; uint8_t x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; uint8_t x_99; lean_object* x_100; uint8_t x_101; uint8_t x_102; lean_object* x_103; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_130; uint8_t x_143; 
x_125 = 2;
x_143 = l_Lean_instBEqMessageSeverity_beq(x_3, x_125);
if (x_143 == 0)
{
x_130 = x_143;
goto block_142;
}
else
{
uint8_t x_144; 
lean_inc_ref(x_2);
x_144 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_130 = x_144;
goto block_142;
}
block_70:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Command_getScope___redArg(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Elab_Command_getScope___redArg(x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_53; 
x_19 = lean_ctor_get(x_18, 0);
x_53 = !lean_is_exclusive(x_18);
if (x_53 == 0)
{
x_20 = x_18;
x_21 = x_53;
goto block_52;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_51; 
x_22 = lean_st_ref_take(x_15);
x_23 = lean_ctor_get(x_17, 2);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_19, 3);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_ctor_get(x_22, 2);
x_28 = lean_ctor_get(x_22, 3);
x_29 = lean_ctor_get(x_22, 4);
x_30 = lean_ctor_get(x_22, 5);
x_31 = lean_ctor_get(x_22, 6);
x_32 = lean_ctor_get(x_22, 7);
x_33 = lean_ctor_get(x_22, 8);
x_34 = lean_ctor_get(x_22, 9);
x_35 = lean_ctor_get(x_22, 10);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
x_36 = x_22;
x_37 = x_51;
goto block_50;
}
else
{
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_22);
x_36 = lean_box(0);
x_37 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_24);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_12);
x_40 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_40, 0, x_9);
lean_ctor_set(x_40, 1, x_10);
lean_ctor_set(x_40, 2, x_8);
lean_ctor_set(x_40, 3, x_11);
lean_ctor_set(x_40, 4, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*5, x_14);
lean_ctor_set_uint8(x_40, sizeof(void*)*5 + 1, x_13);
lean_ctor_set_uint8(x_40, sizeof(void*)*5 + 2, x_4);
x_41 = l_Lean_MessageLog_add(x_40, x_26);
if (x_37 == 0)
{
lean_ctor_set(x_36, 1, x_41);
x_42 = x_36;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_49, 0, x_25);
lean_ctor_set(x_49, 1, x_41);
lean_ctor_set(x_49, 2, x_27);
lean_ctor_set(x_49, 3, x_28);
lean_ctor_set(x_49, 4, x_29);
lean_ctor_set(x_49, 5, x_30);
lean_ctor_set(x_49, 6, x_31);
lean_ctor_set(x_49, 7, x_32);
lean_ctor_set(x_49, 8, x_33);
lean_ctor_set(x_49, 9, x_34);
lean_ctor_set(x_49, 10, x_35);
x_42 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_st_ref_set(x_15, x_42);
x_44 = lean_box(0);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_44);
x_45 = x_20;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec(x_17);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_54 = lean_ctor_get(x_18, 0);
x_61 = !lean_is_exclusive(x_18);
if (x_61 == 0)
{
x_55 = x_18;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_18);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_62 = lean_ctor_get(x_16, 0);
x_69 = !lean_is_exclusive(x_16);
if (x_69 == 0)
{
x_63 = x_16;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_16);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
block_98:
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_97; 
x_76 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_77);
x_78 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
lean_dec_ref(x_5);
x_79 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_80 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg(x_79, x_6);
x_81 = lean_ctor_get(x_80, 0);
x_97 = !lean_is_exclusive(x_80);
if (x_97 == 0)
{
x_82 = x_80;
x_83 = x_97;
goto block_96;
}
else
{
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_box(0);
x_83 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_inc_ref(x_77);
x_84 = l_Lean_FileMap_toPosition(x_77, x_72);
lean_dec(x_72);
x_85 = l_Lean_FileMap_toPosition(x_77, x_75);
lean_dec(x_75);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__0));
if (x_78 == 0)
{
lean_del_object(x_82);
x_8 = x_86;
x_9 = x_76;
x_10 = x_84;
x_11 = x_87;
x_12 = x_81;
x_13 = x_73;
x_14 = x_74;
x_15 = x_6;
goto block_70;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_box(x_71);
x_89 = lean_box(x_78);
x_90 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(x_90, 0, x_88);
lean_closure_set(x_90, 1, x_89);
lean_inc(x_81);
x_91 = l_Lean_MessageData_hasTag(x_90, x_81);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_86);
lean_dec_ref(x_84);
lean_dec(x_81);
lean_dec_ref(x_76);
x_92 = lean_box(0);
if (x_83 == 0)
{
lean_ctor_set(x_82, 0, x_92);
x_93 = x_82;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_92);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
else
{
lean_del_object(x_82);
x_8 = x_86;
x_9 = x_76;
x_10 = x_84;
x_11 = x_87;
x_12 = x_81;
x_13 = x_73;
x_14 = x_74;
x_15 = x_6;
goto block_70;
}
}
}
}
block_106:
{
lean_object* x_104; 
x_104 = l_Lean_Syntax_getTailPos_x3f(x_100, x_102);
lean_dec(x_100);
if (lean_obj_tag(x_104) == 0)
{
lean_inc(x_103);
x_71 = x_99;
x_72 = x_103;
x_73 = x_101;
x_74 = x_102;
x_75 = x_103;
goto block_98;
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_71 = x_99;
x_72 = x_103;
x_73 = x_101;
x_74 = x_102;
x_75 = x_105;
goto block_98;
}
}
block_124:
{
lean_object* x_110; 
x_110 = l_Lean_Elab_Command_getRef___redArg(x_5);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = l_Lean_replaceRef(x_1, x_111);
lean_dec(x_111);
x_113 = l_Lean_Syntax_getPos_x3f(x_112, x_108);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
x_114 = lean_unsigned_to_nat(0u);
x_99 = x_107;
x_100 = x_112;
x_101 = x_109;
x_102 = x_108;
x_103 = x_114;
goto block_106;
}
else
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
lean_dec_ref(x_113);
x_99 = x_107;
x_100 = x_112;
x_101 = x_109;
x_102 = x_108;
x_103 = x_115;
goto block_106;
}
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_123; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_116 = lean_ctor_get(x_110, 0);
x_123 = !lean_is_exclusive(x_110);
if (x_123 == 0)
{
x_117 = x_110;
x_118 = x_123;
goto block_122;
}
else
{
lean_inc(x_116);
lean_dec(x_110);
x_117 = lean_box(0);
x_118 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_119; 
if (x_118 == 0)
{
x_119 = x_117;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_116);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
}
block_129:
{
if (x_128 == 0)
{
x_107 = x_126;
x_108 = x_127;
x_109 = x_3;
goto block_124;
}
else
{
x_107 = x_126;
x_108 = x_127;
x_109 = x_125;
goto block_124;
}
}
block_142:
{
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; uint8_t x_137; 
x_131 = lean_st_ref_get(x_6);
x_132 = lean_ctor_get(x_131, 2);
lean_inc(x_132);
lean_dec(x_131);
x_133 = l_Lean_Elab_Command_instInhabitedScope_default;
x_134 = l_List_head_x21___redArg(x_133, x_132);
lean_dec(x_132);
x_135 = lean_ctor_get(x_134, 1);
lean_inc_ref(x_135);
lean_dec(x_134);
x_136 = 1;
x_137 = l_Lean_instBEqMessageSeverity_beq(x_3, x_136);
if (x_137 == 0)
{
lean_dec_ref(x_135);
x_126 = x_130;
x_127 = x_130;
x_128 = x_137;
goto block_129;
}
else
{
lean_object* x_138; uint8_t x_139; 
x_138 = l_Lean_warningAsError;
x_139 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__2(x_135, x_138);
lean_dec_ref(x_135);
x_126 = x_130;
x_127 = x_130;
x_128 = x_139;
goto block_129;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
x_9 = lean_unbox(x_4);
x_10 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1(x_1, x_2, x_8, x_9, x_5, x_6);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Command_getRef___redArg(x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1(x_8, x_1, x_2, x_3, x_4, x_5);
lean_dec(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_17; 
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_7, 0);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
x_11 = x_7;
x_12 = x_17;
goto block_16;
}
else
{
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_box(0);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_12 == 0)
{
x_13 = x_11;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_10);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_2);
x_8 = lean_unbox(x_3);
x_9 = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = 0;
x_6 = 0;
x_7 = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(x_1, x_2, x_3, x_4, x_5, x_9, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0(x_11, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
lean_dec_ref(x_6);
x_13 = lean_ctor_get(x_10, 0);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
x_14 = x_10;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_1, x_2, x_3, x_4, x_9, x_6, x_7);
lean_dec(x_7);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_1 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(x_2, x_3, x_4, x_5, x_7, x_11, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkOmittedMsg(x_6);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0(x_19, x_8, x_9);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec_ref(x_8);
lean_dec(x_6);
x_21 = lean_ctor_get(x_12, 0);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
x_22 = x_12;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_6);
x_29 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_2, x_3, x_4, x_5, x_7, x_8, x_9);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox(x_7);
x_13 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(x_11, x_2, x_3, x_4, x_5, x_6, x_12, x_8, x_9);
lean_dec(x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___closed__0));
x_8 = 1;
x_9 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_7, x_1, x_2, x_3, x_8, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_Lean_Name_isAnonymous(x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_6);
x_10 = l_Lean_Environment_setExporting(x_6, x_7);
lean_inc(x_2);
lean_inc_ref(x_10);
x_11 = l_Lean_Environment_contains(x_10, x_2, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_10);
lean_dec_ref(x_6);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__2);
x_14 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__5);
x_15 = l_Lean_Options_empty;
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
lean_inc(x_2);
x_17 = l_Lean_MessageData_ofConstName(x_2, x_7);
x_18 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Environment_getModuleIdxFor_x3f(x_6, x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_20 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_MessageData_note(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_62; 
x_27 = lean_ctor_get(x_19, 0);
x_62 = !lean_is_exclusive(x_19);
if (x_62 == 0)
{
x_28 = x_19;
x_29 = x_62;
goto block_61;
}
else
{
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_box(0);
x_29 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_box(0);
x_31 = l_Lean_Environment_header(x_6);
lean_dec_ref(x_6);
x_32 = l_Lean_EnvironmentHeader_moduleNames(x_31);
x_33 = lean_array_get(x_30, x_32, x_27);
lean_dec(x_27);
lean_dec_ref(x_32);
x_34 = l_Lean_isPrivateName(x_2);
lean_dec(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_18);
x_37 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_MessageData_ofName(x_33);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_MessageData_note(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_44);
x_45 = x_28;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_18);
x_50 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_MessageData_ofName(x_33);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_MessageData_note(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_57);
x_58 = x_28;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_57);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
}
}
else
{
lean_object* x_63; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_1);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_16; 
x_6 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(x_1, x_2, x_4);
x_7 = lean_ctor_get(x_6, 0);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
x_8 = x_6;
x_9 = x_16;
goto block_15;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_unknownIdentifierMessageTag;
x_11 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_11);
x_12 = x_8;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_getRef___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_26; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_ctor_get(x_3, 3);
x_12 = lean_ctor_get(x_3, 4);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_ctor_get(x_3, 6);
x_15 = lean_ctor_get(x_3, 8);
x_16 = lean_ctor_get(x_3, 9);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_3, 7);
lean_dec(x_27);
x_18 = x_3;
x_19 = x_26;
goto block_25;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
if (x_19 == 0)
{
lean_ctor_set(x_18, 7, x_20);
x_21 = x_18;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_9);
lean_ctor_set(x_24, 2, x_10);
lean_ctor_set(x_24, 3, x_11);
lean_ctor_set(x_24, 4, x_12);
lean_ctor_set(x_24, 5, x_13);
lean_ctor_set(x_24, 6, x_14);
lean_ctor_set(x_24, 7, x_20);
lean_ctor_set(x_24, 8, x_15);
lean_ctor_set(x_24, 9, x_16);
lean_ctor_set_uint8(x_24, sizeof(void*)*10, x_17);
x_21 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_22; 
x_22 = l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0___redArg(x_2, x_21, x_4);
return x_22;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_28 = lean_ctor_get(x_6, 0);
x_35 = !lean_is_exclusive(x_6);
if (x_35 == 0)
{
x_29 = x_6;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_6);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4(x_2, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(x_1, x_8, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg___closed__1);
x_7 = 0;
lean_inc(x_2);
x_8 = l_Lean_MessageData_ofConstName(x_2, x_7);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3___redArg(x_1, x_11, x_2, x_3, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg(x_6, x_1, x_2, x_3);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_15; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 0);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
x_9 = x_5;
x_10 = x_15;
goto block_14;
}
else
{
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_11; 
if (x_10 == 0)
{
x_11 = x_9;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = 0;
lean_inc(x_1);
x_8 = l_Lean_Environment_find_x3f(x_6, x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0___redArg(x_1, x_2, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_17; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_11 = x_8;
x_12 = x_17;
goto block_16;
}
else
{
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_12 == 0)
{
lean_ctor_set_tag(x_11, 0);
x_13 = x_11;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_10);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___redArg___closed__0));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec_ref(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_34; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
x_9 = x_1;
x_10 = x_34;
goto block_33;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_11; 
lean_inc_ref(x_3);
lean_inc(x_7);
x_11 = l_Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0(x_7, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0);
if (x_10 == 0)
{
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_13);
lean_ctor_set(x_9, 0, x_2);
x_14 = x_9;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_13);
x_14 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = l_Lean_MessageData_ofName(x_7);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___redArg___closed__1);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_ConstantInfo_type(x_12);
lean_dec(x_12);
x_20 = l_Lean_MessageData_ofExpr(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_1 = x_8;
x_2 = x_21;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_del_object(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_25 = lean_ctor_get(x_11, 0);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
x_26 = x_11;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__5));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_10 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__0));
x_11 = 1;
if (x_6 == 0)
{
uint8_t x_46; 
x_46 = 1;
x_12 = x_46;
goto block_45;
}
else
{
uint8_t x_47; 
x_47 = 0;
x_12 = x_47;
goto block_45;
}
block_45:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(x_10, x_1, x_2, x_4, x_12, x_11, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Nat_reprFast(x_3);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_MessageData_ofFormat(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
x_24 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__6, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__6_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__6);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_inc_ref(x_7);
x_26 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___redArg(x_5, x_25, x_7, x_8);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0(x_27, x_7, x_8);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec_ref(x_7);
x_29 = lean_ctor_get(x_26, 0);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
x_30 = x_26;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_37 = lean_ctor_get(x_13, 0);
x_44 = !lean_is_exclusive(x_13);
if (x_44 == 0)
{
x_38 = x_13;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_13);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
x_11 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___redArg(x_2, x_3, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_32; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
x_7 = x_1;
x_8 = x_32;
goto block_31;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_11);
lean_dec(x_5);
x_12 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 7);
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_2);
x_13 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_12);
x_13 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__1);
x_15 = l_Lean_MessageData_ofName(x_9);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__3);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Nat_reprFast(x_10);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_MessageData_ofFormat(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___closed__5);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_MessageData_ofExpr(x_11);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_26);
x_1 = x_6;
x_2 = x_27;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__9));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__11));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 6);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
lean_dec_ref(x_1);
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_26);
lean_dec_ref(x_5);
x_27 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__3));
x_28 = 1;
if (x_12 == 0)
{
uint8_t x_73; 
x_73 = 1;
x_29 = x_73;
goto block_72;
}
else
{
uint8_t x_74; 
x_74 = 0;
x_29 = x_74;
goto block_72;
}
block_23:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_13);
x_18 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__2, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__2_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__2);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg(x_10, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0(x_21, x_15, x_16);
return x_22;
}
block_72:
{
lean_object* x_30; 
x_30 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(x_27, x_24, x_25, x_26, x_29, x_28, x_2, x_3);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__4, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__4_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__4);
x_35 = l_Nat_reprFast(x_6);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_MessageData_ofFormat(x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
x_41 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__6, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__6_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__6);
x_42 = l_Nat_reprFast(x_7);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l_Lean_MessageData_ofFormat(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_32);
x_48 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__8, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__8_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__8);
x_49 = l_Nat_reprFast(x_8);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_MessageData_ofFormat(x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_32);
x_55 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__10, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__10_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__10);
x_56 = l_Nat_reprFast(x_9);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Lean_MessageData_ofFormat(x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_59);
if (x_11 == 0)
{
x_13 = x_32;
x_14 = x_60;
x_15 = x_2;
x_16 = x_3;
goto block_23;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_32);
x_62 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__12, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__12_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__12);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_13 = x_32;
x_14 = x_63;
x_15 = x_2;
x_16 = x_3;
goto block_23;
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_64 = lean_ctor_get(x_30, 0);
x_71 = !lean_is_exclusive(x_30);
if (x_71 == 0)
{
x_65 = x_30;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_30);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___redArg(x_2, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_8 = lean_st_ref_get(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
lean_inc(x_1);
lean_inc_ref(x_9);
x_10 = l_Lean_getStructureParentInfo(x_9, x_1);
x_11 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__0___closed__0));
x_12 = lean_array_size(x_10);
x_13 = 0;
lean_inc(x_2);
lean_inc_ref(x_9);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__0(x_9, x_2, x_10, x_12, x_13, x_11, x_3, x_4, x_5, x_6);
lean_dec_ref(x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_44; 
x_15 = lean_ctor_get(x_14, 0);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
x_16 = x_14;
x_17 = x_44;
goto block_43;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_41; 
x_18 = lean_ctor_get(x_15, 0);
x_41 = !lean_is_exclusive(x_15);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_15, 1);
lean_dec(x_42);
x_19 = x_15;
x_20 = x_41;
goto block_40;
}
else
{
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = x_41;
goto block_40;
}
block_40:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_21; 
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Lean_getFieldInfo_x3f(x_9, x_1, x_2);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; 
lean_del_object(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_22);
x_23 = x_16;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_21);
lean_del_object(x_16);
x_26 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__1, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__1_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__1);
x_27 = l_Lean_MessageData_ofName(x_2);
if (x_20 == 0)
{
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_27);
lean_ctor_set(x_19, 0, x_26);
x_28 = x_19;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_27);
x_28 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__3, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__3_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___closed__3);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_MessageData_ofName(x_1);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1___redArg(x_32, x_3, x_4, x_5, x_6);
return x_33;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_del_object(x_19);
lean_dec_ref(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_ctor_get(x_18, 0);
lean_inc(x_36);
lean_dec_ref(x_18);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_36);
x_37 = x_16;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_dec_ref(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_ctor_get(x_14, 0);
x_52 = !lean_is_exclusive(x_14);
if (x_52 == 0)
{
x_46 = x_14;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_14);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_6);
x_14 = lean_array_uget_borrowed(x_3, x_5);
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_box(0);
lean_inc(x_15);
lean_inc_ref(x_1);
x_17 = l_Lean_findField_x3f(x_1, x_15, x_2);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; size_t x_19; size_t x_20; 
x_18 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__0___closed__0));
x_19 = 1;
x_20 = lean_usize_add(x_5, x_19);
x_5 = x_20;
x_6 = x_18;
goto _start;
}
else
{
lean_object* x_22; uint8_t x_23; uint8_t x_46; 
lean_dec_ref(x_1);
x_46 = !lean_is_exclusive(x_17);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_17, 0);
lean_dec(x_47);
x_22 = x_17;
x_23 = x_46;
goto block_45;
}
else
{
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_24; 
lean_inc(x_15);
x_24 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin(x_15, x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_36; 
x_25 = lean_ctor_get(x_24, 0);
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
x_26 = x_24;
x_27 = x_36;
goto block_35;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_28; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_25);
x_28 = x_22;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_25);
x_28 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_16);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_29);
x_30 = x_26;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_del_object(x_22);
x_37 = lean_ctor_get(x_24, 0);
x_44 = !lean_is_exclusive(x_24);
if (x_44 == 0)
{
x_38 = x_24;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_24);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__0(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_19; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
x_6 = x_1;
x_7 = x_19;
goto block_18;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_8, 0, x_3);
lean_inc(x_2);
x_9 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_2, x_8, x_4);
if (x_5 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__3___closed__0));
x_11 = l_Lean_Name_isPrefixOf(x_10, x_2);
lean_dec(x_2);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_9);
x_12 = x_6;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_9);
x_12 = x_14;
goto block_13;
}
block_13:
{
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
else
{
lean_object* x_15; 
lean_dec(x_2);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_9);
x_15 = x_6;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_5);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Options_set___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__3(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_dec(x_7);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__4(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_5);
x_12 = 0;
x_13 = lean_box(0);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), x_12, x_13, x_1, x_11, x_3, x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_15 = lean_ctor_get(x_14, 0);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
x_16 = x_14;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9___redArg(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__12___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__12___closed__0, &l_panic___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__12___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__12___closed__0);
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_panic___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_Elab_pp_macroStack;
x_7 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__2(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_26; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_10, 0);
lean_dec(x_27);
x_12 = x_10;
x_13 = x_26;
goto block_25;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_14);
lean_ctor_set(x_12, 0, x_1);
x_15 = x_12;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_14);
x_15 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1___redArg___closed__2);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_MessageData_ofSyntax(x_11);
x_19 = l_Lean_indentD(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3(x_20, x_2);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0_spec__5___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1_spec__1(x_1, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
lean_inc(x_12);
x_13 = l_Lean_Elab_getBetterRef(x_9, x_12);
x_14 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0_spec__5___redArg(x_11, x_12, x_6);
x_15 = lean_ctor_get(x_14, 0);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
x_16 = x_14;
x_17 = x_23;
goto block_22;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_15);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = l_Lean_stringToMessageData(x_9);
x_11 = l_Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0___redArg(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
lean_dec_ref(x_2);
x_12 = lean_ctor_get(x_1, 0);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
x_13 = x_1;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_58; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_58 = !lean_is_exclusive(x_1);
if (x_58 == 0)
{
x_13 = x_1;
x_14 = x_58;
goto block_57;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = x_58;
goto block_57;
}
block_57:
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_11, x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_del_object(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_array_fget_borrowed(x_10, x_11);
x_18 = l_Lean_Expr_fvarId_x21(x_17);
lean_inc_ref(x_5);
x_19 = l_Lean_FVarId_getDecl___redArg(x_18, x_5, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_11, x_21);
lean_dec(x_11);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_22);
x_23 = x_13;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_10);
lean_ctor_set(x_48, 1, x_22);
lean_ctor_set(x_48, 2, x_12);
x_23 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_LocalDecl_type(x_20);
x_25 = l_Lean_Expr_getAutoParamTactic_x3f(x_24);
lean_dec_ref(x_24);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
if (lean_obj_tag(x_26) == 4)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_st_ref_get(x_8);
x_29 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_7, 2);
x_31 = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(x_29, x_30, x_27);
lean_inc_ref(x_3);
x_32 = l_Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0___redArg(x_31, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Lean_LocalDecl_userName(x_20);
lean_dec(x_20);
x_35 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_34, x_33, x_2);
x_1 = x_23;
x_2 = x_35;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec_ref(x_23);
lean_dec(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_37 = lean_ctor_get(x_32, 0);
x_44 = !lean_is_exclusive(x_32);
if (x_44 == 0)
{
x_38 = x_32;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_dec(x_26);
lean_dec(x_20);
x_1 = x_23;
goto _start;
}
}
else
{
lean_dec(x_25);
lean_dec(x_20);
x_1 = x_23;
goto _start;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_del_object(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_49 = lean_ctor_get(x_19, 0);
x_56 = !lean_is_exclusive(x_19);
if (x_56 == 0)
{
x_50 = x_19;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_19);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_box(1);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_2);
x_19 = lean_nat_dec_le(x_1, x_17);
if (x_19 == 0)
{
x_12 = x_1;
x_13 = x_18;
goto block_16;
}
else
{
lean_dec(x_1);
x_12 = x_17;
x_13 = x_18;
goto block_16;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Array_toSubarray___redArg(x_2, x_12, x_13);
x_15 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__1___redArg(x_14, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
x_9 = l_Lean_PrettyPrinter_delabCore___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_36; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_10, 1);
x_36 = !lean_is_exclusive(x_10);
if (x_36 == 0)
{
x_13 = x_10;
x_14 = x_36;
goto block_35;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_15; 
x_15 = l_Lean_PrettyPrinter_ppTerm(x_11, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_26; 
x_16 = lean_ctor_get(x_15, 0);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
x_17 = x_15;
x_18 = x_26;
goto block_25;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_19; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_16);
x_19 = x_13;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_12);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_19);
x_20 = x_17;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_del_object(x_13);
lean_dec(x_12);
x_27 = lean_ctor_get(x_15, 0);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
x_28 = x_15;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_7);
lean_dec_ref(x_6);
x_37 = lean_ctor_get(x_9, 0);
x_44 = !lean_is_exclusive(x_9);
if (x_44 == 0)
{
x_38 = x_9;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_9);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_1, x_2);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 6)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_17);
lean_dec_ref(x_3);
lean_inc_ref(x_1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_15);
x_18 = lean_apply_8(x_1, x_15, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_60; 
x_19 = lean_ctor_get(x_18, 0);
x_60 = !lean_is_exclusive(x_18);
if (x_60 == 0)
{
x_20 = x_18;
x_21 = x_60;
goto block_59;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_60;
goto block_59;
}
block_59:
{
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_22; lean_object* x_23; 
lean_del_object(x_20);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec_ref(x_19);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_22);
x_23 = lean_infer_type(x_22, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_25 = l_Lean_Meta_isExprDefEq(x_24, x_16, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_38; 
x_26 = lean_ctor_get(x_25, 0);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
x_27 = x_25;
x_28 = x_38;
goto block_37;
}
else
{
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = x_38;
goto block_37;
}
block_37:
{
uint8_t x_29; 
x_29 = lean_unbox(x_26);
lean_dec(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_22);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_30 = lean_box(0);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_30);
x_31 = x_27;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_del_object(x_27);
x_34 = l_Lean_NameSet_insert(x_2, x_15);
x_35 = lean_expr_instantiate1(x_17, x_22);
lean_dec(x_22);
lean_dec_ref(x_17);
x_2 = x_34;
x_3 = x_35;
goto _start;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_22);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_39 = lean_ctor_get(x_25, 0);
x_46 = !lean_is_exclusive(x_25);
if (x_46 == 0)
{
x_40 = x_25;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_25);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec(x_22);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_47 = lean_ctor_get(x_23, 0);
x_54 = !lean_is_exclusive(x_23);
if (x_54 == 0)
{
x_48 = x_23;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_23);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_55 = lean_box(0);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_55);
x_56 = x_20;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_55);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_61 = lean_ctor_get(x_18, 0);
x_68 = !lean_is_exclusive(x_18);
if (x_68 == 0)
{
x_62 = x_18;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_18);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
else
{
lean_object* x_69; uint8_t x_70; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
lean_inc_ref(x_3);
x_69 = l_Lean_Expr_cleanupAnnotations(x_3);
x_70 = l_Lean_Expr_isApp(x_69);
if (x_70 == 0)
{
lean_dec_ref(x_69);
goto block_14;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_69, 1);
lean_inc_ref(x_71);
x_72 = l_Lean_Expr_appFnCleanup___redArg(x_69);
x_73 = l_Lean_Expr_isApp(x_72);
if (x_73 == 0)
{
lean_dec_ref(x_72);
lean_dec_ref(x_71);
goto block_14;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = l_Lean_Expr_appFnCleanup___redArg(x_72);
x_75 = ((lean_object*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__18___closed__1));
x_76 = l_Lean_Expr_isConstOf(x_74, x_75);
lean_dec_ref(x_74);
if (x_76 == 0)
{
lean_dec_ref(x_71);
goto block_14;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_3);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_2);
lean_ctor_set(x_77, 1, x_71);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
}
block_14:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__19___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_27; 
x_8 = lean_ctor_get(x_4, 1);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_4, 0);
lean_dec(x_28);
x_9 = x_4;
x_10 = x_27;
goto block_26;
}
else
{
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = x_27;
goto block_26;
}
block_26:
{
if (lean_obj_tag(x_8) == 6)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc_ref(x_11);
lean_dec_ref(x_8);
x_12 = lean_box(0);
x_13 = lean_array_uget_borrowed(x_1, x_3);
x_14 = lean_expr_instantiate1(x_11, x_13);
lean_dec_ref(x_11);
if (x_10 == 0)
{
lean_ctor_set(x_9, 1, x_14);
lean_ctor_set(x_9, 0, x_12);
x_15 = x_9;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_14);
x_15 = x_20;
goto block_19;
}
block_19:
{
size_t x_16; size_t x_17; 
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_4 = x_15;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__19___redArg___closed__0));
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_21);
x_22 = x_9;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_8);
x_22 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__19___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__19___redArg(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_102; 
x_9 = lean_obj_once(&l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__0, &l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__0_once, _init_l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__0);
x_10 = l_ReaderT_instMonad___redArg(x_9);
x_11 = lean_ctor_get(x_10, 0);
x_102 = !lean_is_exclusive(x_10);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_10, 1);
lean_dec(x_103);
x_12 = x_10;
x_13 = x_102;
goto block_101;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_99; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_ctor_get(x_11, 4);
x_99 = !lean_is_exclusive(x_11);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_11, 1);
lean_dec(x_100);
x_18 = x_11;
x_19 = x_99;
goto block_98;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = ((lean_object*)(l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__1));
x_21 = ((lean_object*)(l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__2));
lean_inc_ref(x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_17);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_16);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_15);
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_25);
lean_ctor_set(x_18, 3, x_26);
lean_ctor_set(x_18, 2, x_27);
lean_ctor_set(x_18, 1, x_20);
lean_ctor_set(x_18, 0, x_24);
x_28 = x_18;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_97, 0, x_24);
lean_ctor_set(x_97, 1, x_20);
lean_ctor_set(x_97, 2, x_27);
lean_ctor_set(x_97, 3, x_26);
lean_ctor_set(x_97, 4, x_25);
x_28 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_29; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_21);
lean_ctor_set(x_12, 0, x_28);
x_29 = x_12;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_28);
lean_ctor_set(x_95, 1, x_21);
x_29 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_92; 
x_30 = l_ReaderT_instMonad___redArg(x_29);
x_31 = lean_ctor_get(x_30, 0);
x_92 = !lean_is_exclusive(x_30);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_30, 1);
lean_dec(x_93);
x_32 = x_30;
x_33 = x_92;
goto block_91;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_89; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 2);
x_36 = lean_ctor_get(x_31, 3);
x_37 = lean_ctor_get(x_31, 4);
x_89 = !lean_is_exclusive(x_31);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_31, 1);
lean_dec(x_90);
x_38 = x_31;
x_39 = x_89;
goto block_88;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = ((lean_object*)(l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__3));
x_41 = ((lean_object*)(l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__4));
lean_inc_ref(x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_34);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_45, 0, x_37);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_46, 0, x_36);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_47, 0, x_35);
if (x_39 == 0)
{
lean_ctor_set(x_38, 4, x_45);
lean_ctor_set(x_38, 3, x_46);
lean_ctor_set(x_38, 2, x_47);
lean_ctor_set(x_38, 1, x_40);
lean_ctor_set(x_38, 0, x_44);
x_48 = x_38;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_44);
lean_ctor_set(x_87, 1, x_40);
lean_ctor_set(x_87, 2, x_47);
lean_ctor_set(x_87, 3, x_46);
lean_ctor_set(x_87, 4, x_45);
x_48 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_49; 
if (x_33 == 0)
{
lean_ctor_set(x_32, 1, x_41);
lean_ctor_set(x_32, 0, x_48);
x_49 = x_32;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_48);
lean_ctor_set(x_85, 1, x_41);
x_49 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_82; 
x_50 = l_ReaderT_instMonad___redArg(x_49);
x_51 = lean_ctor_get(x_50, 0);
x_82 = !lean_is_exclusive(x_50);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_50, 1);
lean_dec(x_83);
x_52 = x_50;
x_53 = x_82;
goto block_81;
}
else
{
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_79; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 2);
x_56 = lean_ctor_get(x_51, 3);
x_57 = lean_ctor_get(x_51, 4);
x_79 = !lean_is_exclusive(x_51);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_51, 1);
lean_dec(x_80);
x_58 = x_51;
x_59 = x_79;
goto block_78;
}
else
{
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_51);
x_58 = lean_box(0);
x_59 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = ((lean_object*)(l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__5));
x_61 = ((lean_object*)(l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___closed__6));
lean_inc_ref(x_54);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_62, 0, x_54);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_63, 0, x_54);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_65, 0, x_57);
x_66 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_66, 0, x_56);
x_67 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_67, 0, x_55);
if (x_59 == 0)
{
lean_ctor_set(x_58, 4, x_65);
lean_ctor_set(x_58, 3, x_66);
lean_ctor_set(x_58, 2, x_67);
lean_ctor_set(x_58, 1, x_60);
lean_ctor_set(x_58, 0, x_64);
x_68 = x_58;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_60);
lean_ctor_set(x_77, 2, x_67);
lean_ctor_set(x_77, 3, x_66);
lean_ctor_set(x_77, 4, x_65);
x_68 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_69; 
if (x_53 == 0)
{
lean_ctor_set(x_52, 1, x_61);
lean_ctor_set(x_52, 0, x_68);
x_69 = x_52;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_68);
lean_ctor_set(x_75, 1, x_61);
x_69 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_box(0);
x_71 = l_instInhabitedOfMonad___redArg(x_69, x_70);
x_72 = lean_panic_fn(x_71, x_1);
x_73 = lean_apply_7(x_72, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_73;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__17___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_expr_instantiate1(x_1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__17___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__17___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_37; 
x_37 = lean_usize_dec_lt(x_5, x_4);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_6);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_89; 
x_39 = lean_ctor_get(x_6, 1);
x_89 = !lean_is_exclusive(x_6);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_6, 0);
lean_dec(x_90);
x_40 = x_6;
x_41 = x_89;
goto block_88;
}
else
{
lean_inc(x_39);
lean_dec(x_6);
x_40 = lean_box(0);
x_41 = x_89;
goto block_88;
}
block_88:
{
if (lean_obj_tag(x_39) == 6)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_ctor_get(x_39, 2);
x_44 = lean_box(0);
x_45 = lean_nat_dec_eq(x_1, x_2);
x_46 = lean_array_uget_borrowed(x_3, x_5);
if (x_45 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_inc_ref(x_43);
lean_dec_ref(x_39);
lean_del_object(x_40);
x_47 = lean_box(0);
x_48 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__17___lam__0(x_43, x_46, x_44, x_47, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_43);
x_14 = x_48;
goto block_36;
}
else
{
lean_object* x_49; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_46);
x_49 = lean_infer_type(x_46, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_42);
x_51 = l_Lean_Meta_isExprDefEq(x_50, x_42, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_66; 
x_52 = lean_ctor_get(x_51, 0);
x_66 = !lean_is_exclusive(x_51);
if (x_66 == 0)
{
x_53 = x_51;
x_54 = x_66;
goto block_65;
}
else
{
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_box(0);
x_54 = x_66;
goto block_65;
}
block_65:
{
uint8_t x_55; 
x_55 = lean_unbox(x_52);
lean_dec(x_52);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_56 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__17___closed__0));
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_56);
x_57 = x_40;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_39);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_54 == 0)
{
lean_ctor_set(x_53, 0, x_57);
x_58 = x_53;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_57);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_inc_ref(x_43);
lean_del_object(x_53);
lean_dec_ref(x_39);
lean_del_object(x_40);
x_63 = lean_box(0);
x_64 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__17___lam__0(x_43, x_46, x_44, x_63, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_43);
x_14 = x_64;
goto block_36;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_74; 
lean_dec_ref(x_39);
lean_del_object(x_40);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_67 = lean_ctor_get(x_51, 0);
x_74 = !lean_is_exclusive(x_51);
if (x_74 == 0)
{
x_68 = x_51;
x_69 = x_74;
goto block_73;
}
else
{
lean_inc(x_67);
lean_dec(x_51);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_67);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_82; 
lean_dec_ref(x_39);
lean_del_object(x_40);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_75 = lean_ctor_get(x_49, 0);
x_82 = !lean_is_exclusive(x_49);
if (x_82 == 0)
{
x_76 = x_49;
x_77 = x_82;
goto block_81;
}
else
{
lean_inc(x_75);
lean_dec(x_49);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_75);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_83 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__19___redArg___closed__0));
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_83);
x_84 = x_40;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_39);
x_84 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
}
block_36:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_27; 
x_15 = lean_ctor_get(x_14, 0);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
x_16 = x_14;
x_17 = x_27;
goto block_26;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_27;
goto block_26;
}
block_26:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; size_t x_23; size_t x_24; 
lean_del_object(x_16);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec_ref(x_15);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
x_5 = x_24;
x_6 = x_22;
goto _start;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_28 = lean_ctor_get(x_14, 0);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
x_29 = x_14;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__17(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__55_spec__61___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_Lean_Name_isAnonymous(x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_6);
x_10 = l_Lean_Environment_setExporting(x_6, x_7);
lean_inc(x_2);
lean_inc_ref(x_10);
x_11 = l_Lean_Environment_contains(x_10, x_2, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_10);
lean_dec_ref(x_6);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__2);
x_14 = lean_unsigned_to_nat(32u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
lean_dec_ref(x_15);
x_16 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__5);
x_17 = l_Lean_Options_empty;
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_17);
lean_inc(x_2);
x_19 = l_Lean_MessageData_ofConstName(x_2, x_7);
x_20 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Environment_getModuleIdxFor_x3f(x_6, x_2);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_22 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_MessageData_note(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_64; 
x_29 = lean_ctor_get(x_21, 0);
x_64 = !lean_is_exclusive(x_21);
if (x_64 == 0)
{
x_30 = x_21;
x_31 = x_64;
goto block_63;
}
else
{
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_box(0);
x_31 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_box(0);
x_33 = l_Lean_Environment_header(x_6);
lean_dec_ref(x_6);
x_34 = l_Lean_EnvironmentHeader_moduleNames(x_33);
x_35 = lean_array_get(x_32, x_34, x_29);
lean_dec(x_29);
lean_dec_ref(x_34);
x_36 = l_Lean_isPrivateName(x_2);
lean_dec(x_2);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_20);
x_39 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_MessageData_ofName(x_35);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_MessageData_note(x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
if (x_31 == 0)
{
lean_ctor_set_tag(x_30, 0);
lean_ctor_set(x_30, 0, x_46);
x_47 = x_30;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_46);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_20);
x_52 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_MessageData_ofName(x_35);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_MessageData_note(x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_58);
if (x_31 == 0)
{
lean_ctor_set_tag(x_30, 0);
lean_ctor_set(x_30, 0, x_59);
x_60 = x_30;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_59);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
}
}
}
else
{
lean_object* x_65; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_1);
return x_65;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__55_spec__61___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__55_spec__61___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__55(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_20; 
x_10 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__55_spec__61___redArg(x_1, x_2, x_8);
x_11 = lean_ctor_get(x_10, 0);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
x_12 = x_10;
x_13 = x_20;
goto block_19;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_unknownIdentifierMessageTag;
x_15 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_15);
x_16 = x_12;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__55___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__55(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__56___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_34; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 2);
x_13 = lean_ctor_get(x_7, 3);
x_14 = lean_ctor_get(x_7, 4);
x_15 = lean_ctor_get(x_7, 5);
x_16 = lean_ctor_get(x_7, 6);
x_17 = lean_ctor_get(x_7, 7);
x_18 = lean_ctor_get(x_7, 8);
x_19 = lean_ctor_get(x_7, 9);
x_20 = lean_ctor_get(x_7, 10);
x_21 = lean_ctor_get(x_7, 11);
x_22 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_23 = lean_ctor_get(x_7, 12);
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_25 = lean_ctor_get(x_7, 13);
x_34 = !lean_is_exclusive(x_7);
if (x_34 == 0)
{
x_26 = x_7;
x_27 = x_34;
goto block_33;
}
else
{
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
x_26 = lean_box(0);
x_27 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
if (x_27 == 0)
{
lean_ctor_set(x_26, 5, x_28);
x_29 = x_26;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_11);
lean_ctor_set(x_32, 2, x_12);
lean_ctor_set(x_32, 3, x_13);
lean_ctor_set(x_32, 4, x_14);
lean_ctor_set(x_32, 5, x_28);
lean_ctor_set(x_32, 6, x_16);
lean_ctor_set(x_32, 7, x_17);
lean_ctor_set(x_32, 8, x_18);
lean_ctor_set(x_32, 9, x_19);
lean_ctor_set(x_32, 10, x_20);
lean_ctor_set(x_32, 11, x_21);
lean_ctor_set(x_32, 12, x_23);
lean_ctor_set(x_32, 13, x_25);
lean_ctor_set_uint8(x_32, sizeof(void*)*14, x_22);
lean_ctor_set_uint8(x_32, sizeof(void*)*14 + 1, x_24);
x_29 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_30; 
x_30 = l_Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_29, x_8);
lean_dec_ref(x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__56___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__56___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__55(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__56___redArg(x_1, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0_spec__0_spec__1___redArg___closed__1);
x_11 = 0;
lean_inc(x_2);
x_12 = l_Lean_MessageData_ofConstName(x_2, x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43___redArg(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 5);
lean_inc(x_9);
x_10 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19___redArg(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_st_ref_get(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = 0;
lean_inc(x_1);
x_12 = l_Lean_Environment_find_x3f(x_10, x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 0);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
x_15 = x_12;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 0);
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__2));
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(202u);
x_4 = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__1));
x_5 = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc_ref(x_9);
lean_inc_ref(x_5);
x_12 = l_Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8(x_1, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_Meta_mkFreshLevelMVarsFor(x_13, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_List_lengthTR___redArg(x_15);
x_17 = l_Lean_ConstantInfo_levelParams(x_13);
x_18 = l_List_lengthTR___redArg(x_17);
lean_dec(x_17);
x_19 = lean_nat_dec_eq(x_16, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec_ref(x_4);
x_20 = lean_obj_once(&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__3, &l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__3_once, _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__3);
x_21 = l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16(x_20, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = l_Lean_Core_instantiateValueLevelParams(x_13, x_15, x_9, x_10);
lean_dec(x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_array_size(x_3);
x_27 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_28 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__17(x_16, x_18, x_3, x_26, x_27, x_25, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_18);
lean_dec(x_16);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_41; 
x_29 = lean_ctor_get(x_28, 0);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
x_30 = x_28;
x_31 = x_41;
goto block_40;
}
else
{
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_29, 0);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_del_object(x_30);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = l_Lean_NameSet_empty;
x_35 = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__18(x_4, x_34, x_33, x_5, x_6, x_7, x_8, x_9, x_10);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_inc_ref(x_32);
lean_dec(x_29);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec_ref(x_32);
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_36);
x_37 = x_30;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_42 = lean_ctor_get(x_28, 0);
x_49 = !lean_is_exclusive(x_28);
if (x_49 == 0)
{
x_43 = x_28;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_28);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_50 = lean_ctor_get(x_22, 0);
x_57 = !lean_is_exclusive(x_22);
if (x_57 == 0)
{
x_51 = x_22;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_22);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_58 = lean_ctor_get(x_14, 0);
x_65 = !lean_is_exclusive(x_14);
if (x_65 == 0)
{
x_59 = x_14;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_14);
x_59 = lean_box(0);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = lean_ctor_get(x_12, 0);
lean_inc(x_66);
lean_dec_ref(x_12);
x_67 = lean_ctor_get(x_2, 0);
lean_inc(x_67);
lean_dec_ref(x_2);
x_68 = l_List_lengthTR___redArg(x_67);
x_69 = l_Lean_ConstantInfo_levelParams(x_66);
x_70 = l_List_lengthTR___redArg(x_69);
lean_dec(x_69);
x_71 = lean_nat_dec_eq(x_68, x_70);
lean_dec(x_70);
lean_dec(x_68);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec_ref(x_4);
x_72 = lean_obj_once(&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__3, &l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__3_once, _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___closed__3);
x_73 = l_panic___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__16(x_72, x_5, x_6, x_7, x_8, x_9, x_10);
return x_73;
}
else
{
lean_object* x_74; 
x_74 = l_Lean_Core_instantiateValueLevelParams(x_66, x_67, x_9, x_10);
lean_dec(x_66);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; size_t x_78; size_t x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_array_size(x_3);
x_79 = 0;
x_80 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__19___redArg(x_3, x_78, x_79, x_77);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_93; 
x_81 = lean_ctor_get(x_80, 0);
x_93 = !lean_is_exclusive(x_80);
if (x_93 == 0)
{
x_82 = x_80;
x_83 = x_93;
goto block_92;
}
else
{
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_box(0);
x_83 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_81, 0);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_del_object(x_82);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = l_Lean_NameSet_empty;
x_87 = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__18(x_4, x_86, x_85, x_5, x_6, x_7, x_8, x_9, x_10);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_inc_ref(x_84);
lean_dec(x_81);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_88 = lean_ctor_get(x_84, 0);
lean_inc(x_88);
lean_dec_ref(x_84);
if (x_83 == 0)
{
lean_ctor_set(x_82, 0, x_88);
x_89 = x_82;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_88);
x_89 = x_91;
goto block_90;
}
block_90:
{
return x_89;
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_101; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_94 = lean_ctor_get(x_80, 0);
x_101 = !lean_is_exclusive(x_80);
if (x_101 == 0)
{
x_95 = x_80;
x_96 = x_101;
goto block_100;
}
else
{
lean_inc(x_94);
lean_dec(x_80);
x_95 = lean_box(0);
x_96 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_97; 
if (x_96 == 0)
{
x_97 = x_95;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_94);
x_97 = x_99;
goto block_98;
}
block_98:
{
return x_97;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_109; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_102 = lean_ctor_get(x_74, 0);
x_109 = !lean_is_exclusive(x_74);
if (x_109 == 0)
{
x_103 = x_74;
x_104 = x_109;
goto block_108;
}
else
{
lean_inc(x_102);
lean_dec(x_74);
x_103 = lean_box(0);
x_104 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_105; 
if (x_104 == 0)
{
x_105 = x_103;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_102);
x_105 = x_107;
goto block_106;
}
block_106:
{
return x_105;
}
}
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_117; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_110 = lean_ctor_get(x_12, 0);
x_117 = !lean_is_exclusive(x_12);
if (x_117 == 0)
{
x_111 = x_12;
x_112 = x_117;
goto block_116;
}
else
{
lean_inc(x_110);
lean_dec(x_12);
x_111 = lean_box(0);
x_112 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_113; 
if (x_112 == 0)
{
x_113 = x_111;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_110);
x_113 = x_115;
goto block_114;
}
block_114:
{
return x_113;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_3);
return x_12;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___closed__2));
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_unsigned_to_nat(227u);
x_4 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___closed__1));
x_5 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
x_8 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_3, x_4);
switch (x_8) {
case 0:
{
x_2 = x_6;
goto _start;
}
case 1:
{
lean_dec(x_1);
lean_inc(x_5);
return x_5;
}
default: 
{
x_2 = x_7;
goto _start;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___closed__3);
x_12 = lean_panic_fn(x_1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__7));
x_2 = lean_unsigned_to_nat(55u);
x_3 = lean_unsigned_to_nat(166u);
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__6));
x_5 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__5));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_9, x_8);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_10);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_array_uget_borrowed(x_7, x_9);
lean_inc(x_2);
lean_inc_ref(x_1);
x_26 = l_Lean_findField_x3f(x_1, x_2, x_25);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
lean_inc(x_25);
x_28 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin(x_27, x_25, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_47; lean_object* x_48; uint8_t x_101; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
lean_inc(x_3);
x_47 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___lam__0___boxed), 9, 1);
lean_closure_set(x_47, 0, x_3);
x_101 = l_Lean_isPrivateName(x_30);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__0));
x_48 = x_102;
goto block_100;
}
else
{
lean_object* x_103; 
x_103 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10));
x_48 = x_103;
goto block_100;
}
block_46:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_34 = l_Lean_stringToMessageData(x_32);
x_35 = l_Lean_MessageData_ofConstName(x_30, x_23);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_unsigned_to_nat(2u);
x_40 = l_Lean_MessageData_ofExpr(x_31);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
x_44 = l_Lean_indentD(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_10);
lean_ctor_set(x_45, 1, x_44);
x_18 = x_45;
goto block_22;
}
block_100:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = l_Lean_instInhabitedExpr;
x_50 = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg(x_49, x_3, x_25);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_51 = lean_infer_type(x_50, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_4, x_25);
if (lean_obj_tag(x_53) == 1)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_47);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__1);
x_56 = l_Lean_MessageData_ofSyntax(x_54);
x_57 = l_Lean_indentD(x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_31 = x_52;
x_32 = x_48;
x_33 = x_58;
goto block_46;
}
else
{
lean_object* x_59; 
lean_dec(x_53);
lean_inc(x_25);
lean_inc(x_2);
lean_inc_ref(x_1);
x_59 = l_Lean_getEffectiveDefaultFnForField_x3f(x_1, x_2, x_25);
if (lean_obj_tag(x_59) == 1)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_90; 
x_60 = lean_ctor_get(x_59, 0);
x_90 = !lean_is_exclusive(x_59);
if (x_90 == 0)
{
x_61 = x_59;
x_62 = x_90;
goto block_89;
}
else
{
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_box(0);
x_62 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_63; 
lean_inc(x_5);
if (x_62 == 0)
{
lean_ctor_set(x_61, 0, x_5);
x_63 = x_61;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_5);
x_63 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_64; 
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_64 = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11(x_60, x_63, x_6, x_47, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
if (lean_obj_tag(x_65) == 1)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_76; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = lean_ctor_get(x_66, 1);
x_76 = !lean_is_exclusive(x_66);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_66, 0);
lean_dec(x_77);
x_68 = x_66;
x_69 = x_76;
goto block_75;
}
else
{
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_box(0);
x_69 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__2);
x_71 = l_Lean_indentExpr(x_67);
if (x_69 == 0)
{
lean_ctor_set_tag(x_68, 7);
lean_ctor_set(x_68, 1, x_71);
lean_ctor_set(x_68, 0, x_70);
x_72 = x_68;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_71);
x_72 = x_74;
goto block_73;
}
block_73:
{
x_31 = x_52;
x_32 = x_48;
x_33 = x_72;
goto block_46;
}
}
}
else
{
lean_object* x_78; 
lean_dec(x_65);
x_78 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__4);
x_31 = x_52;
x_32 = x_48;
x_33 = x_78;
goto block_46;
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec(x_52);
lean_dec_ref(x_48);
lean_dec(x_30);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_79 = lean_ctor_get(x_64, 0);
x_86 = !lean_is_exclusive(x_64);
if (x_86 == 0)
{
x_80 = x_64;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_64);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_79);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
}
}
else
{
lean_object* x_91; 
lean_dec(x_59);
lean_dec_ref(x_47);
x_91 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19);
x_31 = x_52;
x_32 = x_48;
x_33 = x_91;
goto block_46;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_99; 
lean_dec_ref(x_48);
lean_dec_ref(x_47);
lean_dec(x_30);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_92 = lean_ctor_get(x_51, 0);
x_99 = !lean_is_exclusive(x_51);
if (x_99 == 0)
{
x_93 = x_51;
x_94 = x_99;
goto block_98;
}
else
{
lean_inc(x_92);
lean_dec(x_51);
x_93 = lean_box(0);
x_94 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_95; 
if (x_94 == 0)
{
x_95 = x_93;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_92);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_111; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_104 = lean_ctor_get(x_28, 0);
x_111 = !lean_is_exclusive(x_28);
if (x_111 == 0)
{
x_105 = x_28;
x_106 = x_111;
goto block_110;
}
else
{
lean_inc(x_104);
lean_dec(x_28);
x_105 = lean_box(0);
x_106 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_107; 
if (x_106 == 0)
{
x_107 = x_105;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_104);
x_107 = x_109;
goto block_108;
}
block_108:
{
return x_107;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_26);
x_112 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___closed__8);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_113 = l_panic___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__12(x_112, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_113) == 0)
{
lean_dec_ref(x_113);
x_18 = x_10;
goto block_22;
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_121; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_114 = lean_ctor_get(x_113, 0);
x_121 = !lean_is_exclusive(x_113);
if (x_121 == 0)
{
x_115 = x_113;
x_116 = x_121;
goto block_120;
}
else
{
lean_inc(x_114);
lean_dec(x_113);
x_115 = lean_box(0);
x_116 = x_121;
goto block_120;
}
block_120:
{
lean_object* x_117; 
if (x_116 == 0)
{
x_117 = x_115;
goto block_118;
}
else
{
lean_object* x_119; 
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_114);
x_117 = x_119;
goto block_118;
}
block_118:
{
return x_117;
}
}
}
}
}
block_22:
{
size_t x_19; size_t x_20; 
x_19 = 1;
x_20 = lean_usize_add(x_9, x_19);
x_9 = x_20;
x_10 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_19 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_18, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__15___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_array_uget_borrowed(x_4, x_6);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_1);
lean_inc(x_16);
x_17 = l_Lean_Expr_const___override(x_16, x_1);
x_18 = l_Lean_mkAppN(x_17, x_2);
lean_inc_ref(x_3);
x_19 = l_Lean_Expr_app___override(x_18, x_3);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_20 = lean_infer_type(x_19, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc(x_16);
x_22 = l_Lean_MessageData_ofConstName(x_16, x_13);
x_23 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_MessageData_ofExpr(x_21);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_indentD(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_27);
x_29 = 1;
x_30 = lean_usize_add(x_6, x_29);
x_6 = x_30;
x_7 = x_28;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
x_32 = lean_ctor_get(x_20, 0);
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
x_33 = x_20;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__15___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__15___redArg(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__7(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_MessageData_ofConstName(x_5, x_4);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__7(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__13(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__13(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__57_spec__59___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_30; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
x_7 = x_1;
x_8 = x_30;
goto block_29;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_lt(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_array_push(x_5, x_3);
x_12 = lean_array_push(x_6, x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_11);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_fget_borrowed(x_5, x_2);
x_17 = lean_name_eq(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
if (x_8 == 0)
{
x_18 = x_7;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_1 = x_18;
x_2 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_array_fset(x_5, x_2, x_3);
x_25 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_24);
x_26 = x_7;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__57___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__57_spec__59___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58___redArg___closed__0(void) {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(1723u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___closed__2(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_50; 
lean_inc_ref(x_6);
x_50 = !lean_is_exclusive(x_1);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
x_14 = x_1;
x_15 = x_50;
goto block_49;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_6, x_11);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_6, x_11, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_36; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
x_27 = x_16;
x_28 = x_36;
goto block_35;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_29; 
x_29 = lean_name_eq(x_4, x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_del_object(x_27);
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_25, x_26, x_4, x_5);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_19 = x_31;
goto block_24;
}
else
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_4);
x_32 = x_27;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_19 = x_32;
goto block_24;
}
}
}
}
case 1:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_47; 
x_37 = lean_ctor_get(x_16, 0);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
x_38 = x_16;
x_39 = x_47;
goto block_46;
}
else
{
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_box(0);
x_39 = x_47;
goto block_46;
}
block_46:
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg(x_37, x_40, x_41, x_4, x_5);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_42);
x_43 = x_38;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
x_19 = x_43;
goto block_24;
}
}
}
default: 
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_19 = x_48;
goto block_24;
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fset(x_18, x_11, x_19);
lean_dec(x_11);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_20);
x_21 = x_14;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_73; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
x_73 = !lean_is_exclusive(x_1);
if (x_73 == 0)
{
x_54 = x_1;
x_55 = x_73;
goto block_72;
}
else
{
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_52);
lean_ctor_set(x_71, 1, x_53);
x_56 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_57; uint8_t x_58; size_t x_65; uint8_t x_66; 
x_57 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__57___redArg(x_56, x_4, x_5);
x_65 = 7;
x_66 = lean_usize_dec_le(x_65, x_3);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_57);
x_68 = lean_unsigned_to_nat(4u);
x_69 = lean_nat_dec_lt(x_67, x_68);
lean_dec(x_67);
x_58 = x_69;
goto block_64;
}
else
{
x_58 = x_66;
goto block_64;
}
block_64:
{
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_60);
lean_dec_ref(x_57);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___closed__2);
x_63 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58___redArg(x_3, x_59, x_60, x_61, x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
return x_63;
}
else
{
return x_57;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint64_t x_22; 
x_22 = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58___redArg___closed__0);
x_10 = x_22;
goto block_21;
}
else
{
uint64_t x_23; 
x_23 = lean_ctor_get_uint64(x_8, sizeof(void*)*2);
x_10 = x_23;
goto block_21;
}
block_21:
{
size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; 
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_9; 
x_9 = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58___redArg___closed__0);
x_4 = x_9;
goto block_8;
}
else
{
uint64_t x_10; 
x_10 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_4 = x_10;
goto block_8;
}
block_8:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40___redArg(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__0, &l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__0_once, _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__1, &l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__1_once, _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__1);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__1, &l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__1_once, _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__1);
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_45; 
x_6 = lean_st_ref_take(x_4);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 2);
x_10 = lean_ctor_get(x_6, 3);
x_11 = lean_ctor_get(x_6, 4);
x_12 = lean_ctor_get(x_6, 6);
x_13 = lean_ctor_get(x_6, 7);
x_14 = lean_ctor_get(x_6, 8);
x_45 = !lean_is_exclusive(x_6);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_6, 5);
lean_dec(x_46);
x_15 = x_6;
x_16 = x_45;
goto block_44;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = l_Lean_structureResolutionExt;
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___lam__0), 3, 2);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
x_20 = lean_box(0);
x_21 = l_Lean_EnvExtension_modifyState___redArg(x_17, x_7, x_19, x_18, x_20);
lean_dec(x_18);
x_22 = lean_obj_once(&l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__2, &l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__2_once, _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__2);
if (x_16 == 0)
{
lean_ctor_set(x_15, 5, x_22);
lean_ctor_set(x_15, 0, x_21);
x_23 = x_15;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_43, 0, x_21);
lean_ctor_set(x_43, 1, x_8);
lean_ctor_set(x_43, 2, x_9);
lean_ctor_set(x_43, 3, x_10);
lean_ctor_set(x_43, 4, x_11);
lean_ctor_set(x_43, 5, x_22);
lean_ctor_set(x_43, 6, x_12);
lean_ctor_set(x_43, 7, x_13);
lean_ctor_set(x_43, 8, x_14);
x_23 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_40; 
x_24 = lean_st_ref_set(x_4, x_23);
x_25 = lean_st_ref_take(x_3);
x_26 = lean_ctor_get(x_25, 0);
x_27 = lean_ctor_get(x_25, 2);
x_28 = lean_ctor_get(x_25, 3);
x_29 = lean_ctor_get(x_25, 4);
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_25, 1);
lean_dec(x_41);
x_30 = x_25;
x_31 = x_40;
goto block_39;
}
else
{
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_obj_once(&l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__3, &l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__3_once, _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__3);
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_32);
x_33 = x_30;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_32);
lean_ctor_set(x_38, 2, x_27);
lean_ctor_set(x_38, 3, x_28);
lean_ctor_set(x_38, 4, x_29);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_st_ref_set(x_3, x_33);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__32_spec__42(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget_borrowed(x_2, x_3);
x_7 = lean_name_eq(x_1, x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__32_spec__42___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__32_spec__42(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__32(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_5;
}
else
{
if (x_5 == 0)
{
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__32_spec__42(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__32___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__32(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__35(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_array_uset(x_3, x_2, x_5);
x_8 = lean_box(0);
x_9 = lean_array_get(x_8, x_6, x_5);
lean_dec(x_6);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__35(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__31_spec__40(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_inc(x_11);
x_15 = lean_array_push(x_4, x_11);
x_5 = x_15;
goto block_9;
}
else
{
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__31_spec__40___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__31_spec__40(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__31(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_inc(x_11);
x_15 = lean_array_push(x_4, x_11);
x_5 = x_15;
goto block_9;
}
else
{
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__31_spec__40(x_1, x_7, x_3, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__31(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__29(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget_borrowed(x_2, x_3);
x_13 = lean_name_eq(x_12, x_1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc(x_12);
x_14 = lean_array_push(x_5, x_12);
x_6 = x_14;
goto block_10;
}
else
{
x_6 = x_5;
goto block_10;
}
}
else
{
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__29(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__30(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_array_uset(x_4, x_3, x_6);
x_15 = lean_array_get_size(x_7);
x_16 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__30___closed__0));
x_17 = lean_nat_dec_lt(x_6, x_15);
if (x_17 == 0)
{
lean_dec(x_7);
x_9 = x_16;
goto block_14;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_15, x_15);
if (x_18 == 0)
{
if (x_17 == 0)
{
lean_dec(x_7);
x_9 = x_16;
goto block_14;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_15);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__29(x_1, x_7, x_19, x_20, x_16);
lean_dec(x_7);
x_9 = x_21;
goto block_14;
}
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_15);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__29(x_1, x_7, x_22, x_23, x_16);
lean_dec(x_7);
x_9 = x_24;
goto block_14;
}
}
block_14:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__30(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__33_spec__44(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_array_uget_borrowed(x_1, x_2);
x_14 = lean_name_eq(x_13, x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; uint8_t x_22; 
lean_inc(x_12);
lean_inc(x_11);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_4, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
x_15 = x_4;
x_16 = x_22;
goto block_21;
}
else
{
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_push(x_12, x_11);
lean_inc(x_13);
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_17);
lean_ctor_set(x_15, 0, x_13);
x_18 = x_15;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
x_5 = x_18;
goto block_9;
}
}
}
else
{
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__33_spec__44___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__33_spec__44(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__33(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__30___closed__0));
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_fget_borrowed(x_1, x_7);
x_12 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__30___closed__0));
if (x_9 == 0)
{
lean_object* x_13; 
lean_inc(x_11);
x_13 = lean_array_push(x_12, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_inc(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_nat_dec_le(x_8, x_8);
if (x_15 == 0)
{
if (x_9 == 0)
{
lean_object* x_16; 
lean_dec_ref(x_14);
lean_inc(x_11);
x_16 = lean_array_push(x_12, x_11);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_8);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__33_spec__44(x_1, x_17, x_18, x_14);
x_2 = x_19;
goto block_6;
}
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_8);
x_22 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__33_spec__44(x_1, x_20, x_21, x_14);
x_2 = x_22;
goto block_6;
}
}
}
block_6:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_array_push(x_4, x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__33___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__33(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__28(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget_borrowed(x_2, x_3);
x_7 = lean_name_eq(x_6, x_1);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__28(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__37(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_26; 
x_12 = lean_array_uget_borrowed(x_2, x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_array_get_size(x_12);
lean_inc(x_12);
x_15 = l_Array_toSubarray___redArg(x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
lean_dec_ref(x_15);
x_26 = lean_nat_dec_lt(x_17, x_18);
if (x_26 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_array_get_size(x_16);
x_28 = lean_nat_dec_le(x_18, x_27);
if (x_28 == 0)
{
lean_dec(x_18);
x_19 = x_27;
goto block_25;
}
else
{
x_19 = x_18;
goto block_25;
}
}
block_25:
{
uint8_t x_20; 
x_20 = lean_nat_dec_lt(x_17, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec_ref(x_16);
x_6 = x_5;
goto block_10;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_22 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_23 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__28(x_1, x_16, x_21, x_22);
lean_dec_ref(x_16);
if (x_23 == 0)
{
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_24; 
lean_inc(x_12);
x_24 = lean_array_push(x_5, x_12);
x_6 = x_24;
goto block_10;
}
}
}
}
else
{
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__37(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__36___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__36___redArg___closed__0));
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__36___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__36___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__36___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__32_spec__35(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_20; uint8_t x_26; 
x_7 = lean_array_uget_borrowed(x_3, x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_array_get_size(x_7);
lean_inc(x_7);
x_10 = l_Array_toSubarray___redArg(x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = 1;
x_26 = lean_nat_dec_lt(x_12, x_13);
if (x_26 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
x_15 = x_6;
goto block_19;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_array_get_size(x_11);
x_28 = lean_nat_dec_le(x_13, x_27);
if (x_28 == 0)
{
lean_dec(x_13);
x_20 = x_27;
goto block_25;
}
else
{
x_20 = x_13;
goto block_25;
}
}
block_19:
{
if (x_15 == 0)
{
size_t x_16; size_t x_17; 
x_16 = 1;
x_17 = lean_usize_add(x_4, x_16);
x_4 = x_17;
goto _start;
}
else
{
return x_14;
}
}
block_25:
{
uint8_t x_21; 
x_21 = lean_nat_dec_lt(x_12, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
x_15 = x_6;
goto block_19;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_23 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_24 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__28(x_1, x_11, x_22, x_23);
lean_dec_ref(x_11);
if (x_24 == 0)
{
x_15 = x_24;
goto block_19;
}
else
{
x_15 = x_2;
goto block_19;
}
}
}
}
else
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__32_spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__32_spec__35(x_1, x_6, x_3, x_7, x_8);
lean_dec_ref(x_3);
lean_dec(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__32(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_20; uint8_t x_26; 
x_7 = lean_array_uget_borrowed(x_3, x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_array_get_size(x_7);
lean_inc(x_7);
x_10 = l_Array_toSubarray___redArg(x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = 1;
x_26 = lean_nat_dec_lt(x_12, x_13);
if (x_26 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
x_15 = x_6;
goto block_19;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_array_get_size(x_11);
x_28 = lean_nat_dec_le(x_13, x_27);
if (x_28 == 0)
{
lean_dec(x_13);
x_20 = x_27;
goto block_25;
}
else
{
x_20 = x_13;
goto block_25;
}
}
block_19:
{
if (x_15 == 0)
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 1;
x_17 = lean_usize_add(x_4, x_16);
x_18 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__32_spec__35(x_1, x_2, x_3, x_17, x_5);
return x_18;
}
else
{
return x_14;
}
}
block_25:
{
uint8_t x_21; 
x_21 = lean_nat_dec_lt(x_12, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
x_15 = x_6;
goto block_19;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_23 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_24 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__28(x_1, x_11, x_22, x_23);
lean_dec_ref(x_11);
if (x_24 == 0)
{
x_15 = x_24;
goto block_19;
}
else
{
x_15 = x_2;
goto block_19;
}
}
}
}
else
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__32(x_1, x_6, x_3, x_7, x_8);
lean_dec_ref(x_3);
lean_dec(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__33_spec__37(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_19; uint8_t x_25; 
x_6 = lean_array_uget_borrowed(x_2, x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_array_get_size(x_6);
lean_inc(x_6);
x_9 = l_Array_toSubarray___redArg(x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
lean_dec_ref(x_9);
x_13 = 1;
x_25 = lean_nat_dec_lt(x_11, x_12);
if (x_25 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_14 = x_5;
goto block_18;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_get_size(x_10);
x_27 = lean_nat_dec_le(x_12, x_26);
if (x_27 == 0)
{
lean_dec(x_12);
x_19 = x_26;
goto block_24;
}
else
{
x_19 = x_12;
goto block_24;
}
}
block_18:
{
if (x_14 == 0)
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
goto _start;
}
else
{
return x_13;
}
}
block_24:
{
uint8_t x_20; 
x_20 = lean_nat_dec_lt(x_11, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
x_14 = x_5;
goto block_18;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_22 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_23 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__28(x_1, x_10, x_21, x_22);
lean_dec_ref(x_10);
x_14 = x_23;
goto block_18;
}
}
}
else
{
uint8_t x_28; 
x_28 = 0;
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__33_spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__33_spec__37(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__33(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_19; uint8_t x_25; 
x_6 = lean_array_uget_borrowed(x_2, x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_array_get_size(x_6);
lean_inc(x_6);
x_9 = l_Array_toSubarray___redArg(x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
lean_dec_ref(x_9);
x_13 = 1;
x_25 = lean_nat_dec_lt(x_11, x_12);
if (x_25 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_14 = x_5;
goto block_18;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_get_size(x_10);
x_27 = lean_nat_dec_le(x_12, x_26);
if (x_27 == 0)
{
lean_dec(x_12);
x_19 = x_26;
goto block_24;
}
else
{
x_19 = x_12;
goto block_24;
}
}
block_18:
{
if (x_14 == 0)
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_17 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__33_spec__37(x_1, x_2, x_16, x_4);
return x_17;
}
else
{
return x_13;
}
}
block_24:
{
uint8_t x_20; 
x_20 = lean_nat_dec_lt(x_11, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
x_14 = x_5;
goto block_18;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_22 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_23 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__28(x_1, x_10, x_21, x_22);
lean_dec_ref(x_10);
x_14 = x_23;
goto block_18;
}
}
}
else
{
uint8_t x_28; 
x_28 = 0;
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__33(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_instInhabited(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_38; 
x_38 = lean_nat_dec_lt(x_5, x_1);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_6);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; uint8_t x_69; uint8_t x_80; lean_object* x_81; 
lean_dec_ref(x_6);
x_40 = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__0);
x_41 = lean_box(0);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_array_get_borrowed(x_40, x_2, x_5);
x_44 = lean_array_get_borrowed(x_41, x_43, x_42);
lean_inc(x_5);
lean_inc_ref(x_2);
x_45 = l_Array_toSubarray___redArg(x_2, x_42, x_5);
x_46 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 2);
lean_inc(x_48);
lean_dec_ref(x_45);
x_49 = lean_box(0);
x_80 = lean_nat_dec_lt(x_47, x_48);
if (x_80 == 0)
{
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
x_69 = x_38;
goto block_79;
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_array_get_size(x_46);
x_88 = lean_nat_dec_le(x_48, x_87);
if (x_88 == 0)
{
lean_dec(x_48);
x_81 = x_87;
goto block_86;
}
else
{
x_81 = x_48;
goto block_86;
}
}
block_57:
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_nat_dec_eq(x_3, x_42);
x_51 = lean_box(x_50);
lean_inc(x_44);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_44);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_56, 0, x_55);
x_14 = x_56;
goto block_37;
}
block_59:
{
lean_object* x_58; 
x_58 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__3));
x_14 = x_58;
goto block_37;
}
block_68:
{
uint8_t x_64; 
x_64 = lean_nat_dec_lt(x_60, x_63);
if (x_64 == 0)
{
lean_dec(x_63);
lean_dec_ref(x_61);
lean_dec(x_60);
goto block_57;
}
else
{
size_t x_65; size_t x_66; uint8_t x_67; 
x_65 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_66 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_67 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__32(x_44, x_62, x_61, x_65, x_66);
lean_dec_ref(x_61);
if (x_67 == 0)
{
goto block_57;
}
else
{
goto block_59;
}
}
}
block_79:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_5, x_70);
lean_inc(x_4);
lean_inc_ref(x_2);
x_72 = l_Array_toSubarray___redArg(x_2, x_71, x_4);
x_73 = lean_ctor_get(x_72, 0);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 2);
lean_inc(x_75);
lean_dec_ref(x_72);
x_76 = lean_nat_dec_lt(x_74, x_75);
if (x_76 == 0)
{
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
goto block_57;
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_array_get_size(x_73);
x_78 = lean_nat_dec_le(x_75, x_77);
if (x_78 == 0)
{
lean_dec(x_75);
x_60 = x_74;
x_61 = x_73;
x_62 = x_69;
x_63 = x_77;
goto block_68;
}
else
{
x_60 = x_74;
x_61 = x_73;
x_62 = x_69;
x_63 = x_75;
goto block_68;
}
}
}
block_86:
{
uint8_t x_82; 
x_82 = lean_nat_dec_lt(x_47, x_81);
if (x_82 == 0)
{
lean_dec(x_81);
lean_dec(x_47);
lean_dec_ref(x_46);
x_69 = x_80;
goto block_79;
}
else
{
size_t x_83; size_t x_84; uint8_t x_85; 
x_83 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_84 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_85 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__33(x_44, x_46, x_83, x_84);
lean_dec_ref(x_46);
if (x_85 == 0)
{
x_69 = x_82;
goto block_79;
}
else
{
goto block_59;
}
}
}
}
block_37:
{
lean_object* x_15; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_15 = lean_apply_7(x_14, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_28; 
x_16 = lean_ctor_get(x_15, 0);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
x_17 = x_15;
x_18 = x_28;
goto block_27;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_28;
goto block_27;
}
block_27:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec_ref(x_16);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_19);
x_20 = x_17;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_del_object(x_17);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec_ref(x_16);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_5 = x_25;
x_6 = x_23;
goto _start;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_29 = lean_ctor_get(x_15, 0);
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
x_30 = x_15;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_15);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_38; 
x_38 = lean_nat_dec_lt(x_5, x_1);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_6);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; uint8_t x_69; uint8_t x_80; lean_object* x_81; 
lean_dec_ref(x_6);
x_40 = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__0);
x_41 = lean_box(0);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_array_get_borrowed(x_40, x_2, x_5);
x_44 = lean_array_get_borrowed(x_41, x_43, x_42);
lean_inc(x_5);
lean_inc_ref(x_2);
x_45 = l_Array_toSubarray___redArg(x_2, x_42, x_5);
x_46 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 2);
lean_inc(x_48);
lean_dec_ref(x_45);
x_49 = lean_box(0);
x_80 = lean_nat_dec_lt(x_47, x_48);
if (x_80 == 0)
{
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
x_69 = x_38;
goto block_79;
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_array_get_size(x_46);
x_88 = lean_nat_dec_le(x_48, x_87);
if (x_88 == 0)
{
lean_dec(x_48);
x_81 = x_87;
goto block_86;
}
else
{
x_81 = x_48;
goto block_86;
}
}
block_57:
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_nat_dec_eq(x_3, x_42);
x_51 = lean_box(x_50);
lean_inc(x_44);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_44);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_56, 0, x_55);
x_14 = x_56;
goto block_37;
}
block_59:
{
lean_object* x_58; 
x_58 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__3));
x_14 = x_58;
goto block_37;
}
block_68:
{
uint8_t x_64; 
x_64 = lean_nat_dec_lt(x_60, x_63);
if (x_64 == 0)
{
lean_dec(x_63);
lean_dec_ref(x_61);
lean_dec(x_60);
goto block_57;
}
else
{
size_t x_65; size_t x_66; uint8_t x_67; 
x_65 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_66 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_67 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__32(x_44, x_62, x_61, x_65, x_66);
lean_dec_ref(x_61);
if (x_67 == 0)
{
goto block_57;
}
else
{
goto block_59;
}
}
}
block_79:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_5, x_70);
lean_inc(x_4);
lean_inc_ref(x_2);
x_72 = l_Array_toSubarray___redArg(x_2, x_71, x_4);
x_73 = lean_ctor_get(x_72, 0);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 2);
lean_inc(x_75);
lean_dec_ref(x_72);
x_76 = lean_nat_dec_lt(x_74, x_75);
if (x_76 == 0)
{
lean_dec(x_75);
lean_dec(x_74);
lean_dec_ref(x_73);
goto block_57;
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_array_get_size(x_73);
x_78 = lean_nat_dec_le(x_75, x_77);
if (x_78 == 0)
{
lean_dec(x_75);
x_60 = x_74;
x_61 = x_73;
x_62 = x_69;
x_63 = x_77;
goto block_68;
}
else
{
x_60 = x_74;
x_61 = x_73;
x_62 = x_69;
x_63 = x_75;
goto block_68;
}
}
}
block_86:
{
uint8_t x_82; 
x_82 = lean_nat_dec_lt(x_47, x_81);
if (x_82 == 0)
{
lean_dec(x_81);
lean_dec(x_47);
lean_dec_ref(x_46);
x_69 = x_80;
goto block_79;
}
else
{
size_t x_83; size_t x_84; uint8_t x_85; 
x_83 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_84 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_85 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__33(x_44, x_46, x_83, x_84);
lean_dec_ref(x_46);
if (x_85 == 0)
{
x_69 = x_82;
goto block_79;
}
else
{
goto block_59;
}
}
}
}
block_37:
{
lean_object* x_15; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_15 = lean_apply_7(x_14, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_28; 
x_16 = lean_ctor_get(x_15, 0);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
x_17 = x_15;
x_18 = x_28;
goto block_27;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_28;
goto block_27;
}
block_27:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec_ref(x_16);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_19);
x_20 = x_17;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_del_object(x_17);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec_ref(x_16);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_26 = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg(x_1, x_2, x_3, x_4, x_25, x_23, x_7, x_8, x_9, x_10, x_11, x_12);
return x_26;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_29 = lean_ctor_get(x_15, 0);
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
x_30 = x_15;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_15);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__35___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_4, x_1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_5);
x_15 = lean_box(0);
x_16 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__1));
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_sub(x_2, x_4);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_3);
lean_inc(x_18);
x_19 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34___redArg(x_18, x_3, x_4, x_18, x_17, x_16, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_39; 
x_20 = lean_ctor_get(x_19, 0);
x_39 = !lean_is_exclusive(x_19);
if (x_39 == 0)
{
x_21 = x_19;
x_22 = x_39;
goto block_38;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_36; 
x_23 = lean_ctor_get(x_20, 0);
x_36 = !lean_is_exclusive(x_20);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_20, 1);
lean_dec(x_37);
x_24 = x_20;
x_25 = x_36;
goto block_35;
}
else
{
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = x_36;
goto block_35;
}
block_35:
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_del_object(x_24);
lean_del_object(x_21);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_4, x_26);
lean_dec(x_4);
x_4 = x_27;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_29; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
if (x_25 == 0)
{
lean_ctor_set(x_24, 1, x_15);
x_29 = x_24;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_15);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_29);
x_30 = x_21;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__35___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__35___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__1));
lean_inc_ref(x_1);
x_12 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__35___redArg(x_9, x_9, x_1, x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_39; 
x_13 = lean_ctor_get(x_12, 0);
x_39 = !lean_is_exclusive(x_12);
if (x_39 == 0)
{
x_14 = x_12;
x_15 = x_39;
goto block_38;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_36; 
x_16 = lean_ctor_get(x_13, 0);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_13, 1);
lean_dec(x_37);
x_17 = x_13;
x_18 = x_36;
goto block_35;
}
else
{
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = x_36;
goto block_35;
}
block_35:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_box(0);
x_20 = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg___closed__0);
x_21 = 0;
x_22 = lean_array_get(x_20, x_1, x_10);
lean_dec_ref(x_1);
x_23 = lean_array_get(x_19, x_22, x_10);
lean_dec(x_22);
x_24 = lean_box(x_21);
if (x_18 == 0)
{
lean_ctor_set(x_17, 1, x_23);
lean_ctor_set(x_17, 0, x_24);
x_25 = x_17;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_23);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_25);
x_26 = x_14;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_del_object(x_17);
lean_dec_ref(x_1);
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
lean_dec_ref(x_16);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_31);
x_32 = x_14;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
lean_dec_ref(x_1);
x_40 = lean_ctor_get(x_12, 0);
x_47 = !lean_is_exclusive(x_12);
if (x_47 == 0)
{
x_41 = x_12;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_12);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__34(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__32(x_1, x_6);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_14 = lean_array_uset(x_8, x_3, x_11);
x_3 = x_13;
x_4 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__34(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__38(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_110; 
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 0);
x_110 = !lean_is_exclusive(x_3);
if (x_110 == 0)
{
x_13 = x_3;
x_14 = x_110;
goto block_109;
}
else
{
lean_inc(x_11);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_108; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
x_108 = !lean_is_exclusive(x_11);
if (x_108 == 0)
{
x_17 = x_11;
x_18 = x_108;
goto block_107;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_12);
x_21 = lean_nat_dec_eq(x_20, x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_12);
x_22 = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27(x_12, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_51; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_72; uint8_t x_82; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_dec(x_23);
x_82 = lean_unbox(x_35);
lean_dec(x_35);
if (x_82 == 0)
{
if (x_1 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__38___closed__0));
x_84 = lean_nat_dec_lt(x_19, x_20);
if (x_84 == 0)
{
x_72 = x_83;
goto block_81;
}
else
{
uint8_t x_85; 
x_85 = lean_nat_dec_le(x_20, x_20);
if (x_85 == 0)
{
if (x_84 == 0)
{
x_72 = x_83;
goto block_81;
}
else
{
size_t x_86; size_t x_87; lean_object* x_88; 
x_86 = 0;
x_87 = lean_usize_of_nat(x_20);
x_88 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__37(x_36, x_12, x_86, x_87, x_83);
x_72 = x_88;
goto block_81;
}
}
else
{
size_t x_89; size_t x_90; lean_object* x_91; 
x_89 = 0;
x_90 = lean_usize_of_nat(x_20);
x_91 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__37(x_36, x_12, x_89, x_90, x_83);
x_72 = x_91;
goto block_81;
}
}
}
else
{
x_37 = x_16;
goto block_50;
}
}
else
{
x_37 = x_16;
goto block_50;
}
block_34:
{
lean_object* x_27; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_25);
x_27 = x_17;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_24);
x_27 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_28; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_27);
lean_ctor_set(x_13, 0, x_26);
x_28 = x_13;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_27);
x_28 = x_31;
goto block_30;
}
block_30:
{
x_3 = x_28;
goto _start;
}
}
}
block_50:
{
lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_inc(x_36);
x_38 = lean_array_push(x_15, x_36);
x_39 = lean_array_size(x_12);
x_40 = 0;
x_41 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__30(x_36, x_39, x_40, x_12);
lean_dec(x_36);
x_42 = lean_array_get_size(x_41);
x_43 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__38___closed__0));
x_44 = lean_nat_dec_lt(x_19, x_42);
if (x_44 == 0)
{
lean_dec_ref(x_41);
x_24 = x_37;
x_25 = x_38;
x_26 = x_43;
goto block_34;
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_le(x_42, x_42);
if (x_45 == 0)
{
if (x_44 == 0)
{
lean_dec_ref(x_41);
x_24 = x_37;
x_25 = x_38;
x_26 = x_43;
goto block_34;
}
else
{
size_t x_46; lean_object* x_47; 
x_46 = lean_usize_of_nat(x_42);
x_47 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__31(x_41, x_40, x_46, x_43);
lean_dec_ref(x_41);
x_24 = x_37;
x_25 = x_38;
x_26 = x_47;
goto block_34;
}
}
else
{
size_t x_48; lean_object* x_49; 
x_48 = lean_usize_of_nat(x_42);
x_49 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__31(x_41, x_40, x_48, x_43);
lean_dec_ref(x_41);
x_24 = x_37;
x_25 = x_38;
x_26 = x_49;
goto block_34;
}
}
}
block_59:
{
lean_object* x_52; uint8_t x_53; size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = l_Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__33(x_51);
lean_dec_ref(x_51);
x_53 = l_Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__32(x_2, x_36);
x_54 = lean_array_size(x_52);
x_55 = 0;
x_56 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__34(x_2, x_54, x_55, x_52);
lean_inc(x_36);
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_36);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_53);
x_58 = lean_array_push(x_16, x_57);
x_37 = x_58;
goto block_50;
}
block_65:
{
lean_object* x_64; 
lean_dec(x_61);
x_64 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__36___redArg(x_60, x_62, x_63);
lean_dec(x_63);
x_51 = x_64;
goto block_59;
}
block_71:
{
uint8_t x_70; 
x_70 = lean_nat_dec_le(x_69, x_68);
if (x_70 == 0)
{
lean_dec(x_68);
lean_inc(x_69);
x_60 = x_66;
x_61 = x_67;
x_62 = x_69;
x_63 = x_69;
goto block_65;
}
else
{
x_60 = x_66;
x_61 = x_67;
x_62 = x_69;
x_63 = x_68;
goto block_65;
}
}
block_81:
{
size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_array_size(x_72);
x_74 = 0;
x_75 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__35(x_73, x_74, x_72);
x_76 = lean_array_get_size(x_75);
x_77 = lean_nat_dec_eq(x_76, x_19);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_sub(x_76, x_78);
x_80 = lean_nat_dec_le(x_19, x_79);
if (x_80 == 0)
{
lean_inc(x_79);
x_66 = x_75;
x_67 = x_76;
x_68 = x_79;
x_69 = x_79;
goto block_71;
}
else
{
x_66 = x_75;
x_67 = x_76;
x_68 = x_79;
x_69 = x_19;
goto block_71;
}
}
else
{
x_51 = x_75;
goto block_59;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_99; 
lean_del_object(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_del_object(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_92 = lean_ctor_get(x_22, 0);
x_99 = !lean_is_exclusive(x_22);
if (x_99 == 0)
{
x_93 = x_22;
x_94 = x_99;
goto block_98;
}
else
{
lean_inc(x_92);
lean_dec(x_22);
x_93 = lean_box(0);
x_94 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_95; 
if (x_94 == 0)
{
x_95 = x_93;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_92);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
}
}
}
else
{
lean_object* x_100; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (x_18 == 0)
{
x_100 = x_17;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_15);
lean_ctor_set(x_106, 1, x_16);
x_100 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_101; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_100);
x_101 = x_13;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_12);
lean_ctor_set(x_104, 1, x_100);
x_101 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__38(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_array_size(x_2);
x_12 = 0;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_2);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__26(x_11, x_12, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_51 = lean_array_get_size(x_14);
lean_inc_ref(x_2);
x_52 = lean_array_push(x_14, x_2);
x_53 = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), x_15, x_52, x_51);
x_54 = lean_array_get_size(x_53);
x_55 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__38___closed__0));
x_56 = lean_nat_dec_lt(x_15, x_54);
if (x_56 == 0)
{
lean_dec_ref(x_53);
x_16 = x_55;
goto block_50;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_54, x_54);
if (x_57 == 0)
{
if (x_56 == 0)
{
lean_dec_ref(x_53);
x_16 = x_55;
goto block_50;
}
else
{
size_t x_58; lean_object* x_59; 
x_58 = lean_usize_of_nat(x_54);
x_59 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__31(x_53, x_12, x_58, x_55);
lean_dec_ref(x_53);
x_16 = x_59;
goto block_50;
}
}
else
{
size_t x_60; lean_object* x_61; 
x_60 = lean_usize_of_nat(x_54);
x_61 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__31(x_53, x_12, x_60, x_55);
lean_dec_ref(x_53);
x_16 = x_61;
goto block_50;
}
}
block_50:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_mk_empty_array_with_capacity(x_17);
x_19 = lean_array_push(x_18, x_1);
x_20 = ((lean_object*)(l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8___closed__0));
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__38(x_3, x_2, x_22, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_41; 
x_24 = lean_ctor_get(x_23, 0);
x_41 = !lean_is_exclusive(x_23);
if (x_41 == 0)
{
x_25 = x_23;
x_26 = x_41;
goto block_40;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_39; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_27, 0);
x_29 = lean_ctor_get(x_27, 1);
x_39 = !lean_is_exclusive(x_27);
if (x_39 == 0)
{
x_30 = x_27;
x_31 = x_39;
goto block_38;
}
else
{
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_27);
x_30 = lean_box(0);
x_31 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_29);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_32);
x_33 = x_25;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
x_42 = lean_ctor_get(x_23, 0);
x_49 = !lean_is_exclusive(x_23);
if (x_49 == 0)
{
x_43 = x_23;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_23);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_62 = lean_ctor_get(x_13, 0);
x_69 = !lean_is_exclusive(x_13);
if (x_69 == 0)
{
x_63 = x_13;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_13);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_st_ref_get(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
lean_inc_ref(x_11);
x_12 = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(x_11, x_1);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_22; 
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
x_14 = x_12;
x_15 = x_22;
goto block_21;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = ((lean_object*)(l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8___closed__0));
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
if (x_15 == 0)
{
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_17);
x_18 = x_14;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
else
{
lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_12);
lean_inc(x_1);
x_23 = l_Lean_getStructureParentInfo(x_11, x_1);
x_24 = lean_array_size(x_23);
x_25 = 0;
x_26 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__13(x_24, x_25, x_23);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_27 = l_Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14(x_1, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_29);
x_30 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg(x_1, x_29, x_6, x_8);
lean_dec(x_8);
lean_dec(x_6);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; uint8_t x_37; 
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_30, 0);
lean_dec(x_38);
x_31 = x_30;
x_32 = x_37;
goto block_36;
}
else
{
lean_dec(x_30);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
lean_ctor_set(x_31, 0, x_28);
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_28);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_28);
x_39 = lean_ctor_get(x_30, 0);
x_46 = !lean_is_exclusive(x_30);
if (x_46 == 0)
{
x_40 = x_30;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_30);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__26(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_uget_borrowed(x_3, x_2);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_13);
x_14 = l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8(x_13, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_3, x_2, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_18, x_2, x_16);
x_2 = x_20;
x_3 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_23 = lean_ctor_get(x_14, 0);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
x_24 = x_14;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__26(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
x_10 = l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_10, 0);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
x_12 = x_10;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_14);
lean_dec(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
x_20 = lean_ctor_get(x_10, 0);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
x_21 = x_10;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__0));
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__1));
x_11 = lean_string_dec_eq(x_7, x_10);
if (x_11 == 0)
{
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__2));
x_13 = lean_string_dec_eq(x_6, x_12);
if (x_13 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__3));
x_15 = lean_string_dec_eq(x_6, x_14);
if (x_15 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
case 1:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_5, 1);
x_20 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__4));
x_21 = lean_string_dec_eq(x_19, x_20);
if (x_21 == 0)
{
return x_1;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__5));
x_23 = lean_string_dec_eq(x_18, x_22);
if (x_23 == 0)
{
return x_1;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___closed__6));
x_25 = lean_string_dec_eq(x_17, x_24);
if (x_25 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
}
else
{
return x_1;
}
}
default: 
{
return x_1;
}
}
}
case 0:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_3, 1);
x_27 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1___lam__0___closed__0));
x_28 = lean_string_dec_eq(x_26, x_27);
if (x_28 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
default: 
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_86; lean_object* x_87; uint8_t x_88; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; uint8_t x_100; uint8_t x_101; uint8_t x_103; uint8_t x_119; 
x_94 = 2;
x_119 = l_Lean_instBEqMessageSeverity_beq(x_3, x_94);
if (x_119 == 0)
{
x_103 = x_119;
goto block_118;
}
else
{
uint8_t x_120; 
lean_inc_ref(x_2);
x_120 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_103 = x_120;
goto block_118;
}
block_45:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_44; 
x_19 = lean_st_ref_take(x_18);
x_20 = lean_ctor_get(x_17, 6);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 7);
lean_inc(x_21);
lean_dec_ref(x_17);
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_19, 2);
x_25 = lean_ctor_get(x_19, 3);
x_26 = lean_ctor_get(x_19, 4);
x_27 = lean_ctor_get(x_19, 5);
x_28 = lean_ctor_get(x_19, 6);
x_29 = lean_ctor_get(x_19, 7);
x_30 = lean_ctor_get(x_19, 8);
x_44 = !lean_is_exclusive(x_19);
if (x_44 == 0)
{
x_31 = x_19;
x_32 = x_44;
goto block_43;
}
else
{
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
x_31 = lean_box(0);
x_32 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_21);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_10);
x_35 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_35, 0, x_13);
lean_ctor_set(x_35, 1, x_16);
lean_ctor_set(x_35, 2, x_11);
lean_ctor_set(x_35, 3, x_12);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_35, sizeof(void*)*5 + 1, x_14);
lean_ctor_set_uint8(x_35, sizeof(void*)*5 + 2, x_4);
x_36 = l_Lean_MessageLog_add(x_35, x_28);
if (x_32 == 0)
{
lean_ctor_set(x_31, 6, x_36);
x_37 = x_31;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_42, 0, x_22);
lean_ctor_set(x_42, 1, x_23);
lean_ctor_set(x_42, 2, x_24);
lean_ctor_set(x_42, 3, x_25);
lean_ctor_set(x_42, 4, x_26);
lean_ctor_set(x_42, 5, x_27);
lean_ctor_set(x_42, 6, x_36);
lean_ctor_set(x_42, 7, x_29);
lean_ctor_set(x_42, 8, x_30);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_st_ref_set(x_18, x_37);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
block_70:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_69; 
x_54 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_55 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_getFieldOrigin_spec__1_spec__1(x_54, x_5, x_6, x_7, x_8);
x_56 = lean_ctor_get(x_55, 0);
x_69 = !lean_is_exclusive(x_55);
if (x_69 == 0)
{
x_57 = x_55;
x_58 = x_69;
goto block_68;
}
else
{
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_inc_ref(x_52);
x_59 = l_Lean_FileMap_toPosition(x_52, x_51);
lean_dec(x_51);
x_60 = l_Lean_FileMap_toPosition(x_52, x_53);
lean_dec(x_53);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__0));
if (x_49 == 0)
{
lean_del_object(x_57);
lean_dec_ref(x_46);
x_10 = x_56;
x_11 = x_61;
x_12 = x_62;
x_13 = x_47;
x_14 = x_48;
x_15 = x_50;
x_16 = x_59;
x_17 = x_7;
x_18 = x_8;
goto block_45;
}
else
{
uint8_t x_63; 
lean_inc(x_56);
x_63 = l_Lean_MessageData_hasTag(x_46, x_56);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_61);
lean_dec_ref(x_59);
lean_dec(x_56);
lean_dec_ref(x_47);
lean_dec_ref(x_7);
x_64 = lean_box(0);
if (x_58 == 0)
{
lean_ctor_set(x_57, 0, x_64);
x_65 = x_57;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_64);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
else
{
lean_del_object(x_57);
x_10 = x_56;
x_11 = x_61;
x_12 = x_62;
x_13 = x_47;
x_14 = x_48;
x_15 = x_50;
x_16 = x_59;
x_17 = x_7;
x_18 = x_8;
goto block_45;
}
}
}
}
block_81:
{
lean_object* x_79; 
x_79 = l_Lean_Syntax_getTailPos_x3f(x_72, x_76);
lean_dec(x_72);
if (lean_obj_tag(x_79) == 0)
{
lean_inc(x_78);
x_46 = x_71;
x_47 = x_73;
x_48 = x_74;
x_49 = x_75;
x_50 = x_76;
x_51 = x_78;
x_52 = x_77;
x_53 = x_78;
goto block_70;
}
else
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_46 = x_71;
x_47 = x_73;
x_48 = x_74;
x_49 = x_75;
x_50 = x_76;
x_51 = x_78;
x_52 = x_77;
x_53 = x_80;
goto block_70;
}
}
block_93:
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Lean_replaceRef(x_1, x_83);
lean_dec(x_83);
x_90 = l_Lean_Syntax_getPos_x3f(x_89, x_86);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_unsigned_to_nat(0u);
x_71 = x_82;
x_72 = x_89;
x_73 = x_84;
x_74 = x_88;
x_75 = x_85;
x_76 = x_86;
x_77 = x_87;
x_78 = x_91;
goto block_81;
}
else
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec_ref(x_90);
x_71 = x_82;
x_72 = x_89;
x_73 = x_84;
x_74 = x_88;
x_75 = x_85;
x_76 = x_86;
x_77 = x_87;
x_78 = x_92;
goto block_81;
}
}
block_102:
{
if (x_101 == 0)
{
x_82 = x_96;
x_83 = x_95;
x_84 = x_97;
x_85 = x_98;
x_86 = x_100;
x_87 = x_99;
x_88 = x_3;
goto block_93;
}
else
{
x_82 = x_96;
x_83 = x_95;
x_84 = x_97;
x_85 = x_98;
x_86 = x_100;
x_87 = x_99;
x_88 = x_94;
goto block_93;
}
}
block_118:
{
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_113; 
x_104 = lean_ctor_get(x_7, 0);
x_105 = lean_ctor_get(x_7, 1);
x_106 = lean_ctor_get(x_7, 2);
x_107 = lean_ctor_get(x_7, 5);
x_108 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_109 = lean_box(x_103);
x_110 = lean_box(x_108);
x_111 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_111, 0, x_109);
lean_closure_set(x_111, 1, x_110);
x_112 = 1;
x_113 = l_Lean_instBEqMessageSeverity_beq(x_3, x_112);
if (x_113 == 0)
{
lean_inc_ref(x_105);
lean_inc_ref(x_104);
lean_inc(x_107);
x_95 = x_107;
x_96 = x_111;
x_97 = x_104;
x_98 = x_108;
x_99 = x_105;
x_100 = x_103;
x_101 = x_113;
goto block_102;
}
else
{
lean_object* x_114; uint8_t x_115; 
x_114 = l_Lean_warningAsError;
x_115 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__2(x_106, x_114);
lean_inc_ref(x_105);
lean_inc_ref(x_104);
lean_inc(x_107);
x_95 = x_107;
x_96 = x_111;
x_97 = x_104;
x_98 = x_108;
x_99 = x_105;
x_100 = x_103;
x_101 = x_115;
goto block_102;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 5);
lean_inc(x_11);
x_12 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg(x_11, x_1, x_2, x_3, x_6, x_7, x_8, x_9);
lean_dec(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_3);
x_13 = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = 0;
x_11 = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6(x_1, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__14___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget_borrowed(x_2, x_3);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_12);
lean_inc_ref(x_1);
x_13 = l_Lean_Meta_mkProjection(x_1, x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_12);
x_15 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_12, x_14, x_5);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_13, 0);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
x_20 = x_13;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_5);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__14___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__14___redArg(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__0));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__3));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__6));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__9));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__12));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__15));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_244; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_130 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__1, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__1_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__1);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_2);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_box(1);
x_133 = lean_box(x_3);
x_134 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delabConstWithSignature___boxed), 8, 1);
lean_closure_set(x_134, 0, x_133);
x_135 = lean_alloc_closure((void*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__1___boxed), 8, 3);
lean_closure_set(x_135, 0, x_4);
lean_closure_set(x_135, 1, x_132);
lean_closure_set(x_135, 2, x_134);
x_136 = l_Lean_MessageData_ofFormatWithInfosM(x_135);
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_131);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0);
x_283 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_283, 0, x_137);
lean_ctor_set(x_283, 1, x_138);
x_284 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__4, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__4_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor___closed__4);
x_285 = l_Nat_reprFast(x_11);
x_286 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_286, 0, x_285);
x_287 = l_Lean_MessageData_ofFormat(x_286);
x_288 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_288, 0, x_284);
lean_ctor_set(x_288, 1, x_287);
x_289 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_289, 0, x_283);
lean_ctor_set(x_289, 1, x_288);
lean_inc(x_5);
lean_inc_ref(x_6);
x_290 = l_Lean_getStructureParentInfo(x_6, x_5);
x_291 = lean_array_get_size(x_290);
x_292 = lean_unsigned_to_nat(0u);
x_293 = lean_nat_dec_eq(x_291, x_292);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; size_t x_297; size_t x_298; lean_object* x_299; 
x_294 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_294, 0, x_289);
lean_ctor_set(x_294, 1, x_138);
x_295 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__16, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__16_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__16);
x_296 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_array_size(x_290);
x_298 = 0;
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc_ref(x_12);
lean_inc(x_7);
x_299 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__15___redArg(x_7, x_8, x_12, x_290, x_297, x_298, x_296, x_15, x_16, x_17, x_18);
lean_dec_ref(x_290);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
lean_dec_ref(x_299);
x_244 = x_300;
goto block_282;
}
else
{
lean_object* x_301; lean_object* x_302; uint8_t x_303; uint8_t x_308; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_301 = lean_ctor_get(x_299, 0);
x_308 = !lean_is_exclusive(x_299);
if (x_308 == 0)
{
x_302 = x_299;
x_303 = x_308;
goto block_307;
}
else
{
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_box(0);
x_303 = x_308;
goto block_307;
}
block_307:
{
lean_object* x_304; 
if (x_303 == 0)
{
x_304 = x_302;
goto block_305;
}
else
{
lean_object* x_306; 
x_306 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_306, 0, x_301);
x_304 = x_306;
goto block_305;
}
block_305:
{
return x_304;
}
}
}
}
else
{
lean_dec_ref(x_290);
x_244 = x_289;
goto block_282;
}
block_45:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = l_Lean_maxRecDepth;
x_42 = l_Lean_Option_get___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__4(x_20, x_41);
x_43 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_43, 0, x_27);
lean_ctor_set(x_43, 1, x_28);
lean_ctor_set(x_43, 2, x_20);
lean_ctor_set(x_43, 3, x_29);
lean_ctor_set(x_43, 4, x_42);
lean_ctor_set(x_43, 5, x_30);
lean_ctor_set(x_43, 6, x_31);
lean_ctor_set(x_43, 7, x_32);
lean_ctor_set(x_43, 8, x_33);
lean_ctor_set(x_43, 9, x_34);
lean_ctor_set(x_43, 10, x_35);
lean_ctor_set(x_43, 11, x_36);
lean_ctor_set(x_43, 12, x_37);
lean_ctor_set(x_43, 13, x_39);
lean_ctor_set_uint8(x_43, sizeof(void*)*14, x_21);
lean_ctor_set_uint8(x_43, sizeof(void*)*14 + 1, x_38);
x_44 = l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5(x_24, x_23, x_26, x_22, x_25, x_43, x_40);
lean_dec(x_40);
lean_dec(x_25);
lean_dec_ref(x_22);
lean_dec(x_26);
lean_dec_ref(x_23);
return x_44;
}
block_68:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_53, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_53, 5);
lean_inc(x_58);
x_59 = lean_ctor_get(x_53, 6);
lean_inc(x_59);
x_60 = lean_ctor_get(x_53, 7);
lean_inc(x_60);
x_61 = lean_ctor_get(x_53, 8);
lean_inc(x_61);
x_62 = lean_ctor_get(x_53, 9);
lean_inc(x_62);
x_63 = lean_ctor_get(x_53, 10);
lean_inc(x_63);
x_64 = lean_ctor_get(x_53, 11);
lean_inc(x_64);
x_65 = lean_ctor_get(x_53, 12);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_53, sizeof(void*)*14 + 1);
x_67 = lean_ctor_get(x_53, 13);
lean_inc_ref(x_67);
lean_dec_ref(x_53);
x_20 = x_46;
x_21 = x_47;
x_22 = x_48;
x_23 = x_49;
x_24 = x_50;
x_25 = x_51;
x_26 = x_52;
x_27 = x_55;
x_28 = x_56;
x_29 = x_57;
x_30 = x_58;
x_31 = x_59;
x_32 = x_60;
x_33 = x_61;
x_34 = x_62;
x_35 = x_63;
x_36 = x_64;
x_37 = x_65;
x_38 = x_66;
x_39 = x_67;
x_40 = x_54;
goto block_45;
}
block_99:
{
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_97; 
x_79 = lean_st_ref_take(x_75);
x_80 = lean_ctor_get(x_79, 0);
x_81 = lean_ctor_get(x_79, 1);
x_82 = lean_ctor_get(x_79, 2);
x_83 = lean_ctor_get(x_79, 3);
x_84 = lean_ctor_get(x_79, 4);
x_85 = lean_ctor_get(x_79, 6);
x_86 = lean_ctor_get(x_79, 7);
x_87 = lean_ctor_get(x_79, 8);
x_97 = !lean_is_exclusive(x_79);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_79, 5);
lean_dec(x_98);
x_88 = x_79;
x_89 = x_97;
goto block_96;
}
else
{
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_79);
x_88 = lean_box(0);
x_89 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = l_Lean_Kernel_enableDiag(x_80, x_70);
x_91 = lean_obj_once(&l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__2, &l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__2_once, _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg___closed__2);
if (x_89 == 0)
{
lean_ctor_set(x_88, 5, x_91);
lean_ctor_set(x_88, 0, x_90);
x_92 = x_88;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_81);
lean_ctor_set(x_95, 2, x_82);
lean_ctor_set(x_95, 3, x_83);
lean_ctor_set(x_95, 4, x_84);
lean_ctor_set(x_95, 5, x_91);
lean_ctor_set(x_95, 6, x_85);
lean_ctor_set(x_95, 7, x_86);
lean_ctor_set(x_95, 8, x_87);
x_92 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_93; 
x_93 = lean_st_ref_set(x_75, x_92);
x_46 = x_69;
x_47 = x_70;
x_48 = x_71;
x_49 = x_74;
x_50 = x_73;
x_51 = x_77;
x_52 = x_76;
x_53 = x_72;
x_54 = x_75;
goto block_68;
}
}
}
else
{
x_46 = x_69;
x_47 = x_70;
x_48 = x_71;
x_49 = x_74;
x_50 = x_73;
x_51 = x_77;
x_52 = x_76;
x_53 = x_72;
x_54 = x_75;
goto block_68;
}
}
block_129:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; 
x_107 = lean_st_ref_get(x_106);
x_108 = lean_ctor_get(x_105, 0);
x_109 = lean_ctor_get(x_105, 1);
x_110 = lean_ctor_get(x_105, 2);
x_111 = lean_ctor_get(x_105, 3);
x_112 = lean_ctor_get(x_105, 5);
x_113 = lean_ctor_get(x_105, 6);
x_114 = lean_ctor_get(x_105, 7);
x_115 = lean_ctor_get(x_105, 8);
x_116 = lean_ctor_get(x_105, 9);
x_117 = lean_ctor_get(x_105, 10);
x_118 = lean_ctor_get(x_105, 11);
x_119 = lean_ctor_get(x_105, 12);
x_120 = lean_ctor_get_uint8(x_105, sizeof(void*)*14 + 1);
x_121 = lean_ctor_get(x_105, 13);
x_122 = l_Lean_pp_proofs;
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_107, 0);
lean_inc_ref(x_124);
lean_dec(x_107);
lean_inc_ref(x_110);
x_125 = l_Lean_Options_set___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__3(x_110, x_123, x_1);
x_126 = l_Lean_diagnostics;
x_127 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__2(x_125, x_126);
x_128 = l_Lean_Kernel_isDiagnosticsEnabled(x_124);
lean_dec_ref(x_124);
if (x_128 == 0)
{
if (x_127 == 0)
{
lean_inc_ref(x_121);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc_ref(x_109);
lean_inc_ref(x_108);
lean_dec_ref(x_105);
x_20 = x_125;
x_21 = x_127;
x_22 = x_103;
x_23 = x_101;
x_24 = x_100;
x_25 = x_104;
x_26 = x_102;
x_27 = x_108;
x_28 = x_109;
x_29 = x_111;
x_30 = x_112;
x_31 = x_113;
x_32 = x_114;
x_33 = x_115;
x_34 = x_116;
x_35 = x_117;
x_36 = x_118;
x_37 = x_119;
x_38 = x_120;
x_39 = x_121;
x_40 = x_106;
goto block_45;
}
else
{
x_69 = x_125;
x_70 = x_127;
x_71 = x_103;
x_72 = x_105;
x_73 = x_100;
x_74 = x_101;
x_75 = x_106;
x_76 = x_102;
x_77 = x_104;
x_78 = x_128;
goto block_99;
}
}
else
{
x_69 = x_125;
x_70 = x_127;
x_71 = x_103;
x_72 = x_105;
x_73 = x_100;
x_74 = x_101;
x_75 = x_106;
x_76 = x_102;
x_77 = x_104;
x_78 = x_127;
goto block_99;
}
}
block_181:
{
lean_object* x_148; 
lean_inc(x_145);
lean_inc_ref(x_143);
lean_inc(x_140);
lean_inc_ref(x_146);
lean_inc(x_144);
lean_inc_ref(x_139);
x_148 = l_Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6(x_5, x_139, x_144, x_146, x_140, x_143, x_145);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec_ref(x_148);
x_150 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_150, 0, x_141);
lean_ctor_set(x_150, 1, x_138);
x_151 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__4, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__4_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__4);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_153, 0, x_147);
x_154 = l_Lean_MessageData_ofFormat(x_153);
x_155 = l_Lean_MessageData_signature(x_142);
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_Lean_indentD(x_156);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_152);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_unsigned_to_nat(1u);
x_160 = lean_array_get_size(x_149);
x_161 = lean_nat_dec_lt(x_159, x_160);
if (x_161 == 0)
{
lean_dec(x_149);
x_100 = x_158;
x_101 = x_139;
x_102 = x_144;
x_103 = x_146;
x_104 = x_140;
x_105 = x_143;
x_106 = x_145;
goto block_129;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; size_t x_165; size_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_138);
x_163 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__7, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__7_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__7);
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_array_size(x_149);
x_166 = 0;
x_167 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__7(x_165, x_166, x_149);
x_168 = lean_array_to_list(x_167);
x_169 = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData_spec__0___redArg___closed__2);
x_170 = l_Lean_MessageData_joinSep(x_168, x_169);
x_171 = l_Lean_indentD(x_170);
x_172 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_172, 0, x_164);
lean_ctor_set(x_172, 1, x_171);
x_100 = x_172;
x_101 = x_139;
x_102 = x_144;
x_103 = x_146;
x_104 = x_140;
x_105 = x_143;
x_106 = x_145;
goto block_129;
}
}
else
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; uint8_t x_180; 
lean_dec_ref(x_147);
lean_dec_ref(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_140);
lean_dec_ref(x_139);
x_173 = lean_ctor_get(x_148, 0);
x_180 = !lean_is_exclusive(x_148);
if (x_180 == 0)
{
x_174 = x_148;
x_175 = x_180;
goto block_179;
}
else
{
lean_inc(x_173);
lean_dec(x_148);
x_174 = lean_box(0);
x_175 = x_180;
goto block_179;
}
block_179:
{
lean_object* x_176; 
if (x_175 == 0)
{
x_176 = x_174;
goto block_177;
}
else
{
lean_object* x_178; 
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_173);
x_176 = x_178;
goto block_177;
}
block_177:
{
return x_176;
}
}
}
}
block_197:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_189 = lean_st_ref_get(x_188);
x_190 = lean_ctor_get(x_189, 0);
lean_inc_ref(x_190);
lean_dec(x_189);
lean_inc(x_5);
x_191 = l_Lean_getStructureCtor(x_190, x_5);
x_192 = lean_ctor_get(x_191, 0);
lean_inc_ref(x_192);
lean_dec_ref(x_191);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
lean_dec_ref(x_192);
x_194 = l_Lean_isPrivateName(x_193);
if (x_194 == 0)
{
lean_object* x_195; 
x_195 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__0));
x_139 = x_183;
x_140 = x_186;
x_141 = x_182;
x_142 = x_193;
x_143 = x_187;
x_144 = x_184;
x_145 = x_188;
x_146 = x_185;
x_147 = x_195;
goto block_181;
}
else
{
lean_object* x_196; 
x_196 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10));
x_139 = x_183;
x_140 = x_186;
x_141 = x_182;
x_142 = x_193;
x_143 = x_187;
x_144 = x_184;
x_145 = x_188;
x_146 = x_185;
x_147 = x_196;
goto block_181;
}
}
block_223:
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; size_t x_211; size_t x_212; lean_object* x_213; 
x_208 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_208, 0, x_198);
lean_ctor_set(x_208, 1, x_138);
x_209 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__10, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__10_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__10);
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_array_size(x_206);
x_212 = 0;
lean_inc(x_203);
lean_inc_ref(x_199);
lean_inc(x_204);
lean_inc_ref(x_205);
lean_inc(x_202);
lean_inc_ref(x_201);
lean_inc(x_5);
x_213 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__13(x_6, x_5, x_207, x_200, x_7, x_8, x_206, x_211, x_212, x_210, x_201, x_202, x_205, x_204, x_199, x_203);
lean_dec_ref(x_206);
lean_dec(x_200);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
lean_dec_ref(x_213);
x_182 = x_214;
x_183 = x_201;
x_184 = x_202;
x_185 = x_205;
x_186 = x_204;
x_187 = x_199;
x_188 = x_203;
goto block_197;
}
else
{
lean_object* x_215; lean_object* x_216; uint8_t x_217; uint8_t x_222; 
lean_dec_ref(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec_ref(x_201);
lean_dec_ref(x_199);
lean_dec(x_5);
x_215 = lean_ctor_get(x_213, 0);
x_222 = !lean_is_exclusive(x_213);
if (x_222 == 0)
{
x_216 = x_213;
x_217 = x_222;
goto block_221;
}
else
{
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_box(0);
x_217 = x_222;
goto block_221;
}
block_221:
{
lean_object* x_218; 
if (x_217 == 0)
{
x_218 = x_216;
goto block_219;
}
else
{
lean_object* x_220; 
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_215);
x_218 = x_220;
goto block_219;
}
block_219:
{
return x_218;
}
}
}
}
block_243:
{
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
lean_dec_ref(x_233);
x_198 = x_224;
x_199 = x_226;
x_200 = x_225;
x_201 = x_227;
x_202 = x_228;
x_203 = x_229;
x_204 = x_230;
x_205 = x_232;
x_206 = x_231;
x_207 = x_234;
goto block_223;
}
else
{
lean_object* x_235; lean_object* x_236; uint8_t x_237; uint8_t x_242; 
lean_dec_ref(x_232);
lean_dec_ref(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec_ref(x_226);
lean_dec(x_225);
lean_dec_ref(x_224);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_235 = lean_ctor_get(x_233, 0);
x_242 = !lean_is_exclusive(x_233);
if (x_242 == 0)
{
x_236 = x_233;
x_237 = x_242;
goto block_241;
}
else
{
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_box(0);
x_237 = x_242;
goto block_241;
}
block_241:
{
lean_object* x_238; 
if (x_237 == 0)
{
x_238 = x_236;
goto block_239;
}
else
{
lean_object* x_240; 
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_235);
x_238 = x_240;
goto block_239;
}
block_239:
{
return x_238;
}
}
}
}
block_282:
{
lean_object* x_245; lean_object* x_246; 
x_245 = l_Lean_mkFlatCtorOfStructCtorName(x_9);
lean_inc_ref(x_17);
lean_inc_ref(x_13);
x_246 = l_Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8(x_245, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_dec_ref(x_246);
x_248 = l_Lean_ConstantInfo_type(x_247);
lean_dec(x_247);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_249 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9___redArg(x_248, x_10, x_1, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_dec_ref(x_249);
lean_inc(x_5);
lean_inc_ref(x_6);
x_251 = l_Lean_getStructureFieldsFlattened(x_6, x_5, x_1);
x_252 = lean_array_get_size(x_251);
x_253 = lean_unsigned_to_nat(0u);
x_254 = lean_nat_dec_eq(x_252, x_253);
if (x_254 == 0)
{
uint8_t x_255; 
x_255 = lean_nat_dec_lt(x_253, x_252);
if (x_255 == 0)
{
lean_dec_ref(x_12);
x_198 = x_244;
x_199 = x_17;
x_200 = x_250;
x_201 = x_13;
x_202 = x_14;
x_203 = x_18;
x_204 = x_16;
x_205 = x_15;
x_206 = x_251;
x_207 = x_132;
goto block_223;
}
else
{
uint8_t x_256; 
x_256 = lean_nat_dec_le(x_252, x_252);
if (x_256 == 0)
{
if (x_255 == 0)
{
lean_dec_ref(x_12);
x_198 = x_244;
x_199 = x_17;
x_200 = x_250;
x_201 = x_13;
x_202 = x_14;
x_203 = x_18;
x_204 = x_16;
x_205 = x_15;
x_206 = x_251;
x_207 = x_132;
goto block_223;
}
else
{
size_t x_257; size_t x_258; lean_object* x_259; 
x_257 = 0;
x_258 = lean_usize_of_nat(x_252);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
x_259 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__14___redArg(x_12, x_251, x_257, x_258, x_132, x_15, x_16, x_17, x_18);
x_224 = x_244;
x_225 = x_250;
x_226 = x_17;
x_227 = x_13;
x_228 = x_14;
x_229 = x_18;
x_230 = x_16;
x_231 = x_251;
x_232 = x_15;
x_233 = x_259;
goto block_243;
}
}
else
{
size_t x_260; size_t x_261; lean_object* x_262; 
x_260 = 0;
x_261 = lean_usize_of_nat(x_252);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
x_262 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__14___redArg(x_12, x_251, x_260, x_261, x_132, x_15, x_16, x_17, x_18);
x_224 = x_244;
x_225 = x_250;
x_226 = x_17;
x_227 = x_13;
x_228 = x_14;
x_229 = x_18;
x_230 = x_16;
x_231 = x_251;
x_232 = x_15;
x_233 = x_262;
goto block_243;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec_ref(x_251);
lean_dec(x_250);
lean_dec_ref(x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
x_263 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_263, 0, x_244);
lean_ctor_set(x_263, 1, x_138);
x_264 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__13, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__13_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___closed__13);
x_265 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
x_182 = x_265;
x_183 = x_13;
x_184 = x_14;
x_185 = x_15;
x_186 = x_16;
x_187 = x_17;
x_188 = x_18;
goto block_197;
}
}
else
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; uint8_t x_273; 
lean_dec_ref(x_244);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_266 = lean_ctor_get(x_249, 0);
x_273 = !lean_is_exclusive(x_249);
if (x_273 == 0)
{
x_267 = x_249;
x_268 = x_273;
goto block_272;
}
else
{
lean_inc(x_266);
lean_dec(x_249);
x_267 = lean_box(0);
x_268 = x_273;
goto block_272;
}
block_272:
{
lean_object* x_269; 
if (x_268 == 0)
{
x_269 = x_267;
goto block_270;
}
else
{
lean_object* x_271; 
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_266);
x_269 = x_271;
goto block_270;
}
block_270:
{
return x_269;
}
}
}
}
else
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; uint8_t x_281; 
lean_dec_ref(x_244);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_274 = lean_ctor_get(x_246, 0);
x_281 = !lean_is_exclusive(x_246);
if (x_281 == 0)
{
x_275 = x_246;
x_276 = x_281;
goto block_280;
}
else
{
lean_inc(x_274);
lean_dec(x_246);
x_275 = lean_box(0);
x_276 = x_281;
goto block_280;
}
block_280:
{
lean_object* x_277; 
if (x_276 == 0)
{
x_277 = x_275;
goto block_278;
}
else
{
lean_object* x_279; 
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_274);
x_277 = x_279;
goto block_278;
}
block_278:
{
return x_277;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox(x_1);
x_21 = lean_unbox(x_3);
x_22 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2(x_20, x_2, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec_ref(x_8);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16_spec__25___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, lean_box(0));
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16_spec__25___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16_spec__25___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16_spec__25___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16_spec__25___redArg___lam__0___boxed), 9, 3);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_13, x_5, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_15 = lean_ctor_get(x_14, 0);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
x_16 = x_14;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16_spec__25___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
x_14 = lean_unbox(x_5);
x_15 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16_spec__25___redArg(x_1, x_13, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = 0;
x_13 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16_spec__25___redArg(x_1, x_11, x_2, x_3, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_Expr_const___override(x_1, x_2);
x_20 = lean_box(x_3);
x_21 = lean_box(x_5);
lean_inc_ref(x_10);
lean_inc_ref(x_19);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__2___boxed), 19, 11);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_4);
lean_closure_set(x_22, 2, x_21);
lean_closure_set(x_22, 3, x_19);
lean_closure_set(x_22, 4, x_1);
lean_closure_set(x_22, 5, x_6);
lean_closure_set(x_22, 6, x_2);
lean_closure_set(x_22, 7, x_10);
lean_closure_set(x_22, 8, x_7);
lean_closure_set(x_22, 9, x_8);
lean_closure_set(x_22, 10, x_9);
x_23 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__3___closed__1));
x_24 = l_Lean_mkAppN(x_19, x_10);
lean_dec_ref(x_10);
x_25 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16___redArg(x_23, x_24, x_22, x_12, x_13, x_14, x_15, x_16, x_17);
return x_25;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_3);
x_20 = lean_unbox(x_5);
x_21 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__3(x_1, x_2, x_19, x_4, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec_ref(x_11);
return x_21;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
x_6 = x_1;
x_7 = x_14;
goto block_13;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Level_param___override(x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_8);
x_9 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
x_9 = x_12;
goto block_11;
}
block_11:
{
x_1 = x_5;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_48; 
x_10 = lean_st_ref_get(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
lean_inc(x_3);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__0___boxed), 10, 1);
lean_closure_set(x_12, 0, x_3);
lean_inc(x_1);
lean_inc_ref(x_11);
x_13 = lean_is_class(x_11, x_1);
x_14 = 1;
if (x_13 == 0)
{
lean_object* x_52; 
x_52 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__0));
x_48 = x_52;
goto block_51;
}
else
{
lean_object* x_53; 
x_53 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__1));
x_48 = x_53;
goto block_51;
}
block_47:
{
uint8_t x_17; lean_object* x_18; 
x_17 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_18 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(x_15, x_1, x_2, x_4, x_16, x_17, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc_ref(x_7);
lean_inc(x_1);
x_20 = l_Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0(x_1, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_box(0);
x_23 = l_List_mapTR_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__2(x_2, x_22);
x_24 = lean_box(x_17);
x_25 = lean_box(x_14);
x_26 = lean_alloc_closure((void*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___lam__3___boxed), 18, 9);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_23);
lean_closure_set(x_26, 2, x_24);
lean_closure_set(x_26, 3, x_19);
lean_closure_set(x_26, 4, x_25);
lean_closure_set(x_26, 5, x_11);
lean_closure_set(x_26, 6, x_5);
lean_closure_set(x_26, 7, x_12);
lean_closure_set(x_26, 8, x_3);
x_27 = l_Lean_ConstantInfo_type(x_21);
lean_dec(x_21);
x_28 = lean_box(x_17);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__9___boxed), 11, 4);
lean_closure_set(x_29, 0, lean_box(0));
lean_closure_set(x_29, 1, x_27);
lean_closure_set(x_29, 2, x_26);
lean_closure_set(x_29, 3, x_28);
x_30 = l_Lean_Elab_Command_liftTermElabM___redArg(x_29, x_7, x_8);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_19);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_ctor_get(x_20, 0);
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
x_32 = x_20;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_ctor_get(x_18, 0);
x_46 = !lean_is_exclusive(x_18);
if (x_46 == 0)
{
x_40 = x_18;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_18);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
block_51:
{
if (x_6 == 0)
{
uint8_t x_49; 
x_49 = 1;
x_15 = x_48;
x_16 = x_49;
goto block_47;
}
else
{
uint8_t x_50; 
x_50 = 0;
x_15 = x_48;
x_16 = x_50;
goto block_47;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
x_11 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__1___redArg(x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10_spec__14___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_panic_fn(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__10(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__14(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__14___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__14(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__15___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__15(x_1, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16_spec__25(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16_spec__25___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16_spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
x_15 = lean_unbox(x_6);
x_16 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16_spec__25(x_1, x_2, x_14, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__19(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__19___redArg(x_1, x_2, x_3, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_instantiateStructDefaultValueFn_x3f___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__11_spec__19(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0_spec__5___redArg(x_1, x_2, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__0_spec__0_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_4);
x_14 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__5_spec__6_spec__10(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___redArg(x_1, x_2, x_6, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__36(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__36___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__36(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__35(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__35___redArg(x_1, x_2, x_3, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__35___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__35(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__55_spec__61(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__55_spec__61___redArg(x_1, x_2, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__55_spec__61___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__55_spec__61(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__56(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__56___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__56___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__8_spec__11_spec__19_spec__43_spec__56(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__27_spec__34_spec__39(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__57(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__57___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__58(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__57_spec__59(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__15_spec__40_spec__52_spec__57_spec__59___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_st_ref_get(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = 0;
lean_inc(x_2);
lean_inc_ref(x_7);
x_9 = l_Lean_Environment_find_x3f(x_7, x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec_ref(x_7);
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId(x_2, x_3, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_105; 
x_11 = lean_ctor_get(x_9, 0);
x_105 = !lean_is_exclusive(x_9);
if (x_105 == 0)
{
x_12 = x_9;
x_13 = x_105;
goto block_104;
}
else
{
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = x_105;
goto block_104;
}
block_104:
{
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_27; 
lean_del_object(x_12);
x_14 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_18);
lean_dec_ref(x_15);
lean_inc(x_2);
x_27 = l_Lean_getOriginalConstKind_x3f(x_7, x_2);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
switch (x_29) {
case 0:
{
lean_object* x_30; lean_object* x_31; 
x_30 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__1));
x_31 = lean_box(0);
if (x_16 == 0)
{
uint8_t x_32; lean_object* x_33; 
x_32 = 1;
x_33 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(x_1, x_30, x_2, x_17, x_18, x_31, x_32, x_3, x_4);
return x_33;
}
else
{
uint8_t x_34; lean_object* x_35; 
x_34 = 0;
x_35 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(x_1, x_30, x_2, x_17, x_18, x_31, x_34, x_3, x_4);
return x_35;
}
}
case 1:
{
lean_object* x_36; lean_object* x_37; 
x_36 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__2));
x_37 = lean_box(0);
if (x_16 == 0)
{
uint8_t x_38; lean_object* x_39; 
x_38 = 1;
x_39 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(x_1, x_36, x_2, x_17, x_18, x_37, x_38, x_3, x_4);
return x_39;
}
else
{
uint8_t x_40; lean_object* x_41; 
x_40 = 0;
x_41 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(x_1, x_36, x_2, x_17, x_18, x_37, x_40, x_3, x_4);
return x_41;
}
}
default: 
{
x_19 = x_3;
x_20 = x_4;
goto block_26;
}
}
}
else
{
lean_dec(x_27);
x_19 = x_3;
x_20 = x_4;
goto block_26;
}
block_26:
{
lean_object* x_21; 
x_21 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__0));
if (x_16 == 0)
{
uint8_t x_22; lean_object* x_23; 
x_22 = 1;
x_23 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_21, x_2, x_17, x_18, x_22, x_19, x_20);
return x_23;
}
else
{
uint8_t x_24; lean_object* x_25; 
x_24 = 0;
x_25 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_21, x_2, x_17, x_18, x_24, x_19, x_20);
return x_25;
}
}
}
case 1:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_7);
x_42 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_42);
lean_dec_ref(x_11);
x_43 = lean_ctor_get(x_42, 0);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc_ref(x_44);
x_45 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
lean_dec_ref(x_42);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 2);
lean_inc_ref(x_47);
lean_dec_ref(x_43);
x_48 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__1));
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_44);
x_49 = x_12;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_44);
x_49 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_50; 
x_50 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(x_1, x_48, x_2, x_46, x_47, x_49, x_45, x_3, x_4);
return x_50;
}
}
case 2:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_7);
x_53 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_53);
lean_dec_ref(x_11);
x_54 = lean_ctor_get(x_53, 0);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc_ref(x_55);
lean_dec_ref(x_53);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 2);
lean_inc_ref(x_57);
lean_dec_ref(x_54);
x_58 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__2));
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_55);
x_59 = x_12;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_55);
x_59 = x_63;
goto block_62;
}
block_62:
{
uint8_t x_60; lean_object* x_61; 
x_60 = 1;
x_61 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(x_1, x_58, x_2, x_56, x_57, x_59, x_60, x_3, x_4);
return x_61;
}
}
case 3:
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_del_object(x_12);
lean_dec_ref(x_7);
x_64 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_64);
lean_dec_ref(x_11);
x_65 = lean_ctor_get(x_64, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get_uint8(x_64, sizeof(void*)*3);
lean_dec_ref(x_64);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_68);
lean_dec_ref(x_65);
x_69 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__3));
if (x_66 == 0)
{
uint8_t x_70; lean_object* x_71; 
x_70 = 1;
x_71 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_69, x_2, x_67, x_68, x_70, x_3, x_4);
return x_71;
}
else
{
uint8_t x_72; lean_object* x_73; 
x_72 = 0;
x_73 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_69, x_2, x_67, x_68, x_72, x_3, x_4);
return x_73;
}
}
case 4:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_del_object(x_12);
lean_dec_ref(x_7);
x_74 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_74);
lean_dec_ref(x_11);
x_75 = lean_ctor_get(x_74, 0);
lean_inc_ref(x_75);
lean_dec_ref(x_74);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 2);
lean_inc_ref(x_77);
lean_dec_ref(x_75);
x_78 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot(x_2, x_76, x_77, x_3, x_4);
return x_78;
}
case 5:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_del_object(x_12);
x_79 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_79);
lean_dec_ref(x_11);
x_80 = lean_ctor_get(x_79, 0);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 4);
lean_inc(x_82);
x_83 = lean_ctor_get_uint8(x_79, sizeof(void*)*6 + 1);
lean_dec_ref(x_79);
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 2);
lean_inc_ref(x_85);
lean_dec_ref(x_80);
lean_inc(x_2);
x_86 = l_Lean_isStructure(x_7, x_2);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct(x_2, x_84, x_81, x_85, x_82, x_83, x_3, x_4);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_box(0);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_List_get_x21Internal___redArg(x_88, x_82, x_89);
lean_dec(x_82);
x_91 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure(x_2, x_84, x_81, x_85, x_90, x_83, x_3, x_4);
return x_91;
}
}
case 6:
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_del_object(x_12);
lean_dec_ref(x_7);
x_92 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_92);
lean_dec_ref(x_11);
x_93 = lean_ctor_get(x_92, 0);
lean_inc_ref(x_93);
x_94 = lean_ctor_get_uint8(x_92, sizeof(void*)*5);
lean_dec_ref(x_92);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 2);
lean_inc_ref(x_96);
lean_dec_ref(x_93);
x_97 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__4));
if (x_94 == 0)
{
uint8_t x_98; lean_object* x_99; 
x_98 = 1;
x_99 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_97, x_2, x_95, x_96, x_98, x_3, x_4);
return x_99;
}
else
{
uint8_t x_100; lean_object* x_101; 
x_100 = 0;
x_101 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_97, x_2, x_95, x_96, x_100, x_3, x_4);
return x_101;
}
}
default: 
{
lean_object* x_102; lean_object* x_103; 
lean_del_object(x_12);
lean_dec_ref(x_7);
lean_dec(x_2);
x_102 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_102);
lean_dec_ref(x_11);
x_103 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printRecursor(x_102, x_3, x_4);
return x_103;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore(x_6, x_2, x_3, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = 0;
lean_inc_ref(x_2);
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore(x_9, x_7, x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_dec_ref(x_10);
x_1 = x_8;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_2);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 8);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
lean_dec_ref(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_42; 
x_9 = lean_st_ref_take(x_2);
x_10 = lean_ctor_get(x_9, 8);
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_16 = lean_ctor_get(x_9, 5);
x_17 = lean_ctor_get(x_9, 6);
x_18 = lean_ctor_get(x_9, 7);
x_19 = lean_ctor_get(x_9, 9);
x_20 = lean_ctor_get(x_9, 10);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
x_21 = x_9;
x_22 = x_42;
goto block_41;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_10);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_21 = lean_box(0);
x_22 = x_42;
goto block_41;
}
block_41:
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_40; 
x_23 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
x_26 = lean_ctor_get(x_10, 2);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
x_27 = x_10;
x_28 = x_40;
goto block_39;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_27 = lean_box(0);
x_28 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_PersistentArray_push___redArg(x_26, x_1);
if (x_28 == 0)
{
lean_ctor_set(x_27, 2, x_29);
x_30 = x_27;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_25);
lean_ctor_set(x_38, 2, x_29);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_23);
x_30 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_31; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 8, x_30);
x_31 = x_21;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_36, 0, x_11);
lean_ctor_set(x_36, 1, x_12);
lean_ctor_set(x_36, 2, x_13);
lean_ctor_set(x_36, 3, x_14);
lean_ctor_set(x_36, 4, x_15);
lean_ctor_set(x_36, 5, x_16);
lean_ctor_set(x_36, 6, x_17);
lean_ctor_set(x_36, 7, x_18);
lean_ctor_set(x_36, 8, x_30);
lean_ctor_set(x_36, 9, x_19);
lean_ctor_set(x_36, 10, x_20);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_st_ref_set(x_2, x_31);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0___closed__1(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0___closed__0);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 8);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
lean_dec_ref(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0___closed__1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0_spec__1___redArg(x_11, x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0(x_5, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__0, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__0_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__0___redArg___closed__4);
x_3 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__1, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__1_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Lean_Syntax_getId(x_1);
x_6 = 0;
x_7 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__2, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__2_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__2);
x_8 = lean_box(0);
lean_inc(x_1);
x_9 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_6);
x_10 = l_Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0(x_9, x_2, x_3);
lean_dec_ref(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_realizeGlobalConstWithInfos___boxed), 5, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_8);
lean_inc_ref(x_2);
x_12 = l_Lean_Elab_Command_liftCoreM___redArg(x_11, x_2, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_List_forM___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__1(x_13, x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
lean_dec_ref(x_2);
x_15 = lean_ctor_get(x_12, 0);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
x_16 = x_12;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0_spec__1___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0_spec__0_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Command_elabPrint_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = 0;
x_7 = 0;
x_8 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0_spec__0_spec__1(x_1, x_2, x_6, x_7, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Command_elabPrint_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_logInfoAt___at___00Lean_Elab_Command_elabPrint_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabPrint___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrint(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l_Lean_Elab_Command_elabPrint___closed__4));
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_obj_once(&l_Lean_Elab_Command_elabPrint___closed__6, &l_Lean_Elab_Command_elabPrint___closed__6_once, _init_l_Lean_Elab_Command_elabPrint___closed__6);
x_8 = l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0___redArg(x_7, x_2, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = ((lean_object*)(l_Lean_Elab_Command_elabPrint___closed__8));
lean_inc(x_12);
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = ((lean_object*)(l_Lean_Elab_Command_elabPrint___closed__10));
lean_inc(x_12);
x_16 = l_Lean_Syntax_isOfKind(x_12, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_10);
x_17 = lean_obj_once(&l_Lean_Elab_Command_elabPrint___closed__6, &l_Lean_Elab_Command_elabPrint___closed__6_once, _init_l_Lean_Elab_Command_elabPrint___closed__6);
x_18 = l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0___redArg(x_17, x_2, x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_TSyntax_getString(x_12);
lean_dec(x_12);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_MessageData_ofFormat(x_20);
x_22 = l_Lean_logInfoAt___at___00Lean_Elab_Command_elabPrint_spec__0(x_10, x_21, x_2, x_3);
lean_dec(x_10);
return x_22;
}
}
else
{
lean_object* x_23; 
x_23 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_43; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get(x_2, 3);
x_29 = lean_ctor_get(x_2, 4);
x_30 = lean_ctor_get(x_2, 5);
x_31 = lean_ctor_get(x_2, 6);
x_32 = lean_ctor_get(x_2, 8);
x_33 = lean_ctor_get(x_2, 9);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_43 = !lean_is_exclusive(x_2);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_2, 7);
lean_dec(x_44);
x_35 = x_2;
x_36 = x_43;
goto block_42;
}
else
{
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_35 = lean_box(0);
x_36 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_replaceRef(x_10, x_24);
lean_dec(x_24);
lean_dec(x_10);
if (x_36 == 0)
{
lean_ctor_set(x_35, 7, x_37);
x_38 = x_35;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_41, 0, x_25);
lean_ctor_set(x_41, 1, x_26);
lean_ctor_set(x_41, 2, x_27);
lean_ctor_set(x_41, 3, x_28);
lean_ctor_set(x_41, 4, x_29);
lean_ctor_set(x_41, 5, x_30);
lean_ctor_set(x_41, 6, x_31);
lean_ctor_set(x_41, 7, x_37);
lean_ctor_set(x_41, 8, x_32);
lean_ctor_set(x_41, 9, x_33);
lean_ctor_set_uint8(x_41, sizeof(void*)*10, x_34);
x_38 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_39; 
x_39 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(x_12, x_38, x_3);
return x_39;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_2);
x_45 = lean_ctor_get(x_23, 0);
x_52 = !lean_is_exclusive(x_23);
if (x_52 == 0)
{
x_46 = x_23;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_23);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabPrint(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Command_elabPrint___closed__4));
x_4 = ((lean_object*)(l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabPrint___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___closed__6));
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3();
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printIdSig_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = 1;
lean_inc_ref(x_2);
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore(x_9, x_7, x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_dec_ref(x_10);
x_1 = x_8;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_2);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printIdSig_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printIdSig_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdSig(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = l_Lean_Syntax_getId(x_1);
x_6 = 0;
x_7 = lean_unsigned_to_nat(32u);
x_8 = lean_mk_empty_array_with_capacity(x_7);
lean_dec_ref(x_8);
x_9 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__2, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__2_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__2);
x_10 = lean_box(0);
lean_inc(x_1);
x_11 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*4, x_6);
x_12 = l_Lean_Elab_addCompletionInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printId_spec__0(x_11, x_2, x_3);
lean_dec_ref(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_realizeGlobalConstWithInfos___boxed), 5, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_10);
lean_inc_ref(x_2);
x_14 = l_Lean_Elab_Command_liftCoreM___redArg(x_13, x_2, x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_List_forM___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printIdSig_spec__0(x_15, x_2, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
lean_dec_ref(x_2);
x_17 = lean_ctor_get(x_14, 0);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
x_18 = x_14;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdSig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdSig(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintSig(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; uint8_t x_29; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_29 = !lean_is_exclusive(x_2);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_2, 7);
lean_dec(x_30);
x_17 = x_2;
x_18 = x_29;
goto block_28;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = l_Lean_replaceRef(x_20, x_6);
lean_dec(x_6);
lean_dec(x_20);
if (x_18 == 0)
{
lean_ctor_set(x_17, 7, x_23);
x_24 = x_17;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_8);
lean_ctor_set(x_27, 2, x_9);
lean_ctor_set(x_27, 3, x_10);
lean_ctor_set(x_27, 4, x_11);
lean_ctor_set(x_27, 5, x_12);
lean_ctor_set(x_27, 6, x_13);
lean_ctor_set(x_27, 7, x_23);
lean_ctor_set(x_27, 8, x_14);
lean_ctor_set(x_27, 9, x_15);
lean_ctor_set_uint8(x_27, sizeof(void*)*10, x_16);
x_24 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_25; 
x_25 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdSig(x_22, x_24, x_3);
return x_25;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec_ref(x_2);
x_31 = lean_ctor_get(x_5, 0);
x_38 = !lean_is_exclusive(x_5);
if (x_38 == 0)
{
x_32 = x_5;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintSig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabPrintSig(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__1));
x_4 = ((lean_object*)(l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___closed__3));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabPrintSig___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1();
return x_2;
}
}
static lean_object* _init_l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__30___closed__0));
x_2 = l_Lean_NameSet_empty;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_obj_once(&l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0___redArg___closed__0, &l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0___redArg___closed__0_once, _init_l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0___redArg___closed__0);
x_7 = l_Lean_CollectAxioms_collect(x_1, x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_1, x_6);
x_8 = lean_array_uget(x_4, x_3);
x_9 = lean_array_uset(x_4, x_3, x_6);
x_10 = l_Lean_MessageData_ofConstName(x_8, x_7);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_9, x_3, x_10);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_13; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
x_6 = x_1;
x_7 = x_13;
goto block_12;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_8; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
x_8 = x_6;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_2);
x_8 = x_11;
goto block_10;
}
block_10:
{
x_1 = x_5;
x_2 = x_8;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_5 = l_Lean_collectAxioms___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__0___redArg(x_1, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_26; lean_object* x_27; 
x_10 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1);
x_11 = l_Lean_MessageData_ofName(x_1);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
if (x_9 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_35; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_7, x_30);
x_35 = lean_nat_dec_le(x_8, x_31);
if (x_35 == 0)
{
lean_inc(x_31);
x_32 = x_31;
goto block_34;
}
else
{
x_32 = x_8;
goto block_34;
}
block_34:
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_32, x_31);
if (x_33 == 0)
{
lean_dec(x_31);
lean_inc(x_32);
x_26 = x_32;
x_27 = x_32;
goto block_29;
}
else
{
x_26 = x_32;
x_27 = x_31;
goto block_29;
}
}
}
else
{
x_15 = x_6;
goto block_25;
}
block_25:
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_array_size(x_15);
x_17 = 0;
x_18 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__1(x_7, x_16, x_17, x_15);
x_19 = lean_array_to_list(x_18);
x_20 = lean_box(0);
x_21 = l_List_mapTR_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_spec__2(x_19, x_20);
x_22 = l_Lean_MessageData_ofList(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0(x_23, x_2, x_3);
return x_24;
}
block_29:
{
lean_object* x_28; 
x_28 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_spec__6_spec__8_spec__14_spec__36___redArg(x_6, x_26, x_27);
lean_dec(x_27);
x_15 = x_28;
goto block_25;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_6);
x_36 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1);
x_37 = l_Lean_MessageData_ofName(x_1);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__5, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__5_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__5);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0(x_40, x_2, x_3);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabPrintAxioms_spec__0___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabPrintAxioms_spec__0___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabPrintAxioms_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabPrintAxioms_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabPrintAxioms_spec__0___redArg___closed__0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabPrintAxioms_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabPrintAxioms_spec__0___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabPrintAxioms_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabPrintAxioms_spec__0___redArg();
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabPrintAxioms_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabPrintAxioms_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Command_elabPrintAxioms_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_9 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf(x_7, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_dec_ref(x_9);
x_1 = x_8;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Command_elabPrintAxioms_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___at___00Lean_Elab_Command_elabPrintAxioms_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrintAxioms___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabPrintAxioms___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintAxioms(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l_Lean_Elab_Command_elabPrintAxioms___closed__1));
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabPrintAxioms_spec__0___redArg();
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; uint8_t x_53; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_st_ref_get(x_3);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_2, 3);
x_15 = lean_ctor_get(x_2, 4);
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_ctor_get(x_2, 6);
x_18 = lean_ctor_get(x_2, 8);
x_19 = lean_ctor_get(x_2, 9);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_53 = !lean_is_exclusive(x_2);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_2, 7);
lean_dec(x_54);
x_21 = x_2;
x_22 = x_53;
goto block_52;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_46; lean_object* x_47; 
x_23 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_23);
lean_dec(x_10);
x_24 = l_Lean_Environment_header(x_23);
lean_dec_ref(x_23);
x_25 = lean_ctor_get_uint8(x_24, sizeof(void*)*7 + 4);
lean_dec_ref(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Syntax_getArg(x_1, x_26);
x_28 = lean_unsigned_to_nat(2u);
x_29 = l_Lean_Syntax_getArg(x_1, x_28);
lean_dec(x_1);
x_46 = l_Lean_replaceRef(x_27, x_9);
lean_dec(x_9);
lean_dec(x_27);
if (x_22 == 0)
{
lean_ctor_set(x_21, 7, x_46);
x_47 = x_21;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_51, 0, x_11);
lean_ctor_set(x_51, 1, x_12);
lean_ctor_set(x_51, 2, x_13);
lean_ctor_set(x_51, 3, x_14);
lean_ctor_set(x_51, 4, x_15);
lean_ctor_set(x_51, 5, x_16);
lean_ctor_set(x_51, 6, x_17);
lean_ctor_set(x_51, 7, x_46);
lean_ctor_set(x_51, 8, x_18);
lean_ctor_set(x_51, 9, x_19);
lean_ctor_set_uint8(x_51, sizeof(void*)*10, x_20);
x_47 = x_51;
goto block_50;
}
block_45:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_box(0);
x_33 = lean_alloc_closure((void*)(l_Lean_Elab_realizeGlobalConstWithInfos___boxed), 5, 2);
lean_closure_set(x_33, 0, x_29);
lean_closure_set(x_33, 1, x_32);
lean_inc_ref(x_30);
x_34 = l_Lean_Elab_Command_liftCoreM___redArg(x_33, x_30, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_List_forM___at___00Lean_Elab_Command_elabPrintAxioms_spec__1(x_35, x_30, x_31);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec_ref(x_30);
x_37 = lean_ctor_get(x_34, 0);
x_44 = !lean_is_exclusive(x_34);
if (x_44 == 0)
{
x_38 = x_34;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
block_50:
{
if (x_25 == 0)
{
x_30 = x_47;
x_31 = x_3;
goto block_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_29);
x_48 = lean_obj_once(&l_Lean_Elab_Command_elabPrintAxioms___closed__3, &l_Lean_Elab_Command_elabPrintAxioms___closed__3_once, _init_l_Lean_Elab_Command_elabPrintAxioms___closed__3);
x_49 = l_Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0___redArg(x_48, x_47, x_3);
return x_49;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_8, 0);
x_62 = !lean_is_exclusive(x_8);
if (x_62 == 0)
{
x_56 = x_8;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_8);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintAxioms___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabPrintAxioms(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Command_elabPrintAxioms___closed__1));
x_4 = ((lean_object*)(l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__1));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabPrintAxioms___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___closed__6));
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getEqnsFor_x3f(x_1, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_5);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget_borrowed(x_1, x_3);
lean_inc_ref(x_5);
lean_inc(x_10);
x_11 = l_Lean_getConstInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct_spec__0(x_10, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__2));
x_14 = l_Lean_ConstantInfo_levelParams(x_12);
x_15 = l_Lean_ConstantInfo_type(x_12);
lean_dec(x_12);
x_16 = 1;
lean_inc(x_10);
x_17 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(x_13, x_10, x_14, x_15, x_16, x_8, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId_spec__0_spec__1_spec__3___closed__0);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
x_4 = x_21;
goto _start;
}
else
{
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_17;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_25 = lean_ctor_get(x_11, 0);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
x_26 = x_11;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf_spec__0(x_1, x_8, x_9, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___lam__0___boxed), 8, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc_ref(x_2);
x_6 = l_Lean_Elab_Command_liftTermElabM___redArg(x_5, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__1, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__1_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__1);
x_10 = lean_array_size(x_8);
x_11 = 0;
lean_inc_ref(x_2);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf_spec__0(x_8, x_10, x_11, x_9, x_2, x_3);
lean_dec(x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0(x_13, x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
lean_dec_ref(x_2);
x_15 = lean_ctor_get(x_12, 0);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
x_16 = x_12;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_7);
x_23 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1);
x_24 = l_Lean_MessageData_ofName(x_1);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_obj_once(&l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__3, &l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__3_once, _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__3);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_logInfo___at___00__private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike_spec__0(x_27, x_2, x_3);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_29 = lean_ctor_get(x_6, 0);
x_36 = !lean_is_exclusive(x_6);
if (x_36 == 0)
{
x_30 = x_6;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Command_elabPrintEqns_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_9 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf(x_7, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_dec_ref(x_9);
x_1 = x_8;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Command_elabPrintEqns_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___at___00Lean_Elab_Command_elabPrintEqns_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintEqns(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_realizeGlobalConstWithInfos___boxed), 5, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
lean_inc_ref(x_2);
x_9 = l_Lean_Elab_Command_liftCoreM___redArg(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_List_forM___at___00Lean_Elab_Command_elabPrintEqns_spec__0(x_10, x_2, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
lean_dec_ref(x_2);
x_12 = lean_ctor_get(x_9, 0);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
x_13 = x_9;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintEqns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabPrintEqns(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__1));
x_4 = ((lean_object*)(l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__3));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabPrintEqns___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__3));
x_3 = ((lean_object*)(l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___closed__6));
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3();
return x_2;
}
}
lean_object* runtime_initialize_Lean_Meta_Eqns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter_Delaborator_Builtins(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Print(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Eqns(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Builtins(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabPrint___regBuiltin_Lean_Elab_Command_elabPrint_declRange__3()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabPrintSig___regBuiltin_Lean_Elab_Command_elabPrintSig__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabPrintAxioms___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__3()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabPrintEqns___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__3()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Print(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter_Delaborator_Builtins(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Print(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Eqns(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Delaborator_Builtins(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Print(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Print(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Print(builtin);
}
#ifdef __cplusplus
}
#endif
