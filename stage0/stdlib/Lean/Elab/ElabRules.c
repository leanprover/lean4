// Lean compiler output
// Module: Lean.Elab.ElabRules
// Imports: public import Lean.Elab.MacroArgUtil public import Lean.Elab.AuxDef public import Lean.Elab.Do.Basic
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
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9_value;
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2;
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0_value;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t l_Lean_Elab_Command_checkRuleKind(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "invalid elab_rules alternative, expected syntax node kind `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "invalid elab_rules alternative, unexpected syntax node kind `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isQuot(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabRules"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__4_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__5;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__4_value),LEAN_SCALAR_PTR_LITERAL(187, 124, 47, 85, 21, 141, 50, 117)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.Term.TermElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__9;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "TermElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__11_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "stx"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__15;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__14_value),LEAN_SCALAR_PTR_LITERAL(89, 124, 230, 186, 154, 11, 21, 78)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__16 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__16_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__17 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__17_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__18 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__18_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__19 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__19_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__20 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__20_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__21 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__21_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__22 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__22_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noErrorIfUnused"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__23 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__23_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "no_error_if_unused%"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__24 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__24_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "throwUnsupportedSyntax"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__25 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__25_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__26;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__25_value),LEAN_SCALAR_PTR_LITERAL(225, 251, 194, 35, 13, 152, 147, 184)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__27 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__27_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__28 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__28_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__29 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "aux_def"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__30 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__28_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__30_value),LEAN_SCALAR_PTR_LITERAL(83, 33, 36, 212, 17, 187, 86, 94)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__31 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__31_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_Elab_Command_elabElabRulesAux___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__32 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__32_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.Elab.Command.CommandElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__33 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__33_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__34;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "CommandElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__35 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__35_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Elab.Do.DoElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__36 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__36_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__37;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__38 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__38_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DoElab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__39 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__39_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cont"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__40 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__40_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__41;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__40_value),LEAN_SCALAR_PTR_LITERAL(53, 231, 177, 147, 174, 255, 200, 174)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__42 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__42_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.Tactic.Tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__43 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__43_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__44;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__45 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__45_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expectedType\?"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__46 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__46_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__47;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__46_value),LEAN_SCALAR_PTR_LITERAL(47, 72, 75, 114, 68, 52, 233, 214)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__48 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__48_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__49 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__49_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Elab.Term.withExpectedType"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__50 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__50_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__51;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "withExpectedType"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__52 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__52_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__53 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__53_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__53_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__54 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__54_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doElem"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__55 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__55_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__55_value),LEAN_SCALAR_PTR_LITERAL(224, 169, 39, 82, 97, 101, 60, 174)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__56 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__56_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "syntax category `"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__57 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__57_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__58;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "` does not support expected type specification"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__59 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__59_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__60;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doElem_elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__61 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__61_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__61_value),LEAN_SCALAR_PTR_LITERAL(211, 179, 163, 70, 253, 44, 85, 125)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__62 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__62_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__63 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__63_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__63_value),LEAN_SCALAR_PTR_LITERAL(226, 9, 43, 122, 104, 86, 206, 223)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__64 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__64_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__65 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__65_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__65_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__66 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__66_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__67 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__67_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__67_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__68 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__68_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "conv"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__69 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__69_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__69_value),LEAN_SCALAR_PTR_LITERAL(232, 67, 39, 189, 45, 247, 54, 81)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__70 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__70_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "unsupported syntax category `"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__71 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__71_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__72;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "command_elab"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__73 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__73_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRulesAux___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__73_value),LEAN_SCALAR_PTR_LITERAL(7, 200, 102, 28, 219, 237, 42, 33)}};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__74 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__74_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRulesAux___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "invalid elab_rules command, specify category using `elab_rules : <cat> ...`"};
static const lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__75 = (const lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__75_value;
static lean_once_cell_t l_Lean_Elab_Command_elabElabRulesAux___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__76;
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Parser_Command_visibility_ofAttrKind(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "<="};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__1___closed__3_value;
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
lean_object* l_Array_mkArray5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elab_rules"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 70, 226, 250, 127, 121, 118, 247)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__22_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value;
lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Command_resolveSyntaxKind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Command_elabElabRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_elabElabRules___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Command_elabElabRules___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___closed__0_value;
static const lean_closure_object l_Lean_Elab_Command_elabElabRules___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_elabElabRules___lam__2___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___closed__0_value)} };
static const lean_object* l_Lean_Elab_Command_elabElabRules___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___closed__1_value;
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "elabElabRules"};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__28_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 97, 52, 186, 206, 196, 221, 235)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(74) << 1) | 1)),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(81) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0_value),((lean_object*)(((size_t)(37) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1_value),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(74) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(74) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3_value),((lean_object*)(((size_t)(41) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4_value),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6_value;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__1_value;
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__2_value;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__1;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__0_value;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__1_value;
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__12_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__17_value;
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___closed__0;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__0_value;
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__1_value;
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__3_value;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__2_value;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0_value;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`("};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elab"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 177, 45, 203, 60, 20, 245, 118)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedPrio"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__4_value),LEAN_SCALAR_PTR_LITERAL(171, 32, 2, 102, 118, 75, 64, 185)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "priority"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namedName"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__7_value),LEAN_SCALAR_PTR_LITERAL(73, 173, 122, 11, 5, 195, 101, 245)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__8_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__9_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "precedence"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__10_value),LEAN_SCALAR_PTR_LITERAL(69, 243, 176, 51, 48, 112, 202, 160)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__11_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__12_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_elabElab___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabTail"};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___closed__14_value),LEAN_SCALAR_PTR_LITERAL(131, 240, 225, 71, 37, 75, 83, 37)}};
static const lean_object* l_Lean_Elab_Command_elabElab___closed__15 = (const lean_object*)&l_Lean_Elab_Command_elabElab___closed__15_value;
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSyntax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalOptPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elabElab"};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__28_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabElabRulesAux___closed__29_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 235, 135, 254, 44, 234, 233, 9)}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(84) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(84) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(84) << 1) | 1)),((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4_value),((lean_object*)(((size_t)(12) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_getRef___redArg(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_14; 
x_6 = lean_ctor_get(x_5, 0);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
x_7 = x_5;
x_8 = x_14;
goto block_13;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_mkIdentFrom(x_6, x_1, x_2);
lean_dec(x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_9);
x_10 = x_7;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_9);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_5, 0);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
x_16 = x_5;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(x_1, x_5, x_3);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0(x_1, x_6, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = l_Lean_Environment_header(x_4);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0(void) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(x_1, x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_Elab_Command_getRef___redArg(x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_40; 
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_13, 0);
lean_dec(x_41);
x_14 = x_13;
x_15 = x_40;
goto block_39;
}
else
{
lean_dec(x_13);
x_14 = lean_box(0);
x_15 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 5);
x_17 = l_Lean_SourceInfo_fromRef(x_12, x_8);
lean_dec(x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_38; 
x_38 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_6);
lean_dec_ref(x_38);
goto block_37;
}
else
{
goto block_37;
}
block_37:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4));
x_19 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7));
x_20 = lean_mk_syntax_ident(x_4);
x_21 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
lean_inc(x_17);
x_22 = l_Lean_Syntax_node1(x_17, x_21, x_10);
lean_inc(x_17);
x_23 = l_Lean_Syntax_node2(x_17, x_19, x_20, x_22);
x_24 = l_Lean_Syntax_node2(x_17, x_18, x_2, x_23);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_mk_empty_array_with_capacity(x_25);
x_27 = lean_array_push(x_26, x_24);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_27);
x_28 = x_14;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_3, 0);
x_32 = l_Lean_Syntax_TSepArray_getElems___redArg(x_31);
x_33 = lean_array_push(x_32, x_24);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_33);
x_34 = x_14;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_33);
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
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_42 = lean_ctor_get(x_13, 0);
x_49 = !lean_is_exclusive(x_13);
if (x_49 == 0)
{
x_43 = x_13;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_13);
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
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_50 = lean_ctor_get(x_11, 0);
x_57 = !lean_is_exclusive(x_11);
if (x_57 == 0)
{
x_51 = x_11;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_11);
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
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec(x_4);
lean_dec(x_2);
x_58 = lean_ctor_get(x_9, 0);
x_65 = !lean_is_exclusive(x_9);
if (x_65 == 0)
{
x_59 = x_9;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_9);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(lean_object* x_1, lean_object* x_2) {
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
x_10 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0);
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
x_12 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3);
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
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(x_9, x_10);
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
x_18 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0);
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
x_20 = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_MessageData_ofSyntax(x_15);
x_23 = l_Lean_indentD(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(x_24, x_2);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1);
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3(void) {
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4);
x_3 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(lean_object* x_1, lean_object* x_2) {
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
x_11 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2);
x_12 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(x_1, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_7);
x_10 = l_Lean_Elab_getBetterRef(x_6, x_7);
lean_dec(x_6);
x_11 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(x_9, x_7, x_3);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_22 = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(x_2, x_21, x_4);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec_ref(x_5);
x_7 = lean_box(0);
x_8 = lean_array_uget_borrowed(x_2, x_4);
lean_inc(x_8);
x_9 = l_Lean_Syntax_getKind(x_8);
lean_inc(x_1);
x_10 = l_Lean_Elab_Command_checkRuleKind(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0));
x_12 = 1;
x_13 = lean_usize_add(x_4, x_12);
x_4 = x_13;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
lean_inc(x_8);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_8);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_19; lean_object* x_30; lean_object* x_31; lean_object* x_39; uint8_t x_40; 
x_10 = lean_array_uget(x_4, x_3);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_4, x_3, x_11);
x_39 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5));
lean_inc(x_10);
x_40 = l_Lean_Syntax_isOfKind(x_10, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_10);
x_41 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
x_19 = x_41;
goto block_29;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_unsigned_to_nat(1u);
x_43 = l_Lean_Syntax_getArg(x_10, x_42);
lean_inc(x_43);
x_44 = l_Lean_Syntax_matchesNull(x_43, x_42);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
lean_dec(x_10);
x_45 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
x_19 = x_45;
goto block_29;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_119; 
x_46 = l_Lean_Syntax_getArg(x_43, x_11);
lean_dec(x_43);
x_47 = lean_unsigned_to_nat(3u);
x_48 = l_Lean_Syntax_getArg(x_10, x_47);
x_62 = l_Lean_Syntax_getArgs(x_46);
lean_dec(x_46);
x_63 = lean_box(0);
x_64 = lean_array_get(x_63, x_62, x_11);
x_119 = l_Lean_Syntax_isQuot(x_64);
if (x_119 == 0)
{
if (x_44 == 0)
{
lean_inc_ref(x_5);
x_65 = x_5;
x_66 = x_6;
goto block_118;
}
else
{
lean_object* x_120; 
x_120 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
if (lean_obj_tag(x_120) == 0)
{
lean_dec_ref(x_120);
lean_inc_ref(x_5);
x_65 = x_5;
x_66 = x_6;
goto block_118;
}
else
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_128; 
lean_dec(x_64);
lean_dec_ref(x_62);
lean_dec(x_48);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec(x_1);
x_121 = lean_ctor_get(x_120, 0);
x_128 = !lean_is_exclusive(x_120);
if (x_128 == 0)
{
x_122 = x_120;
x_123 = x_128;
goto block_127;
}
else
{
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_box(0);
x_123 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_124; 
if (x_123 == 0)
{
x_124 = x_122;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_121);
x_124 = x_126;
goto block_125;
}
block_125:
{
return x_124;
}
}
}
}
}
else
{
lean_inc_ref(x_5);
x_65 = x_5;
x_66 = x_6;
goto block_118;
}
block_61:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_51 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(x_50);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
x_54 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
x_55 = l_Array_append___redArg(x_54, x_49);
lean_dec_ref(x_49);
lean_inc(x_50);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_56, 2, x_55);
lean_inc(x_50);
x_57 = l_Lean_Syntax_node1(x_50, x_53, x_56);
x_58 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(x_50);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Syntax_node4(x_50, x_39, x_52, x_57, x_59, x_48);
x_13 = x_60;
goto block_18;
}
block_118:
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_inc(x_64);
x_67 = l_Lean_Syntax_getQuotContent(x_64);
lean_inc(x_67);
x_68 = l_Lean_Syntax_getKind(x_67);
lean_inc(x_1);
x_69 = l_Lean_Elab_Command_checkRuleKind(x_68, x_1);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10));
x_71 = lean_name_eq(x_68, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_67);
lean_dec(x_64);
lean_dec_ref(x_62);
lean_dec(x_48);
x_72 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12);
x_73 = l_Lean_MessageData_ofName(x_68);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(x_10, x_76, x_65, x_66);
lean_dec(x_10);
x_19 = x_77;
goto block_29;
}
else
{
lean_object* x_78; lean_object* x_79; size_t x_80; size_t x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_68);
x_78 = l_Lean_Syntax_getArgs(x_67);
lean_dec(x_67);
x_79 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0));
x_80 = lean_array_size(x_78);
x_81 = 0;
lean_inc(x_1);
x_82 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(x_1, x_78, x_80, x_81, x_79);
lean_dec_ref(x_78);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_dec(x_64);
lean_dec_ref(x_62);
lean_dec(x_48);
x_30 = x_66;
x_31 = x_65;
goto block_38;
}
else
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_dec(x_64);
lean_dec_ref(x_62);
lean_dec(x_48);
x_30 = x_66;
x_31 = x_65;
goto block_38;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_10);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = l_Lean_Elab_Command_getRef___redArg(x_65);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_65);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_88);
x_89 = lean_ctor_get(x_65, 5);
lean_inc(x_89);
lean_dec_ref(x_65);
x_90 = l_Lean_Syntax_setArg(x_64, x_42, x_85);
x_91 = lean_array_set(x_62, x_11, x_90);
x_92 = l_Lean_SourceInfo_fromRef(x_87, x_69);
lean_dec(x_87);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_93; 
x_93 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_66);
if (lean_obj_tag(x_93) == 0)
{
lean_dec_ref(x_93);
x_49 = x_91;
x_50 = x_92;
goto block_61;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_101; 
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_48);
lean_dec_ref(x_12);
lean_dec_ref(x_5);
lean_dec(x_1);
x_94 = lean_ctor_get(x_93, 0);
x_101 = !lean_is_exclusive(x_93);
if (x_101 == 0)
{
x_95 = x_93;
x_96 = x_101;
goto block_100;
}
else
{
lean_inc(x_94);
lean_dec(x_93);
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
lean_dec_ref(x_89);
x_49 = x_91;
x_50 = x_92;
goto block_61;
}
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_109; 
lean_dec(x_87);
lean_dec(x_85);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_62);
lean_dec(x_48);
lean_dec_ref(x_12);
lean_dec_ref(x_5);
lean_dec(x_1);
x_102 = lean_ctor_get(x_88, 0);
x_109 = !lean_is_exclusive(x_88);
if (x_109 == 0)
{
x_103 = x_88;
x_104 = x_109;
goto block_108;
}
else
{
lean_inc(x_102);
lean_dec(x_88);
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
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_117; 
lean_dec(x_85);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_62);
lean_dec(x_48);
lean_dec_ref(x_12);
lean_dec_ref(x_5);
lean_dec(x_1);
x_110 = lean_ctor_get(x_86, 0);
x_117 = !lean_is_exclusive(x_86);
if (x_117 == 0)
{
x_111 = x_86;
x_112 = x_117;
goto block_116;
}
else
{
lean_inc(x_110);
lean_dec(x_86);
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
}
}
else
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_62);
lean_dec(x_48);
x_13 = x_10;
goto block_18;
}
}
}
}
block_18:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_16 = lean_array_uset(x_12, x_3, x_13);
x_3 = x_15;
x_4 = x_16;
goto _start;
}
block_29:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_13 = x_20;
goto block_18;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec_ref(x_12);
lean_dec_ref(x_5);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 0);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
x_22 = x_19;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_19);
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
block_38:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1);
lean_inc(x_1);
x_33 = l_Lean_MessageData_ofName(x_1);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(x_10, x_36, x_31, x_30);
lean_dec(x_10);
x_19 = x_37;
goto block_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(x_1, x_8, x_9, x_4, x_5, x_6);
lean_dec(x_6);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__4));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__8));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__14));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__34(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__33));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__37(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__36));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__41(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__40));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__44(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__43));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__47(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__46));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__51(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__50));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__58(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__57));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__60(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__59));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__72(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__71));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__75));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_array_size(x_7);
x_12 = 0;
lean_inc_ref(x_8);
lean_inc(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(x_4, x_11, x_12, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_1024; 
x_14 = lean_ctor_get(x_13, 0);
x_1024 = !lean_is_exclusive(x_13);
if (x_1024 == 0)
{
x_15 = x_13;
x_16 = x_1024;
goto block_1023;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_1024;
goto block_1023;
}
block_1023:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; uint8_t x_807; lean_object* x_836; lean_object* x_837; lean_object* x_838; 
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_1010; lean_object* x_1011; 
x_1010 = lean_ctor_get(x_5, 0);
x_1011 = l_Lean_TSyntax_getId(x_1010);
x_836 = x_1011;
x_837 = x_8;
x_838 = x_9;
goto block_1009;
}
else
{
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_1012; 
x_1012 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
x_836 = x_1012;
x_837 = x_8;
x_838 = x_9;
goto block_1009;
}
else
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; uint8_t x_1017; uint8_t x_1022; 
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1013 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__76, &l_Lean_Elab_Command_elabElabRulesAux___closed__76_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76);
x_1014 = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(x_1013, x_8, x_9);
x_1015 = lean_ctor_get(x_1014, 0);
x_1022 = !lean_is_exclusive(x_1014);
if (x_1022 == 0)
{
x_1016 = x_1014;
x_1017 = x_1022;
goto block_1021;
}
else
{
lean_inc(x_1015);
lean_dec(x_1014);
x_1016 = lean_box(0);
x_1017 = x_1022;
goto block_1021;
}
block_1021:
{
lean_object* x_1018; 
if (x_1017 == 0)
{
x_1018 = x_1016;
goto block_1019;
}
else
{
lean_object* x_1020; 
x_1020 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1020, 0, x_1015);
x_1018 = x_1020;
goto block_1019;
}
block_1019:
{
return x_1018;
}
}
}
}
block_135:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_inc_ref(x_21);
x_29 = l_Array_append___redArg(x_21, x_28);
lean_dec_ref(x_28);
lean_inc(x_27);
lean_inc(x_20);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_29);
x_31 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
x_32 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
x_33 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(x_19);
x_34 = l_Lean_Name_mkStr4(x_19, x_31, x_32, x_33);
x_35 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(x_20);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
x_37 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
x_38 = l_Lean_Syntax_SepArray_ofElems(x_37, x_18);
lean_dec_ref(x_18);
lean_inc_ref(x_21);
x_39 = l_Array_append___redArg(x_21, x_38);
lean_dec_ref(x_38);
lean_inc(x_27);
lean_inc(x_20);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_20);
lean_ctor_set(x_40, 1, x_27);
lean_ctor_set(x_40, 2, x_39);
x_41 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(x_20);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_20);
lean_ctor_set(x_42, 1, x_41);
lean_inc(x_20);
x_43 = l_Lean_Syntax_node3(x_20, x_34, x_36, x_40, x_42);
lean_inc(x_27);
lean_inc(x_20);
x_44 = l_Lean_Syntax_node1(x_20, x_27, x_43);
lean_inc(x_20);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_20);
lean_ctor_set(x_45, 1, x_23);
x_46 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
x_47 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc(x_26);
lean_inc(x_24);
x_48 = l_Lean_addMacroScope(x_24, x_47, x_26);
x_49 = lean_box(0);
lean_inc(x_20);
x_50 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_50, 0, x_20);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_48);
lean_ctor_set(x_50, 3, x_49);
x_51 = lean_mk_syntax_ident(x_4);
lean_inc(x_27);
lean_inc(x_20);
x_52 = l_Lean_Syntax_node2(x_20, x_27, x_50, x_51);
x_53 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(x_20);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_20);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
x_56 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
lean_inc_ref(x_17);
lean_inc_ref(x_19);
x_57 = l_Lean_Name_mkStr4(x_19, x_17, x_32, x_56);
lean_inc(x_26);
lean_inc(x_57);
lean_inc(x_24);
x_58 = l_Lean_addMacroScope(x_24, x_57, x_26);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_49);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_49);
lean_inc(x_20);
x_61 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_61, 0, x_20);
lean_ctor_set(x_61, 1, x_55);
lean_ctor_set(x_61, 2, x_58);
lean_ctor_set(x_61, 3, x_60);
x_62 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(x_20);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_20);
lean_ctor_set(x_63, 1, x_62);
x_64 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
lean_inc_ref(x_19);
x_65 = l_Lean_Name_mkStr4(x_19, x_31, x_32, x_64);
lean_inc(x_20);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_20);
lean_ctor_set(x_66, 1, x_64);
x_67 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
lean_inc_ref(x_19);
x_68 = l_Lean_Name_mkStr4(x_19, x_31, x_32, x_67);
x_69 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
x_70 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
lean_inc(x_26);
lean_inc(x_24);
x_71 = l_Lean_addMacroScope(x_24, x_70, x_26);
lean_inc(x_20);
x_72 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_72, 0, x_20);
lean_ctor_set(x_72, 1, x_69);
lean_ctor_set(x_72, 2, x_71);
lean_ctor_set(x_72, 3, x_49);
x_73 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
lean_inc_ref(x_19);
x_74 = l_Lean_Name_mkStr4(x_19, x_31, x_32, x_73);
x_75 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
lean_inc(x_20);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_20);
lean_ctor_set(x_76, 1, x_75);
lean_inc(x_20);
x_77 = l_Lean_Syntax_node1(x_20, x_74, x_76);
lean_inc(x_77);
lean_inc_ref(x_72);
lean_inc(x_27);
lean_inc(x_20);
x_78 = l_Lean_Syntax_node2(x_20, x_27, x_72, x_77);
lean_inc_ref(x_21);
lean_inc(x_27);
lean_inc(x_20);
x_79 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_79, 0, x_20);
lean_ctor_set(x_79, 1, x_27);
lean_ctor_set(x_79, 2, x_21);
x_80 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(x_20);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_20);
lean_ctor_set(x_81, 1, x_80);
x_82 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
lean_inc_ref(x_19);
x_83 = l_Lean_Name_mkStr4(x_19, x_31, x_32, x_82);
lean_inc(x_20);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_20);
lean_ctor_set(x_84, 1, x_82);
x_85 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
lean_inc_ref(x_19);
x_86 = l_Lean_Name_mkStr4(x_19, x_31, x_32, x_85);
lean_inc_ref(x_79);
lean_inc(x_20);
x_87 = l_Lean_Syntax_node2(x_20, x_86, x_79, x_72);
lean_inc(x_27);
lean_inc(x_20);
x_88 = l_Lean_Syntax_node1(x_20, x_27, x_87);
x_89 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc(x_20);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_20);
lean_ctor_set(x_90, 1, x_89);
x_91 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(x_19);
x_92 = l_Lean_Name_mkStr4(x_19, x_31, x_32, x_91);
x_93 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(x_19);
x_94 = l_Lean_Name_mkStr4(x_19, x_31, x_32, x_93);
x_95 = l_Array_append___redArg(x_21, x_14);
lean_dec(x_14);
x_96 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(x_20);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_20);
lean_ctor_set(x_97, 1, x_96);
lean_inc(x_27);
lean_inc(x_20);
x_98 = l_Lean_Syntax_node1(x_20, x_27, x_77);
lean_inc(x_27);
lean_inc(x_20);
x_99 = l_Lean_Syntax_node1(x_20, x_27, x_98);
x_100 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
lean_inc_ref(x_19);
x_101 = l_Lean_Name_mkStr4(x_19, x_31, x_32, x_100);
x_102 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
lean_inc(x_20);
x_103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_103, 0, x_20);
lean_ctor_set(x_103, 1, x_102);
x_104 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
x_105 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
x_106 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
x_107 = l_Lean_addMacroScope(x_24, x_106, x_26);
x_108 = l_Lean_Name_mkStr3(x_19, x_17, x_104);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_49);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_49);
lean_inc(x_20);
x_111 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_111, 0, x_20);
lean_ctor_set(x_111, 1, x_105);
lean_ctor_set(x_111, 2, x_107);
lean_ctor_set(x_111, 3, x_110);
lean_inc(x_20);
x_112 = l_Lean_Syntax_node2(x_20, x_101, x_103, x_111);
lean_inc_ref(x_81);
lean_inc(x_20);
x_113 = l_Lean_Syntax_node4(x_20, x_94, x_97, x_99, x_81, x_112);
x_114 = lean_array_push(x_95, x_113);
lean_inc(x_20);
x_115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_115, 0, x_20);
lean_ctor_set(x_115, 1, x_27);
lean_ctor_set(x_115, 2, x_114);
lean_inc(x_20);
x_116 = l_Lean_Syntax_node1(x_20, x_92, x_115);
lean_inc_ref_n(x_79, 2);
lean_inc(x_20);
x_117 = l_Lean_Syntax_node6(x_20, x_83, x_84, x_79, x_79, x_88, x_90, x_116);
lean_inc(x_20);
x_118 = l_Lean_Syntax_node4(x_20, x_68, x_78, x_79, x_81, x_117);
lean_inc(x_20);
x_119 = l_Lean_Syntax_node2(x_20, x_65, x_66, x_118);
x_120 = lean_unsigned_to_nat(9u);
x_121 = lean_mk_empty_array_with_capacity(x_120);
x_122 = lean_array_push(x_121, x_30);
x_123 = lean_array_push(x_122, x_44);
x_124 = lean_array_push(x_123, x_25);
x_125 = lean_array_push(x_124, x_45);
x_126 = lean_array_push(x_125, x_52);
x_127 = lean_array_push(x_126, x_54);
x_128 = lean_array_push(x_127, x_61);
x_129 = lean_array_push(x_128, x_63);
x_130 = lean_array_push(x_129, x_119);
x_131 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_131, 0, x_20);
lean_ctor_set(x_131, 1, x_22);
lean_ctor_set(x_131, 2, x_130);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_131);
x_132 = x_15;
goto block_133;
}
else
{
lean_object* x_134; 
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_131);
x_132 = x_134;
goto block_133;
}
block_133:
{
return x_132;
}
}
block_150:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_141 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
x_142 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
x_143 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
x_144 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
x_145 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
x_146 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_1, 0);
lean_inc(x_147);
lean_dec_ref(x_1);
x_148 = l_Array_mkArray1___redArg(x_147);
x_17 = x_142;
x_18 = x_136;
x_19 = x_141;
x_20 = x_137;
x_21 = x_146;
x_22 = x_144;
x_23 = x_143;
x_24 = x_140;
x_25 = x_138;
x_26 = x_139;
x_27 = x_145;
x_28 = x_148;
goto block_135;
}
else
{
lean_object* x_149; 
lean_dec(x_1);
x_149 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
x_17 = x_142;
x_18 = x_136;
x_19 = x_141;
x_20 = x_137;
x_21 = x_146;
x_22 = x_144;
x_23 = x_143;
x_24 = x_140;
x_25 = x_138;
x_26 = x_139;
x_27 = x_145;
x_28 = x_149;
goto block_135;
}
}
block_249:
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_inc_ref(x_160);
x_164 = l_Array_append___redArg(x_160, x_163);
lean_dec_ref(x_163);
lean_inc(x_151);
lean_inc(x_153);
x_165 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_165, 0, x_153);
lean_ctor_set(x_165, 1, x_151);
lean_ctor_set(x_165, 2, x_164);
x_166 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
x_167 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
x_168 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(x_161);
x_169 = l_Lean_Name_mkStr4(x_161, x_166, x_167, x_168);
x_170 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(x_153);
x_171 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_171, 0, x_153);
lean_ctor_set(x_171, 1, x_170);
x_172 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
x_173 = l_Lean_Syntax_SepArray_ofElems(x_172, x_162);
lean_dec_ref(x_162);
lean_inc_ref(x_160);
x_174 = l_Array_append___redArg(x_160, x_173);
lean_dec_ref(x_173);
lean_inc(x_151);
lean_inc(x_153);
x_175 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_175, 0, x_153);
lean_ctor_set(x_175, 1, x_151);
lean_ctor_set(x_175, 2, x_174);
x_176 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(x_153);
x_177 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_177, 0, x_153);
lean_ctor_set(x_177, 1, x_176);
lean_inc(x_153);
x_178 = l_Lean_Syntax_node3(x_153, x_169, x_171, x_175, x_177);
lean_inc(x_151);
lean_inc(x_153);
x_179 = l_Lean_Syntax_node1(x_153, x_151, x_178);
lean_inc(x_153);
x_180 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_180, 0, x_153);
lean_ctor_set(x_180, 1, x_156);
x_181 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
x_182 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc(x_152);
lean_inc(x_154);
x_183 = l_Lean_addMacroScope(x_154, x_182, x_152);
x_184 = lean_box(0);
lean_inc(x_153);
x_185 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_185, 0, x_153);
lean_ctor_set(x_185, 1, x_181);
lean_ctor_set(x_185, 2, x_183);
lean_ctor_set(x_185, 3, x_184);
x_186 = lean_mk_syntax_ident(x_4);
lean_inc(x_151);
lean_inc(x_153);
x_187 = l_Lean_Syntax_node2(x_153, x_151, x_185, x_186);
x_188 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(x_153);
x_189 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_189, 0, x_153);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__34, &l_Lean_Elab_Command_elabElabRulesAux___closed__34_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__34);
x_191 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__35));
lean_inc_ref(x_155);
lean_inc_ref(x_161);
x_192 = l_Lean_Name_mkStr4(x_161, x_155, x_157, x_191);
lean_inc(x_152);
lean_inc(x_192);
lean_inc(x_154);
x_193 = l_Lean_addMacroScope(x_154, x_192, x_152);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_184);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_184);
lean_inc(x_153);
x_196 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_196, 0, x_153);
lean_ctor_set(x_196, 1, x_190);
lean_ctor_set(x_196, 2, x_193);
lean_ctor_set(x_196, 3, x_195);
x_197 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(x_153);
x_198 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_198, 0, x_153);
lean_ctor_set(x_198, 1, x_197);
x_199 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
lean_inc_ref(x_161);
x_200 = l_Lean_Name_mkStr4(x_161, x_166, x_167, x_199);
lean_inc(x_153);
x_201 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_201, 0, x_153);
lean_ctor_set(x_201, 1, x_199);
x_202 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(x_161);
x_203 = l_Lean_Name_mkStr4(x_161, x_166, x_167, x_202);
x_204 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(x_161);
x_205 = l_Lean_Name_mkStr4(x_161, x_166, x_167, x_204);
x_206 = l_Array_append___redArg(x_160, x_14);
lean_dec(x_14);
x_207 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(x_153);
x_208 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_208, 0, x_153);
lean_ctor_set(x_208, 1, x_207);
x_209 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
lean_inc_ref(x_161);
x_210 = l_Lean_Name_mkStr4(x_161, x_166, x_167, x_209);
x_211 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
lean_inc(x_153);
x_212 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_212, 0, x_153);
lean_ctor_set(x_212, 1, x_211);
lean_inc(x_153);
x_213 = l_Lean_Syntax_node1(x_153, x_210, x_212);
lean_inc(x_151);
lean_inc(x_153);
x_214 = l_Lean_Syntax_node1(x_153, x_151, x_213);
lean_inc(x_151);
lean_inc(x_153);
x_215 = l_Lean_Syntax_node1(x_153, x_151, x_214);
x_216 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(x_153);
x_217 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_217, 0, x_153);
lean_ctor_set(x_217, 1, x_216);
x_218 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
lean_inc_ref(x_161);
x_219 = l_Lean_Name_mkStr4(x_161, x_166, x_167, x_218);
x_220 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
lean_inc(x_153);
x_221 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_221, 0, x_153);
lean_ctor_set(x_221, 1, x_220);
x_222 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
x_223 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
x_224 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
x_225 = l_Lean_addMacroScope(x_154, x_224, x_152);
x_226 = l_Lean_Name_mkStr3(x_161, x_155, x_222);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_184);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_184);
lean_inc(x_153);
x_229 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_229, 0, x_153);
lean_ctor_set(x_229, 1, x_223);
lean_ctor_set(x_229, 2, x_225);
lean_ctor_set(x_229, 3, x_228);
lean_inc(x_153);
x_230 = l_Lean_Syntax_node2(x_153, x_219, x_221, x_229);
lean_inc(x_153);
x_231 = l_Lean_Syntax_node4(x_153, x_205, x_208, x_215, x_217, x_230);
x_232 = lean_array_push(x_206, x_231);
lean_inc(x_153);
x_233 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_233, 0, x_153);
lean_ctor_set(x_233, 1, x_151);
lean_ctor_set(x_233, 2, x_232);
lean_inc(x_153);
x_234 = l_Lean_Syntax_node1(x_153, x_203, x_233);
lean_inc(x_153);
x_235 = l_Lean_Syntax_node2(x_153, x_200, x_201, x_234);
x_236 = lean_unsigned_to_nat(9u);
x_237 = lean_mk_empty_array_with_capacity(x_236);
x_238 = lean_array_push(x_237, x_165);
x_239 = lean_array_push(x_238, x_179);
x_240 = lean_array_push(x_239, x_159);
x_241 = lean_array_push(x_240, x_180);
x_242 = lean_array_push(x_241, x_187);
x_243 = lean_array_push(x_242, x_189);
x_244 = lean_array_push(x_243, x_196);
x_245 = lean_array_push(x_244, x_198);
x_246 = lean_array_push(x_245, x_235);
x_247 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_247, 0, x_153);
lean_ctor_set(x_247, 1, x_158);
lean_ctor_set(x_247, 2, x_246);
x_248 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_248, 0, x_247);
return x_248;
}
block_265:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_255 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
x_256 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
x_257 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__29));
x_258 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
x_259 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
x_260 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
x_261 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_1, 0);
lean_inc(x_262);
lean_dec_ref(x_1);
x_263 = l_Array_mkArray1___redArg(x_262);
x_151 = x_260;
x_152 = x_250;
x_153 = x_251;
x_154 = x_254;
x_155 = x_256;
x_156 = x_258;
x_157 = x_257;
x_158 = x_259;
x_159 = x_252;
x_160 = x_261;
x_161 = x_255;
x_162 = x_253;
x_163 = x_263;
goto block_249;
}
else
{
lean_object* x_264; 
lean_dec(x_1);
x_264 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
x_151 = x_260;
x_152 = x_250;
x_153 = x_251;
x_154 = x_254;
x_155 = x_256;
x_156 = x_258;
x_157 = x_257;
x_158 = x_259;
x_159 = x_252;
x_160 = x_261;
x_161 = x_255;
x_162 = x_253;
x_163 = x_264;
goto block_249;
}
}
block_387:
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_inc_ref(x_267);
x_278 = l_Array_append___redArg(x_267, x_277);
lean_dec_ref(x_277);
lean_inc(x_270);
lean_inc(x_276);
x_279 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_270);
lean_ctor_set(x_279, 2, x_278);
x_280 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
x_281 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
x_282 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(x_275);
x_283 = l_Lean_Name_mkStr4(x_275, x_280, x_281, x_282);
x_284 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(x_276);
x_285 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_285, 0, x_276);
lean_ctor_set(x_285, 1, x_284);
x_286 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
x_287 = l_Lean_Syntax_SepArray_ofElems(x_286, x_269);
lean_dec_ref(x_269);
lean_inc_ref(x_267);
x_288 = l_Array_append___redArg(x_267, x_287);
lean_dec_ref(x_287);
lean_inc(x_270);
lean_inc(x_276);
x_289 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_289, 0, x_276);
lean_ctor_set(x_289, 1, x_270);
lean_ctor_set(x_289, 2, x_288);
x_290 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(x_276);
x_291 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_291, 0, x_276);
lean_ctor_set(x_291, 1, x_290);
lean_inc(x_276);
x_292 = l_Lean_Syntax_node3(x_276, x_283, x_285, x_289, x_291);
lean_inc(x_270);
lean_inc(x_276);
x_293 = l_Lean_Syntax_node1(x_276, x_270, x_292);
lean_inc(x_276);
x_294 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_294, 0, x_276);
lean_ctor_set(x_294, 1, x_266);
x_295 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
x_296 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc(x_274);
lean_inc(x_272);
x_297 = l_Lean_addMacroScope(x_272, x_296, x_274);
x_298 = lean_box(0);
lean_inc(x_276);
x_299 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_299, 0, x_276);
lean_ctor_set(x_299, 1, x_295);
lean_ctor_set(x_299, 2, x_297);
lean_ctor_set(x_299, 3, x_298);
x_300 = lean_mk_syntax_ident(x_4);
lean_inc(x_270);
lean_inc(x_276);
x_301 = l_Lean_Syntax_node2(x_276, x_270, x_299, x_300);
x_302 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(x_276);
x_303 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_303, 0, x_276);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__37, &l_Lean_Elab_Command_elabElabRulesAux___closed__37_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__37);
x_305 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__38));
x_306 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__39));
lean_inc_ref(x_273);
lean_inc_ref(x_275);
x_307 = l_Lean_Name_mkStr4(x_275, x_273, x_305, x_306);
lean_inc(x_274);
lean_inc(x_307);
lean_inc(x_272);
x_308 = l_Lean_addMacroScope(x_272, x_307, x_274);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_298);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_298);
lean_inc(x_276);
x_311 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_311, 0, x_276);
lean_ctor_set(x_311, 1, x_304);
lean_ctor_set(x_311, 2, x_308);
lean_ctor_set(x_311, 3, x_310);
x_312 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(x_276);
x_313 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_313, 0, x_276);
lean_ctor_set(x_313, 1, x_312);
x_314 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
lean_inc_ref(x_275);
x_315 = l_Lean_Name_mkStr4(x_275, x_280, x_281, x_314);
lean_inc(x_276);
x_316 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_316, 0, x_276);
lean_ctor_set(x_316, 1, x_314);
x_317 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
lean_inc_ref(x_275);
x_318 = l_Lean_Name_mkStr4(x_275, x_280, x_281, x_317);
x_319 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
x_320 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
lean_inc(x_274);
lean_inc(x_272);
x_321 = l_Lean_addMacroScope(x_272, x_320, x_274);
lean_inc(x_276);
x_322 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_322, 0, x_276);
lean_ctor_set(x_322, 1, x_319);
lean_ctor_set(x_322, 2, x_321);
lean_ctor_set(x_322, 3, x_298);
x_323 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__41, &l_Lean_Elab_Command_elabElabRulesAux___closed__41_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__41);
x_324 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__42));
lean_inc(x_274);
lean_inc(x_272);
x_325 = l_Lean_addMacroScope(x_272, x_324, x_274);
lean_inc(x_276);
x_326 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_326, 0, x_276);
lean_ctor_set(x_326, 1, x_323);
lean_ctor_set(x_326, 2, x_325);
lean_ctor_set(x_326, 3, x_298);
lean_inc_ref(x_322);
lean_inc(x_270);
lean_inc(x_276);
x_327 = l_Lean_Syntax_node2(x_276, x_270, x_322, x_326);
lean_inc_ref(x_267);
lean_inc(x_270);
lean_inc(x_276);
x_328 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_328, 0, x_276);
lean_ctor_set(x_328, 1, x_270);
lean_ctor_set(x_328, 2, x_267);
x_329 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(x_276);
x_330 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_330, 0, x_276);
lean_ctor_set(x_330, 1, x_329);
x_331 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
lean_inc_ref(x_275);
x_332 = l_Lean_Name_mkStr4(x_275, x_280, x_281, x_331);
lean_inc(x_276);
x_333 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_333, 0, x_276);
lean_ctor_set(x_333, 1, x_331);
x_334 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
lean_inc_ref(x_275);
x_335 = l_Lean_Name_mkStr4(x_275, x_280, x_281, x_334);
lean_inc_ref(x_328);
lean_inc(x_276);
x_336 = l_Lean_Syntax_node2(x_276, x_335, x_328, x_322);
lean_inc(x_270);
lean_inc(x_276);
x_337 = l_Lean_Syntax_node1(x_276, x_270, x_336);
x_338 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc(x_276);
x_339 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_339, 0, x_276);
lean_ctor_set(x_339, 1, x_338);
x_340 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(x_275);
x_341 = l_Lean_Name_mkStr4(x_275, x_280, x_281, x_340);
x_342 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(x_275);
x_343 = l_Lean_Name_mkStr4(x_275, x_280, x_281, x_342);
x_344 = l_Array_append___redArg(x_267, x_14);
lean_dec(x_14);
x_345 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(x_276);
x_346 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_346, 0, x_276);
lean_ctor_set(x_346, 1, x_345);
x_347 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
lean_inc_ref(x_275);
x_348 = l_Lean_Name_mkStr4(x_275, x_280, x_281, x_347);
x_349 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
lean_inc(x_276);
x_350 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_350, 0, x_276);
lean_ctor_set(x_350, 1, x_349);
lean_inc(x_276);
x_351 = l_Lean_Syntax_node1(x_276, x_348, x_350);
lean_inc(x_270);
lean_inc(x_276);
x_352 = l_Lean_Syntax_node1(x_276, x_270, x_351);
lean_inc(x_270);
lean_inc(x_276);
x_353 = l_Lean_Syntax_node1(x_276, x_270, x_352);
x_354 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
lean_inc_ref(x_275);
x_355 = l_Lean_Name_mkStr4(x_275, x_280, x_281, x_354);
x_356 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
lean_inc(x_276);
x_357 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_357, 0, x_276);
lean_ctor_set(x_357, 1, x_356);
x_358 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
x_359 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
x_360 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
x_361 = l_Lean_addMacroScope(x_272, x_360, x_274);
x_362 = l_Lean_Name_mkStr3(x_275, x_273, x_358);
x_363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_298);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_298);
lean_inc(x_276);
x_365 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_365, 0, x_276);
lean_ctor_set(x_365, 1, x_359);
lean_ctor_set(x_365, 2, x_361);
lean_ctor_set(x_365, 3, x_364);
lean_inc(x_276);
x_366 = l_Lean_Syntax_node2(x_276, x_355, x_357, x_365);
lean_inc_ref(x_330);
lean_inc(x_276);
x_367 = l_Lean_Syntax_node4(x_276, x_343, x_346, x_353, x_330, x_366);
x_368 = lean_array_push(x_344, x_367);
lean_inc(x_276);
x_369 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_369, 0, x_276);
lean_ctor_set(x_369, 1, x_270);
lean_ctor_set(x_369, 2, x_368);
lean_inc(x_276);
x_370 = l_Lean_Syntax_node1(x_276, x_341, x_369);
lean_inc_ref_n(x_328, 2);
lean_inc(x_276);
x_371 = l_Lean_Syntax_node6(x_276, x_332, x_333, x_328, x_328, x_337, x_339, x_370);
lean_inc(x_276);
x_372 = l_Lean_Syntax_node4(x_276, x_318, x_327, x_328, x_330, x_371);
lean_inc(x_276);
x_373 = l_Lean_Syntax_node2(x_276, x_315, x_316, x_372);
x_374 = lean_unsigned_to_nat(9u);
x_375 = lean_mk_empty_array_with_capacity(x_374);
x_376 = lean_array_push(x_375, x_279);
x_377 = lean_array_push(x_376, x_293);
x_378 = lean_array_push(x_377, x_271);
x_379 = lean_array_push(x_378, x_294);
x_380 = lean_array_push(x_379, x_301);
x_381 = lean_array_push(x_380, x_303);
x_382 = lean_array_push(x_381, x_311);
x_383 = lean_array_push(x_382, x_313);
x_384 = lean_array_push(x_383, x_373);
x_385 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_385, 0, x_276);
lean_ctor_set(x_385, 1, x_268);
lean_ctor_set(x_385, 2, x_384);
x_386 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_386, 0, x_385);
return x_386;
}
block_402:
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_393 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
x_394 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
x_395 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
x_396 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
x_397 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
x_398 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_1, 0);
lean_inc(x_399);
lean_dec_ref(x_1);
x_400 = l_Array_mkArray1___redArg(x_399);
x_266 = x_395;
x_267 = x_398;
x_268 = x_396;
x_269 = x_388;
x_270 = x_397;
x_271 = x_389;
x_272 = x_392;
x_273 = x_394;
x_274 = x_391;
x_275 = x_393;
x_276 = x_390;
x_277 = x_400;
goto block_387;
}
else
{
lean_object* x_401; 
lean_dec(x_1);
x_401 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
x_266 = x_395;
x_267 = x_398;
x_268 = x_396;
x_269 = x_388;
x_270 = x_397;
x_271 = x_389;
x_272 = x_392;
x_273 = x_394;
x_274 = x_391;
x_275 = x_393;
x_276 = x_390;
x_277 = x_401;
goto block_387;
}
}
block_500:
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
lean_inc_ref(x_410);
x_415 = l_Array_append___redArg(x_410, x_414);
lean_dec_ref(x_414);
lean_inc(x_406);
lean_inc(x_403);
x_416 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_416, 0, x_403);
lean_ctor_set(x_416, 1, x_406);
lean_ctor_set(x_416, 2, x_415);
x_417 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
x_418 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
x_419 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(x_409);
x_420 = l_Lean_Name_mkStr4(x_409, x_417, x_418, x_419);
x_421 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(x_403);
x_422 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_422, 0, x_403);
lean_ctor_set(x_422, 1, x_421);
x_423 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
x_424 = l_Lean_Syntax_SepArray_ofElems(x_423, x_405);
lean_dec_ref(x_405);
lean_inc_ref(x_410);
x_425 = l_Array_append___redArg(x_410, x_424);
lean_dec_ref(x_424);
lean_inc(x_406);
lean_inc(x_403);
x_426 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_426, 0, x_403);
lean_ctor_set(x_426, 1, x_406);
lean_ctor_set(x_426, 2, x_425);
x_427 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(x_403);
x_428 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_428, 0, x_403);
lean_ctor_set(x_428, 1, x_427);
lean_inc(x_403);
x_429 = l_Lean_Syntax_node3(x_403, x_420, x_422, x_426, x_428);
lean_inc(x_406);
lean_inc(x_403);
x_430 = l_Lean_Syntax_node1(x_403, x_406, x_429);
lean_inc(x_403);
x_431 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_431, 0, x_403);
lean_ctor_set(x_431, 1, x_411);
x_432 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
x_433 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc(x_408);
lean_inc(x_413);
x_434 = l_Lean_addMacroScope(x_413, x_433, x_408);
x_435 = lean_box(0);
lean_inc(x_403);
x_436 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_436, 0, x_403);
lean_ctor_set(x_436, 1, x_432);
lean_ctor_set(x_436, 2, x_434);
lean_ctor_set(x_436, 3, x_435);
x_437 = lean_mk_syntax_ident(x_4);
lean_inc(x_406);
lean_inc(x_403);
x_438 = l_Lean_Syntax_node2(x_403, x_406, x_436, x_437);
x_439 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(x_403);
x_440 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_440, 0, x_403);
lean_ctor_set(x_440, 1, x_439);
x_441 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__44, &l_Lean_Elab_Command_elabElabRulesAux___closed__44_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__44);
x_442 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__45));
lean_inc_ref(x_412);
lean_inc_ref(x_409);
x_443 = l_Lean_Name_mkStr4(x_409, x_412, x_442, x_442);
lean_inc(x_408);
lean_inc(x_443);
lean_inc(x_413);
x_444 = l_Lean_addMacroScope(x_413, x_443, x_408);
x_445 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_435);
x_446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_435);
lean_inc(x_403);
x_447 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_447, 0, x_403);
lean_ctor_set(x_447, 1, x_441);
lean_ctor_set(x_447, 2, x_444);
lean_ctor_set(x_447, 3, x_446);
x_448 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(x_403);
x_449 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_449, 0, x_403);
lean_ctor_set(x_449, 1, x_448);
x_450 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
lean_inc_ref(x_409);
x_451 = l_Lean_Name_mkStr4(x_409, x_417, x_418, x_450);
lean_inc(x_403);
x_452 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_452, 0, x_403);
lean_ctor_set(x_452, 1, x_450);
x_453 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(x_409);
x_454 = l_Lean_Name_mkStr4(x_409, x_417, x_418, x_453);
x_455 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(x_409);
x_456 = l_Lean_Name_mkStr4(x_409, x_417, x_418, x_455);
x_457 = l_Array_append___redArg(x_410, x_14);
lean_dec(x_14);
x_458 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(x_403);
x_459 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_459, 0, x_403);
lean_ctor_set(x_459, 1, x_458);
x_460 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
lean_inc_ref(x_409);
x_461 = l_Lean_Name_mkStr4(x_409, x_417, x_418, x_460);
x_462 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
lean_inc(x_403);
x_463 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_463, 0, x_403);
lean_ctor_set(x_463, 1, x_462);
lean_inc(x_403);
x_464 = l_Lean_Syntax_node1(x_403, x_461, x_463);
lean_inc(x_406);
lean_inc(x_403);
x_465 = l_Lean_Syntax_node1(x_403, x_406, x_464);
lean_inc(x_406);
lean_inc(x_403);
x_466 = l_Lean_Syntax_node1(x_403, x_406, x_465);
x_467 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(x_403);
x_468 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_468, 0, x_403);
lean_ctor_set(x_468, 1, x_467);
x_469 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
lean_inc_ref(x_409);
x_470 = l_Lean_Name_mkStr4(x_409, x_417, x_418, x_469);
x_471 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
lean_inc(x_403);
x_472 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_472, 0, x_403);
lean_ctor_set(x_472, 1, x_471);
x_473 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
x_474 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
x_475 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
x_476 = l_Lean_addMacroScope(x_413, x_475, x_408);
x_477 = l_Lean_Name_mkStr3(x_409, x_412, x_473);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_478, 1, x_435);
x_479 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_435);
lean_inc(x_403);
x_480 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_480, 0, x_403);
lean_ctor_set(x_480, 1, x_474);
lean_ctor_set(x_480, 2, x_476);
lean_ctor_set(x_480, 3, x_479);
lean_inc(x_403);
x_481 = l_Lean_Syntax_node2(x_403, x_470, x_472, x_480);
lean_inc(x_403);
x_482 = l_Lean_Syntax_node4(x_403, x_456, x_459, x_466, x_468, x_481);
x_483 = lean_array_push(x_457, x_482);
lean_inc(x_403);
x_484 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_484, 0, x_403);
lean_ctor_set(x_484, 1, x_406);
lean_ctor_set(x_484, 2, x_483);
lean_inc(x_403);
x_485 = l_Lean_Syntax_node1(x_403, x_454, x_484);
lean_inc(x_403);
x_486 = l_Lean_Syntax_node2(x_403, x_451, x_452, x_485);
x_487 = lean_unsigned_to_nat(9u);
x_488 = lean_mk_empty_array_with_capacity(x_487);
x_489 = lean_array_push(x_488, x_416);
x_490 = lean_array_push(x_489, x_430);
x_491 = lean_array_push(x_490, x_407);
x_492 = lean_array_push(x_491, x_431);
x_493 = lean_array_push(x_492, x_438);
x_494 = lean_array_push(x_493, x_440);
x_495 = lean_array_push(x_494, x_447);
x_496 = lean_array_push(x_495, x_449);
x_497 = lean_array_push(x_496, x_486);
x_498 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_498, 0, x_403);
lean_ctor_set(x_498, 1, x_404);
lean_ctor_set(x_498, 2, x_497);
x_499 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_499, 0, x_498);
return x_499;
}
block_515:
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_506 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
x_507 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
x_508 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
x_509 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
x_510 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
x_511 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_512; lean_object* x_513; 
x_512 = lean_ctor_get(x_1, 0);
lean_inc(x_512);
lean_dec_ref(x_1);
x_513 = l_Array_mkArray1___redArg(x_512);
x_403 = x_501;
x_404 = x_509;
x_405 = x_502;
x_406 = x_510;
x_407 = x_503;
x_408 = x_504;
x_409 = x_506;
x_410 = x_511;
x_411 = x_508;
x_412 = x_507;
x_413 = x_505;
x_414 = x_513;
goto block_500;
}
else
{
lean_object* x_514; 
lean_dec(x_1);
x_514 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
x_403 = x_501;
x_404 = x_509;
x_405 = x_502;
x_406 = x_510;
x_407 = x_503;
x_408 = x_504;
x_409 = x_506;
x_410 = x_511;
x_411 = x_508;
x_412 = x_507;
x_413 = x_505;
x_414 = x_514;
goto block_500;
}
}
block_651:
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; 
lean_inc_ref(x_520);
x_529 = l_Array_append___redArg(x_520, x_528);
lean_dec_ref(x_528);
lean_inc(x_524);
lean_inc(x_522);
x_530 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_530, 0, x_522);
lean_ctor_set(x_530, 1, x_524);
lean_ctor_set(x_530, 2, x_529);
x_531 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
x_532 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
x_533 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(x_517);
x_534 = l_Lean_Name_mkStr4(x_517, x_531, x_532, x_533);
x_535 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(x_522);
x_536 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_536, 0, x_522);
lean_ctor_set(x_536, 1, x_535);
x_537 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
x_538 = l_Lean_Syntax_SepArray_ofElems(x_537, x_526);
lean_dec_ref(x_526);
lean_inc_ref(x_520);
x_539 = l_Array_append___redArg(x_520, x_538);
lean_dec_ref(x_538);
lean_inc(x_524);
lean_inc(x_522);
x_540 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_540, 0, x_522);
lean_ctor_set(x_540, 1, x_524);
lean_ctor_set(x_540, 2, x_539);
x_541 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(x_522);
x_542 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_542, 0, x_522);
lean_ctor_set(x_542, 1, x_541);
lean_inc(x_522);
x_543 = l_Lean_Syntax_node3(x_522, x_534, x_536, x_540, x_542);
lean_inc(x_524);
lean_inc(x_522);
x_544 = l_Lean_Syntax_node1(x_522, x_524, x_543);
lean_inc(x_522);
x_545 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_545, 0, x_522);
lean_ctor_set(x_545, 1, x_525);
x_546 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
x_547 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc(x_518);
lean_inc(x_516);
x_548 = l_Lean_addMacroScope(x_516, x_547, x_518);
x_549 = lean_box(0);
lean_inc(x_522);
x_550 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_550, 0, x_522);
lean_ctor_set(x_550, 1, x_546);
lean_ctor_set(x_550, 2, x_548);
lean_ctor_set(x_550, 3, x_549);
x_551 = lean_mk_syntax_ident(x_4);
lean_inc(x_524);
lean_inc(x_522);
x_552 = l_Lean_Syntax_node2(x_522, x_524, x_550, x_551);
x_553 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(x_522);
x_554 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_554, 0, x_522);
lean_ctor_set(x_554, 1, x_553);
x_555 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__9, &l_Lean_Elab_Command_elabElabRulesAux___closed__9_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9);
x_556 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__10));
lean_inc_ref(x_527);
lean_inc_ref(x_517);
x_557 = l_Lean_Name_mkStr4(x_517, x_527, x_532, x_556);
lean_inc(x_518);
lean_inc(x_557);
lean_inc(x_516);
x_558 = l_Lean_addMacroScope(x_516, x_557, x_518);
x_559 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_559, 0, x_557);
lean_ctor_set(x_559, 1, x_549);
x_560 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_560, 0, x_559);
lean_ctor_set(x_560, 1, x_549);
lean_inc(x_522);
x_561 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_561, 0, x_522);
lean_ctor_set(x_561, 1, x_555);
lean_ctor_set(x_561, 2, x_558);
lean_ctor_set(x_561, 3, x_560);
x_562 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(x_522);
x_563 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_563, 0, x_522);
lean_ctor_set(x_563, 1, x_562);
x_564 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
lean_inc_ref(x_517);
x_565 = l_Lean_Name_mkStr4(x_517, x_531, x_532, x_564);
lean_inc(x_522);
x_566 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_566, 0, x_522);
lean_ctor_set(x_566, 1, x_564);
x_567 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
lean_inc_ref(x_517);
x_568 = l_Lean_Name_mkStr4(x_517, x_531, x_532, x_567);
x_569 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
x_570 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
lean_inc(x_518);
lean_inc(x_516);
x_571 = l_Lean_addMacroScope(x_516, x_570, x_518);
lean_inc(x_522);
x_572 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_572, 0, x_522);
lean_ctor_set(x_572, 1, x_569);
lean_ctor_set(x_572, 2, x_571);
lean_ctor_set(x_572, 3, x_549);
x_573 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__47, &l_Lean_Elab_Command_elabElabRulesAux___closed__47_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__47);
x_574 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__48));
lean_inc(x_518);
lean_inc(x_516);
x_575 = l_Lean_addMacroScope(x_516, x_574, x_518);
lean_inc(x_522);
x_576 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_576, 0, x_522);
lean_ctor_set(x_576, 1, x_573);
lean_ctor_set(x_576, 2, x_575);
lean_ctor_set(x_576, 3, x_549);
lean_inc_ref(x_576);
lean_inc_ref(x_572);
lean_inc(x_524);
lean_inc(x_522);
x_577 = l_Lean_Syntax_node2(x_522, x_524, x_572, x_576);
lean_inc_ref(x_520);
lean_inc(x_524);
lean_inc(x_522);
x_578 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_578, 0, x_522);
lean_ctor_set(x_578, 1, x_524);
lean_ctor_set(x_578, 2, x_520);
x_579 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(x_522);
x_580 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_580, 0, x_522);
lean_ctor_set(x_580, 1, x_579);
x_581 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__49));
lean_inc_ref(x_517);
x_582 = l_Lean_Name_mkStr4(x_517, x_531, x_532, x_581);
x_583 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__51, &l_Lean_Elab_Command_elabElabRulesAux___closed__51_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__51);
x_584 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__52));
lean_inc_ref(x_527);
lean_inc_ref(x_517);
x_585 = l_Lean_Name_mkStr4(x_517, x_527, x_532, x_584);
lean_inc(x_518);
lean_inc(x_585);
lean_inc(x_516);
x_586 = l_Lean_addMacroScope(x_516, x_585, x_518);
x_587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_587, 0, x_585);
lean_ctor_set(x_587, 1, x_549);
x_588 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_588, 0, x_587);
lean_ctor_set(x_588, 1, x_549);
lean_inc(x_522);
x_589 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_589, 0, x_522);
lean_ctor_set(x_589, 1, x_583);
lean_ctor_set(x_589, 2, x_586);
lean_ctor_set(x_589, 3, x_588);
lean_inc(x_524);
lean_inc(x_522);
x_590 = l_Lean_Syntax_node1(x_522, x_524, x_521);
x_591 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
lean_inc_ref(x_517);
x_592 = l_Lean_Name_mkStr4(x_517, x_531, x_532, x_591);
lean_inc(x_522);
x_593 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_593, 0, x_522);
lean_ctor_set(x_593, 1, x_591);
x_594 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
lean_inc_ref(x_517);
x_595 = l_Lean_Name_mkStr4(x_517, x_531, x_532, x_594);
lean_inc_ref(x_578);
lean_inc(x_522);
x_596 = l_Lean_Syntax_node2(x_522, x_595, x_578, x_572);
lean_inc(x_524);
lean_inc(x_522);
x_597 = l_Lean_Syntax_node1(x_522, x_524, x_596);
x_598 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc(x_522);
x_599 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_599, 0, x_522);
lean_ctor_set(x_599, 1, x_598);
x_600 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(x_517);
x_601 = l_Lean_Name_mkStr4(x_517, x_531, x_532, x_600);
x_602 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(x_517);
x_603 = l_Lean_Name_mkStr4(x_517, x_531, x_532, x_602);
x_604 = l_Array_append___redArg(x_520, x_14);
lean_dec(x_14);
x_605 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(x_522);
x_606 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_606, 0, x_522);
lean_ctor_set(x_606, 1, x_605);
x_607 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
lean_inc_ref(x_517);
x_608 = l_Lean_Name_mkStr4(x_517, x_531, x_532, x_607);
x_609 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
lean_inc(x_522);
x_610 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_610, 0, x_522);
lean_ctor_set(x_610, 1, x_609);
lean_inc(x_522);
x_611 = l_Lean_Syntax_node1(x_522, x_608, x_610);
lean_inc(x_524);
lean_inc(x_522);
x_612 = l_Lean_Syntax_node1(x_522, x_524, x_611);
lean_inc(x_524);
lean_inc(x_522);
x_613 = l_Lean_Syntax_node1(x_522, x_524, x_612);
x_614 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
lean_inc_ref(x_517);
x_615 = l_Lean_Name_mkStr4(x_517, x_531, x_532, x_614);
x_616 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
lean_inc(x_522);
x_617 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_617, 0, x_522);
lean_ctor_set(x_617, 1, x_616);
x_618 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
x_619 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
x_620 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
x_621 = l_Lean_addMacroScope(x_516, x_620, x_518);
x_622 = l_Lean_Name_mkStr3(x_517, x_527, x_618);
x_623 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_623, 0, x_622);
lean_ctor_set(x_623, 1, x_549);
x_624 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_624, 0, x_623);
lean_ctor_set(x_624, 1, x_549);
lean_inc(x_522);
x_625 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_625, 0, x_522);
lean_ctor_set(x_625, 1, x_619);
lean_ctor_set(x_625, 2, x_621);
lean_ctor_set(x_625, 3, x_624);
lean_inc(x_522);
x_626 = l_Lean_Syntax_node2(x_522, x_615, x_617, x_625);
lean_inc_ref(x_580);
lean_inc(x_522);
x_627 = l_Lean_Syntax_node4(x_522, x_603, x_606, x_613, x_580, x_626);
x_628 = lean_array_push(x_604, x_627);
lean_inc(x_524);
lean_inc(x_522);
x_629 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_629, 0, x_522);
lean_ctor_set(x_629, 1, x_524);
lean_ctor_set(x_629, 2, x_628);
lean_inc(x_522);
x_630 = l_Lean_Syntax_node1(x_522, x_601, x_629);
lean_inc_ref_n(x_578, 2);
lean_inc(x_522);
x_631 = l_Lean_Syntax_node6(x_522, x_592, x_593, x_578, x_578, x_597, x_599, x_630);
lean_inc_ref(x_580);
lean_inc_ref(x_578);
lean_inc(x_568);
lean_inc(x_522);
x_632 = l_Lean_Syntax_node4(x_522, x_568, x_590, x_578, x_580, x_631);
lean_inc_ref(x_566);
lean_inc(x_565);
lean_inc(x_522);
x_633 = l_Lean_Syntax_node2(x_522, x_565, x_566, x_632);
lean_inc(x_522);
x_634 = l_Lean_Syntax_node2(x_522, x_524, x_576, x_633);
lean_inc(x_522);
x_635 = l_Lean_Syntax_node2(x_522, x_582, x_589, x_634);
lean_inc(x_522);
x_636 = l_Lean_Syntax_node4(x_522, x_568, x_577, x_578, x_580, x_635);
lean_inc(x_522);
x_637 = l_Lean_Syntax_node2(x_522, x_565, x_566, x_636);
x_638 = lean_unsigned_to_nat(9u);
x_639 = lean_mk_empty_array_with_capacity(x_638);
x_640 = lean_array_push(x_639, x_530);
x_641 = lean_array_push(x_640, x_544);
x_642 = lean_array_push(x_641, x_523);
x_643 = lean_array_push(x_642, x_545);
x_644 = lean_array_push(x_643, x_552);
x_645 = lean_array_push(x_644, x_554);
x_646 = lean_array_push(x_645, x_561);
x_647 = lean_array_push(x_646, x_563);
x_648 = lean_array_push(x_647, x_637);
x_649 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_649, 0, x_522);
lean_ctor_set(x_649, 1, x_519);
lean_ctor_set(x_649, 2, x_648);
x_650 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_650, 0, x_649);
return x_650;
}
block_667:
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_658 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
x_659 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
x_660 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
x_661 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
x_662 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
x_663 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_664; lean_object* x_665; 
x_664 = lean_ctor_get(x_1, 0);
lean_inc(x_664);
lean_dec_ref(x_1);
x_665 = l_Array_mkArray1___redArg(x_664);
x_516 = x_657;
x_517 = x_658;
x_518 = x_655;
x_519 = x_661;
x_520 = x_663;
x_521 = x_652;
x_522 = x_653;
x_523 = x_654;
x_524 = x_662;
x_525 = x_660;
x_526 = x_656;
x_527 = x_659;
x_528 = x_665;
goto block_651;
}
else
{
lean_object* x_666; 
lean_dec(x_1);
x_666 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
x_516 = x_657;
x_517 = x_658;
x_518 = x_655;
x_519 = x_661;
x_520 = x_663;
x_521 = x_652;
x_522 = x_653;
x_523 = x_654;
x_524 = x_662;
x_525 = x_660;
x_526 = x_656;
x_527 = x_659;
x_528 = x_666;
goto block_651;
}
}
block_786:
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
lean_inc_ref(x_677);
x_681 = l_Array_append___redArg(x_677, x_680);
lean_dec_ref(x_680);
lean_inc(x_674);
lean_inc(x_670);
x_682 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_682, 0, x_670);
lean_ctor_set(x_682, 1, x_674);
lean_ctor_set(x_682, 2, x_681);
x_683 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
x_684 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
x_685 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(x_671);
x_686 = l_Lean_Name_mkStr4(x_671, x_683, x_684, x_685);
x_687 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(x_670);
x_688 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_688, 0, x_670);
lean_ctor_set(x_688, 1, x_687);
x_689 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__2));
x_690 = l_Lean_Syntax_SepArray_ofElems(x_689, x_672);
lean_dec_ref(x_672);
lean_inc_ref(x_677);
x_691 = l_Array_append___redArg(x_677, x_690);
lean_dec_ref(x_690);
lean_inc(x_674);
lean_inc(x_670);
x_692 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_692, 0, x_670);
lean_ctor_set(x_692, 1, x_674);
lean_ctor_set(x_692, 2, x_691);
x_693 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(x_670);
x_694 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_694, 0, x_670);
lean_ctor_set(x_694, 1, x_693);
lean_inc(x_670);
x_695 = l_Lean_Syntax_node3(x_670, x_686, x_688, x_692, x_694);
lean_inc(x_674);
lean_inc(x_670);
x_696 = l_Lean_Syntax_node1(x_670, x_674, x_695);
lean_inc(x_670);
x_697 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_697, 0, x_670);
lean_ctor_set(x_697, 1, x_679);
x_698 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__5, &l_Lean_Elab_Command_elabElabRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5);
x_699 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__6));
lean_inc(x_669);
lean_inc(x_668);
x_700 = l_Lean_addMacroScope(x_668, x_699, x_669);
x_701 = lean_box(0);
lean_inc(x_670);
x_702 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_702, 0, x_670);
lean_ctor_set(x_702, 1, x_698);
lean_ctor_set(x_702, 2, x_700);
lean_ctor_set(x_702, 3, x_701);
x_703 = lean_mk_syntax_ident(x_4);
lean_inc(x_674);
lean_inc(x_670);
x_704 = l_Lean_Syntax_node2(x_670, x_674, x_702, x_703);
x_705 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(x_670);
x_706 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_706, 0, x_670);
lean_ctor_set(x_706, 1, x_705);
x_707 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__37, &l_Lean_Elab_Command_elabElabRulesAux___closed__37_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__37);
x_708 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__38));
x_709 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__39));
lean_inc_ref(x_673);
lean_inc_ref(x_671);
x_710 = l_Lean_Name_mkStr4(x_671, x_673, x_708, x_709);
lean_inc(x_669);
lean_inc(x_710);
lean_inc(x_668);
x_711 = l_Lean_addMacroScope(x_668, x_710, x_669);
x_712 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_712, 0, x_710);
lean_ctor_set(x_712, 1, x_701);
x_713 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_713, 0, x_712);
lean_ctor_set(x_713, 1, x_701);
lean_inc(x_670);
x_714 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_714, 0, x_670);
lean_ctor_set(x_714, 1, x_707);
lean_ctor_set(x_714, 2, x_711);
lean_ctor_set(x_714, 3, x_713);
x_715 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(x_670);
x_716 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_716, 0, x_670);
lean_ctor_set(x_716, 1, x_715);
x_717 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__12));
lean_inc_ref(x_671);
x_718 = l_Lean_Name_mkStr4(x_671, x_683, x_684, x_717);
lean_inc(x_670);
x_719 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_719, 0, x_670);
lean_ctor_set(x_719, 1, x_717);
x_720 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__13));
lean_inc_ref(x_671);
x_721 = l_Lean_Name_mkStr4(x_671, x_683, x_684, x_720);
x_722 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__15, &l_Lean_Elab_Command_elabElabRulesAux___closed__15_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15);
x_723 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__16));
lean_inc(x_669);
lean_inc(x_668);
x_724 = l_Lean_addMacroScope(x_668, x_723, x_669);
lean_inc(x_670);
x_725 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_725, 0, x_670);
lean_ctor_set(x_725, 1, x_722);
lean_ctor_set(x_725, 2, x_724);
lean_ctor_set(x_725, 3, x_701);
lean_inc_ref(x_725);
lean_inc(x_674);
lean_inc(x_670);
x_726 = l_Lean_Syntax_node2(x_670, x_674, x_725, x_675);
lean_inc_ref(x_677);
lean_inc(x_674);
lean_inc(x_670);
x_727 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_727, 0, x_670);
lean_ctor_set(x_727, 1, x_674);
lean_ctor_set(x_727, 2, x_677);
x_728 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(x_670);
x_729 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_729, 0, x_670);
lean_ctor_set(x_729, 1, x_728);
x_730 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__19));
lean_inc_ref(x_671);
x_731 = l_Lean_Name_mkStr4(x_671, x_683, x_684, x_730);
lean_inc(x_670);
x_732 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_732, 0, x_670);
lean_ctor_set(x_732, 1, x_730);
x_733 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__20));
lean_inc_ref(x_671);
x_734 = l_Lean_Name_mkStr4(x_671, x_683, x_684, x_733);
lean_inc_ref(x_727);
lean_inc(x_670);
x_735 = l_Lean_Syntax_node2(x_670, x_734, x_727, x_725);
lean_inc(x_674);
lean_inc(x_670);
x_736 = l_Lean_Syntax_node1(x_670, x_674, x_735);
x_737 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__21));
lean_inc(x_670);
x_738 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_738, 0, x_670);
lean_ctor_set(x_738, 1, x_737);
x_739 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(x_671);
x_740 = l_Lean_Name_mkStr4(x_671, x_683, x_684, x_739);
x_741 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(x_671);
x_742 = l_Lean_Name_mkStr4(x_671, x_683, x_684, x_741);
x_743 = l_Array_append___redArg(x_677, x_14);
lean_dec(x_14);
x_744 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(x_670);
x_745 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_745, 0, x_670);
lean_ctor_set(x_745, 1, x_744);
x_746 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__17));
lean_inc_ref(x_671);
x_747 = l_Lean_Name_mkStr4(x_671, x_683, x_684, x_746);
x_748 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__18));
lean_inc(x_670);
x_749 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_749, 0, x_670);
lean_ctor_set(x_749, 1, x_748);
lean_inc(x_670);
x_750 = l_Lean_Syntax_node1(x_670, x_747, x_749);
lean_inc(x_674);
lean_inc(x_670);
x_751 = l_Lean_Syntax_node1(x_670, x_674, x_750);
lean_inc(x_674);
lean_inc(x_670);
x_752 = l_Lean_Syntax_node1(x_670, x_674, x_751);
x_753 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__23));
lean_inc_ref(x_671);
x_754 = l_Lean_Name_mkStr4(x_671, x_683, x_684, x_753);
x_755 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__24));
lean_inc(x_670);
x_756 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_756, 0, x_670);
lean_ctor_set(x_756, 1, x_755);
x_757 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__25));
x_758 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__26, &l_Lean_Elab_Command_elabElabRulesAux___closed__26_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26);
x_759 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__27));
x_760 = l_Lean_addMacroScope(x_668, x_759, x_669);
x_761 = l_Lean_Name_mkStr3(x_671, x_673, x_757);
x_762 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_762, 0, x_761);
lean_ctor_set(x_762, 1, x_701);
x_763 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_763, 0, x_762);
lean_ctor_set(x_763, 1, x_701);
lean_inc(x_670);
x_764 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_764, 0, x_670);
lean_ctor_set(x_764, 1, x_758);
lean_ctor_set(x_764, 2, x_760);
lean_ctor_set(x_764, 3, x_763);
lean_inc(x_670);
x_765 = l_Lean_Syntax_node2(x_670, x_754, x_756, x_764);
lean_inc_ref(x_729);
lean_inc(x_670);
x_766 = l_Lean_Syntax_node4(x_670, x_742, x_745, x_752, x_729, x_765);
x_767 = lean_array_push(x_743, x_766);
lean_inc(x_670);
x_768 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_768, 0, x_670);
lean_ctor_set(x_768, 1, x_674);
lean_ctor_set(x_768, 2, x_767);
lean_inc(x_670);
x_769 = l_Lean_Syntax_node1(x_670, x_740, x_768);
lean_inc_ref_n(x_727, 2);
lean_inc(x_670);
x_770 = l_Lean_Syntax_node6(x_670, x_731, x_732, x_727, x_727, x_736, x_738, x_769);
lean_inc(x_670);
x_771 = l_Lean_Syntax_node4(x_670, x_721, x_726, x_727, x_729, x_770);
lean_inc(x_670);
x_772 = l_Lean_Syntax_node2(x_670, x_718, x_719, x_771);
x_773 = lean_unsigned_to_nat(9u);
x_774 = lean_mk_empty_array_with_capacity(x_773);
x_775 = lean_array_push(x_774, x_682);
x_776 = lean_array_push(x_775, x_696);
x_777 = lean_array_push(x_776, x_676);
x_778 = lean_array_push(x_777, x_697);
x_779 = lean_array_push(x_778, x_704);
x_780 = lean_array_push(x_779, x_706);
x_781 = lean_array_push(x_780, x_714);
x_782 = lean_array_push(x_781, x_716);
x_783 = lean_array_push(x_782, x_772);
x_784 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_784, 0, x_670);
lean_ctor_set(x_784, 1, x_678);
lean_ctor_set(x_784, 2, x_783);
x_785 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_785, 0, x_784);
return x_785;
}
block_802:
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
x_793 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
x_794 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__28));
x_795 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__30));
x_796 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__31));
x_797 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
x_798 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_799; lean_object* x_800; 
x_799 = lean_ctor_get(x_1, 0);
lean_inc(x_799);
lean_dec_ref(x_1);
x_800 = l_Array_mkArray1___redArg(x_799);
x_668 = x_792;
x_669 = x_787;
x_670 = x_789;
x_671 = x_793;
x_672 = x_791;
x_673 = x_794;
x_674 = x_797;
x_675 = x_788;
x_676 = x_790;
x_677 = x_798;
x_678 = x_796;
x_679 = x_795;
x_680 = x_800;
goto block_786;
}
else
{
lean_object* x_801; 
lean_dec(x_1);
x_801 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
x_668 = x_792;
x_669 = x_787;
x_670 = x_789;
x_671 = x_793;
x_672 = x_791;
x_673 = x_794;
x_674 = x_797;
x_675 = x_788;
x_676 = x_790;
x_677 = x_798;
x_678 = x_796;
x_679 = x_795;
x_680 = x_801;
goto block_786;
}
}
block_835:
{
lean_object* x_808; 
lean_inc(x_4);
x_808 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_4, x_3, x_2, x_806, x_803, x_805);
if (lean_obj_tag(x_808) == 0)
{
lean_object* x_809; lean_object* x_810; 
x_809 = lean_ctor_get(x_808, 0);
lean_inc(x_809);
lean_dec_ref(x_808);
x_810 = l_Lean_Elab_Command_getRef___redArg(x_803);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; lean_object* x_812; 
x_811 = lean_ctor_get(x_810, 0);
lean_inc(x_811);
lean_dec_ref(x_810);
x_812 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_803);
if (lean_obj_tag(x_812) == 0)
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_813 = lean_ctor_get(x_812, 0);
lean_inc(x_813);
lean_dec_ref(x_812);
x_814 = lean_ctor_get(x_803, 5);
lean_inc(x_814);
lean_dec_ref(x_803);
x_815 = l_Lean_SourceInfo_fromRef(x_811, x_807);
lean_dec(x_811);
if (lean_obj_tag(x_814) == 0)
{
lean_object* x_816; lean_object* x_817; 
x_816 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_805);
x_817 = lean_ctor_get(x_816, 0);
lean_inc(x_817);
lean_dec_ref(x_816);
x_501 = x_815;
x_502 = x_809;
x_503 = x_804;
x_504 = x_813;
x_505 = x_817;
goto block_515;
}
else
{
lean_object* x_818; 
x_818 = lean_ctor_get(x_814, 0);
lean_inc(x_818);
lean_dec_ref(x_814);
x_501 = x_815;
x_502 = x_809;
x_503 = x_804;
x_504 = x_813;
x_505 = x_818;
goto block_515;
}
}
else
{
lean_object* x_819; lean_object* x_820; uint8_t x_821; uint8_t x_826; 
lean_dec(x_811);
lean_dec(x_809);
lean_dec(x_804);
lean_dec_ref(x_803);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_819 = lean_ctor_get(x_812, 0);
x_826 = !lean_is_exclusive(x_812);
if (x_826 == 0)
{
x_820 = x_812;
x_821 = x_826;
goto block_825;
}
else
{
lean_inc(x_819);
lean_dec(x_812);
x_820 = lean_box(0);
x_821 = x_826;
goto block_825;
}
block_825:
{
lean_object* x_822; 
if (x_821 == 0)
{
x_822 = x_820;
goto block_823;
}
else
{
lean_object* x_824; 
x_824 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_824, 0, x_819);
x_822 = x_824;
goto block_823;
}
block_823:
{
return x_822;
}
}
}
}
else
{
lean_dec(x_809);
lean_dec(x_804);
lean_dec_ref(x_803);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
return x_810;
}
}
else
{
lean_object* x_827; lean_object* x_828; uint8_t x_829; uint8_t x_834; 
lean_dec(x_804);
lean_dec_ref(x_803);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_827 = lean_ctor_get(x_808, 0);
x_834 = !lean_is_exclusive(x_808);
if (x_834 == 0)
{
x_828 = x_808;
x_829 = x_834;
goto block_833;
}
else
{
lean_inc(x_827);
lean_dec(x_808);
x_828 = lean_box(0);
x_829 = x_834;
goto block_833;
}
block_833:
{
lean_object* x_830; 
if (x_829 == 0)
{
x_830 = x_828;
goto block_831;
}
else
{
lean_object* x_832; 
x_832 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_832, 0, x_827);
x_830 = x_832;
goto block_831;
}
block_831:
{
return x_830;
}
}
}
}
block_1009:
{
lean_object* x_839; 
lean_inc(x_3);
x_839 = l_Lean_Parser_Command_visibility_ofAttrKind(x_3);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_840; lean_object* x_841; uint8_t x_842; 
lean_del_object(x_15);
x_840 = lean_ctor_get(x_6, 0);
lean_inc(x_840);
lean_dec_ref(x_6);
x_841 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
x_842 = lean_name_eq(x_836, x_841);
if (x_842 == 0)
{
lean_object* x_843; uint8_t x_844; 
x_843 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__56));
x_844 = lean_name_eq(x_836, x_843);
if (x_844 == 0)
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; 
lean_dec(x_839);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_845 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__58, &l_Lean_Elab_Command_elabElabRulesAux___closed__58_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__58);
x_846 = l_Lean_MessageData_ofName(x_836);
x_847 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_847, 0, x_845);
lean_ctor_set(x_847, 1, x_846);
x_848 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__60, &l_Lean_Elab_Command_elabElabRulesAux___closed__60_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__60);
x_849 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_849, 0, x_847);
lean_ctor_set(x_849, 1, x_848);
x_850 = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(x_840, x_849, x_837, x_838);
lean_dec(x_840);
return x_850;
}
else
{
lean_object* x_851; lean_object* x_852; 
lean_dec(x_836);
x_851 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__62));
lean_inc(x_4);
x_852 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_4, x_3, x_2, x_851, x_837, x_838);
if (lean_obj_tag(x_852) == 0)
{
lean_object* x_853; lean_object* x_854; 
x_853 = lean_ctor_get(x_852, 0);
lean_inc(x_853);
lean_dec_ref(x_852);
x_854 = l_Lean_Elab_Command_getRef___redArg(x_837);
if (lean_obj_tag(x_854) == 0)
{
lean_object* x_855; lean_object* x_856; 
x_855 = lean_ctor_get(x_854, 0);
lean_inc(x_855);
lean_dec_ref(x_854);
x_856 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_837);
if (lean_obj_tag(x_856) == 0)
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; 
x_857 = lean_ctor_get(x_856, 0);
lean_inc(x_857);
lean_dec_ref(x_856);
x_858 = lean_ctor_get(x_837, 5);
lean_inc(x_858);
lean_dec_ref(x_837);
x_859 = l_Lean_SourceInfo_fromRef(x_855, x_842);
lean_dec(x_855);
if (lean_obj_tag(x_858) == 0)
{
lean_object* x_860; lean_object* x_861; 
x_860 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_838);
x_861 = lean_ctor_get(x_860, 0);
lean_inc(x_861);
lean_dec_ref(x_860);
x_787 = x_857;
x_788 = x_840;
x_789 = x_859;
x_790 = x_839;
x_791 = x_853;
x_792 = x_861;
goto block_802;
}
else
{
lean_object* x_862; 
x_862 = lean_ctor_get(x_858, 0);
lean_inc(x_862);
lean_dec_ref(x_858);
x_787 = x_857;
x_788 = x_840;
x_789 = x_859;
x_790 = x_839;
x_791 = x_853;
x_792 = x_862;
goto block_802;
}
}
else
{
lean_object* x_863; lean_object* x_864; uint8_t x_865; uint8_t x_870; 
lean_dec(x_855);
lean_dec(x_853);
lean_dec(x_840);
lean_dec(x_839);
lean_dec_ref(x_837);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_863 = lean_ctor_get(x_856, 0);
x_870 = !lean_is_exclusive(x_856);
if (x_870 == 0)
{
x_864 = x_856;
x_865 = x_870;
goto block_869;
}
else
{
lean_inc(x_863);
lean_dec(x_856);
x_864 = lean_box(0);
x_865 = x_870;
goto block_869;
}
block_869:
{
lean_object* x_866; 
if (x_865 == 0)
{
x_866 = x_864;
goto block_867;
}
else
{
lean_object* x_868; 
x_868 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_868, 0, x_863);
x_866 = x_868;
goto block_867;
}
block_867:
{
return x_866;
}
}
}
}
else
{
lean_dec(x_853);
lean_dec(x_840);
lean_dec(x_839);
lean_dec_ref(x_837);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
return x_854;
}
}
else
{
lean_object* x_871; lean_object* x_872; uint8_t x_873; uint8_t x_878; 
lean_dec(x_840);
lean_dec(x_839);
lean_dec_ref(x_837);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_871 = lean_ctor_get(x_852, 0);
x_878 = !lean_is_exclusive(x_852);
if (x_878 == 0)
{
x_872 = x_852;
x_873 = x_878;
goto block_877;
}
else
{
lean_inc(x_871);
lean_dec(x_852);
x_872 = lean_box(0);
x_873 = x_878;
goto block_877;
}
block_877:
{
lean_object* x_874; 
if (x_873 == 0)
{
x_874 = x_872;
goto block_875;
}
else
{
lean_object* x_876; 
x_876 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_876, 0, x_871);
x_874 = x_876;
goto block_875;
}
block_875:
{
return x_874;
}
}
}
}
}
else
{
lean_object* x_879; lean_object* x_880; 
lean_dec(x_836);
x_879 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__64));
lean_inc(x_4);
x_880 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_4, x_3, x_2, x_879, x_837, x_838);
if (lean_obj_tag(x_880) == 0)
{
lean_object* x_881; lean_object* x_882; 
x_881 = lean_ctor_get(x_880, 0);
lean_inc(x_881);
lean_dec_ref(x_880);
x_882 = l_Lean_Elab_Command_getRef___redArg(x_837);
if (lean_obj_tag(x_882) == 0)
{
lean_object* x_883; lean_object* x_884; 
x_883 = lean_ctor_get(x_882, 0);
lean_inc(x_883);
lean_dec_ref(x_882);
x_884 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_837);
if (lean_obj_tag(x_884) == 0)
{
lean_object* x_885; lean_object* x_886; uint8_t x_887; lean_object* x_888; 
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
lean_dec_ref(x_884);
x_886 = lean_ctor_get(x_837, 5);
lean_inc(x_886);
lean_dec_ref(x_837);
x_887 = 0;
x_888 = l_Lean_SourceInfo_fromRef(x_883, x_887);
lean_dec(x_883);
if (lean_obj_tag(x_886) == 0)
{
lean_object* x_889; lean_object* x_890; 
x_889 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_838);
x_890 = lean_ctor_get(x_889, 0);
lean_inc(x_890);
lean_dec_ref(x_889);
x_652 = x_840;
x_653 = x_888;
x_654 = x_839;
x_655 = x_885;
x_656 = x_881;
x_657 = x_890;
goto block_667;
}
else
{
lean_object* x_891; 
x_891 = lean_ctor_get(x_886, 0);
lean_inc(x_891);
lean_dec_ref(x_886);
x_652 = x_840;
x_653 = x_888;
x_654 = x_839;
x_655 = x_885;
x_656 = x_881;
x_657 = x_891;
goto block_667;
}
}
else
{
lean_object* x_892; lean_object* x_893; uint8_t x_894; uint8_t x_899; 
lean_dec(x_883);
lean_dec(x_881);
lean_dec(x_840);
lean_dec(x_839);
lean_dec_ref(x_837);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_892 = lean_ctor_get(x_884, 0);
x_899 = !lean_is_exclusive(x_884);
if (x_899 == 0)
{
x_893 = x_884;
x_894 = x_899;
goto block_898;
}
else
{
lean_inc(x_892);
lean_dec(x_884);
x_893 = lean_box(0);
x_894 = x_899;
goto block_898;
}
block_898:
{
lean_object* x_895; 
if (x_894 == 0)
{
x_895 = x_893;
goto block_896;
}
else
{
lean_object* x_897; 
x_897 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_897, 0, x_892);
x_895 = x_897;
goto block_896;
}
block_896:
{
return x_895;
}
}
}
}
else
{
lean_dec(x_881);
lean_dec(x_840);
lean_dec(x_839);
lean_dec_ref(x_837);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
return x_882;
}
}
else
{
lean_object* x_900; lean_object* x_901; uint8_t x_902; uint8_t x_907; 
lean_dec(x_840);
lean_dec(x_839);
lean_dec_ref(x_837);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_900 = lean_ctor_get(x_880, 0);
x_907 = !lean_is_exclusive(x_880);
if (x_907 == 0)
{
x_901 = x_880;
x_902 = x_907;
goto block_906;
}
else
{
lean_inc(x_900);
lean_dec(x_880);
x_901 = lean_box(0);
x_902 = x_907;
goto block_906;
}
block_906:
{
lean_object* x_903; 
if (x_902 == 0)
{
x_903 = x_901;
goto block_904;
}
else
{
lean_object* x_905; 
x_905 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_905, 0, x_900);
x_903 = x_905;
goto block_904;
}
block_904:
{
return x_903;
}
}
}
}
}
else
{
lean_object* x_908; uint8_t x_909; 
lean_dec(x_6);
x_908 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__54));
x_909 = lean_name_eq(x_836, x_908);
if (x_909 == 0)
{
lean_object* x_910; uint8_t x_911; 
lean_del_object(x_15);
x_910 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__66));
x_911 = lean_name_eq(x_836, x_910);
if (x_911 == 0)
{
lean_object* x_912; uint8_t x_913; 
x_912 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__68));
x_913 = lean_name_eq(x_836, x_912);
if (x_913 == 0)
{
lean_object* x_914; uint8_t x_915; 
x_914 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__70));
x_915 = lean_name_eq(x_836, x_914);
if (x_915 == 0)
{
lean_object* x_916; uint8_t x_917; 
x_916 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__56));
x_917 = lean_name_eq(x_836, x_916);
if (x_917 == 0)
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; 
lean_dec(x_839);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_918 = lean_obj_once(&l_Lean_Elab_Command_elabElabRulesAux___closed__72, &l_Lean_Elab_Command_elabElabRulesAux___closed__72_once, _init_l_Lean_Elab_Command_elabElabRulesAux___closed__72);
x_919 = l_Lean_MessageData_ofName(x_836);
x_920 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_920, 0, x_918);
lean_ctor_set(x_920, 1, x_919);
x_921 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
x_922 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_922, 0, x_920);
lean_ctor_set(x_922, 1, x_921);
x_923 = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(x_922, x_837, x_838);
return x_923;
}
else
{
lean_object* x_924; lean_object* x_925; 
lean_dec(x_836);
x_924 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__62));
lean_inc(x_4);
x_925 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_4, x_3, x_2, x_924, x_837, x_838);
if (lean_obj_tag(x_925) == 0)
{
lean_object* x_926; lean_object* x_927; 
x_926 = lean_ctor_get(x_925, 0);
lean_inc(x_926);
lean_dec_ref(x_925);
x_927 = l_Lean_Elab_Command_getRef___redArg(x_837);
if (lean_obj_tag(x_927) == 0)
{
lean_object* x_928; lean_object* x_929; 
x_928 = lean_ctor_get(x_927, 0);
lean_inc(x_928);
lean_dec_ref(x_927);
x_929 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_837);
if (lean_obj_tag(x_929) == 0)
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; 
x_930 = lean_ctor_get(x_929, 0);
lean_inc(x_930);
lean_dec_ref(x_929);
x_931 = lean_ctor_get(x_837, 5);
lean_inc(x_931);
lean_dec_ref(x_837);
x_932 = l_Lean_SourceInfo_fromRef(x_928, x_915);
lean_dec(x_928);
if (lean_obj_tag(x_931) == 0)
{
lean_object* x_933; lean_object* x_934; 
x_933 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_838);
x_934 = lean_ctor_get(x_933, 0);
lean_inc(x_934);
lean_dec_ref(x_933);
x_388 = x_926;
x_389 = x_839;
x_390 = x_932;
x_391 = x_930;
x_392 = x_934;
goto block_402;
}
else
{
lean_object* x_935; 
x_935 = lean_ctor_get(x_931, 0);
lean_inc(x_935);
lean_dec_ref(x_931);
x_388 = x_926;
x_389 = x_839;
x_390 = x_932;
x_391 = x_930;
x_392 = x_935;
goto block_402;
}
}
else
{
lean_object* x_936; lean_object* x_937; uint8_t x_938; uint8_t x_943; 
lean_dec(x_928);
lean_dec(x_926);
lean_dec(x_839);
lean_dec_ref(x_837);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_936 = lean_ctor_get(x_929, 0);
x_943 = !lean_is_exclusive(x_929);
if (x_943 == 0)
{
x_937 = x_929;
x_938 = x_943;
goto block_942;
}
else
{
lean_inc(x_936);
lean_dec(x_929);
x_937 = lean_box(0);
x_938 = x_943;
goto block_942;
}
block_942:
{
lean_object* x_939; 
if (x_938 == 0)
{
x_939 = x_937;
goto block_940;
}
else
{
lean_object* x_941; 
x_941 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_941, 0, x_936);
x_939 = x_941;
goto block_940;
}
block_940:
{
return x_939;
}
}
}
}
else
{
lean_dec(x_926);
lean_dec(x_839);
lean_dec_ref(x_837);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
return x_927;
}
}
else
{
lean_object* x_944; lean_object* x_945; uint8_t x_946; uint8_t x_951; 
lean_dec(x_839);
lean_dec_ref(x_837);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_944 = lean_ctor_get(x_925, 0);
x_951 = !lean_is_exclusive(x_925);
if (x_951 == 0)
{
x_945 = x_925;
x_946 = x_951;
goto block_950;
}
else
{
lean_inc(x_944);
lean_dec(x_925);
x_945 = lean_box(0);
x_946 = x_951;
goto block_950;
}
block_950:
{
lean_object* x_947; 
if (x_946 == 0)
{
x_947 = x_945;
goto block_948;
}
else
{
lean_object* x_949; 
x_949 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_949, 0, x_944);
x_947 = x_949;
goto block_948;
}
block_948:
{
return x_947;
}
}
}
}
}
else
{
lean_dec(x_836);
x_803 = x_837;
x_804 = x_839;
x_805 = x_838;
x_806 = x_912;
x_807 = x_911;
goto block_835;
}
}
else
{
lean_dec(x_836);
x_803 = x_837;
x_804 = x_839;
x_805 = x_838;
x_806 = x_912;
x_807 = x_911;
goto block_835;
}
}
else
{
lean_object* x_952; lean_object* x_953; 
lean_dec(x_836);
x_952 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__74));
lean_inc(x_4);
x_953 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_4, x_3, x_2, x_952, x_837, x_838);
if (lean_obj_tag(x_953) == 0)
{
lean_object* x_954; lean_object* x_955; 
x_954 = lean_ctor_get(x_953, 0);
lean_inc(x_954);
lean_dec_ref(x_953);
x_955 = l_Lean_Elab_Command_getRef___redArg(x_837);
if (lean_obj_tag(x_955) == 0)
{
lean_object* x_956; lean_object* x_957; 
x_956 = lean_ctor_get(x_955, 0);
lean_inc(x_956);
lean_dec_ref(x_955);
x_957 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_837);
if (lean_obj_tag(x_957) == 0)
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; 
x_958 = lean_ctor_get(x_957, 0);
lean_inc(x_958);
lean_dec_ref(x_957);
x_959 = lean_ctor_get(x_837, 5);
lean_inc(x_959);
lean_dec_ref(x_837);
x_960 = l_Lean_SourceInfo_fromRef(x_956, x_909);
lean_dec(x_956);
if (lean_obj_tag(x_959) == 0)
{
lean_object* x_961; lean_object* x_962; 
x_961 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_838);
x_962 = lean_ctor_get(x_961, 0);
lean_inc(x_962);
lean_dec_ref(x_961);
x_250 = x_958;
x_251 = x_960;
x_252 = x_839;
x_253 = x_954;
x_254 = x_962;
goto block_265;
}
else
{
lean_object* x_963; 
x_963 = lean_ctor_get(x_959, 0);
lean_inc(x_963);
lean_dec_ref(x_959);
x_250 = x_958;
x_251 = x_960;
x_252 = x_839;
x_253 = x_954;
x_254 = x_963;
goto block_265;
}
}
else
{
lean_object* x_964; lean_object* x_965; uint8_t x_966; uint8_t x_971; 
lean_dec(x_956);
lean_dec(x_954);
lean_dec(x_839);
lean_dec_ref(x_837);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_964 = lean_ctor_get(x_957, 0);
x_971 = !lean_is_exclusive(x_957);
if (x_971 == 0)
{
x_965 = x_957;
x_966 = x_971;
goto block_970;
}
else
{
lean_inc(x_964);
lean_dec(x_957);
x_965 = lean_box(0);
x_966 = x_971;
goto block_970;
}
block_970:
{
lean_object* x_967; 
if (x_966 == 0)
{
x_967 = x_965;
goto block_968;
}
else
{
lean_object* x_969; 
x_969 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_969, 0, x_964);
x_967 = x_969;
goto block_968;
}
block_968:
{
return x_967;
}
}
}
}
else
{
lean_dec(x_954);
lean_dec(x_839);
lean_dec_ref(x_837);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
return x_955;
}
}
else
{
lean_object* x_972; lean_object* x_973; uint8_t x_974; uint8_t x_979; 
lean_dec(x_839);
lean_dec_ref(x_837);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_972 = lean_ctor_get(x_953, 0);
x_979 = !lean_is_exclusive(x_953);
if (x_979 == 0)
{
x_973 = x_953;
x_974 = x_979;
goto block_978;
}
else
{
lean_inc(x_972);
lean_dec(x_953);
x_973 = lean_box(0);
x_974 = x_979;
goto block_978;
}
block_978:
{
lean_object* x_975; 
if (x_974 == 0)
{
x_975 = x_973;
goto block_976;
}
else
{
lean_object* x_977; 
x_977 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_977, 0, x_972);
x_975 = x_977;
goto block_976;
}
block_976:
{
return x_975;
}
}
}
}
}
else
{
lean_object* x_980; lean_object* x_981; 
lean_dec(x_836);
x_980 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__64));
lean_inc(x_4);
x_981 = l_Lean_Elab_Command_elabElabRulesAux___lam__0(x_4, x_3, x_2, x_980, x_837, x_838);
if (lean_obj_tag(x_981) == 0)
{
lean_object* x_982; lean_object* x_983; 
x_982 = lean_ctor_get(x_981, 0);
lean_inc(x_982);
lean_dec_ref(x_981);
x_983 = l_Lean_Elab_Command_getRef___redArg(x_837);
if (lean_obj_tag(x_983) == 0)
{
lean_object* x_984; lean_object* x_985; 
x_984 = lean_ctor_get(x_983, 0);
lean_inc(x_984);
lean_dec_ref(x_983);
x_985 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_837);
if (lean_obj_tag(x_985) == 0)
{
lean_object* x_986; lean_object* x_987; uint8_t x_988; lean_object* x_989; 
x_986 = lean_ctor_get(x_985, 0);
lean_inc(x_986);
lean_dec_ref(x_985);
x_987 = lean_ctor_get(x_837, 5);
lean_inc(x_987);
lean_dec_ref(x_837);
x_988 = 0;
x_989 = l_Lean_SourceInfo_fromRef(x_984, x_988);
lean_dec(x_984);
if (lean_obj_tag(x_987) == 0)
{
lean_object* x_990; lean_object* x_991; 
x_990 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_838);
x_991 = lean_ctor_get(x_990, 0);
lean_inc(x_991);
lean_dec_ref(x_990);
x_136 = x_982;
x_137 = x_989;
x_138 = x_839;
x_139 = x_986;
x_140 = x_991;
goto block_150;
}
else
{
lean_object* x_992; 
x_992 = lean_ctor_get(x_987, 0);
lean_inc(x_992);
lean_dec_ref(x_987);
x_136 = x_982;
x_137 = x_989;
x_138 = x_839;
x_139 = x_986;
x_140 = x_992;
goto block_150;
}
}
else
{
lean_object* x_993; lean_object* x_994; uint8_t x_995; uint8_t x_1000; 
lean_dec(x_984);
lean_dec(x_982);
lean_dec(x_839);
lean_dec_ref(x_837);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_993 = lean_ctor_get(x_985, 0);
x_1000 = !lean_is_exclusive(x_985);
if (x_1000 == 0)
{
x_994 = x_985;
x_995 = x_1000;
goto block_999;
}
else
{
lean_inc(x_993);
lean_dec(x_985);
x_994 = lean_box(0);
x_995 = x_1000;
goto block_999;
}
block_999:
{
lean_object* x_996; 
if (x_995 == 0)
{
x_996 = x_994;
goto block_997;
}
else
{
lean_object* x_998; 
x_998 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_998, 0, x_993);
x_996 = x_998;
goto block_997;
}
block_997:
{
return x_996;
}
}
}
}
else
{
lean_dec(x_982);
lean_dec(x_839);
lean_dec_ref(x_837);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
return x_983;
}
}
else
{
lean_object* x_1001; lean_object* x_1002; uint8_t x_1003; uint8_t x_1008; 
lean_dec(x_839);
lean_dec_ref(x_837);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_1001 = lean_ctor_get(x_981, 0);
x_1008 = !lean_is_exclusive(x_981);
if (x_1008 == 0)
{
x_1002 = x_981;
x_1003 = x_1008;
goto block_1007;
}
else
{
lean_inc(x_1001);
lean_dec(x_981);
x_1002 = lean_box(0);
x_1003 = x_1008;
goto block_1007;
}
block_1007:
{
lean_object* x_1004; 
if (x_1003 == 0)
{
x_1004 = x_1002;
goto block_1005;
}
else
{
lean_object* x_1006; 
x_1006 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1006, 0, x_1001);
x_1004 = x_1006;
goto block_1005;
}
block_1005:
{
return x_1004;
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
lean_object* x_1025; lean_object* x_1026; uint8_t x_1027; uint8_t x_1032; 
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1025 = lean_ctor_get(x_13, 0);
x_1032 = !lean_is_exclusive(x_13);
if (x_1032 == 0)
{
x_1026 = x_13;
x_1027 = x_1032;
goto block_1031;
}
else
{
lean_inc(x_1025);
lean_dec(x_13);
x_1026 = lean_box(0);
x_1027 = x_1032;
goto block_1031;
}
block_1031:
{
lean_object* x_1028; 
if (x_1027 == 0)
{
x_1028 = x_1026;
goto block_1029;
}
else
{
lean_object* x_1030; 
x_1030 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1030, 0, x_1025);
x_1028 = x_1030;
goto block_1029;
}
block_1029:
{
return x_1028;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabElabRulesAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabElabRules___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; 
x_19 = l_Lean_Elab_Command_getRef___redArg(x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; uint8_t x_120; 
x_120 = !lean_is_exclusive(x_21);
if (x_120 == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_21, 0);
lean_dec(x_121);
x_22 = x_21;
x_23 = x_120;
goto block_119;
}
else
{
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_24 = lean_ctor_get(x_16, 5);
x_25 = 0;
x_26 = l_Lean_SourceInfo_fromRef(x_20, x_25);
lean_dec(x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_118; 
x_118 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_17);
lean_dec_ref(x_118);
goto block_117;
}
else
{
goto block_117;
}
block_44:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc_ref(x_29);
x_35 = l_Array_append___redArg(x_29, x_34);
lean_dec_ref(x_34);
lean_inc(x_30);
lean_inc(x_26);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_35);
x_37 = l_Array_append___redArg(x_29, x_15);
lean_inc(x_26);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_30);
lean_ctor_set(x_38, 2, x_37);
lean_inc(x_26);
x_39 = l_Lean_Syntax_node1(x_26, x_1, x_38);
x_40 = l_Lean_Syntax_node8(x_26, x_2, x_28, x_31, x_3, x_32, x_27, x_33, x_36, x_39);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_40);
x_41 = x_22;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
block_59:
{
lean_object* x_52; lean_object* x_53; 
lean_inc_ref(x_47);
x_52 = l_Array_append___redArg(x_47, x_51);
lean_dec_ref(x_51);
lean_inc(x_48);
lean_inc(x_26);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_26);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_52);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec_ref(x_5);
x_54 = lean_ctor_get(x_4, 0);
lean_inc(x_54);
lean_dec_ref(x_4);
x_55 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(x_26);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_26);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Array_mkArray2___redArg(x_56, x_54);
x_27 = x_45;
x_28 = x_46;
x_29 = x_47;
x_30 = x_48;
x_31 = x_49;
x_32 = x_50;
x_33 = x_53;
x_34 = x_57;
goto block_44;
}
else
{
lean_object* x_58; 
x_58 = lean_apply_1(x_5, x_4);
x_27 = x_45;
x_28 = x_46;
x_29 = x_47;
x_30 = x_48;
x_31 = x_49;
x_32 = x_50;
x_33 = x_53;
x_34 = x_58;
goto block_44;
}
}
block_73:
{
lean_object* x_66; lean_object* x_67; 
lean_inc_ref(x_61);
x_66 = l_Array_append___redArg(x_61, x_65);
lean_dec_ref(x_65);
lean_inc(x_62);
lean_inc(x_26);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_26);
lean_ctor_set(x_67, 1, x_62);
lean_ctor_set(x_67, 2, x_66);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_6, 0);
lean_inc(x_68);
lean_dec_ref(x_6);
x_69 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(x_26);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_26);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Array_mkArray2___redArg(x_70, x_68);
x_45 = x_67;
x_46 = x_60;
x_47 = x_61;
x_48 = x_62;
x_49 = x_63;
x_50 = x_64;
x_51 = x_71;
goto block_59;
}
else
{
lean_object* x_72; 
lean_inc_ref(x_5);
x_72 = lean_apply_1(x_5, x_6);
x_45 = x_67;
x_46 = x_60;
x_47 = x_61;
x_48 = x_62;
x_49 = x_63;
x_50 = x_64;
x_51 = x_72;
goto block_59;
}
}
block_93:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_inc_ref(x_75);
x_78 = l_Array_append___redArg(x_75, x_77);
lean_dec_ref(x_77);
lean_inc(x_76);
lean_inc(x_26);
x_79 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_79, 0, x_26);
lean_ctor_set(x_79, 1, x_76);
lean_ctor_set(x_79, 2, x_78);
lean_inc(x_26);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_26);
lean_ctor_set(x_80, 1, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_81; 
x_81 = lean_mk_empty_array_with_capacity(x_8);
x_60 = x_74;
x_61 = x_75;
x_62 = x_76;
x_63 = x_79;
x_64 = x_80;
x_65 = x_81;
goto block_73;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_82 = lean_ctor_get(x_14, 0);
lean_inc(x_82);
lean_dec_ref(x_14);
x_83 = lean_mk_syntax_ident(x_82);
x_84 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc(x_26);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_26);
lean_ctor_set(x_85, 1, x_84);
x_86 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__2));
lean_inc(x_26);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_26);
lean_ctor_set(x_87, 1, x_86);
x_88 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(x_26);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_26);
lean_ctor_set(x_89, 1, x_88);
x_90 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
lean_inc(x_26);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_26);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Array_mkArray5___redArg(x_85, x_87, x_89, x_83, x_91);
x_60 = x_74;
x_61 = x_75;
x_62 = x_76;
x_63 = x_79;
x_64 = x_80;
x_65 = x_92;
goto block_73;
}
}
block_111:
{
lean_object* x_97; lean_object* x_98; 
lean_inc_ref(x_94);
x_97 = l_Array_append___redArg(x_94, x_96);
lean_dec_ref(x_96);
lean_inc(x_95);
lean_inc(x_26);
x_98 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_98, 0, x_26);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set(x_98, 2, x_97);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_99 = lean_ctor_get(x_9, 0);
x_100 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
x_101 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_100);
x_102 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(x_26);
x_103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_103, 0, x_26);
lean_ctor_set(x_103, 1, x_102);
lean_inc_ref(x_94);
x_104 = l_Array_append___redArg(x_94, x_99);
lean_inc(x_95);
lean_inc(x_26);
x_105 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_105, 0, x_26);
lean_ctor_set(x_105, 1, x_95);
lean_ctor_set(x_105, 2, x_104);
x_106 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(x_26);
x_107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_107, 0, x_26);
lean_ctor_set(x_107, 1, x_106);
lean_inc(x_26);
x_108 = l_Lean_Syntax_node3(x_26, x_101, x_103, x_105, x_107);
x_109 = l_Array_mkArray1___redArg(x_108);
x_74 = x_98;
x_75 = x_94;
x_76 = x_95;
x_77 = x_109;
goto block_93;
}
else
{
lean_object* x_110; 
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
x_110 = lean_mk_empty_array_with_capacity(x_8);
x_74 = x_98;
x_75 = x_94;
x_76 = x_95;
x_77 = x_110;
goto block_93;
}
}
block_117:
{
lean_object* x_112; lean_object* x_113; 
x_112 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
x_113 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_13, 0);
lean_inc(x_114);
lean_dec_ref(x_13);
x_115 = l_Array_mkArray1___redArg(x_114);
x_94 = x_113;
x_95 = x_112;
x_96 = x_115;
goto block_111;
}
else
{
lean_object* x_116; 
lean_dec(x_13);
x_116 = lean_mk_empty_array_with_capacity(x_8);
x_94 = x_113;
x_95 = x_112;
x_96 = x_116;
goto block_111;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_129; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = lean_ctor_get(x_21, 0);
x_129 = !lean_is_exclusive(x_21);
if (x_129 == 0)
{
x_123 = x_21;
x_124 = x_129;
goto block_128;
}
else
{
lean_inc(x_122);
lean_dec(x_21);
x_123 = lean_box(0);
x_124 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_125; 
if (x_124 == 0)
{
x_125 = x_123;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_122);
x_125 = x_127;
goto block_126;
}
block_126:
{
return x_125;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_137; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_130 = lean_ctor_get(x_19, 0);
x_137 = !lean_is_exclusive(x_19);
if (x_137 == 0)
{
x_131 = x_19;
x_132 = x_137;
goto block_136;
}
else
{
lean_inc(x_130);
lean_dec(x_19);
x_131 = lean_box(0);
x_132 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_133; 
if (x_132 == 0)
{
x_133 = x_131;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_130);
x_133 = x_135;
goto block_134;
}
block_134:
{
return x_133;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__1___boxed(lean_object** _args) {
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
lean_object* x_19; 
x_19 = l_Lean_Elab_Command_elabElabRules___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec(x_8);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
x_7 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
x_8 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
x_9 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
lean_inc(x_2);
x_10 = l_Lean_Syntax_isOfKind(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_165; uint8_t x_166; 
x_12 = lean_unsigned_to_nat(0u);
x_165 = l_Lean_Syntax_getArg(x_2, x_12);
x_166 = l_Lean_Syntax_isNone(x_165);
if (x_166 == 0)
{
lean_object* x_167; uint8_t x_168; 
x_167 = lean_unsigned_to_nat(1u);
lean_inc(x_165);
x_168 = l_Lean_Syntax_matchesNull(x_165, x_167);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_165);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_169 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_170 = l_Lean_Syntax_getArg(x_165, x_12);
lean_dec(x_165);
x_171 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7));
lean_inc(x_170);
x_172 = l_Lean_Syntax_isOfKind(x_170, x_171);
if (x_172 == 0)
{
lean_object* x_173; 
lean_dec(x_170);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_173 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_173;
}
else
{
lean_object* x_174; 
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_170);
x_148 = x_174;
x_149 = x_3;
x_150 = x_4;
goto block_164;
}
}
}
else
{
lean_object* x_175; 
lean_dec(x_165);
x_175 = lean_box(0);
x_148 = x_175;
x_149 = x_3;
x_150 = x_4;
goto block_164;
}
block_46:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_unsigned_to_nat(7u);
x_21 = l_Lean_Syntax_getArg(x_2, x_20);
lean_dec(x_2);
x_22 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
x_23 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__2));
lean_inc(x_21);
x_24 = l_Lean_Syntax_isOfKind(x_21, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_1);
x_25 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___lam__1___boxed), 18, 13);
lean_closure_set(x_26, 0, x_23);
lean_closure_set(x_26, 1, x_9);
lean_closure_set(x_26, 2, x_16);
lean_closure_set(x_26, 3, x_19);
lean_closure_set(x_26, 4, x_1);
lean_closure_set(x_26, 5, x_15);
lean_closure_set(x_26, 6, x_8);
lean_closure_set(x_26, 7, x_12);
lean_closure_set(x_26, 8, x_13);
lean_closure_set(x_26, 9, x_6);
lean_closure_set(x_26, 10, x_7);
lean_closure_set(x_26, 11, x_22);
lean_closure_set(x_26, 12, x_17);
x_27 = l_Lean_Syntax_getArg(x_21, x_12);
lean_dec(x_21);
x_28 = l_Lean_Syntax_getArgs(x_27);
lean_dec(x_27);
x_29 = l_Lean_Elab_Command_expandNoKindMacroRulesAux(x_28, x_8, x_26, x_14, x_18);
lean_dec_ref(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
x_30 = lean_ctor_get(x_29, 0);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
x_31 = x_29;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_30);
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
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
x_38 = lean_ctor_get(x_29, 0);
x_45 = !lean_is_exclusive(x_29);
if (x_45 == 0)
{
x_39 = x_29;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
block_63:
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_unsigned_to_nat(6u);
x_56 = l_Lean_Syntax_getArg(x_2, x_55);
x_57 = l_Lean_Syntax_isNone(x_56);
if (x_57 == 0)
{
uint8_t x_58; 
lean_inc(x_56);
x_58 = l_Lean_Syntax_matchesNull(x_56, x_51);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_56);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_2);
lean_dec_ref(x_1);
x_59 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Syntax_getArg(x_56, x_50);
lean_dec(x_56);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_13 = x_47;
x_14 = x_53;
x_15 = x_52;
x_16 = x_48;
x_17 = x_49;
x_18 = x_54;
x_19 = x_61;
goto block_46;
}
}
else
{
lean_object* x_62; 
lean_dec(x_56);
x_62 = lean_box(0);
x_13 = x_47;
x_14 = x_53;
x_15 = x_52;
x_16 = x_48;
x_17 = x_49;
x_18 = x_54;
x_19 = x_62;
goto block_46;
}
}
block_93:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_unsigned_to_nat(7u);
x_74 = l_Lean_Syntax_getArg(x_2, x_73);
lean_dec(x_2);
x_75 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
x_76 = l_Lean_Name_mkStr4(x_6, x_7, x_64, x_75);
lean_inc(x_74);
x_77 = l_Lean_Syntax_isOfKind(x_74, x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
x_78 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Lean_TSyntax_getId(x_65);
lean_dec(x_65);
lean_inc_ref(x_71);
x_80 = l_Lean_Elab_Command_resolveSyntaxKind(x_79, x_71, x_72);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = l_Lean_Syntax_getArg(x_74, x_12);
lean_dec(x_74);
x_83 = l_Lean_Syntax_getArgs(x_82);
lean_dec(x_82);
x_84 = l_Lean_Elab_Command_elabElabRulesAux(x_69, x_68, x_67, x_81, x_66, x_70, x_83, x_71, x_72);
lean_dec(x_72);
lean_dec(x_66);
lean_dec(x_68);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_92; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
x_85 = lean_ctor_get(x_80, 0);
x_92 = !lean_is_exclusive(x_80);
if (x_92 == 0)
{
x_86 = x_80;
x_87 = x_92;
goto block_91;
}
else
{
lean_inc(x_85);
lean_dec(x_80);
x_86 = lean_box(0);
x_87 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_88; 
if (x_87 == 0)
{
x_88 = x_86;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_85);
x_88 = x_90;
goto block_89;
}
block_89:
{
return x_88;
}
}
}
}
}
block_112:
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_unsigned_to_nat(6u);
x_105 = l_Lean_Syntax_getArg(x_2, x_104);
x_106 = l_Lean_Syntax_isNone(x_105);
if (x_106 == 0)
{
uint8_t x_107; 
lean_inc(x_105);
x_107 = l_Lean_Syntax_matchesNull(x_105, x_97);
if (x_107 == 0)
{
lean_object* x_108; 
lean_dec(x_105);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_96);
lean_dec_ref(x_95);
lean_dec(x_2);
x_108 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = l_Lean_Syntax_getArg(x_105, x_94);
lean_dec(x_105);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_64 = x_95;
x_65 = x_96;
x_66 = x_101;
x_67 = x_98;
x_68 = x_100;
x_69 = x_99;
x_70 = x_110;
x_71 = x_102;
x_72 = x_103;
goto block_93;
}
}
else
{
lean_object* x_111; 
lean_dec(x_105);
x_111 = lean_box(0);
x_64 = x_95;
x_65 = x_96;
x_66 = x_101;
x_67 = x_98;
x_68 = x_100;
x_69 = x_99;
x_70 = x_111;
x_71 = x_102;
x_72 = x_103;
goto block_93;
}
}
block_147:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_118 = lean_unsigned_to_nat(2u);
x_119 = l_Lean_Syntax_getArg(x_2, x_118);
x_120 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
x_121 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(x_119);
x_122 = l_Lean_Syntax_isOfKind(x_119, x_121);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_2);
lean_dec_ref(x_1);
x_123 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_124 = lean_unsigned_to_nat(4u);
x_125 = l_Lean_Syntax_getArg(x_2, x_124);
lean_inc(x_125);
x_126 = l_Lean_Syntax_matchesNull(x_125, x_12);
if (x_126 == 0)
{
lean_object* x_127; uint8_t x_128; 
lean_dec_ref(x_1);
x_127 = lean_unsigned_to_nat(5u);
lean_inc(x_125);
x_128 = l_Lean_Syntax_matchesNull(x_125, x_127);
if (x_128 == 0)
{
lean_object* x_129; 
lean_dec(x_125);
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_2);
x_129 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_unsigned_to_nat(3u);
x_131 = l_Lean_Syntax_getArg(x_125, x_130);
lean_dec(x_125);
x_132 = l_Lean_Syntax_getArg(x_2, x_127);
x_133 = l_Lean_Syntax_isNone(x_132);
if (x_133 == 0)
{
uint8_t x_134; 
lean_inc(x_132);
x_134 = l_Lean_Syntax_matchesNull(x_132, x_118);
if (x_134 == 0)
{
lean_object* x_135; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_2);
x_135 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = l_Lean_Syntax_getArg(x_132, x_116);
lean_dec(x_132);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_94 = x_116;
x_95 = x_120;
x_96 = x_131;
x_97 = x_118;
x_98 = x_119;
x_99 = x_114;
x_100 = x_117;
x_101 = x_137;
x_102 = x_113;
x_103 = x_115;
goto block_112;
}
}
else
{
lean_object* x_138; 
lean_dec(x_132);
x_138 = lean_box(0);
x_94 = x_116;
x_95 = x_120;
x_96 = x_131;
x_97 = x_118;
x_98 = x_119;
x_99 = x_114;
x_100 = x_117;
x_101 = x_138;
x_102 = x_113;
x_103 = x_115;
goto block_112;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
lean_dec(x_125);
x_139 = lean_unsigned_to_nat(5u);
x_140 = l_Lean_Syntax_getArg(x_2, x_139);
x_141 = l_Lean_Syntax_isNone(x_140);
if (x_141 == 0)
{
uint8_t x_142; 
lean_inc(x_140);
x_142 = l_Lean_Syntax_matchesNull(x_140, x_118);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_140);
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_2);
lean_dec_ref(x_1);
x_143 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = l_Lean_Syntax_getArg(x_140, x_116);
lean_dec(x_140);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_47 = x_117;
x_48 = x_119;
x_49 = x_114;
x_50 = x_116;
x_51 = x_118;
x_52 = x_145;
x_53 = x_113;
x_54 = x_115;
goto block_63;
}
}
else
{
lean_object* x_146; 
lean_dec(x_140);
x_146 = lean_box(0);
x_47 = x_117;
x_48 = x_119;
x_49 = x_114;
x_50 = x_116;
x_51 = x_118;
x_52 = x_146;
x_53 = x_113;
x_54 = x_115;
goto block_63;
}
}
}
}
block_164:
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_151 = lean_unsigned_to_nat(1u);
x_152 = l_Lean_Syntax_getArg(x_2, x_151);
x_153 = l_Lean_Syntax_isNone(x_152);
if (x_153 == 0)
{
uint8_t x_154; 
lean_inc(x_152);
x_154 = l_Lean_Syntax_matchesNull(x_152, x_151);
if (x_154 == 0)
{
lean_object* x_155; 
lean_dec(x_152);
lean_dec(x_150);
lean_dec_ref(x_149);
lean_dec(x_148);
lean_dec(x_2);
lean_dec_ref(x_1);
x_155 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_156 = l_Lean_Syntax_getArg(x_152, x_12);
lean_dec(x_152);
x_157 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5));
lean_inc(x_156);
x_158 = l_Lean_Syntax_isOfKind(x_156, x_157);
if (x_158 == 0)
{
lean_object* x_159; 
lean_dec(x_156);
lean_dec(x_150);
lean_dec_ref(x_149);
lean_dec(x_148);
lean_dec(x_2);
lean_dec_ref(x_1);
x_159 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = l_Lean_Syntax_getArg(x_156, x_151);
lean_dec(x_156);
x_161 = l_Lean_Syntax_getArgs(x_160);
lean_dec(x_160);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_161);
x_113 = x_149;
x_114 = x_148;
x_115 = x_150;
x_116 = x_151;
x_117 = x_162;
goto block_147;
}
}
}
else
{
lean_object* x_163; 
lean_dec(x_152);
x_163 = lean_box(0);
x_113 = x_149;
x_114 = x_148;
x_115 = x_150;
x_116 = x_151;
x_117 = x_163;
goto block_147;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_elabElabRules___lam__2(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___closed__1));
x_6 = l_Lean_Elab_Command_adaptExpander(x_5, x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabElabRules(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
x_4 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6));
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_4);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget_borrowed(x_3, x_2);
lean_inc_ref(x_4);
lean_inc(x_9);
x_10 = l_Lean_Elab_Command_expandMacroArg(x_9, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_18 = lean_ctor_get(x_10, 0);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
x_19 = x_10;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(x_7, x_8, x_3, x_4, x_5);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lean_inheritedTraceOptions;
x_5 = lean_st_ref_get(x_4);
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
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___closed__1));
x_15 = l_Lean_Name_append(x_14, x_1);
x_16 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_5, x_10, x_15);
lean_dec(x_15);
lean_dec_ref(x_10);
lean_dec(x_5);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_getRef___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_55; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(x_2, x_4);
x_9 = lean_ctor_get(x_8, 0);
x_55 = !lean_is_exclusive(x_8);
if (x_55 == 0)
{
x_10 = x_8;
x_11 = x_55;
goto block_54;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_53; 
x_12 = lean_st_ref_take(x_4);
x_13 = lean_ctor_get(x_12, 9);
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_19 = lean_ctor_get(x_12, 5);
x_20 = lean_ctor_get(x_12, 6);
x_21 = lean_ctor_get(x_12, 7);
x_22 = lean_ctor_get(x_12, 8);
x_23 = lean_ctor_get(x_12, 10);
x_53 = !lean_is_exclusive(x_12);
if (x_53 == 0)
{
x_24 = x_12;
x_25 = x_53;
goto block_52;
}
else
{
lean_inc(x_23);
lean_inc(x_13);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_24 = lean_box(0);
x_25 = x_53;
goto block_52;
}
block_52:
{
uint64_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_51; 
x_26 = lean_ctor_get_uint64(x_13, sizeof(void*)*1);
x_27 = lean_ctor_get(x_13, 0);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
x_28 = x_13;
x_29 = x_51;
goto block_50;
}
else
{
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_box(0);
x_29 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_30; double x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_box(0);
x_31 = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__0);
x_32 = 0;
x_33 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__1));
x_34 = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set_float(x_34, sizeof(void*)*3, x_31);
lean_ctor_set_float(x_34, sizeof(void*)*3 + 8, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*3 + 16, x_32);
x_35 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__2));
x_36 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_9);
lean_ctor_set(x_36, 2, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_PersistentArray_push___redArg(x_27, x_37);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_38);
x_39 = x_28;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set_uint64(x_49, sizeof(void*)*1, x_26);
x_39 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_40; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 9, x_39);
x_40 = x_24;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_47, 0, x_14);
lean_ctor_set(x_47, 1, x_15);
lean_ctor_set(x_47, 2, x_16);
lean_ctor_set(x_47, 3, x_17);
lean_ctor_set(x_47, 4, x_18);
lean_ctor_set(x_47, 5, x_19);
lean_ctor_set(x_47, 6, x_20);
lean_ctor_set(x_47, 7, x_21);
lean_ctor_set(x_47, 8, x_22);
lean_ctor_set(x_47, 9, x_39);
lean_ctor_set(x_47, 10, x_23);
x_40 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_st_ref_set(x_4, x_40);
x_42 = lean_box(0);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_42);
x_43 = x_10;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_42);
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
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_56 = lean_ctor_get(x_6, 0);
x_63 = !lean_is_exclusive(x_6);
if (x_63 == 0)
{
x_57 = x_6;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_6);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_24; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_9);
x_11 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg(x_9, x_3);
x_12 = lean_ctor_get(x_11, 0);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
x_13 = x_11;
x_14 = x_24;
goto block_23;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_24;
goto block_23;
}
block_23:
{
uint8_t x_15; 
x_15 = lean_unbox(x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_del_object(x_13);
lean_dec(x_10);
lean_dec(x_9);
x_1 = x_8;
goto _start;
}
else
{
lean_object* x_17; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 3);
lean_ctor_set(x_13, 0, x_10);
x_17 = x_13;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_10);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_MessageData_ofFormat(x_17);
x_19 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(x_9, x_18, x_2, x_3);
if (lean_obj_tag(x_19) == 0)
{
lean_dec_ref(x_19);
x_1 = x_8;
goto _start;
}
else
{
lean_dec(x_8);
return x_19;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_5 = 0;
x_6 = l_Lean_Environment_setExporting(x_1, x_5);
lean_inc(x_2);
x_7 = l_Lean_mkPrivateName(x_6, x_2);
x_8 = 1;
lean_inc_ref(x_6);
x_9 = l_Lean_Environment_contains(x_6, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_privateToUserName(x_2);
x_11 = l_Lean_Environment_contains(x_6, x_10, x_8);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_14 = lean_box(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_15; 
x_7 = lean_ctor_get(x_5, 1);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_8 = x_5;
x_9 = x_15;
goto block_14;
}
else
{
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_10);
x_11 = x_8;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_7);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_45; 
x_17 = lean_ctor_get(x_6, 0);
x_45 = !lean_is_exclusive(x_6);
if (x_45 == 0)
{
x_18 = x_6;
x_19 = x_45;
goto block_44;
}
else
{
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_box(0);
x_19 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_30; 
lean_del_object(x_18);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_dec_ref(x_5);
x_22 = lean_ctor_get(x_20, 0);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
x_23 = x_20;
x_24 = x_30;
goto block_29;
}
else
{
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_22);
x_25 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_26; 
x_26 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg(x_25, x_21);
lean_dec_ref(x_25);
return x_26;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_43; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec_ref(x_5);
x_32 = lean_ctor_get(x_20, 0);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
x_33 = x_20;
x_34 = x_43;
goto block_42;
}
else
{
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_box(0);
x_34 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_35; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_32);
x_35 = x_18;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_32);
x_35 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_36; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_35);
x_36 = x_33;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_35);
x_36 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_37; 
x_37 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg(x_36, x_31);
lean_dec_ref(x_36);
return x_37;
}
}
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
x_46 = lean_ctor_get(x_5, 0);
x_47 = lean_ctor_get(x_5, 1);
x_54 = !lean_is_exclusive(x_5);
if (x_54 == 0)
{
x_48 = x_5;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_5);
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
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_47);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_instBEqExtraModUse_beq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___closed__1);
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_instBEqExtraModUse_beq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableExtraModUse_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__1));
x_2 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__0));
x_3 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__12));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_44; uint8_t x_45; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
lean_dec_ref(x_8);
x_10 = lean_st_ref_get(x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__2);
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_9);
lean_ctor_set_uint8(x_13, sizeof(void*)*1 + 1, x_2);
x_14 = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
x_15 = lean_box(1);
x_16 = lean_box(0);
x_44 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_12, x_14, x_11, x_15, x_16);
x_45 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg(x_44, x_13);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_54; lean_object* x_55; uint8_t x_68; 
x_46 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__4));
x_47 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg(x_46, x_5);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_68 = lean_unbox(x_48);
lean_dec(x_48);
if (x_68 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
x_17 = x_5;
goto block_43;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__11);
if (x_9 == 0)
{
lean_object* x_78; 
x_78 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__16));
x_70 = x_78;
goto block_77;
}
else
{
lean_object* x_79; 
x_79 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__17));
x_70 = x_79;
goto block_77;
}
block_77:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = l_Lean_stringToMessageData(x_70);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__13);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
if (x_2 == 0)
{
lean_object* x_75; 
x_75 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__14));
x_54 = x_74;
x_55 = x_75;
goto block_67;
}
else
{
lean_object* x_76; 
x_76 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__15));
x_54 = x_74;
x_55 = x_76;
goto block_67;
}
}
}
block_53:
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(x_46, x_51, x_4, x_5);
if (lean_obj_tag(x_52) == 0)
{
lean_dec_ref(x_52);
x_17 = x_5;
goto block_43;
}
else
{
lean_dec_ref(x_13);
return x_52;
}
}
block_67:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_56 = l_Lean_stringToMessageData(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__6);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_MessageData_ofName(x_1);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_Name_isAnonymous(x_3);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__8);
x_64 = l_Lean_MessageData_ofName(x_3);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_49 = x_61;
x_50 = x_65;
goto block_53;
}
else
{
lean_object* x_66; 
lean_dec(x_3);
x_66 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___closed__9);
x_49 = x_61;
x_50 = x_66;
goto block_53;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec_ref(x_13);
lean_dec(x_3);
lean_dec(x_1);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
block_43:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_42; 
x_18 = lean_st_ref_take(x_17);
x_19 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_18, 2);
x_23 = lean_ctor_get(x_18, 3);
x_24 = lean_ctor_get(x_18, 4);
x_25 = lean_ctor_get(x_18, 5);
x_26 = lean_ctor_get(x_18, 6);
x_27 = lean_ctor_get(x_18, 7);
x_28 = lean_ctor_get(x_18, 8);
x_29 = lean_ctor_get(x_18, 9);
x_30 = lean_ctor_get(x_18, 10);
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
x_31 = x_18;
x_32 = x_42;
goto block_41;
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
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_31 = lean_box(0);
x_32 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 2);
lean_inc(x_33);
lean_dec_ref(x_19);
x_34 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_14, x_20, x_13, x_33, x_16);
lean_dec(x_33);
if (x_32 == 0)
{
lean_ctor_set(x_31, 0, x_34);
x_35 = x_31;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_21);
lean_ctor_set(x_40, 2, x_22);
lean_ctor_set(x_40, 3, x_23);
lean_ctor_set(x_40, 4, x_24);
lean_ctor_set(x_40, 5, x_25);
lean_ctor_set(x_40, 6, x_26);
lean_ctor_set(x_40, 7, x_27);
lean_ctor_set(x_40, 8, x_28);
lean_ctor_set(x_40, 9, x_29);
lean_ctor_set(x_40, 10, x_30);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_st_ref_set(x_17, x_35);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4(x_1, x_7, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_12 = l_Lean_Environment_header(x_1);
x_13 = lean_ctor_get(x_12, 3);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_instInhabitedEffectiveImport_default;
x_15 = lean_array_uget_borrowed(x_3, x_5);
x_16 = lean_array_get(x_14, x_13, x_15);
lean_dec_ref(x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = 0;
lean_inc(x_2);
x_20 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4(x_18, x_19, x_2, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; 
lean_dec_ref(x_20);
x_21 = lean_box(0);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
x_5 = x_23;
x_6 = x_21;
goto _start;
}
else
{
lean_dec(x_2);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__5(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___closed__0(void) {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(1723u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_20; 
x_20 = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___closed__0);
x_5 = x_20;
goto block_19;
}
else
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_5 = x_21;
goto block_19;
}
block_19:
{
uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg(x_2, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__1));
x_2 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__0));
x_3 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_10; lean_object* x_11; lean_object* x_25; 
x_6 = lean_st_ref_get(x_4);
x_10 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_10);
lean_dec(x_6);
x_25 = l_Lean_Environment_getModuleIdxFor_x3f(x_10, x_1);
if (lean_obj_tag(x_25) == 0)
{
lean_dec_ref(x_10);
lean_dec(x_1);
goto block_9;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_Environment_header(x_10);
x_28 = lean_ctor_get(x_27, 3);
lean_inc_ref(x_28);
lean_dec_ref(x_27);
x_29 = lean_array_get_size(x_28);
x_30 = lean_nat_dec_lt(x_26, x_29);
if (x_30 == 0)
{
lean_dec_ref(x_28);
lean_dec(x_26);
lean_dec_ref(x_10);
lean_dec(x_1);
goto block_9;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_st_ref_get(x_4);
x_32 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_32);
lean_dec(x_31);
x_33 = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__2);
x_34 = lean_array_fget(x_28, x_26);
lean_dec(x_26);
lean_dec_ref(x_28);
if (x_2 == 0)
{
lean_dec_ref(x_32);
x_35 = x_2;
goto block_46;
}
else
{
uint8_t x_47; 
lean_inc(x_1);
x_47 = l_Lean_isMarkedMeta(x_32, x_1);
if (x_47 == 0)
{
x_35 = x_2;
goto block_46;
}
else
{
uint8_t x_48; 
x_48 = 0;
x_35 = x_48;
goto block_46;
}
}
block_46:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
lean_inc(x_1);
x_38 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4(x_37, x_35, x_1, x_3, x_4);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_38);
x_39 = l_Lean_indirectModUseExt;
x_40 = lean_box(1);
x_41 = lean_box(0);
lean_inc_ref(x_10);
x_42 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_33, x_39, x_10, x_40, x_41);
x_43 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg(x_42, x_1);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___closed__3));
x_11 = x_44;
goto block_24;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec_ref(x_43);
x_11 = x_45;
goto block_24;
}
}
else
{
lean_dec_ref(x_10);
lean_dec(x_1);
return x_38;
}
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_24:
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_box(0);
x_13 = lean_array_size(x_11);
x_14 = 0;
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__5(x_10, x_1, x_11, x_13, x_14, x_12, x_3, x_4);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
x_16 = x_15;
x_17 = x_22;
goto block_21;
}
else
{
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_12);
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_12);
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
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(x_1, x_6, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_2);
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
x_10 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(x_7, x_9, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_10);
x_11 = lean_box(0);
x_1 = x_8;
x_2 = x_11;
goto _start;
}
else
{
lean_dec(x_8);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__3);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__4);
x_2 = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__2));
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___closed__5);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_st_ref_get(x_3);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Elab_Command_instInhabitedScope_default;
x_10 = l_List_head_x21___redArg(x_9, x_8);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_Command_getScope___redArg(x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Elab_Command_getScope___redArg(x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_2);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_24, 0, x_6);
lean_inc_ref(x_6);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(x_25, 0, x_6);
lean_inc(x_14);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(x_26, 0, x_14);
lean_inc(x_17);
lean_inc(x_14);
lean_inc_ref(x_6);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed), 6, 3);
lean_closure_set(x_27, 0, x_6);
lean_closure_set(x_27, 1, x_14);
lean_closure_set(x_27, 2, x_17);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(x_28, 0, x_6);
lean_closure_set(x_28, 1, x_11);
lean_closure_set(x_28, 2, x_14);
lean_closure_set(x_28, 3, x_17);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 4, x_28);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_3);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_30 = x_104;
goto block_102;
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_23, 0);
lean_inc(x_105);
x_30 = x_105;
goto block_102;
}
block_102:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_st_ref_get(x_3);
x_32 = lean_ctor_get(x_31, 5);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_st_ref_get(x_3);
x_34 = lean_ctor_get(x_33, 4);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_22);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_21);
lean_ctor_set(x_35, 3, x_22);
lean_ctor_set(x_35, 4, x_32);
lean_ctor_set(x_35, 5, x_19);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_apply_2(x_1, x_35, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 2);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_box(0);
x_45 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg(x_43, x_44, x_2, x_3);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_82; 
lean_dec_ref(x_45);
x_46 = lean_st_ref_take(x_3);
x_47 = lean_ctor_get(x_46, 0);
x_48 = lean_ctor_get(x_46, 1);
x_49 = lean_ctor_get(x_46, 2);
x_50 = lean_ctor_get(x_46, 3);
x_51 = lean_ctor_get(x_46, 5);
x_52 = lean_ctor_get(x_46, 6);
x_53 = lean_ctor_get(x_46, 7);
x_54 = lean_ctor_get(x_46, 8);
x_55 = lean_ctor_get(x_46, 9);
x_56 = lean_ctor_get(x_46, 10);
x_82 = !lean_is_exclusive(x_46);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_46, 4);
lean_dec(x_83);
x_57 = x_46;
x_58 = x_82;
goto block_81;
}
else
{
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_46);
x_57 = lean_box(0);
x_58 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_59; 
if (x_58 == 0)
{
lean_ctor_set(x_57, 4, x_41);
x_59 = x_57;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_80, 0, x_47);
lean_ctor_set(x_80, 1, x_48);
lean_ctor_set(x_80, 2, x_49);
lean_ctor_set(x_80, 3, x_50);
lean_ctor_set(x_80, 4, x_41);
lean_ctor_set(x_80, 5, x_51);
lean_ctor_set(x_80, 6, x_52);
lean_ctor_set(x_80, 7, x_53);
lean_ctor_set(x_80, 8, x_54);
lean_ctor_set(x_80, 9, x_55);
lean_ctor_set(x_80, 10, x_56);
x_59 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_st_ref_set(x_3, x_59);
x_61 = l_List_reverse___redArg(x_42);
x_62 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(x_61, x_2, x_3);
lean_dec_ref(x_2);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; uint8_t x_69; 
x_69 = !lean_is_exclusive(x_62);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_62, 0);
lean_dec(x_70);
x_63 = x_62;
x_64 = x_69;
goto block_68;
}
else
{
lean_dec(x_62);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
lean_ctor_set(x_63, 0, x_40);
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_40);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
lean_dec(x_40);
x_71 = lean_ctor_get(x_62, 0);
x_78 = !lean_is_exclusive(x_62);
if (x_78 == 0)
{
x_72 = x_62;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_62);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_91; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_2);
x_84 = lean_ctor_get(x_45, 0);
x_91 = !lean_is_exclusive(x_45);
if (x_91 == 0)
{
x_85 = x_45;
x_86 = x_91;
goto block_90;
}
else
{
lean_inc(x_84);
lean_dec(x_45);
x_85 = lean_box(0);
x_86 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_87; 
if (x_86 == 0)
{
x_87 = x_85;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_84);
x_87 = x_89;
goto block_88;
}
block_88:
{
return x_87;
}
}
}
}
else
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_38, 0);
lean_inc(x_92);
lean_dec_ref(x_38);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc_ref(x_94);
lean_dec_ref(x_92);
x_95 = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0));
x_96 = lean_string_dec_eq(x_94, x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_97, 0, x_94);
x_98 = l_Lean_MessageData_ofFormat(x_97);
x_99 = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(x_93, x_98, x_2, x_3);
lean_dec(x_93);
return x_99;
}
else
{
lean_object* x_100; 
lean_dec_ref(x_94);
lean_dec_ref(x_2);
x_100 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg(x_93);
return x_100;
}
}
else
{
lean_object* x_101; 
lean_dec_ref(x_2);
x_101 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_101;
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_113; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_106 = lean_ctor_get(x_20, 0);
x_113 = !lean_is_exclusive(x_20);
if (x_113 == 0)
{
x_107 = x_20;
x_108 = x_113;
goto block_112;
}
else
{
lean_inc(x_106);
lean_dec(x_20);
x_107 = lean_box(0);
x_108 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_109; 
if (x_108 == 0)
{
x_109 = x_107;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_106);
x_109 = x_111;
goto block_110;
}
block_110:
{
return x_109;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_121; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_114 = lean_ctor_get(x_18, 0);
x_121 = !lean_is_exclusive(x_18);
if (x_121 == 0)
{
x_115 = x_18;
x_116 = x_121;
goto block_120;
}
else
{
lean_inc(x_114);
lean_dec(x_18);
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
else
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_129; 
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_122 = lean_ctor_get(x_15, 0);
x_129 = !lean_is_exclusive(x_15);
if (x_129 == 0)
{
x_123 = x_15;
x_124 = x_129;
goto block_128;
}
else
{
lean_inc(x_122);
lean_dec(x_15);
x_123 = lean_box(0);
x_124 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_125; 
if (x_124 == 0)
{
x_125 = x_123;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_122);
x_125 = x_127;
goto block_126;
}
block_126:
{
return x_125;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_137; 
lean_dec_ref(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_130 = lean_ctor_get(x_12, 0);
x_137 = !lean_is_exclusive(x_12);
if (x_137 == 0)
{
x_131 = x_12;
x_132 = x_137;
goto block_136;
}
else
{
lean_inc(x_130);
lean_dec(x_12);
x_131 = lean_box(0);
x_132 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_133; 
if (x_132 == 0)
{
x_133 = x_131;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_130);
x_133 = x_135;
goto block_134;
}
block_134:
{
return x_133;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_47; uint8_t x_48; 
x_5 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0));
x_6 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1));
x_47 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
lean_inc(x_1);
x_48 = l_Lean_Syntax_isOfKind(x_1, x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_49 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; size_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; size_t x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; size_t x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; size_t x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; size_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_527; uint8_t x_528; 
x_50 = lean_unsigned_to_nat(0u);
x_527 = l_Lean_Syntax_getArg(x_1, x_50);
x_528 = l_Lean_Syntax_isNone(x_527);
if (x_528 == 0)
{
lean_object* x_529; uint8_t x_530; 
x_529 = lean_unsigned_to_nat(1u);
lean_inc(x_527);
x_530 = l_Lean_Syntax_matchesNull(x_527, x_529);
if (x_530 == 0)
{
lean_object* x_531; 
lean_dec(x_527);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_531 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; uint8_t x_534; 
x_532 = l_Lean_Syntax_getArg(x_527, x_50);
lean_dec(x_527);
x_533 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7));
lean_inc(x_532);
x_534 = l_Lean_Syntax_isOfKind(x_532, x_533);
if (x_534 == 0)
{
lean_object* x_535; 
lean_dec(x_532);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_535 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_535;
}
else
{
lean_object* x_536; 
x_536 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_536, 0, x_532);
x_510 = x_536;
x_511 = x_2;
x_512 = x_3;
goto block_526;
}
}
}
else
{
lean_object* x_537; 
lean_dec(x_527);
x_537 = lean_box(0);
x_510 = x_537;
x_511 = x_2;
x_512 = x_3;
goto block_526;
}
block_79:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_inc_ref(x_51);
x_67 = l_Array_append___redArg(x_51, x_66);
lean_dec_ref(x_66);
lean_inc(x_61);
lean_inc(x_57);
x_68 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_68, 0, x_57);
lean_ctor_set(x_68, 1, x_61);
lean_ctor_set(x_68, 2, x_67);
lean_inc_ref(x_51);
lean_inc(x_61);
lean_inc(x_57);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_57);
lean_ctor_set(x_69, 1, x_61);
lean_ctor_set(x_69, 2, x_51);
lean_inc_ref(x_69);
lean_inc(x_57);
x_70 = l_Lean_Syntax_node1(x_57, x_64, x_69);
lean_inc(x_57);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_57);
lean_ctor_set(x_71, 1, x_55);
lean_inc(x_57);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_57);
lean_ctor_set(x_72, 1, x_60);
lean_inc(x_61);
lean_inc(x_57);
x_73 = l_Lean_Syntax_node2(x_57, x_61, x_72, x_53);
if (lean_obj_tag(x_58) == 1)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_58, 0);
lean_inc(x_74);
lean_dec_ref(x_58);
x_75 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0));
lean_inc(x_57);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_57);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Array_mkArray2___redArg(x_76, x_74);
x_7 = x_51;
x_8 = x_70;
x_9 = x_52;
x_10 = x_54;
x_11 = x_56;
x_12 = x_57;
x_13 = x_59;
x_14 = x_73;
x_15 = x_61;
x_16 = x_62;
x_17 = x_63;
x_18 = x_69;
x_19 = x_71;
x_20 = x_65;
x_21 = x_68;
x_22 = x_77;
goto block_46;
}
else
{
lean_object* x_78; 
lean_dec(x_58);
x_78 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
x_7 = x_51;
x_8 = x_70;
x_9 = x_52;
x_10 = x_54;
x_11 = x_56;
x_12 = x_57;
x_13 = x_59;
x_14 = x_73;
x_15 = x_61;
x_16 = x_62;
x_17 = x_63;
x_18 = x_69;
x_19 = x_71;
x_20 = x_65;
x_21 = x_68;
x_22 = x_78;
goto block_46;
}
}
block_99:
{
lean_object* x_94; lean_object* x_95; 
x_94 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0));
x_95 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1));
if (lean_obj_tag(x_88) == 1)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_88, 0);
lean_inc(x_96);
lean_dec_ref(x_88);
x_97 = l_Array_mkArray1___redArg(x_96);
x_51 = x_80;
x_52 = x_81;
x_53 = x_82;
x_54 = x_83;
x_55 = x_94;
x_56 = x_95;
x_57 = x_84;
x_58 = x_85;
x_59 = x_86;
x_60 = x_87;
x_61 = x_89;
x_62 = x_90;
x_63 = x_91;
x_64 = x_92;
x_65 = x_93;
x_66 = x_97;
goto block_79;
}
else
{
lean_object* x_98; 
lean_dec(x_88);
x_98 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
x_51 = x_80;
x_52 = x_81;
x_53 = x_82;
x_54 = x_83;
x_55 = x_94;
x_56 = x_95;
x_57 = x_84;
x_58 = x_85;
x_59 = x_86;
x_60 = x_87;
x_61 = x_89;
x_62 = x_90;
x_63 = x_91;
x_64 = x_92;
x_65 = x_93;
x_66 = x_98;
goto block_79;
}
}
block_191:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; size_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_inc_ref(x_100);
x_123 = l_Array_append___redArg(x_100, x_122);
lean_dec_ref(x_122);
lean_inc(x_115);
lean_inc(x_121);
x_124 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_115);
lean_ctor_set(x_124, 2, x_123);
x_125 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
x_126 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc(x_121);
x_127 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_127, 0, x_121);
lean_ctor_set(x_127, 1, x_126);
x_128 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__6));
lean_inc(x_121);
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_121);
lean_ctor_set(x_129, 1, x_128);
x_130 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(x_121);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_121);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Nat_reprFast(x_120);
x_133 = lean_box(2);
x_134 = l_Lean_Syntax_mkNumLit(x_132, x_133);
x_135 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
lean_inc(x_121);
x_136 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_136, 0, x_121);
lean_ctor_set(x_136, 1, x_135);
lean_inc(x_121);
x_137 = l_Lean_Syntax_node5(x_121, x_125, x_127, x_129, x_131, x_134, x_136);
lean_inc(x_115);
lean_inc(x_121);
x_138 = l_Lean_Syntax_node1(x_121, x_115, x_137);
x_139 = lean_array_size(x_101);
x_140 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(x_139, x_110, x_101);
lean_inc_ref(x_100);
x_141 = l_Array_append___redArg(x_100, x_140);
lean_dec_ref(x_140);
lean_inc(x_115);
lean_inc(x_121);
x_142 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_142, 0, x_121);
lean_ctor_set(x_142, 1, x_115);
lean_ctor_set(x_142, 2, x_141);
x_143 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(x_121);
x_144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_144, 0, x_121);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_unsigned_to_nat(10u);
x_146 = lean_mk_empty_array_with_capacity(x_145);
x_147 = lean_array_push(x_146, x_107);
x_148 = lean_array_push(x_147, x_103);
x_149 = lean_array_push(x_148, x_113);
x_150 = lean_array_push(x_149, x_117);
x_151 = lean_array_push(x_150, x_111);
x_152 = lean_array_push(x_151, x_124);
x_153 = lean_array_push(x_152, x_138);
x_154 = lean_array_push(x_153, x_142);
x_155 = lean_array_push(x_154, x_144);
lean_inc(x_105);
x_156 = lean_array_push(x_155, x_105);
x_157 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_157, 0, x_121);
lean_ctor_set(x_157, 1, x_106);
lean_ctor_set(x_157, 2, x_156);
lean_inc(x_116);
lean_inc_ref(x_104);
x_158 = l_Lean_Elab_Command_elabSyntax(x_157, x_104, x_116);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_dec_ref(x_158);
x_160 = l_Lean_Elab_Command_getRef___redArg(x_104);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
lean_dec_ref(x_160);
x_162 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_104);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec_ref(x_162);
x_163 = lean_ctor_get(x_104, 5);
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_133);
lean_ctor_set(x_164, 1, x_159);
lean_ctor_set(x_164, 2, x_119);
x_165 = l_Lean_SourceInfo_fromRef(x_161, x_114);
lean_dec(x_161);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_166; 
x_166 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_116);
lean_dec_ref(x_166);
x_80 = x_100;
x_81 = x_102;
x_82 = x_105;
x_83 = x_104;
x_84 = x_165;
x_85 = x_109;
x_86 = x_108;
x_87 = x_143;
x_88 = x_112;
x_89 = x_115;
x_90 = x_116;
x_91 = x_135;
x_92 = x_118;
x_93 = x_164;
goto block_99;
}
else
{
x_80 = x_100;
x_81 = x_102;
x_82 = x_105;
x_83 = x_104;
x_84 = x_165;
x_85 = x_109;
x_86 = x_108;
x_87 = x_143;
x_88 = x_112;
x_89 = x_115;
x_90 = x_116;
x_91 = x_135;
x_92 = x_118;
x_93 = x_164;
goto block_99;
}
}
else
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_174; 
lean_dec(x_161);
lean_dec(x_159);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec_ref(x_102);
lean_dec_ref(x_100);
x_167 = lean_ctor_get(x_162, 0);
x_174 = !lean_is_exclusive(x_162);
if (x_174 == 0)
{
x_168 = x_162;
x_169 = x_174;
goto block_173;
}
else
{
lean_inc(x_167);
lean_dec(x_162);
x_168 = lean_box(0);
x_169 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_170; 
if (x_169 == 0)
{
x_170 = x_168;
goto block_171;
}
else
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_167);
x_170 = x_172;
goto block_171;
}
block_171:
{
return x_170;
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_182; 
lean_dec(x_159);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec_ref(x_102);
lean_dec_ref(x_100);
x_175 = lean_ctor_get(x_160, 0);
x_182 = !lean_is_exclusive(x_160);
if (x_182 == 0)
{
x_176 = x_160;
x_177 = x_182;
goto block_181;
}
else
{
lean_inc(x_175);
lean_dec(x_160);
x_176 = lean_box(0);
x_177 = x_182;
goto block_181;
}
block_181:
{
lean_object* x_178; 
if (x_177 == 0)
{
x_178 = x_176;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_175);
x_178 = x_180;
goto block_179;
}
block_179:
{
return x_178;
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; uint8_t x_190; 
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec_ref(x_102);
lean_dec_ref(x_100);
x_183 = lean_ctor_get(x_158, 0);
x_190 = !lean_is_exclusive(x_158);
if (x_190 == 0)
{
x_184 = x_158;
x_185 = x_190;
goto block_189;
}
else
{
lean_inc(x_183);
lean_dec(x_158);
x_184 = lean_box(0);
x_185 = x_190;
goto block_189;
}
block_189:
{
lean_object* x_186; 
if (x_185 == 0)
{
x_186 = x_184;
goto block_187;
}
else
{
lean_object* x_188; 
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_183);
x_186 = x_188;
goto block_187;
}
block_187:
{
return x_186;
}
}
}
}
block_230:
{
lean_object* x_215; lean_object* x_216; 
lean_inc_ref(x_192);
x_215 = l_Array_append___redArg(x_192, x_214);
lean_dec_ref(x_214);
lean_inc(x_207);
lean_inc(x_213);
x_216 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_207);
lean_ctor_set(x_216, 2, x_215);
if (lean_obj_tag(x_193) == 1)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_217 = lean_ctor_get(x_193, 0);
lean_inc(x_217);
lean_dec_ref(x_193);
x_218 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
x_219 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1));
lean_inc(x_213);
x_220 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_220, 0, x_213);
lean_ctor_set(x_220, 1, x_219);
x_221 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__9));
lean_inc(x_213);
x_222 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_222, 0, x_213);
lean_ctor_set(x_222, 1, x_221);
x_223 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__11));
lean_inc(x_213);
x_224 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_224, 0, x_213);
lean_ctor_set(x_224, 1, x_223);
x_225 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3));
lean_inc(x_213);
x_226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_226, 0, x_213);
lean_ctor_set(x_226, 1, x_225);
lean_inc(x_213);
x_227 = l_Lean_Syntax_node5(x_213, x_218, x_220, x_222, x_224, x_217, x_226);
x_228 = l_Array_mkArray1___redArg(x_227);
x_100 = x_192;
x_101 = x_194;
x_102 = x_195;
x_103 = x_196;
x_104 = x_197;
x_105 = x_198;
x_106 = x_199;
x_107 = x_200;
x_108 = x_201;
x_109 = x_202;
x_110 = x_203;
x_111 = x_216;
x_112 = x_204;
x_113 = x_205;
x_114 = x_206;
x_115 = x_207;
x_116 = x_208;
x_117 = x_209;
x_118 = x_210;
x_119 = x_211;
x_120 = x_212;
x_121 = x_213;
x_122 = x_228;
goto block_191;
}
else
{
lean_object* x_229; 
lean_dec(x_193);
x_229 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
x_100 = x_192;
x_101 = x_194;
x_102 = x_195;
x_103 = x_196;
x_104 = x_197;
x_105 = x_198;
x_106 = x_199;
x_107 = x_200;
x_108 = x_201;
x_109 = x_202;
x_110 = x_203;
x_111 = x_216;
x_112 = x_204;
x_113 = x_205;
x_114 = x_206;
x_115 = x_207;
x_116 = x_208;
x_117 = x_209;
x_118 = x_210;
x_119 = x_211;
x_120 = x_212;
x_121 = x_213;
x_122 = x_229;
goto block_191;
}
}
block_266:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_inc_ref(x_231);
x_255 = l_Array_append___redArg(x_231, x_254);
lean_dec_ref(x_254);
lean_inc(x_247);
lean_inc(x_252);
x_256 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_256, 0, x_252);
lean_ctor_set(x_256, 1, x_247);
lean_ctor_set(x_256, 2, x_255);
x_257 = l_Lean_SourceInfo_fromRef(x_253, x_48);
lean_dec(x_253);
x_258 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_238);
if (lean_obj_tag(x_240) == 1)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_259 = lean_ctor_get(x_240, 0);
lean_inc(x_259);
lean_dec_ref(x_240);
x_260 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
x_261 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__7));
lean_inc(x_252);
x_262 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_262, 0, x_252);
lean_ctor_set(x_262, 1, x_261);
lean_inc(x_252);
x_263 = l_Lean_Syntax_node2(x_252, x_260, x_262, x_259);
x_264 = l_Array_mkArray1___redArg(x_263);
x_192 = x_231;
x_193 = x_232;
x_194 = x_233;
x_195 = x_234;
x_196 = x_256;
x_197 = x_235;
x_198 = x_236;
x_199 = x_237;
x_200 = x_239;
x_201 = x_242;
x_202 = x_241;
x_203 = x_243;
x_204 = x_244;
x_205 = x_245;
x_206 = x_246;
x_207 = x_247;
x_208 = x_248;
x_209 = x_258;
x_210 = x_249;
x_211 = x_250;
x_212 = x_251;
x_213 = x_252;
x_214 = x_264;
goto block_230;
}
else
{
lean_object* x_265; 
lean_dec(x_240);
x_265 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
x_192 = x_231;
x_193 = x_232;
x_194 = x_233;
x_195 = x_234;
x_196 = x_256;
x_197 = x_235;
x_198 = x_236;
x_199 = x_237;
x_200 = x_239;
x_201 = x_242;
x_202 = x_241;
x_203 = x_243;
x_204 = x_244;
x_205 = x_245;
x_206 = x_246;
x_207 = x_247;
x_208 = x_248;
x_209 = x_258;
x_210 = x_249;
x_211 = x_250;
x_212 = x_251;
x_213 = x_252;
x_214 = x_265;
goto block_230;
}
}
block_305:
{
lean_object* x_291; lean_object* x_292; 
lean_inc_ref(x_267);
x_291 = l_Array_append___redArg(x_267, x_290);
lean_dec_ref(x_290);
lean_inc(x_283);
lean_inc(x_288);
x_292 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_292, 0, x_288);
lean_ctor_set(x_292, 1, x_283);
lean_ctor_set(x_292, 2, x_291);
if (lean_obj_tag(x_279) == 1)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_293 = lean_ctor_get(x_279, 0);
lean_inc(x_293);
lean_dec_ref(x_279);
x_294 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__0));
lean_inc_ref(x_270);
x_295 = l_Lean_Name_mkStr4(x_5, x_6, x_270, x_294);
x_296 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__1));
lean_inc(x_288);
x_297 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_297, 0, x_288);
lean_ctor_set(x_297, 1, x_296);
lean_inc_ref(x_267);
x_298 = l_Array_append___redArg(x_267, x_293);
lean_dec(x_293);
lean_inc(x_283);
lean_inc(x_288);
x_299 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_299, 0, x_288);
lean_ctor_set(x_299, 1, x_283);
lean_ctor_set(x_299, 2, x_298);
x_300 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__3));
lean_inc(x_288);
x_301 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_301, 0, x_288);
lean_ctor_set(x_301, 1, x_300);
lean_inc(x_288);
x_302 = l_Lean_Syntax_node3(x_288, x_295, x_297, x_299, x_301);
x_303 = l_Array_mkArray1___redArg(x_302);
x_231 = x_267;
x_232 = x_268;
x_233 = x_269;
x_234 = x_270;
x_235 = x_271;
x_236 = x_272;
x_237 = x_273;
x_238 = x_274;
x_239 = x_292;
x_240 = x_275;
x_241 = x_276;
x_242 = x_277;
x_243 = x_278;
x_244 = x_280;
x_245 = x_281;
x_246 = x_282;
x_247 = x_283;
x_248 = x_284;
x_249 = x_285;
x_250 = x_286;
x_251 = x_287;
x_252 = x_288;
x_253 = x_289;
x_254 = x_303;
goto block_266;
}
else
{
lean_object* x_304; 
lean_dec(x_279);
x_304 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
x_231 = x_267;
x_232 = x_268;
x_233 = x_269;
x_234 = x_270;
x_235 = x_271;
x_236 = x_272;
x_237 = x_273;
x_238 = x_274;
x_239 = x_292;
x_240 = x_275;
x_241 = x_276;
x_242 = x_277;
x_243 = x_278;
x_244 = x_280;
x_245 = x_281;
x_246 = x_282;
x_247 = x_283;
x_248 = x_284;
x_249 = x_285;
x_250 = x_286;
x_251 = x_287;
x_252 = x_288;
x_253 = x_289;
x_254 = x_304;
goto block_266;
}
}
block_332:
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_325 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__12));
x_326 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__13));
x_327 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9));
x_328 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
if (lean_obj_tag(x_316) == 1)
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_316, 0);
lean_inc(x_329);
x_330 = l_Array_mkArray1___redArg(x_329);
x_267 = x_328;
x_268 = x_306;
x_269 = x_307;
x_270 = x_308;
x_271 = x_309;
x_272 = x_310;
x_273 = x_326;
x_274 = x_325;
x_275 = x_311;
x_276 = x_312;
x_277 = x_313;
x_278 = x_314;
x_279 = x_315;
x_280 = x_316;
x_281 = x_317;
x_282 = x_318;
x_283 = x_327;
x_284 = x_319;
x_285 = x_320;
x_286 = x_321;
x_287 = x_322;
x_288 = x_323;
x_289 = x_324;
x_290 = x_330;
goto block_305;
}
else
{
lean_object* x_331; 
x_331 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__32));
x_267 = x_328;
x_268 = x_306;
x_269 = x_307;
x_270 = x_308;
x_271 = x_309;
x_272 = x_310;
x_273 = x_326;
x_274 = x_325;
x_275 = x_311;
x_276 = x_312;
x_277 = x_313;
x_278 = x_314;
x_279 = x_315;
x_280 = x_316;
x_281 = x_317;
x_282 = x_318;
x_283 = x_327;
x_284 = x_319;
x_285 = x_320;
x_286 = x_321;
x_287 = x_322;
x_288 = x_323;
x_289 = x_324;
x_290 = x_331;
goto block_305;
}
}
block_400:
{
lean_object* x_349; lean_object* x_350; 
x_349 = lean_alloc_closure((void*)(l_Lean_evalOptPrio), 3, 1);
lean_closure_set(x_349, 0, x_339);
lean_inc_ref(x_347);
x_350 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(x_349, x_347, x_348);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; size_t x_353; size_t x_354; lean_object* x_355; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
lean_dec_ref(x_350);
x_352 = l_Lean_Syntax_getArgs(x_344);
lean_dec(x_344);
x_353 = lean_array_size(x_352);
x_354 = 0;
lean_inc_ref(x_347);
x_355 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(x_353, x_354, x_352, x_347, x_348);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
lean_dec_ref(x_355);
x_357 = l_Array_unzip___redArg(x_356);
lean_dec(x_356);
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec_ref(x_357);
x_360 = l_Lean_Elab_Command_getRef___redArg(x_347);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
lean_dec_ref(x_360);
x_362 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_347);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; uint8_t x_365; lean_object* x_366; 
lean_dec_ref(x_362);
x_363 = lean_ctor_get(x_347, 5);
x_364 = l_Lean_Syntax_getArg(x_335, x_338);
lean_dec(x_335);
x_365 = 0;
x_366 = l_Lean_SourceInfo_fromRef(x_361, x_365);
lean_dec(x_361);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_367; 
x_367 = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(x_348);
lean_dec_ref(x_367);
x_306 = x_333;
x_307 = x_358;
x_308 = x_334;
x_309 = x_347;
x_310 = x_336;
x_311 = x_337;
x_312 = x_346;
x_313 = x_364;
x_314 = x_354;
x_315 = x_340;
x_316 = x_341;
x_317 = x_342;
x_318 = x_365;
x_319 = x_348;
x_320 = x_343;
x_321 = x_359;
x_322 = x_351;
x_323 = x_366;
x_324 = x_345;
goto block_332;
}
else
{
x_306 = x_333;
x_307 = x_358;
x_308 = x_334;
x_309 = x_347;
x_310 = x_336;
x_311 = x_337;
x_312 = x_346;
x_313 = x_364;
x_314 = x_354;
x_315 = x_340;
x_316 = x_341;
x_317 = x_342;
x_318 = x_365;
x_319 = x_348;
x_320 = x_343;
x_321 = x_359;
x_322 = x_351;
x_323 = x_366;
x_324 = x_345;
goto block_332;
}
}
else
{
lean_object* x_368; lean_object* x_369; uint8_t x_370; uint8_t x_375; 
lean_dec(x_361);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_351);
lean_dec(x_348);
lean_dec_ref(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec(x_333);
x_368 = lean_ctor_get(x_362, 0);
x_375 = !lean_is_exclusive(x_362);
if (x_375 == 0)
{
x_369 = x_362;
x_370 = x_375;
goto block_374;
}
else
{
lean_inc(x_368);
lean_dec(x_362);
x_369 = lean_box(0);
x_370 = x_375;
goto block_374;
}
block_374:
{
lean_object* x_371; 
if (x_370 == 0)
{
x_371 = x_369;
goto block_372;
}
else
{
lean_object* x_373; 
x_373 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_373, 0, x_368);
x_371 = x_373;
goto block_372;
}
block_372:
{
return x_371;
}
}
}
}
else
{
lean_object* x_376; lean_object* x_377; uint8_t x_378; uint8_t x_383; 
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_351);
lean_dec(x_348);
lean_dec_ref(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec(x_333);
x_376 = lean_ctor_get(x_360, 0);
x_383 = !lean_is_exclusive(x_360);
if (x_383 == 0)
{
x_377 = x_360;
x_378 = x_383;
goto block_382;
}
else
{
lean_inc(x_376);
lean_dec(x_360);
x_377 = lean_box(0);
x_378 = x_383;
goto block_382;
}
block_382:
{
lean_object* x_379; 
if (x_378 == 0)
{
x_379 = x_377;
goto block_380;
}
else
{
lean_object* x_381; 
x_381 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_381, 0, x_376);
x_379 = x_381;
goto block_380;
}
block_380:
{
return x_379;
}
}
}
}
else
{
lean_object* x_384; lean_object* x_385; uint8_t x_386; uint8_t x_391; 
lean_dec(x_351);
lean_dec(x_348);
lean_dec_ref(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec(x_333);
x_384 = lean_ctor_get(x_355, 0);
x_391 = !lean_is_exclusive(x_355);
if (x_391 == 0)
{
x_385 = x_355;
x_386 = x_391;
goto block_390;
}
else
{
lean_inc(x_384);
lean_dec(x_355);
x_385 = lean_box(0);
x_386 = x_391;
goto block_390;
}
block_390:
{
lean_object* x_387; 
if (x_386 == 0)
{
x_387 = x_385;
goto block_388;
}
else
{
lean_object* x_389; 
x_389 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_389, 0, x_384);
x_387 = x_389;
goto block_388;
}
block_388:
{
return x_387;
}
}
}
}
else
{
lean_object* x_392; lean_object* x_393; uint8_t x_394; uint8_t x_399; 
lean_dec(x_348);
lean_dec_ref(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec(x_333);
x_392 = lean_ctor_get(x_350, 0);
x_399 = !lean_is_exclusive(x_350);
if (x_399 == 0)
{
x_393 = x_350;
x_394 = x_399;
goto block_398;
}
else
{
lean_inc(x_392);
lean_dec(x_350);
x_393 = lean_box(0);
x_394 = x_399;
goto block_398;
}
block_398:
{
lean_object* x_395; 
if (x_394 == 0)
{
x_395 = x_393;
goto block_396;
}
else
{
lean_object* x_397; 
x_397 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_397, 0, x_392);
x_395 = x_397;
goto block_396;
}
block_396:
{
return x_395;
}
}
}
}
block_430:
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
x_415 = lean_unsigned_to_nat(8u);
x_416 = l_Lean_Syntax_getArg(x_1, x_415);
x_417 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__15));
lean_inc(x_416);
x_418 = l_Lean_Syntax_isOfKind(x_416, x_417);
if (x_418 == 0)
{
lean_object* x_419; 
lean_dec(x_416);
lean_dec(x_414);
lean_dec_ref(x_413);
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_408);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec_ref(x_403);
lean_dec(x_402);
lean_dec(x_401);
lean_dec(x_1);
x_419 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_419;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
x_420 = lean_unsigned_to_nat(7u);
x_421 = l_Lean_Syntax_getArg(x_1, x_420);
lean_dec(x_1);
x_422 = l_Lean_Syntax_getArg(x_416, x_407);
x_423 = l_Lean_Syntax_getArg(x_416, x_410);
x_424 = l_Lean_Syntax_isNone(x_423);
if (x_424 == 0)
{
uint8_t x_425; 
lean_inc(x_423);
x_425 = l_Lean_Syntax_matchesNull(x_423, x_410);
if (x_425 == 0)
{
lean_object* x_426; 
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_416);
lean_dec(x_414);
lean_dec_ref(x_413);
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_408);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec_ref(x_403);
lean_dec(x_402);
lean_dec(x_401);
x_426 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_426;
}
else
{
lean_object* x_427; lean_object* x_428; 
x_427 = l_Lean_Syntax_getArg(x_423, x_407);
lean_dec(x_423);
x_428 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_428, 0, x_427);
x_333 = x_401;
x_334 = x_403;
x_335 = x_416;
x_336 = x_422;
x_337 = x_406;
x_338 = x_409;
x_339 = x_412;
x_340 = x_402;
x_341 = x_404;
x_342 = x_405;
x_343 = x_408;
x_344 = x_421;
x_345 = x_411;
x_346 = x_428;
x_347 = x_413;
x_348 = x_414;
goto block_400;
}
}
else
{
lean_object* x_429; 
lean_dec(x_423);
x_429 = lean_box(0);
x_333 = x_401;
x_334 = x_403;
x_335 = x_416;
x_336 = x_422;
x_337 = x_406;
x_338 = x_409;
x_339 = x_412;
x_340 = x_402;
x_341 = x_404;
x_342 = x_405;
x_343 = x_408;
x_344 = x_421;
x_345 = x_411;
x_346 = x_429;
x_347 = x_413;
x_348 = x_414;
goto block_400;
}
}
}
block_457:
{
lean_object* x_445; lean_object* x_446; uint8_t x_447; 
x_445 = lean_unsigned_to_nat(6u);
x_446 = l_Lean_Syntax_getArg(x_1, x_445);
x_447 = l_Lean_Syntax_isNone(x_446);
if (x_447 == 0)
{
uint8_t x_448; 
lean_inc(x_446);
x_448 = l_Lean_Syntax_matchesNull(x_446, x_436);
if (x_448 == 0)
{
lean_object* x_449; 
lean_dec(x_446);
lean_dec(x_444);
lean_dec_ref(x_443);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_438);
lean_dec(x_437);
lean_dec(x_435);
lean_dec(x_434);
lean_dec(x_433);
lean_dec_ref(x_432);
lean_dec(x_1);
x_449 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_449;
}
else
{
lean_object* x_450; lean_object* x_451; uint8_t x_452; 
x_450 = l_Lean_Syntax_getArg(x_446, x_50);
lean_dec(x_446);
x_451 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__5));
lean_inc(x_450);
x_452 = l_Lean_Syntax_isOfKind(x_450, x_451);
if (x_452 == 0)
{
lean_object* x_453; 
lean_dec(x_450);
lean_dec(x_444);
lean_dec_ref(x_443);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_438);
lean_dec(x_437);
lean_dec(x_435);
lean_dec(x_434);
lean_dec(x_433);
lean_dec_ref(x_432);
lean_dec(x_1);
x_453 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_453;
}
else
{
lean_object* x_454; lean_object* x_455; 
x_454 = l_Lean_Syntax_getArg(x_450, x_431);
lean_dec(x_450);
x_455 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_455, 0, x_454);
x_401 = x_442;
x_402 = x_433;
x_403 = x_432;
x_404 = x_434;
x_405 = x_435;
x_406 = x_437;
x_407 = x_436;
x_408 = x_438;
x_409 = x_439;
x_410 = x_440;
x_411 = x_441;
x_412 = x_455;
x_413 = x_443;
x_414 = x_444;
goto block_430;
}
}
}
else
{
lean_object* x_456; 
lean_dec(x_446);
x_456 = lean_box(0);
x_401 = x_442;
x_402 = x_433;
x_403 = x_432;
x_404 = x_434;
x_405 = x_435;
x_406 = x_437;
x_407 = x_436;
x_408 = x_438;
x_409 = x_439;
x_410 = x_440;
x_411 = x_441;
x_412 = x_456;
x_413 = x_443;
x_414 = x_444;
goto block_430;
}
}
block_483:
{
lean_object* x_471; lean_object* x_472; uint8_t x_473; 
x_471 = lean_unsigned_to_nat(5u);
x_472 = l_Lean_Syntax_getArg(x_1, x_471);
x_473 = l_Lean_Syntax_isNone(x_472);
if (x_473 == 0)
{
uint8_t x_474; 
lean_inc(x_472);
x_474 = l_Lean_Syntax_matchesNull(x_472, x_463);
if (x_474 == 0)
{
lean_object* x_475; 
lean_dec(x_472);
lean_dec(x_470);
lean_dec_ref(x_469);
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_464);
lean_dec(x_462);
lean_dec(x_461);
lean_dec_ref(x_460);
lean_dec(x_459);
lean_dec(x_1);
x_475 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_475;
}
else
{
lean_object* x_476; lean_object* x_477; uint8_t x_478; 
x_476 = l_Lean_Syntax_getArg(x_472, x_50);
lean_dec(x_472);
x_477 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__8));
lean_inc(x_476);
x_478 = l_Lean_Syntax_isOfKind(x_476, x_477);
if (x_478 == 0)
{
lean_object* x_479; 
lean_dec(x_476);
lean_dec(x_470);
lean_dec_ref(x_469);
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_464);
lean_dec(x_462);
lean_dec(x_461);
lean_dec_ref(x_460);
lean_dec(x_459);
lean_dec(x_1);
x_479 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_479;
}
else
{
lean_object* x_480; lean_object* x_481; 
x_480 = l_Lean_Syntax_getArg(x_476, x_458);
lean_dec(x_476);
x_481 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_481, 0, x_480);
x_431 = x_458;
x_432 = x_460;
x_433 = x_459;
x_434 = x_461;
x_435 = x_462;
x_436 = x_463;
x_437 = x_468;
x_438 = x_464;
x_439 = x_465;
x_440 = x_466;
x_441 = x_467;
x_442 = x_481;
x_443 = x_469;
x_444 = x_470;
goto block_457;
}
}
}
else
{
lean_object* x_482; 
lean_dec(x_472);
x_482 = lean_box(0);
x_431 = x_458;
x_432 = x_460;
x_433 = x_459;
x_434 = x_461;
x_435 = x_462;
x_436 = x_463;
x_437 = x_468;
x_438 = x_464;
x_439 = x_465;
x_440 = x_466;
x_441 = x_467;
x_442 = x_482;
x_443 = x_469;
x_444 = x_470;
goto block_457;
}
}
block_509:
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; uint8_t x_493; 
x_489 = lean_unsigned_to_nat(2u);
x_490 = l_Lean_Syntax_getArg(x_1, x_489);
x_491 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2));
x_492 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4));
lean_inc(x_490);
x_493 = l_Lean_Syntax_isOfKind(x_490, x_492);
if (x_493 == 0)
{
lean_object* x_494; 
lean_dec(x_490);
lean_dec(x_488);
lean_dec_ref(x_487);
lean_dec(x_486);
lean_dec(x_484);
lean_dec(x_1);
x_494 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_494;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; uint8_t x_499; 
x_495 = lean_unsigned_to_nat(3u);
x_496 = l_Lean_Syntax_getArg(x_1, x_495);
x_497 = lean_unsigned_to_nat(4u);
x_498 = l_Lean_Syntax_getArg(x_1, x_497);
x_499 = l_Lean_Syntax_isNone(x_498);
if (x_499 == 0)
{
uint8_t x_500; 
lean_inc(x_498);
x_500 = l_Lean_Syntax_matchesNull(x_498, x_485);
if (x_500 == 0)
{
lean_object* x_501; 
lean_dec(x_498);
lean_dec(x_496);
lean_dec(x_490);
lean_dec(x_488);
lean_dec_ref(x_487);
lean_dec(x_486);
lean_dec(x_484);
lean_dec(x_1);
x_501 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_501;
}
else
{
lean_object* x_502; lean_object* x_503; uint8_t x_504; 
x_502 = l_Lean_Syntax_getArg(x_498, x_50);
lean_dec(x_498);
x_503 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__11));
lean_inc(x_502);
x_504 = l_Lean_Syntax_isOfKind(x_502, x_503);
if (x_504 == 0)
{
lean_object* x_505; 
lean_dec(x_502);
lean_dec(x_496);
lean_dec(x_490);
lean_dec(x_488);
lean_dec_ref(x_487);
lean_dec(x_486);
lean_dec(x_484);
lean_dec(x_1);
x_505 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_505;
}
else
{
lean_object* x_506; lean_object* x_507; 
x_506 = l_Lean_Syntax_getArg(x_502, x_485);
lean_dec(x_502);
x_507 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_507, 0, x_506);
x_458 = x_495;
x_459 = x_486;
x_460 = x_491;
x_461 = x_484;
x_462 = x_490;
x_463 = x_485;
x_464 = x_492;
x_465 = x_497;
x_466 = x_489;
x_467 = x_496;
x_468 = x_507;
x_469 = x_487;
x_470 = x_488;
goto block_483;
}
}
}
else
{
lean_object* x_508; 
lean_dec(x_498);
x_508 = lean_box(0);
x_458 = x_495;
x_459 = x_486;
x_460 = x_491;
x_461 = x_484;
x_462 = x_490;
x_463 = x_485;
x_464 = x_492;
x_465 = x_497;
x_466 = x_489;
x_467 = x_496;
x_468 = x_508;
x_469 = x_487;
x_470 = x_488;
goto block_483;
}
}
}
block_526:
{
lean_object* x_513; lean_object* x_514; uint8_t x_515; 
x_513 = lean_unsigned_to_nat(1u);
x_514 = l_Lean_Syntax_getArg(x_1, x_513);
x_515 = l_Lean_Syntax_isNone(x_514);
if (x_515 == 0)
{
uint8_t x_516; 
lean_inc(x_514);
x_516 = l_Lean_Syntax_matchesNull(x_514, x_513);
if (x_516 == 0)
{
lean_object* x_517; 
lean_dec(x_514);
lean_dec(x_512);
lean_dec_ref(x_511);
lean_dec(x_510);
lean_dec(x_1);
x_517 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_517;
}
else
{
lean_object* x_518; lean_object* x_519; uint8_t x_520; 
x_518 = l_Lean_Syntax_getArg(x_514, x_50);
lean_dec(x_514);
x_519 = ((lean_object*)(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5));
lean_inc(x_518);
x_520 = l_Lean_Syntax_isOfKind(x_518, x_519);
if (x_520 == 0)
{
lean_object* x_521; 
lean_dec(x_518);
lean_dec(x_512);
lean_dec_ref(x_511);
lean_dec(x_510);
lean_dec(x_1);
x_521 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
return x_521;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_522 = l_Lean_Syntax_getArg(x_518, x_513);
lean_dec(x_518);
x_523 = l_Lean_Syntax_getArgs(x_522);
lean_dec(x_522);
x_524 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_524, 0, x_523);
x_484 = x_510;
x_485 = x_513;
x_486 = x_524;
x_487 = x_511;
x_488 = x_512;
goto block_509;
}
}
}
else
{
lean_object* x_525; 
lean_dec(x_514);
x_525 = lean_box(0);
x_484 = x_510;
x_485 = x_513;
x_486 = x_525;
x_487 = x_511;
x_488 = x_512;
goto block_509;
}
}
}
block_46:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_23 = l_Array_append___redArg(x_7, x_22);
lean_dec_ref(x_22);
lean_inc(x_15);
lean_inc(x_12);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_24, 2, x_23);
x_25 = ((lean_object*)(l_Lean_Elab_Command_elabElabRulesAux___closed__22));
lean_inc_ref(x_9);
x_26 = l_Lean_Name_mkStr4(x_5, x_6, x_9, x_25);
x_27 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4));
lean_inc_ref(x_9);
x_28 = l_Lean_Name_mkStr4(x_5, x_6, x_9, x_27);
x_29 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6));
lean_inc(x_12);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_29);
x_31 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__0));
x_32 = l_Lean_Name_mkStr4(x_5, x_6, x_9, x_31);
x_33 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__1));
lean_inc(x_12);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_12);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_12);
lean_ctor_set(x_35, 1, x_17);
lean_inc(x_12);
x_36 = l_Lean_Syntax_node3(x_12, x_32, x_34, x_20, x_35);
lean_inc(x_15);
lean_inc(x_12);
x_37 = l_Lean_Syntax_node1(x_12, x_15, x_36);
lean_inc(x_15);
lean_inc(x_12);
x_38 = l_Lean_Syntax_node1(x_12, x_15, x_37);
x_39 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8));
lean_inc(x_12);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_12);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_12);
x_41 = l_Lean_Syntax_node4(x_12, x_28, x_30, x_38, x_40, x_13);
lean_inc(x_12);
x_42 = l_Lean_Syntax_node1(x_12, x_15, x_41);
lean_inc(x_12);
x_43 = l_Lean_Syntax_node1(x_12, x_26, x_42);
lean_inc(x_18);
x_44 = l_Lean_Syntax_node8(x_12, x_11, x_21, x_18, x_8, x_19, x_18, x_14, x_24, x_43);
x_45 = l_Lean_Elab_Command_elabCommand(x_44, x_10, x_16);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabElab(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___redArg(x_2, x_3, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8(x_1, x_2, x_3);
lean_dec_ref(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__6_spec__11(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3_spec__4_spec__8_spec__11_spec__14(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = ((lean_object*)(l_Lean_Elab_Command_elabElab___closed__3));
x_4 = ((lean_object*)(l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElab___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1));
x_3 = ((lean_object*)(l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6));
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
return x_2;
}
}
lean_object* runtime_initialize_Lean_Elab_MacroArgUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_AuxDef(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ElabRules(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_MacroArgUtil(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_AuxDef(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_ElabRules(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_MacroArgUtil(uint8_t builtin);
lean_object* initialize_Lean_Elab_AuxDef(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ElabRules(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_MacroArgUtil(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AuxDef(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ElabRules(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_ElabRules(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_ElabRules(builtin);
}
#ifdef __cplusplus
}
#endif
