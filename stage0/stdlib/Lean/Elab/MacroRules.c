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
lean_object* l_String_toRawSubstring_x27(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Command_checkRuleAltKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Parser_Command_visibility_ofAttrKind(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_resolveSyntaxKind(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "macro_rules"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "macroRules"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Command_elabMacroRulesAux___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__6;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__5_value),LEAN_SCALAR_PTR_LITERAL(6, 217, 176, 227, 245, 86, 100, 50)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__7_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__8_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Macro"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Command_elabMacroRulesAux___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__10;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__9_value),LEAN_SCALAR_PTR_LITERAL(153, 13, 84, 30, 172, 208, 133, 203)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__11_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__14_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__15 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__15_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__16 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__16_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__17 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__17_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__18 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__18_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__19 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__19_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noErrorIfUnused"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__20 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__20_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "no_error_if_unused%"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__21 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__21_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__22 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__22_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "throw"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__23 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__23_value;
static lean_once_cell_t l_Lean_Elab_Command_elabMacroRulesAux___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__24;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__23_value),LEAN_SCALAR_PTR_LITERAL(60, 81, 80, 209, 187, 239, 255, 113)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__25 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__25_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MonadExcept"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__26 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__26_value),LEAN_SCALAR_PTR_LITERAL(162, 154, 253, 120, 110, 153, 103, 113)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__27_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__23_value),LEAN_SCALAR_PTR_LITERAL(121, 11, 61, 69, 62, 207, 229, 53)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__27 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__27_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__28 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__28_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__29 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__29_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Macro.Exception.unsupportedSyntax"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__30 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value;
static lean_once_cell_t l_Lean_Elab_Command_elabMacroRulesAux___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__31;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Exception"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__32 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "unsupportedSyntax"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__33 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__33_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__34 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__35 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__36 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__36_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "aux_def"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__37 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__37_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__36_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__37_value),LEAN_SCALAR_PTR_LITERAL(83, 33, 36, 212, 17, 187, 86, 94)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__38 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__39 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__39_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__39_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__40 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__40_value;
static lean_once_cell_t l_Lean_Elab_Command_elabMacroRulesAux___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__41;
static const lean_array_object l_Lean_Elab_Command_elabMacroRulesAux___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__42 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__42_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__43 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__43_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__44_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__44_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__44_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__43_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__44 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__44_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__45 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__45_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "macro"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__46 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__46_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__47_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__47_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__45_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__47_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__46_value),LEAN_SCALAR_PTR_LITERAL(17, 202, 70, 6, 8, 133, 137, 74)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__47 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__47_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__48 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__48_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__36_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 80, 75, 5, 165, 87, 197, 1)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__9_value),LEAN_SCALAR_PTR_LITERAL(168, 205, 218, 0, 241, 122, 66, 251)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value),((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__4_value)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__5_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__14_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(136, 104, 45, 91, 146, 14, 86, 4)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__15_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__2_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__16 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__36_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
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
static const lean_ctor_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__36_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
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
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(lean_object* v___y_1_){
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
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg___boxed(lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v___y_8_);
lean_dec(v___y_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v___y_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___boxed(lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0(lean_object* v_k_20_, size_t v_sz_21_, size_t v_i_22_, lean_object* v_bs_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
uint8_t v___x_27_; 
v___x_27_ = lean_usize_dec_lt(v_i_22_, v_sz_21_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; 
lean_dec(v_k_20_);
v___x_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_28_, 0, v_bs_23_);
return v___x_28_;
}
else
{
lean_object* v___x_29_; lean_object* v_v_30_; lean_object* v___x_31_; lean_object* v_bs_x27_32_; lean_object* v___x_33_; 
v___x_29_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___closed__0));
v_v_30_ = lean_array_uget(v_bs_23_, v_i_22_);
v___x_31_ = lean_unsigned_to_nat(0u);
v_bs_x27_32_ = lean_array_uset(v_bs_23_, v_i_22_, v___x_31_);
lean_inc(v_k_20_);
v___x_33_ = l_Lean_Elab_Command_checkRuleAltKind(v___x_29_, v_k_20_, v_v_30_, v___y_24_, v___y_25_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v_a_34_; size_t v___x_35_; size_t v___x_36_; lean_object* v___x_37_; 
v_a_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_a_34_);
lean_dec_ref_known(v___x_33_, 1);
v___x_35_ = ((size_t)1ULL);
v___x_36_ = lean_usize_add(v_i_22_, v___x_35_);
v___x_37_ = lean_array_uset(v_bs_x27_32_, v_i_22_, v_a_34_);
v_i_22_ = v___x_36_;
v_bs_23_ = v___x_37_;
goto _start;
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
lean_dec_ref(v_bs_x27_32_);
lean_dec(v_k_20_);
v_a_39_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_33_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_33_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___boxed(lean_object* v_k_47_, lean_object* v_sz_48_, lean_object* v_i_49_, lean_object* v_bs_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
size_t v_sz_boxed_54_; size_t v_i_boxed_55_; lean_object* v_res_56_; 
v_sz_boxed_54_ = lean_unbox_usize(v_sz_48_);
lean_dec(v_sz_48_);
v_i_boxed_55_ = lean_unbox_usize(v_i_49_);
lean_dec(v_i_49_);
v_res_56_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0(v_k_47_, v_sz_boxed_54_, v_i_boxed_55_, v_bs_50_, v___y_51_, v___y_52_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
return v_res_56_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__6(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__5));
v___x_64_ = l_String_toRawSubstring_x27(v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__10(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__9));
v___x_70_ = l_String_toRawSubstring_x27(v___x_69_);
return v___x_70_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__24(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__23));
v___x_86_ = l_String_toRawSubstring_x27(v___x_85_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__31(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__30));
v___x_101_ = l_String_toRawSubstring_x27(v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__41(void){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Array_mkArray0___redArg();
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux(lean_object* v_doc_x3f_133_, lean_object* v_attrs_x3f_134_, lean_object* v_attrKind_135_, lean_object* v_tk_136_, lean_object* v_k_137_, lean_object* v_alts_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
size_t v_sz_142_; size_t v___x_143_; lean_object* v___x_144_; 
v_sz_142_ = lean_array_size(v_alts_138_);
v___x_143_ = ((size_t)0ULL);
lean_inc(v_k_137_);
v___x_144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0(v_k_137_, v_sz_142_, v___x_143_, v_alts_138_, v_a_139_, v_a_140_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_329_; 
v_a_145_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_329_ == 0)
{
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_329_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_329_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___y_150_; lean_object* v___y_151_; lean_object* v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v_a_266_; lean_object* v___x_275_; 
v___x_275_ = l_Lean_Elab_Command_getRef___redArg(v_a_139_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; uint8_t v___x_277_; lean_object* v___y_279_; lean_object* v___x_299_; lean_object* v___x_318_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
v___x_277_ = 0;
v___x_299_ = l_Lean_SourceInfo_fromRef(v_a_276_, v___x_277_);
lean_dec(v_a_276_);
v___x_318_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_139_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_quotContext_x3f_319_; 
lean_dec_ref_known(v___x_318_, 1);
v_quotContext_x3f_319_ = lean_ctor_get(v_a_139_, 5);
if (lean_obj_tag(v_quotContext_x3f_319_) == 0)
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_a_140_);
lean_dec_ref(v___x_320_);
goto v___jp_300_;
}
else
{
goto v___jp_300_;
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec(v___x_299_);
lean_del_object(v___x_147_);
lean_dec(v_a_145_);
lean_dec(v_k_137_);
lean_dec(v_attrKind_135_);
lean_dec(v_doc_x3f_133_);
v_a_321_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_318_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_318_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
v___jp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_135_);
v___x_281_ = l_Lean_Elab_Command_getRef___redArg(v_a_139_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_a_282_);
lean_dec_ref_known(v___x_281_, 1);
v___x_283_ = l_Lean_SourceInfo_fromRef(v_a_282_, v___x_277_);
lean_dec(v_a_282_);
v___x_284_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_139_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_quotContext_x3f_285_; 
v_quotContext_x3f_285_ = lean_ctor_get(v_a_139_, 5);
if (lean_obj_tag(v_quotContext_x3f_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_287_; lean_object* v_a_288_; 
v_a_286_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_a_286_);
lean_dec_ref_known(v___x_284_, 1);
v___x_287_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_a_140_);
v_a_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_288_);
lean_dec_ref(v___x_287_);
v___y_262_ = v_a_286_;
v___y_263_ = v___x_280_;
v___y_264_ = v___x_283_;
v___y_265_ = v___y_279_;
v_a_266_ = v_a_288_;
goto v___jp_261_;
}
else
{
lean_object* v_a_289_; lean_object* v_val_290_; 
v_a_289_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_a_289_);
lean_dec_ref_known(v___x_284_, 1);
v_val_290_ = lean_ctor_get(v_quotContext_x3f_285_, 0);
lean_inc(v_val_290_);
v___y_262_ = v_a_289_;
v___y_263_ = v___x_280_;
v___y_264_ = v___x_283_;
v___y_265_ = v___y_279_;
v_a_266_ = v_val_290_;
goto v___jp_261_;
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec(v___x_283_);
lean_dec(v___x_280_);
lean_dec_ref(v___y_279_);
lean_del_object(v___x_147_);
lean_dec(v_a_145_);
lean_dec(v_k_137_);
lean_dec(v_doc_x3f_133_);
v_a_291_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_284_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_284_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
else
{
lean_dec(v___x_280_);
lean_dec_ref(v___y_279_);
lean_del_object(v___x_147_);
lean_dec(v_a_145_);
lean_dec(v_k_137_);
lean_dec(v_doc_x3f_133_);
return v___x_281_;
}
}
v___jp_300_:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_301_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__44));
v___x_302_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__46));
v___x_303_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__47));
lean_inc_n(v___x_299_, 2);
v___x_304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_299_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
lean_inc(v_k_137_);
v___x_305_ = l_Lean_mkIdent(v_k_137_);
v___x_306_ = l_Lean_Syntax_node2(v___x_299_, v___x_303_, v___x_304_, v___x_305_);
lean_inc(v_attrKind_135_);
v___x_307_ = l_Lean_Syntax_node2(v___x_299_, v___x_301_, v_attrKind_135_, v___x_306_);
if (lean_obj_tag(v_attrs_x3f_134_) == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_308_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__48));
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = lean_mk_empty_array_with_capacity(v___x_309_);
v___x_311_ = lean_array_push(v___x_310_, v___x_307_);
v___x_312_ = l_Lean_Syntax_SepArray_ofElems(v___x_308_, v___x_311_);
lean_dec_ref(v___x_311_);
v___y_279_ = v___x_312_;
goto v___jp_278_;
}
else
{
lean_object* v_val_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_val_313_ = lean_ctor_get(v_attrs_x3f_134_, 0);
v___x_314_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__48));
v___x_315_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_313_);
v___x_316_ = lean_array_push(v___x_315_, v___x_307_);
v___x_317_ = l_Lean_Syntax_SepArray_ofElems(v___x_314_, v___x_316_);
lean_dec_ref(v___x_316_);
v___y_279_ = v___x_317_;
goto v___jp_278_;
}
}
}
else
{
lean_del_object(v___x_147_);
lean_dec(v_a_145_);
lean_dec(v_k_137_);
lean_dec(v_attrKind_135_);
lean_dec(v_doc_x3f_133_);
return v___x_275_;
}
v___jp_149_:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
lean_inc_ref_n(v___y_155_, 3);
v___x_161_ = l_Array_append___redArg(v___y_155_, v___y_160_);
lean_dec_ref(v___y_160_);
lean_inc_n(v___y_156_, 8);
lean_inc_n(v___y_153_, 29);
v___x_162_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_162_, 0, v___y_153_);
lean_ctor_set(v___x_162_, 1, v___y_156_);
lean_ctor_set(v___x_162_, 2, v___x_161_);
v___x_163_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
v___x_164_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
v___x_165_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
lean_inc_ref_n(v___y_159_, 9);
v___x_166_ = l_Lean_Name_mkStr4(v___y_159_, v___x_163_, v___x_164_, v___x_165_);
v___x_167_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__3));
v___x_168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_168_, 0, v___y_153_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = l_Array_append___redArg(v___y_155_, v___y_158_);
lean_dec_ref(v___y_158_);
v___x_170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_170_, 0, v___y_153_);
lean_ctor_set(v___x_170_, 1, v___y_156_);
lean_ctor_set(v___x_170_, 2, v___x_169_);
v___x_171_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__4));
v___x_172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_172_, 0, v___y_153_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = l_Lean_Syntax_node3(v___y_153_, v___x_166_, v___x_168_, v___x_170_, v___x_172_);
v___x_174_ = l_Lean_Syntax_node1(v___y_153_, v___y_156_, v___x_173_);
lean_inc_ref(v___y_152_);
v___x_175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_175_, 0, v___y_153_);
lean_ctor_set(v___x_175_, 1, v___y_152_);
v___x_176_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__6, &l_Lean_Elab_Command_elabMacroRulesAux___closed__6_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__6);
v___x_177_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__7));
lean_inc_n(v___y_151_, 3);
lean_inc_n(v___y_154_, 3);
v___x_178_ = l_Lean_addMacroScope(v___y_154_, v___x_177_, v___y_151_);
v___x_179_ = lean_box(0);
v___x_180_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_180_, 0, v___y_153_);
lean_ctor_set(v___x_180_, 1, v___x_176_);
lean_ctor_set(v___x_180_, 2, v___x_178_);
lean_ctor_set(v___x_180_, 3, v___x_179_);
v___x_181_ = 1;
v___x_182_ = l_Lean_mkIdentFrom(v_tk_136_, v_k_137_, v___x_181_);
v___x_183_ = l_Lean_Syntax_node2(v___y_153_, v___y_156_, v___x_180_, v___x_182_);
v___x_184_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__8));
v___x_185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_185_, 0, v___y_153_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__9));
v___x_187_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__10, &l_Lean_Elab_Command_elabMacroRulesAux___closed__10_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__10);
v___x_188_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__11));
v___x_189_ = l_Lean_addMacroScope(v___y_154_, v___x_188_, v___y_151_);
v___x_190_ = l_Lean_Name_mkStr2(v___y_159_, v___x_186_);
lean_inc(v___x_190_);
v___x_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_179_);
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v___x_190_);
v___x_193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v___x_179_);
v___x_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_191_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_195_, 0, v___y_153_);
lean_ctor_set(v___x_195_, 1, v___x_187_);
lean_ctor_set(v___x_195_, 2, v___x_189_);
lean_ctor_set(v___x_195_, 3, v___x_194_);
v___x_196_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__12));
v___x_197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_197_, 0, v___y_153_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__13));
v___x_199_ = l_Lean_Name_mkStr4(v___y_159_, v___x_163_, v___x_164_, v___x_198_);
v___x_200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_200_, 0, v___y_153_);
lean_ctor_set(v___x_200_, 1, v___x_198_);
v___x_201_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__14));
v___x_202_ = l_Lean_Name_mkStr4(v___y_159_, v___x_163_, v___x_164_, v___x_201_);
v___x_203_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__15));
v___x_204_ = l_Lean_Name_mkStr4(v___y_159_, v___x_163_, v___x_164_, v___x_203_);
v___x_205_ = l_Array_append___redArg(v___y_155_, v_a_145_);
lean_dec(v_a_145_);
v___x_206_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__16));
v___x_207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_207_, 0, v___y_153_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__17));
v___x_209_ = l_Lean_Name_mkStr4(v___y_159_, v___x_163_, v___x_164_, v___x_208_);
v___x_210_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__18));
v___x_211_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_211_, 0, v___y_153_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = l_Lean_Syntax_node1(v___y_153_, v___x_209_, v___x_211_);
v___x_213_ = l_Lean_Syntax_node1(v___y_153_, v___y_156_, v___x_212_);
v___x_214_ = l_Lean_Syntax_node1(v___y_153_, v___y_156_, v___x_213_);
v___x_215_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__19));
v___x_216_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_216_, 0, v___y_153_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
v___x_217_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__20));
v___x_218_ = l_Lean_Name_mkStr4(v___y_159_, v___x_163_, v___x_164_, v___x_217_);
v___x_219_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__21));
v___x_220_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_220_, 0, v___y_153_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v___x_221_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__22));
v___x_222_ = l_Lean_Name_mkStr4(v___y_159_, v___x_163_, v___x_164_, v___x_221_);
v___x_223_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__24, &l_Lean_Elab_Command_elabMacroRulesAux___closed__24_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__24);
v___x_224_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__25));
v___x_225_ = l_Lean_addMacroScope(v___y_154_, v___x_224_, v___y_151_);
v___x_226_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__29));
v___x_227_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_227_, 0, v___y_153_);
lean_ctor_set(v___x_227_, 1, v___x_223_);
lean_ctor_set(v___x_227_, 2, v___x_225_);
lean_ctor_set(v___x_227_, 3, v___x_226_);
v___x_228_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__31, &l_Lean_Elab_Command_elabMacroRulesAux___closed__31_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__31);
v___x_229_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__32));
v___x_230_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__33));
v___x_231_ = l_Lean_Name_mkStr4(v___y_159_, v___x_186_, v___x_229_, v___x_230_);
lean_inc_n(v___x_231_, 2);
v___x_232_ = l_Lean_addMacroScope(v___y_154_, v___x_231_, v___y_151_);
v___x_233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_179_);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_231_);
v___x_235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___x_179_);
v___x_236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_233_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_237_, 0, v___y_153_);
lean_ctor_set(v___x_237_, 1, v___x_228_);
lean_ctor_set(v___x_237_, 2, v___x_232_);
lean_ctor_set(v___x_237_, 3, v___x_236_);
v___x_238_ = l_Lean_Syntax_node1(v___y_153_, v___y_156_, v___x_237_);
v___x_239_ = l_Lean_Syntax_node2(v___y_153_, v___x_222_, v___x_227_, v___x_238_);
v___x_240_ = l_Lean_Syntax_node2(v___y_153_, v___x_218_, v___x_220_, v___x_239_);
v___x_241_ = l_Lean_Syntax_node4(v___y_153_, v___x_204_, v___x_207_, v___x_214_, v___x_216_, v___x_240_);
v___x_242_ = lean_array_push(v___x_205_, v___x_241_);
v___x_243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_243_, 0, v___y_153_);
lean_ctor_set(v___x_243_, 1, v___y_156_);
lean_ctor_set(v___x_243_, 2, v___x_242_);
v___x_244_ = l_Lean_Syntax_node1(v___y_153_, v___x_202_, v___x_243_);
v___x_245_ = l_Lean_Syntax_node2(v___y_153_, v___x_199_, v___x_200_, v___x_244_);
v___x_246_ = lean_unsigned_to_nat(9u);
v___x_247_ = lean_mk_empty_array_with_capacity(v___x_246_);
v___x_248_ = lean_array_push(v___x_247_, v___x_162_);
v___x_249_ = lean_array_push(v___x_248_, v___x_174_);
v___x_250_ = lean_array_push(v___x_249_, v___y_150_);
v___x_251_ = lean_array_push(v___x_250_, v___x_175_);
v___x_252_ = lean_array_push(v___x_251_, v___x_183_);
v___x_253_ = lean_array_push(v___x_252_, v___x_185_);
v___x_254_ = lean_array_push(v___x_253_, v___x_195_);
v___x_255_ = lean_array_push(v___x_254_, v___x_197_);
v___x_256_ = lean_array_push(v___x_255_, v___x_245_);
lean_inc(v___y_157_);
v___x_257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_257_, 0, v___y_153_);
lean_ctor_set(v___x_257_, 1, v___y_157_);
lean_ctor_set(v___x_257_, 2, v___x_256_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_257_);
v___x_259_ = v___x_147_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
v___jp_261_:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_267_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__34));
v___x_268_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__37));
v___x_269_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__38));
v___x_270_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__40));
v___x_271_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__41, &l_Lean_Elab_Command_elabMacroRulesAux___closed__41_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__41);
if (lean_obj_tag(v_doc_x3f_133_) == 1)
{
lean_object* v_val_272_; lean_object* v___x_273_; 
v_val_272_ = lean_ctor_get(v_doc_x3f_133_, 0);
lean_inc(v_val_272_);
lean_dec_ref_known(v_doc_x3f_133_, 1);
v___x_273_ = l_Array_mkArray1___redArg(v_val_272_);
v___y_150_ = v___y_263_;
v___y_151_ = v___y_262_;
v___y_152_ = v___x_268_;
v___y_153_ = v___y_264_;
v___y_154_ = v_a_266_;
v___y_155_ = v___x_271_;
v___y_156_ = v___x_270_;
v___y_157_ = v___x_269_;
v___y_158_ = v___y_265_;
v___y_159_ = v___x_267_;
v___y_160_ = v___x_273_;
goto v___jp_149_;
}
else
{
lean_object* v___x_274_; 
lean_dec(v_doc_x3f_133_);
v___x_274_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__42));
v___y_150_ = v___y_263_;
v___y_151_ = v___y_262_;
v___y_152_ = v___x_268_;
v___y_153_ = v___y_264_;
v___y_154_ = v_a_266_;
v___y_155_ = v___x_271_;
v___y_156_ = v___x_270_;
v___y_157_ = v___x_269_;
v___y_158_ = v___y_265_;
v___y_159_ = v___x_267_;
v___y_160_ = v___x_274_;
goto v___jp_149_;
}
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec(v_k_137_);
lean_dec(v_attrKind_135_);
lean_dec(v_doc_x3f_133_);
v_a_330_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_144_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_144_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux___boxed(lean_object* v_doc_x3f_338_, lean_object* v_attrs_x3f_339_, lean_object* v_attrKind_340_, lean_object* v_tk_341_, lean_object* v_k_342_, lean_object* v_alts_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Elab_Command_elabMacroRulesAux(v_doc_x3f_338_, v_attrs_x3f_339_, v_attrKind_340_, v_tk_341_, v_k_342_, v_alts_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_tk_341_);
lean_dec(v_attrs_x3f_339_);
return v_res_347_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = lean_box(0);
v___x_349_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___closed__0);
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___boxed(lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0(lean_object* v_00_u03b1_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___boxed(lean_object* v_00_u03b1_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0(v_00_u03b1_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg___lam__0(lean_object* v___y_366_, uint8_t v_isExporting_367_, lean_object* v_a_x3f_368_){
_start:
{
lean_object* v___x_370_; lean_object* v_env_371_; lean_object* v_messages_372_; lean_object* v_scopes_373_; lean_object* v_usedQuotCtxts_374_; lean_object* v_nextMacroScope_375_; lean_object* v_maxRecDepth_376_; lean_object* v_ngen_377_; lean_object* v_auxDeclNGen_378_; lean_object* v_infoState_379_; lean_object* v_traceState_380_; lean_object* v_snapshotTasks_381_; lean_object* v_prevLinterStates_382_; lean_object* v_codeQualityEntryTasks_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_394_; 
v___x_370_ = lean_st_ref_take(v___y_366_);
v_env_371_ = lean_ctor_get(v___x_370_, 0);
v_messages_372_ = lean_ctor_get(v___x_370_, 1);
v_scopes_373_ = lean_ctor_get(v___x_370_, 2);
v_usedQuotCtxts_374_ = lean_ctor_get(v___x_370_, 3);
v_nextMacroScope_375_ = lean_ctor_get(v___x_370_, 4);
v_maxRecDepth_376_ = lean_ctor_get(v___x_370_, 5);
v_ngen_377_ = lean_ctor_get(v___x_370_, 6);
v_auxDeclNGen_378_ = lean_ctor_get(v___x_370_, 7);
v_infoState_379_ = lean_ctor_get(v___x_370_, 8);
v_traceState_380_ = lean_ctor_get(v___x_370_, 9);
v_snapshotTasks_381_ = lean_ctor_get(v___x_370_, 10);
v_prevLinterStates_382_ = lean_ctor_get(v___x_370_, 11);
v_codeQualityEntryTasks_383_ = lean_ctor_get(v___x_370_, 12);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_394_ == 0)
{
v___x_385_ = v___x_370_;
v_isShared_386_ = v_isSharedCheck_394_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_codeQualityEntryTasks_383_);
lean_inc(v_prevLinterStates_382_);
lean_inc(v_snapshotTasks_381_);
lean_inc(v_traceState_380_);
lean_inc(v_infoState_379_);
lean_inc(v_auxDeclNGen_378_);
lean_inc(v_ngen_377_);
lean_inc(v_maxRecDepth_376_);
lean_inc(v_nextMacroScope_375_);
lean_inc(v_usedQuotCtxts_374_);
lean_inc(v_scopes_373_);
lean_inc(v_messages_372_);
lean_inc(v_env_371_);
lean_dec(v___x_370_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_394_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_387_ = lean_box(0);
v___x_388_ = l_Lean_Environment_setExporting(v_env_371_, v_isExporting_367_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_388_);
v___x_390_ = v___x_385_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_messages_372_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v_scopes_373_);
lean_ctor_set(v_reuseFailAlloc_393_, 3, v_usedQuotCtxts_374_);
lean_ctor_set(v_reuseFailAlloc_393_, 4, v_nextMacroScope_375_);
lean_ctor_set(v_reuseFailAlloc_393_, 5, v_maxRecDepth_376_);
lean_ctor_set(v_reuseFailAlloc_393_, 6, v_ngen_377_);
lean_ctor_set(v_reuseFailAlloc_393_, 7, v_auxDeclNGen_378_);
lean_ctor_set(v_reuseFailAlloc_393_, 8, v_infoState_379_);
lean_ctor_set(v_reuseFailAlloc_393_, 9, v_traceState_380_);
lean_ctor_set(v_reuseFailAlloc_393_, 10, v_snapshotTasks_381_);
lean_ctor_set(v_reuseFailAlloc_393_, 11, v_prevLinterStates_382_);
lean_ctor_set(v_reuseFailAlloc_393_, 12, v_codeQualityEntryTasks_383_);
v___x_390_ = v_reuseFailAlloc_393_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_st_ref_put(v___y_366_, v___x_390_);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_387_);
return v___x_392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg___lam__0___boxed(lean_object* v___y_395_, lean_object* v_isExporting_396_, lean_object* v_a_x3f_397_, lean_object* v___y_398_){
_start:
{
uint8_t v_isExporting_boxed_399_; lean_object* v_res_400_; 
v_isExporting_boxed_399_ = lean_unbox(v_isExporting_396_);
v_res_400_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg___lam__0(v___y_395_, v_isExporting_boxed_399_, v_a_x3f_397_);
lean_dec(v_a_x3f_397_);
lean_dec(v___y_395_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(lean_object* v_x_401_, uint8_t v_isExporting_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___x_406_; lean_object* v_env_407_; lean_object* v___x_408_; uint8_t v_isModule_409_; 
v___x_406_ = lean_st_ref_get(v___y_404_);
v_env_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc_ref(v_env_407_);
lean_dec(v___x_406_);
v___x_408_ = l_Lean_Environment_header(v_env_407_);
v_isModule_409_ = lean_ctor_get_uint8(v___x_408_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_408_);
if (v_isModule_409_ == 0)
{
lean_object* v___x_410_; 
lean_dec_ref(v_env_407_);
lean_inc(v___y_404_);
lean_inc_ref(v___y_403_);
v___x_410_ = lean_apply_3(v_x_401_, v___y_403_, v___y_404_, lean_box(0));
return v___x_410_;
}
else
{
uint8_t v_isExporting_411_; 
v_isExporting_411_ = lean_ctor_get_uint8(v_env_407_, sizeof(void*)*13);
lean_dec_ref(v_env_407_);
if (v_isExporting_402_ == 0)
{
if (v_isExporting_411_ == 0)
{
lean_object* v___x_465_; 
lean_inc(v___y_404_);
lean_inc_ref(v___y_403_);
v___x_465_ = lean_apply_3(v_x_401_, v___y_403_, v___y_404_, lean_box(0));
return v___x_465_;
}
else
{
goto v___jp_412_;
}
}
else
{
if (v_isExporting_411_ == 0)
{
goto v___jp_412_;
}
else
{
lean_object* v___x_466_; 
lean_inc(v___y_404_);
lean_inc_ref(v___y_403_);
v___x_466_ = lean_apply_3(v_x_401_, v___y_403_, v___y_404_, lean_box(0));
return v___x_466_;
}
}
v___jp_412_:
{
lean_object* v___x_413_; lean_object* v_env_414_; lean_object* v_messages_415_; lean_object* v_scopes_416_; lean_object* v_usedQuotCtxts_417_; lean_object* v_nextMacroScope_418_; lean_object* v_maxRecDepth_419_; lean_object* v_ngen_420_; lean_object* v_auxDeclNGen_421_; lean_object* v_infoState_422_; lean_object* v_traceState_423_; lean_object* v_snapshotTasks_424_; lean_object* v_prevLinterStates_425_; lean_object* v_codeQualityEntryTasks_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_464_; 
v___x_413_ = lean_st_ref_take(v___y_404_);
v_env_414_ = lean_ctor_get(v___x_413_, 0);
v_messages_415_ = lean_ctor_get(v___x_413_, 1);
v_scopes_416_ = lean_ctor_get(v___x_413_, 2);
v_usedQuotCtxts_417_ = lean_ctor_get(v___x_413_, 3);
v_nextMacroScope_418_ = lean_ctor_get(v___x_413_, 4);
v_maxRecDepth_419_ = lean_ctor_get(v___x_413_, 5);
v_ngen_420_ = lean_ctor_get(v___x_413_, 6);
v_auxDeclNGen_421_ = lean_ctor_get(v___x_413_, 7);
v_infoState_422_ = lean_ctor_get(v___x_413_, 8);
v_traceState_423_ = lean_ctor_get(v___x_413_, 9);
v_snapshotTasks_424_ = lean_ctor_get(v___x_413_, 10);
v_prevLinterStates_425_ = lean_ctor_get(v___x_413_, 11);
v_codeQualityEntryTasks_426_ = lean_ctor_get(v___x_413_, 12);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_464_ == 0)
{
v___x_428_ = v___x_413_;
v_isShared_429_ = v_isSharedCheck_464_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_codeQualityEntryTasks_426_);
lean_inc(v_prevLinterStates_425_);
lean_inc(v_snapshotTasks_424_);
lean_inc(v_traceState_423_);
lean_inc(v_infoState_422_);
lean_inc(v_auxDeclNGen_421_);
lean_inc(v_ngen_420_);
lean_inc(v_maxRecDepth_419_);
lean_inc(v_nextMacroScope_418_);
lean_inc(v_usedQuotCtxts_417_);
lean_inc(v_scopes_416_);
lean_inc(v_messages_415_);
lean_inc(v_env_414_);
lean_dec(v___x_413_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_464_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_430_ = l_Lean_Environment_setExporting(v_env_414_, v_isExporting_402_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_messages_415_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_scopes_416_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_usedQuotCtxts_417_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_nextMacroScope_418_);
lean_ctor_set(v_reuseFailAlloc_463_, 5, v_maxRecDepth_419_);
lean_ctor_set(v_reuseFailAlloc_463_, 6, v_ngen_420_);
lean_ctor_set(v_reuseFailAlloc_463_, 7, v_auxDeclNGen_421_);
lean_ctor_set(v_reuseFailAlloc_463_, 8, v_infoState_422_);
lean_ctor_set(v_reuseFailAlloc_463_, 9, v_traceState_423_);
lean_ctor_set(v_reuseFailAlloc_463_, 10, v_snapshotTasks_424_);
lean_ctor_set(v_reuseFailAlloc_463_, 11, v_prevLinterStates_425_);
lean_ctor_set(v_reuseFailAlloc_463_, 12, v_codeQualityEntryTasks_426_);
v___x_432_ = v_reuseFailAlloc_463_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; lean_object* v_r_434_; 
v___x_433_ = lean_st_ref_put(v___y_404_, v___x_432_);
lean_inc(v___y_404_);
lean_inc_ref(v___y_403_);
v_r_434_ = lean_apply_3(v_x_401_, v___y_403_, v___y_404_, lean_box(0));
if (lean_obj_tag(v_r_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_451_; 
v_a_435_ = lean_ctor_get(v_r_434_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v_r_434_);
if (v_isSharedCheck_451_ == 0)
{
v___x_437_ = v_r_434_;
v_isShared_438_ = v_isSharedCheck_451_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v_r_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_451_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
lean_inc(v_a_435_);
if (v_isShared_438_ == 0)
{
lean_ctor_set_tag(v___x_437_, 1);
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_435_);
v___x_440_ = v_reuseFailAlloc_450_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
v___x_441_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg___lam__0(v___y_404_, v_isExporting_411_, v___x_440_);
lean_dec_ref(v___x_440_);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; 
v_unused_449_ = lean_ctor_get(v___x_441_, 0);
lean_dec(v_unused_449_);
v___x_443_ = v___x_441_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_dec(v___x_441_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v_a_435_);
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_435_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
v_a_452_ = lean_ctor_get(v_r_434_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v_r_434_, 1);
v___x_453_ = lean_box(0);
v___x_454_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg___lam__0(v___y_404_, v_isExporting_411_, v___x_453_);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; 
v_unused_462_ = lean_ctor_get(v___x_454_, 0);
lean_dec(v_unused_462_);
v___x_456_ = v___x_454_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_dec(v___x_454_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set_tag(v___x_456_, 1);
lean_ctor_set(v___x_456_, 0, v_a_452_);
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_452_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg___boxed(lean_object* v_x_467_, lean_object* v_isExporting_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
uint8_t v_isExporting_boxed_472_; lean_object* v_res_473_; 
v_isExporting_boxed_472_ = lean_unbox(v_isExporting_468_);
v_res_473_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v_x_467_, v_isExporting_boxed_472_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1(lean_object* v_00_u03b1_474_, lean_object* v_x_475_, uint8_t v_isExporting_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v_x_475_, v_isExporting_476_, v___y_477_, v___y_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___boxed(lean_object* v_00_u03b1_481_, lean_object* v_x_482_, lean_object* v_isExporting_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
uint8_t v_isExporting_boxed_487_; lean_object* v_res_488_; 
v_isExporting_boxed_487_ = lean_unbox(v_isExporting_483_);
v_res_488_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1(v_00_u03b1_481_, v_x_482_, v_isExporting_boxed_487_, v___y_484_, v___y_485_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0(lean_object* v___x_489_, lean_object* v___x_490_, lean_object* v_doc_x3f_491_, lean_object* v_attrs_x3f_492_, lean_object* v_attrKind_493_, lean_object* v_tk_494_, lean_object* v_alts_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Elab_Command_getRef___redArg(v___y_496_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v_fileName_501_; lean_object* v_fileMap_502_; lean_object* v_currRecDepth_503_; lean_object* v_cmdPos_504_; lean_object* v_macroStack_505_; lean_object* v_quotContext_x3f_506_; lean_object* v_currMacroScope_507_; lean_object* v_snap_x3f_508_; lean_object* v_cancelTk_x3f_509_; uint8_t v_suppressElabErrors_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_529_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_499_, 1);
v_fileName_501_ = lean_ctor_get(v___y_496_, 0);
v_fileMap_502_ = lean_ctor_get(v___y_496_, 1);
v_currRecDepth_503_ = lean_ctor_get(v___y_496_, 2);
v_cmdPos_504_ = lean_ctor_get(v___y_496_, 3);
v_macroStack_505_ = lean_ctor_get(v___y_496_, 4);
v_quotContext_x3f_506_ = lean_ctor_get(v___y_496_, 5);
v_currMacroScope_507_ = lean_ctor_get(v___y_496_, 6);
v_snap_x3f_508_ = lean_ctor_get(v___y_496_, 8);
v_cancelTk_x3f_509_ = lean_ctor_get(v___y_496_, 9);
v_suppressElabErrors_510_ = lean_ctor_get_uint8(v___y_496_, sizeof(void*)*10);
v_isSharedCheck_529_ = !lean_is_exclusive(v___y_496_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; 
v_unused_530_ = lean_ctor_get(v___y_496_, 7);
lean_dec(v_unused_530_);
v___x_512_ = v___y_496_;
v_isShared_513_ = v_isSharedCheck_529_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_cancelTk_x3f_509_);
lean_inc(v_snap_x3f_508_);
lean_inc(v_currMacroScope_507_);
lean_inc(v_quotContext_x3f_506_);
lean_inc(v_macroStack_505_);
lean_inc(v_cmdPos_504_);
lean_inc(v_currRecDepth_503_);
lean_inc(v_fileMap_502_);
lean_inc(v_fileName_501_);
lean_dec(v___y_496_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_529_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v_ref_514_; lean_object* v___x_516_; 
v_ref_514_ = l_Lean_replaceRef(v___x_489_, v_a_500_);
lean_dec(v_a_500_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 7, v_ref_514_);
v___x_516_ = v___x_512_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_fileName_501_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_fileMap_502_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v_currRecDepth_503_);
lean_ctor_set(v_reuseFailAlloc_528_, 3, v_cmdPos_504_);
lean_ctor_set(v_reuseFailAlloc_528_, 4, v_macroStack_505_);
lean_ctor_set(v_reuseFailAlloc_528_, 5, v_quotContext_x3f_506_);
lean_ctor_set(v_reuseFailAlloc_528_, 6, v_currMacroScope_507_);
lean_ctor_set(v_reuseFailAlloc_528_, 7, v_ref_514_);
lean_ctor_set(v_reuseFailAlloc_528_, 8, v_snap_x3f_508_);
lean_ctor_set(v_reuseFailAlloc_528_, 9, v_cancelTk_x3f_509_);
lean_ctor_set_uint8(v_reuseFailAlloc_528_, sizeof(void*)*10, v_suppressElabErrors_510_);
v___x_516_ = v_reuseFailAlloc_528_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_Elab_Command_resolveSyntaxKind(v___x_490_, v___x_516_, v___y_497_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_519_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v___x_517_, 1);
v___x_519_ = l_Lean_Elab_Command_elabMacroRulesAux(v_doc_x3f_491_, v_attrs_x3f_492_, v_attrKind_493_, v_tk_494_, v_a_518_, v_alts_495_, v___x_516_, v___y_497_);
lean_dec_ref(v___x_516_);
return v___x_519_;
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec_ref(v___x_516_);
lean_dec_ref(v_alts_495_);
lean_dec(v_attrKind_493_);
lean_dec(v_doc_x3f_491_);
v_a_520_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_517_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_517_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_496_);
lean_dec_ref(v_alts_495_);
lean_dec(v_attrKind_493_);
lean_dec(v_doc_x3f_491_);
lean_dec(v___x_490_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0___boxed(lean_object* v___x_531_, lean_object* v___x_532_, lean_object* v_doc_x3f_533_, lean_object* v_attrs_x3f_534_, lean_object* v_attrKind_535_, lean_object* v_tk_536_, lean_object* v_alts_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_Elab_Command_elabMacroRules___lam__0(v___x_531_, v___x_532_, v_doc_x3f_533_, v_attrs_x3f_534_, v_attrKind_535_, v_tk_536_, v_alts_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec(v_tk_536_);
lean_dec(v_attrs_x3f_534_);
lean_dec(v___x_531_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5(lean_object* v___x_545_, lean_object* v___x_546_, lean_object* v_attrKind_547_, lean_object* v___x_548_, lean_object* v___x_549_, lean_object* v_attrs_x3f_550_, lean_object* v___x_551_, lean_object* v___x_552_, lean_object* v___x_553_, lean_object* v_doc_x3f_554_, lean_object* v_kind_x3f_555_, lean_object* v_alts_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_Elab_Command_getRef___redArg(v___y_557_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_638_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_638_ == 0)
{
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_638_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_638_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
uint8_t v___x_565_; lean_object* v___x_566_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___x_627_; 
v___x_565_ = 0;
v___x_566_ = l_Lean_SourceInfo_fromRef(v_a_561_, v___x_565_);
lean_dec(v_a_561_);
v___x_627_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_557_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_quotContext_x3f_628_; 
lean_dec_ref_known(v___x_627_, 1);
v_quotContext_x3f_628_ = lean_ctor_get(v___y_557_, 5);
if (lean_obj_tag(v_quotContext_x3f_628_) == 0)
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v___y_558_);
lean_dec_ref(v___x_629_);
goto v___jp_621_;
}
else
{
goto v___jp_621_;
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec(v___x_566_);
lean_del_object(v___x_563_);
lean_dec(v_kind_x3f_555_);
lean_dec(v_doc_x3f_554_);
lean_dec_ref(v___x_553_);
lean_dec_ref(v___x_552_);
lean_dec_ref(v___x_551_);
lean_dec_ref(v___x_548_);
lean_dec(v_attrKind_547_);
lean_dec(v___x_546_);
lean_dec(v___x_545_);
v_a_630_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_627_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_627_);
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
v___jp_567_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
lean_inc_ref_n(v___y_570_, 2);
v___x_574_ = l_Array_append___redArg(v___y_570_, v___y_573_);
lean_dec_ref(v___y_573_);
lean_inc_n(v___y_569_, 2);
lean_inc_n(v___x_566_, 3);
v___x_575_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_575_, 0, v___x_566_);
lean_ctor_set(v___x_575_, 1, v___y_569_);
lean_ctor_set(v___x_575_, 2, v___x_574_);
v___x_576_ = l_Array_append___redArg(v___y_570_, v_alts_556_);
v___x_577_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_577_, 0, v___x_566_);
lean_ctor_set(v___x_577_, 1, v___y_569_);
lean_ctor_set(v___x_577_, 2, v___x_576_);
v___x_578_ = l_Lean_Syntax_node1(v___x_566_, v___x_545_, v___x_577_);
v___x_579_ = l_Lean_Syntax_node6(v___x_566_, v___x_546_, v___y_572_, v___y_568_, v_attrKind_547_, v___y_571_, v___x_575_, v___x_578_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_579_);
v___x_581_ = v___x_563_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
v___jp_583_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
lean_inc_ref(v___y_585_);
v___x_588_ = l_Array_append___redArg(v___y_585_, v___y_587_);
lean_dec_ref(v___y_587_);
lean_inc(v___y_584_);
lean_inc_n(v___x_566_, 2);
v___x_589_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_589_, 0, v___x_566_);
lean_ctor_set(v___x_589_, 1, v___y_584_);
lean_ctor_set(v___x_589_, 2, v___x_588_);
v___x_590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_566_);
lean_ctor_set(v___x_590_, 1, v___x_548_);
if (lean_obj_tag(v_kind_x3f_555_) == 0)
{
lean_object* v___x_591_; 
v___x_591_ = lean_mk_empty_array_with_capacity(v___x_549_);
v___y_568_ = v___x_589_;
v___y_569_ = v___y_584_;
v___y_570_ = v___y_585_;
v___y_571_ = v___x_590_;
v___y_572_ = v___y_586_;
v___y_573_ = v___x_591_;
goto v___jp_567_;
}
else
{
lean_object* v_val_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_val_592_ = lean_ctor_get(v_kind_x3f_555_, 0);
lean_inc(v_val_592_);
lean_dec_ref_known(v_kind_x3f_555_, 1);
v___x_593_ = l_Lean_mkIdent(v_val_592_);
v___x_594_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0));
lean_inc_n(v___x_566_, 4);
v___x_595_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_566_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1));
v___x_597_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_566_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__12));
v___x_599_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_566_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2));
v___x_601_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_566_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l_Array_mkArray5___redArg(v___x_595_, v___x_597_, v___x_599_, v___x_593_, v___x_601_);
v___y_568_ = v___x_589_;
v___y_569_ = v___y_584_;
v___y_570_ = v___y_585_;
v___y_571_ = v___x_590_;
v___y_572_ = v___y_586_;
v___y_573_ = v___x_602_;
goto v___jp_567_;
}
}
v___jp_603_:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
lean_inc_ref(v___y_605_);
v___x_607_ = l_Array_append___redArg(v___y_605_, v___y_606_);
lean_dec_ref(v___y_606_);
lean_inc(v___y_604_);
lean_inc(v___x_566_);
v___x_608_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_608_, 0, v___x_566_);
lean_ctor_set(v___x_608_, 1, v___y_604_);
lean_ctor_set(v___x_608_, 2, v___x_607_);
if (lean_obj_tag(v_attrs_x3f_550_) == 1)
{
lean_object* v_val_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v_val_609_ = lean_ctor_get(v_attrs_x3f_550_, 0);
v___x_610_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
v___x_611_ = l_Lean_Name_mkStr4(v___x_551_, v___x_552_, v___x_553_, v___x_610_);
v___x_612_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__3));
lean_inc_n(v___x_566_, 4);
v___x_613_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_566_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
lean_inc_ref(v___y_605_);
v___x_614_ = l_Array_append___redArg(v___y_605_, v_val_609_);
lean_inc(v___y_604_);
v___x_615_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_615_, 0, v___x_566_);
lean_ctor_set(v___x_615_, 1, v___y_604_);
lean_ctor_set(v___x_615_, 2, v___x_614_);
v___x_616_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__4));
v___x_617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_566_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = l_Lean_Syntax_node3(v___x_566_, v___x_611_, v___x_613_, v___x_615_, v___x_617_);
v___x_619_ = l_Array_mkArray1___redArg(v___x_618_);
v___y_584_ = v___y_604_;
v___y_585_ = v___y_605_;
v___y_586_ = v___x_608_;
v___y_587_ = v___x_619_;
goto v___jp_583_;
}
else
{
lean_object* v___x_620_; 
lean_dec_ref(v___x_553_);
lean_dec_ref(v___x_552_);
lean_dec_ref(v___x_551_);
v___x_620_ = lean_mk_empty_array_with_capacity(v___x_549_);
v___y_584_ = v___y_604_;
v___y_585_ = v___y_605_;
v___y_586_ = v___x_608_;
v___y_587_ = v___x_620_;
goto v___jp_583_;
}
}
v___jp_621_:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__40));
v___x_623_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__41, &l_Lean_Elab_Command_elabMacroRulesAux___closed__41_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__41);
if (lean_obj_tag(v_doc_x3f_554_) == 1)
{
lean_object* v_val_624_; lean_object* v___x_625_; 
v_val_624_ = lean_ctor_get(v_doc_x3f_554_, 0);
lean_inc(v_val_624_);
lean_dec_ref_known(v_doc_x3f_554_, 1);
v___x_625_ = l_Array_mkArray1___redArg(v_val_624_);
v___y_604_ = v___x_622_;
v___y_605_ = v___x_623_;
v___y_606_ = v___x_625_;
goto v___jp_603_;
}
else
{
lean_object* v___x_626_; 
lean_dec(v_doc_x3f_554_);
v___x_626_ = lean_mk_empty_array_with_capacity(v___x_549_);
v___y_604_ = v___x_622_;
v___y_605_ = v___x_623_;
v___y_606_ = v___x_626_;
goto v___jp_603_;
}
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v_kind_x3f_555_);
lean_dec(v_doc_x3f_554_);
lean_dec_ref(v___x_553_);
lean_dec_ref(v___x_552_);
lean_dec_ref(v___x_551_);
lean_dec_ref(v___x_548_);
lean_dec(v_attrKind_547_);
lean_dec(v___x_546_);
lean_dec(v___x_545_);
v_a_639_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_560_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_560_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5___boxed(lean_object* v___x_647_, lean_object* v___x_648_, lean_object* v_attrKind_649_, lean_object* v___x_650_, lean_object* v___x_651_, lean_object* v_attrs_x3f_652_, lean_object* v___x_653_, lean_object* v___x_654_, lean_object* v___x_655_, lean_object* v_doc_x3f_656_, lean_object* v_kind_x3f_657_, lean_object* v_alts_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_Elab_Command_elabMacroRules___lam__5(v___x_647_, v___x_648_, v_attrKind_649_, v___x_650_, v___x_651_, v_attrs_x3f_652_, v___x_653_, v___x_654_, v___x_655_, v_doc_x3f_656_, v_kind_x3f_657_, v_alts_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec_ref(v_alts_658_);
lean_dec(v_attrs_x3f_652_);
lean_dec(v___x_651_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1(lean_object* v_stx_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; 
v___x_723_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__34));
v___x_724_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
v___x_725_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___closed__0));
v___x_726_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0));
lean_inc(v_stx_719_);
v___x_727_ = l_Lean_Syntax_isOfKind(v_stx_719_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_793_; 
lean_dec(v_stx_719_);
v___x_793_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_793_;
}
else
{
lean_object* v___x_794_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v_a_807_; uint8_t v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; uint8_t v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v_attrs_x3f_883_; lean_object* v_doc_x3f_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_1102_ = l_Lean_Syntax_getArg(v_stx_719_, v___x_794_);
v___x_1103_ = l_Lean_Syntax_isNone(v___x_1102_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1104_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1102_);
v___x_1105_ = l_Lean_Syntax_matchesNull(v___x_1102_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; 
lean_dec(v___x_1102_);
lean_dec(v_stx_719_);
v___x_1106_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_1106_;
}
else
{
lean_object* v_doc_x3f_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v_doc_x3f_1107_ = l_Lean_Syntax_getArg(v___x_1102_, v___x_794_);
lean_dec(v___x_1102_);
v___x_1108_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17));
lean_inc(v_doc_x3f_1107_);
v___x_1109_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1107_, v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; 
lean_dec(v_doc_x3f_1107_);
lean_dec(v_stx_719_);
v___x_1110_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_1110_;
}
else
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1111_, 0, v_doc_x3f_1107_);
v_doc_x3f_1086_ = v___x_1111_;
v___y_1087_ = v___y_720_;
v___y_1088_ = v___y_721_;
goto v___jp_1085_;
}
}
}
else
{
lean_object* v___x_1112_; 
lean_dec(v___x_1102_);
v___x_1112_ = lean_box(0);
v_doc_x3f_1086_ = v___x_1112_;
v___y_1087_ = v___y_720_;
v___y_1088_ = v___y_721_;
goto v___jp_1085_;
}
v___jp_795_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__37));
v___x_809_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__38));
v___x_810_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__41, &l_Lean_Elab_Command_elabMacroRulesAux___closed__41_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__41);
if (lean_obj_tag(v___y_799_) == 1)
{
lean_object* v_val_811_; lean_object* v___x_812_; 
v_val_811_ = lean_ctor_get(v___y_799_, 0);
lean_inc(v_val_811_);
lean_dec_ref_known(v___y_799_, 1);
v___x_812_ = l_Array_mkArray1___redArg(v_val_811_);
v___y_729_ = v___y_796_;
v___y_730_ = v___y_797_;
v___y_731_ = v___y_798_;
v___y_732_ = v___x_810_;
v___y_733_ = v___y_800_;
v___y_734_ = v___y_803_;
v___y_735_ = v___y_802_;
v___y_736_ = v___y_806_;
v___y_737_ = v___x_809_;
v___y_738_ = v___x_808_;
v___y_739_ = v___y_801_;
v___y_740_ = v___y_805_;
v___y_741_ = v___y_804_;
v___y_742_ = v_a_807_;
v___y_743_ = v___x_812_;
goto v___jp_728_;
}
else
{
lean_object* v___x_813_; 
lean_dec(v___y_799_);
v___x_813_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__42));
v___y_729_ = v___y_796_;
v___y_730_ = v___y_797_;
v___y_731_ = v___y_798_;
v___y_732_ = v___x_810_;
v___y_733_ = v___y_800_;
v___y_734_ = v___y_803_;
v___y_735_ = v___y_802_;
v___y_736_ = v___y_806_;
v___y_737_ = v___x_809_;
v___y_738_ = v___x_808_;
v___y_739_ = v___y_801_;
v___y_740_ = v___y_805_;
v___y_741_ = v___y_804_;
v___y_742_ = v_a_807_;
v___y_743_ = v___x_813_;
goto v___jp_728_;
}
}
v___jp_814_:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = l_Lean_Parser_Command_visibility_ofAttrKind(v___y_820_);
v___x_829_ = l_Lean_Elab_Command_getRef___redArg(v___y_823_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_829_, 1);
v___x_831_ = l_Lean_SourceInfo_fromRef(v_a_830_, v___y_815_);
lean_dec(v_a_830_);
v___x_832_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_823_);
lean_dec_ref(v___y_823_);
if (lean_obj_tag(v___x_832_) == 0)
{
if (lean_obj_tag(v___y_824_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_834_; lean_object* v_a_835_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_832_, 1);
v___x_834_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v___y_821_);
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
lean_dec_ref(v___x_834_);
v___y_796_ = v_a_833_;
v___y_797_ = v___y_816_;
v___y_798_ = v___y_817_;
v___y_799_ = v___y_818_;
v___y_800_ = v___x_828_;
v___y_801_ = v___y_827_;
v___y_802_ = v___y_819_;
v___y_803_ = v___x_831_;
v___y_804_ = v___y_825_;
v___y_805_ = v___y_826_;
v___y_806_ = v___y_822_;
v_a_807_ = v_a_835_;
goto v___jp_795_;
}
else
{
lean_object* v_a_836_; lean_object* v_val_837_; 
v_a_836_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_836_);
lean_dec_ref_known(v___x_832_, 1);
v_val_837_ = lean_ctor_get(v___y_824_, 0);
lean_inc(v_val_837_);
v___y_796_ = v_a_836_;
v___y_797_ = v___y_816_;
v___y_798_ = v___y_817_;
v___y_799_ = v___y_818_;
v___y_800_ = v___x_828_;
v___y_801_ = v___y_827_;
v___y_802_ = v___y_819_;
v___y_803_ = v___x_831_;
v___y_804_ = v___y_825_;
v___y_805_ = v___y_826_;
v___y_806_ = v___y_822_;
v_a_807_ = v_val_837_;
goto v___jp_795_;
}
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_dec(v___x_831_);
lean_dec(v___x_828_);
lean_dec_ref(v___y_827_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_822_);
lean_dec(v___y_819_);
lean_dec(v___y_818_);
lean_dec(v___y_817_);
lean_dec(v___y_816_);
v_a_838_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_832_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_832_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
else
{
lean_dec(v___x_828_);
lean_dec_ref(v___y_827_);
lean_dec_ref(v___y_825_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec(v___y_819_);
lean_dec(v___y_818_);
lean_dec(v___y_817_);
lean_dec(v___y_816_);
return v___x_829_;
}
}
v___jp_846_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_862_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__43));
lean_inc_ref(v___y_860_);
v___x_863_ = l_Lean_Name_mkStr4(v___x_723_, v___x_724_, v___y_860_, v___x_862_);
v___x_864_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__46));
v___x_865_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__47));
lean_inc_n(v___y_857_, 2);
v___x_866_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_866_, 0, v___y_857_);
lean_ctor_set(v___x_866_, 1, v___x_864_);
lean_inc(v___y_848_);
v___x_867_ = l_Lean_Syntax_node2(v___y_857_, v___x_865_, v___x_866_, v___y_848_);
lean_inc(v___y_853_);
v___x_868_ = l_Lean_Syntax_node2(v___y_857_, v___x_863_, v___y_853_, v___x_867_);
if (lean_obj_tag(v___y_856_) == 0)
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_869_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__48));
v___x_870_ = lean_mk_empty_array_with_capacity(v___y_852_);
v___x_871_ = lean_array_push(v___x_870_, v___x_868_);
v___x_872_ = l_Lean_Syntax_SepArray_ofElems(v___x_869_, v___x_871_);
lean_dec_ref(v___x_871_);
v___y_815_ = v___y_847_;
v___y_816_ = v___y_848_;
v___y_817_ = v___y_849_;
v___y_818_ = v___y_850_;
v___y_819_ = v___y_851_;
v___y_820_ = v___y_853_;
v___y_821_ = v___y_854_;
v___y_822_ = v___y_855_;
v___y_823_ = v___y_858_;
v___y_824_ = v___y_859_;
v___y_825_ = v___y_860_;
v___y_826_ = v___y_861_;
v___y_827_ = v___x_872_;
goto v___jp_814_;
}
else
{
lean_object* v_val_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_val_873_ = lean_ctor_get(v___y_856_, 0);
lean_inc(v_val_873_);
lean_dec_ref_known(v___y_856_, 1);
v___x_874_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__48));
v___x_875_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_873_);
lean_dec(v_val_873_);
v___x_876_ = lean_array_push(v___x_875_, v___x_868_);
v___x_877_ = l_Lean_Syntax_SepArray_ofElems(v___x_874_, v___x_876_);
lean_dec_ref(v___x_876_);
v___y_815_ = v___y_847_;
v___y_816_ = v___y_848_;
v___y_817_ = v___y_849_;
v___y_818_ = v___y_850_;
v___y_819_ = v___y_851_;
v___y_820_ = v___y_853_;
v___y_821_ = v___y_854_;
v___y_822_ = v___y_855_;
v___y_823_ = v___y_858_;
v___y_824_ = v___y_859_;
v___y_825_ = v___y_860_;
v___y_826_ = v___y_861_;
v___y_827_ = v___x_877_;
goto v___jp_814_;
}
}
v___jp_878_:
{
lean_object* v___x_884_; lean_object* v_attrKind_885_; lean_object* v___x_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v___x_884_ = lean_unsigned_to_nat(2u);
v_attrKind_885_ = l_Lean_Syntax_getArg(v_stx_719_, v___x_884_);
v___x_886_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
v___x_887_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8));
lean_inc(v_attrKind_885_);
v___x_888_ = l_Lean_Syntax_isOfKind(v_attrKind_885_, v___x_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; 
lean_dec(v_attrKind_885_);
lean_dec(v_attrs_x3f_883_);
lean_dec(v___y_880_);
lean_dec(v_stx_719_);
v___x_889_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_889_;
}
else
{
lean_object* v___x_890_; lean_object* v_tk_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_890_ = lean_unsigned_to_nat(3u);
v_tk_891_ = l_Lean_Syntax_getArg(v_stx_719_, v___x_890_);
v___x_892_ = lean_unsigned_to_nat(4u);
v___x_893_ = l_Lean_Syntax_getArg(v_stx_719_, v___x_892_);
lean_inc(v___x_893_);
v___x_894_ = l_Lean_Syntax_matchesNull(v___x_893_, v___x_794_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_895_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_893_);
v___x_896_ = l_Lean_Syntax_matchesNull(v___x_893_, v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
lean_dec(v___x_893_);
lean_dec(v_tk_891_);
lean_dec(v_attrKind_885_);
lean_dec(v_attrs_x3f_883_);
lean_dec(v___y_880_);
lean_dec(v_stx_719_);
v___x_897_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_897_;
}
else
{
lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_898_ = l_Lean_Syntax_getArg(v_stx_719_, v___x_895_);
lean_dec(v_stx_719_);
v___x_899_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9));
lean_inc(v___x_898_);
v___x_900_ = l_Lean_Syntax_isOfKind(v___x_898_, v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
lean_dec(v___x_898_);
lean_dec(v___x_893_);
lean_dec(v_tk_891_);
lean_dec(v_attrKind_885_);
lean_dec(v_attrs_x3f_883_);
lean_dec(v___y_880_);
v___x_901_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_901_;
}
else
{
lean_object* v_kind_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v_kind_902_ = l_Lean_Syntax_getArg(v___x_893_, v___x_890_);
lean_dec(v___x_893_);
v___x_903_ = l_Lean_Syntax_getArg(v___x_898_, v___x_794_);
lean_dec(v___x_898_);
lean_inc(v___x_903_);
v___x_904_ = l_Lean_Syntax_matchesNull(v___x_903_, v___y_882_);
if (v___x_904_ == 0)
{
lean_object* v_alts_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___f_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_alts_905_ = l_Lean_Syntax_getArgs(v___x_903_);
lean_dec(v___x_903_);
v___x_906_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__40));
v___x_907_ = lean_box(2);
lean_inc_ref(v_alts_905_);
v___x_908_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v___x_906_);
lean_ctor_set(v___x_908_, 2, v_alts_905_);
v___x_909_ = lean_mk_empty_array_with_capacity(v___x_884_);
lean_inc(v_tk_891_);
v___x_910_ = lean_array_push(v___x_909_, v_tk_891_);
v___x_911_ = lean_array_push(v___x_910_, v___x_908_);
v___x_912_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_912_, 0, v___x_907_);
lean_ctor_set(v___x_912_, 1, v___x_906_);
lean_ctor_set(v___x_912_, 2, v___x_911_);
v___x_913_ = l_Lean_TSyntax_getId(v_kind_902_);
lean_dec(v_kind_902_);
lean_inc(v_attrKind_885_);
v___f_914_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_914_, 0, v___x_912_);
lean_closure_set(v___f_914_, 1, v___x_913_);
lean_closure_set(v___f_914_, 2, v___y_880_);
lean_closure_set(v___f_914_, 3, v_attrs_x3f_883_);
lean_closure_set(v___f_914_, 4, v_attrKind_885_);
lean_closure_set(v___f_914_, 5, v_tk_891_);
lean_closure_set(v___f_914_, 6, v_alts_905_);
v___x_915_ = l_Lean_Syntax_getArg(v_attrKind_885_, v___x_794_);
lean_dec(v_attrKind_885_);
lean_inc(v___x_915_);
v___x_916_ = l_Lean_Syntax_matchesNull(v___x_915_, v___y_882_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; 
lean_dec(v___x_915_);
v___x_917_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_914_, v___x_900_, v___y_881_, v___y_879_);
return v___x_917_;
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_918_ = l_Lean_Syntax_getArg(v___x_915_, v___x_794_);
lean_dec(v___x_915_);
v___x_919_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11));
v___x_920_ = l_Lean_Syntax_isOfKind(v___x_918_, v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_914_, v___x_900_, v___y_881_, v___y_879_);
return v___x_921_;
}
else
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_914_, v___x_904_, v___y_881_, v___y_879_);
return v___x_922_;
}
}
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_923_ = l_Lean_Syntax_getArg(v___x_903_, v___x_794_);
v___x_924_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
lean_inc(v___x_923_);
v___x_925_ = l_Lean_Syntax_isOfKind(v___x_923_, v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v_alts_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___f_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
lean_dec(v___x_923_);
v_alts_926_ = l_Lean_Syntax_getArgs(v___x_903_);
lean_dec(v___x_903_);
v___x_927_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__40));
v___x_928_ = lean_box(2);
lean_inc_ref(v_alts_926_);
v___x_929_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v___x_927_);
lean_ctor_set(v___x_929_, 2, v_alts_926_);
v___x_930_ = lean_mk_empty_array_with_capacity(v___x_884_);
lean_inc(v_tk_891_);
v___x_931_ = lean_array_push(v___x_930_, v_tk_891_);
v___x_932_ = lean_array_push(v___x_931_, v___x_929_);
v___x_933_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_933_, 0, v___x_928_);
lean_ctor_set(v___x_933_, 1, v___x_927_);
lean_ctor_set(v___x_933_, 2, v___x_932_);
v___x_934_ = l_Lean_TSyntax_getId(v_kind_902_);
lean_dec(v_kind_902_);
lean_inc(v_attrKind_885_);
v___f_935_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_935_, 0, v___x_933_);
lean_closure_set(v___f_935_, 1, v___x_934_);
lean_closure_set(v___f_935_, 2, v___y_880_);
lean_closure_set(v___f_935_, 3, v_attrs_x3f_883_);
lean_closure_set(v___f_935_, 4, v_attrKind_885_);
lean_closure_set(v___f_935_, 5, v_tk_891_);
lean_closure_set(v___f_935_, 6, v_alts_926_);
v___x_936_ = l_Lean_Syntax_getArg(v_attrKind_885_, v___x_794_);
lean_dec(v_attrKind_885_);
lean_inc(v___x_936_);
v___x_937_ = l_Lean_Syntax_matchesNull(v___x_936_, v___y_882_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; 
lean_dec(v___x_936_);
v___x_938_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_935_, v___x_904_, v___y_881_, v___y_879_);
return v___x_938_;
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_939_ = l_Lean_Syntax_getArg(v___x_936_, v___x_794_);
lean_dec(v___x_936_);
v___x_940_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11));
v___x_941_ = l_Lean_Syntax_isOfKind(v___x_939_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_935_, v___x_904_, v___y_881_, v___y_879_);
return v___x_942_;
}
else
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_935_, v___x_925_, v___y_881_, v___y_879_);
return v___x_943_;
}
}
}
else
{
lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_944_ = l_Lean_Syntax_getArg(v___x_923_, v___y_882_);
lean_inc(v___x_944_);
v___x_945_ = l_Lean_Syntax_matchesNull(v___x_944_, v___y_882_);
if (v___x_945_ == 0)
{
lean_object* v_alts_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___f_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
lean_dec(v___x_944_);
lean_dec(v___x_923_);
v_alts_946_ = l_Lean_Syntax_getArgs(v___x_903_);
lean_dec(v___x_903_);
v___x_947_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__40));
v___x_948_ = lean_box(2);
lean_inc_ref(v_alts_946_);
v___x_949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v___x_947_);
lean_ctor_set(v___x_949_, 2, v_alts_946_);
v___x_950_ = lean_mk_empty_array_with_capacity(v___x_884_);
lean_inc(v_tk_891_);
v___x_951_ = lean_array_push(v___x_950_, v_tk_891_);
v___x_952_ = lean_array_push(v___x_951_, v___x_949_);
v___x_953_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_953_, 0, v___x_948_);
lean_ctor_set(v___x_953_, 1, v___x_947_);
lean_ctor_set(v___x_953_, 2, v___x_952_);
v___x_954_ = l_Lean_TSyntax_getId(v_kind_902_);
lean_dec(v_kind_902_);
lean_inc(v_attrKind_885_);
v___f_955_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_955_, 0, v___x_953_);
lean_closure_set(v___f_955_, 1, v___x_954_);
lean_closure_set(v___f_955_, 2, v___y_880_);
lean_closure_set(v___f_955_, 3, v_attrs_x3f_883_);
lean_closure_set(v___f_955_, 4, v_attrKind_885_);
lean_closure_set(v___f_955_, 5, v_tk_891_);
lean_closure_set(v___f_955_, 6, v_alts_946_);
v___x_956_ = l_Lean_Syntax_getArg(v_attrKind_885_, v___x_794_);
lean_dec(v_attrKind_885_);
lean_inc(v___x_956_);
v___x_957_ = l_Lean_Syntax_matchesNull(v___x_956_, v___y_882_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
lean_dec(v___x_956_);
v___x_958_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_955_, v___x_925_, v___y_881_, v___y_879_);
return v___x_958_;
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_959_ = l_Lean_Syntax_getArg(v___x_956_, v___x_794_);
lean_dec(v___x_956_);
v___x_960_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11));
v___x_961_ = l_Lean_Syntax_isOfKind(v___x_959_, v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_955_, v___x_925_, v___y_881_, v___y_879_);
return v___x_962_;
}
else
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_955_, v___x_945_, v___y_881_, v___y_879_);
return v___x_963_;
}
}
}
else
{
lean_object* v___x_964_; uint8_t v___x_965_; 
v___x_964_ = l_Lean_Syntax_getArg(v___x_944_, v___x_794_);
lean_dec(v___x_944_);
lean_inc(v___x_964_);
v___x_965_ = l_Lean_Syntax_matchesNull(v___x_964_, v___y_882_);
if (v___x_965_ == 0)
{
lean_object* v_alts_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___f_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
lean_dec(v___x_964_);
lean_dec(v___x_923_);
v_alts_966_ = l_Lean_Syntax_getArgs(v___x_903_);
lean_dec(v___x_903_);
v___x_967_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__40));
v___x_968_ = lean_box(2);
lean_inc_ref(v_alts_966_);
v___x_969_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___x_967_);
lean_ctor_set(v___x_969_, 2, v_alts_966_);
v___x_970_ = lean_mk_empty_array_with_capacity(v___x_884_);
lean_inc(v_tk_891_);
v___x_971_ = lean_array_push(v___x_970_, v_tk_891_);
v___x_972_ = lean_array_push(v___x_971_, v___x_969_);
v___x_973_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_973_, 0, v___x_968_);
lean_ctor_set(v___x_973_, 1, v___x_967_);
lean_ctor_set(v___x_973_, 2, v___x_972_);
v___x_974_ = l_Lean_TSyntax_getId(v_kind_902_);
lean_dec(v_kind_902_);
lean_inc(v_attrKind_885_);
v___f_975_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_975_, 0, v___x_973_);
lean_closure_set(v___f_975_, 1, v___x_974_);
lean_closure_set(v___f_975_, 2, v___y_880_);
lean_closure_set(v___f_975_, 3, v_attrs_x3f_883_);
lean_closure_set(v___f_975_, 4, v_attrKind_885_);
lean_closure_set(v___f_975_, 5, v_tk_891_);
lean_closure_set(v___f_975_, 6, v_alts_966_);
v___x_976_ = l_Lean_Syntax_getArg(v_attrKind_885_, v___x_794_);
lean_dec(v_attrKind_885_);
lean_inc(v___x_976_);
v___x_977_ = l_Lean_Syntax_matchesNull(v___x_976_, v___y_882_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; 
lean_dec(v___x_976_);
v___x_978_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_975_, v___x_945_, v___y_881_, v___y_879_);
return v___x_978_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_979_ = l_Lean_Syntax_getArg(v___x_976_, v___x_794_);
lean_dec(v___x_976_);
v___x_980_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11));
v___x_981_ = l_Lean_Syntax_isOfKind(v___x_979_, v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_975_, v___x_945_, v___y_881_, v___y_879_);
return v___x_982_;
}
else
{
lean_object* v___x_983_; 
v___x_983_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_975_, v___x_965_, v___y_881_, v___y_879_);
return v___x_983_;
}
}
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_984_ = l_Lean_Syntax_getArg(v___x_964_, v___x_794_);
lean_dec(v___x_964_);
v___x_985_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14));
lean_inc(v___x_984_);
v___x_986_ = l_Lean_Syntax_isOfKind(v___x_984_, v___x_985_);
if (v___x_986_ == 0)
{
lean_object* v_alts_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___f_996_; lean_object* v___x_997_; uint8_t v___x_998_; 
lean_dec(v___x_984_);
lean_dec(v___x_923_);
v_alts_987_ = l_Lean_Syntax_getArgs(v___x_903_);
lean_dec(v___x_903_);
v___x_988_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__40));
v___x_989_ = lean_box(2);
lean_inc_ref(v_alts_987_);
v___x_990_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v___x_988_);
lean_ctor_set(v___x_990_, 2, v_alts_987_);
v___x_991_ = lean_mk_empty_array_with_capacity(v___x_884_);
lean_inc(v_tk_891_);
v___x_992_ = lean_array_push(v___x_991_, v_tk_891_);
v___x_993_ = lean_array_push(v___x_992_, v___x_990_);
v___x_994_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_994_, 0, v___x_989_);
lean_ctor_set(v___x_994_, 1, v___x_988_);
lean_ctor_set(v___x_994_, 2, v___x_993_);
v___x_995_ = l_Lean_TSyntax_getId(v_kind_902_);
lean_dec(v_kind_902_);
lean_inc(v_attrKind_885_);
v___f_996_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_996_, 0, v___x_994_);
lean_closure_set(v___f_996_, 1, v___x_995_);
lean_closure_set(v___f_996_, 2, v___y_880_);
lean_closure_set(v___f_996_, 3, v_attrs_x3f_883_);
lean_closure_set(v___f_996_, 4, v_attrKind_885_);
lean_closure_set(v___f_996_, 5, v_tk_891_);
lean_closure_set(v___f_996_, 6, v_alts_987_);
v___x_997_ = l_Lean_Syntax_getArg(v_attrKind_885_, v___x_794_);
lean_dec(v_attrKind_885_);
lean_inc(v___x_997_);
v___x_998_ = l_Lean_Syntax_matchesNull(v___x_997_, v___y_882_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; 
lean_dec(v___x_997_);
v___x_999_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_996_, v___x_965_, v___y_881_, v___y_879_);
return v___x_999_;
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1000_ = l_Lean_Syntax_getArg(v___x_997_, v___x_794_);
lean_dec(v___x_997_);
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11));
v___x_1002_ = l_Lean_Syntax_isOfKind(v___x_1000_, v___x_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_996_, v___x_965_, v___y_881_, v___y_879_);
return v___x_1003_;
}
else
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_996_, v___x_894_, v___y_881_, v___y_879_);
return v___x_1004_;
}
}
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec(v___x_903_);
v___x_1005_ = l_Lean_Syntax_getArg(v___x_923_, v___x_890_);
lean_dec(v___x_923_);
v___x_1006_ = lean_mk_empty_array_with_capacity(v___x_884_);
lean_inc(v_tk_891_);
v___x_1007_ = lean_array_push(v___x_1006_, v_tk_891_);
lean_inc(v___x_1005_);
v___x_1008_ = lean_array_push(v___x_1007_, v___x_1005_);
v___x_1009_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__40));
v___x_1010_ = lean_box(2);
v___x_1011_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_1009_);
lean_ctor_set(v___x_1011_, 2, v___x_1008_);
v___x_1012_ = l_Lean_Elab_Command_getRef___redArg(v___y_881_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v_fileName_1014_; lean_object* v_fileMap_1015_; lean_object* v_currRecDepth_1016_; lean_object* v_cmdPos_1017_; lean_object* v_macroStack_1018_; lean_object* v_quotContext_x3f_1019_; lean_object* v_currMacroScope_1020_; lean_object* v_snap_x3f_1021_; lean_object* v_cancelTk_x3f_1022_; uint8_t v_suppressElabErrors_1023_; lean_object* v_ref_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
v_fileName_1014_ = lean_ctor_get(v___y_881_, 0);
v_fileMap_1015_ = lean_ctor_get(v___y_881_, 1);
v_currRecDepth_1016_ = lean_ctor_get(v___y_881_, 2);
v_cmdPos_1017_ = lean_ctor_get(v___y_881_, 3);
v_macroStack_1018_ = lean_ctor_get(v___y_881_, 4);
v_quotContext_x3f_1019_ = lean_ctor_get(v___y_881_, 5);
v_currMacroScope_1020_ = lean_ctor_get(v___y_881_, 6);
v_snap_x3f_1021_ = lean_ctor_get(v___y_881_, 8);
v_cancelTk_x3f_1022_ = lean_ctor_get(v___y_881_, 9);
v_suppressElabErrors_1023_ = lean_ctor_get_uint8(v___y_881_, sizeof(void*)*10);
v_ref_1024_ = l_Lean_replaceRef(v___x_1011_, v_a_1013_);
lean_dec(v_a_1013_);
lean_dec_ref_known(v___x_1011_, 3);
lean_inc(v_cancelTk_x3f_1022_);
lean_inc(v_snap_x3f_1021_);
lean_inc(v_currMacroScope_1020_);
lean_inc(v_quotContext_x3f_1019_);
lean_inc(v_macroStack_1018_);
lean_inc(v_cmdPos_1017_);
lean_inc(v_currRecDepth_1016_);
lean_inc_ref(v_fileMap_1015_);
lean_inc_ref(v_fileName_1014_);
v___x_1025_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1025_, 0, v_fileName_1014_);
lean_ctor_set(v___x_1025_, 1, v_fileMap_1015_);
lean_ctor_set(v___x_1025_, 2, v_currRecDepth_1016_);
lean_ctor_set(v___x_1025_, 3, v_cmdPos_1017_);
lean_ctor_set(v___x_1025_, 4, v_macroStack_1018_);
lean_ctor_set(v___x_1025_, 5, v_quotContext_x3f_1019_);
lean_ctor_set(v___x_1025_, 6, v_currMacroScope_1020_);
lean_ctor_set(v___x_1025_, 7, v_ref_1024_);
lean_ctor_set(v___x_1025_, 8, v_snap_x3f_1021_);
lean_ctor_set(v___x_1025_, 9, v_cancelTk_x3f_1022_);
lean_ctor_set_uint8(v___x_1025_, sizeof(void*)*10, v_suppressElabErrors_1023_);
v___x_1026_ = l_Lean_Elab_Command_getRef___redArg(v___x_1025_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1028_ = l_Lean_SourceInfo_fromRef(v_a_1027_, v___x_894_);
lean_dec(v_a_1027_);
v___x_1029_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_1025_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_dec_ref_known(v___x_1029_, 1);
if (lean_obj_tag(v_quotContext_x3f_1019_) == 0)
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v___y_879_);
lean_dec_ref(v___x_1030_);
v___y_847_ = v___x_894_;
v___y_848_ = v_kind_902_;
v___y_849_ = v_tk_891_;
v___y_850_ = v___y_880_;
v___y_851_ = v___x_1005_;
v___y_852_ = v___y_882_;
v___y_853_ = v_attrKind_885_;
v___y_854_ = v___y_879_;
v___y_855_ = v___x_984_;
v___y_856_ = v_attrs_x3f_883_;
v___y_857_ = v___x_1028_;
v___y_858_ = v___x_1025_;
v___y_859_ = v_quotContext_x3f_1019_;
v___y_860_ = v___x_886_;
v___y_861_ = v___x_1009_;
goto v___jp_846_;
}
else
{
v___y_847_ = v___x_894_;
v___y_848_ = v_kind_902_;
v___y_849_ = v_tk_891_;
v___y_850_ = v___y_880_;
v___y_851_ = v___x_1005_;
v___y_852_ = v___y_882_;
v___y_853_ = v_attrKind_885_;
v___y_854_ = v___y_879_;
v___y_855_ = v___x_984_;
v___y_856_ = v_attrs_x3f_883_;
v___y_857_ = v___x_1028_;
v___y_858_ = v___x_1025_;
v___y_859_ = v_quotContext_x3f_1019_;
v___y_860_ = v___x_886_;
v___y_861_ = v___x_1009_;
goto v___jp_846_;
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec(v___x_1028_);
lean_dec_ref_known(v___x_1025_, 10);
lean_dec(v___x_1005_);
lean_dec(v___x_984_);
lean_dec(v_kind_902_);
lean_dec(v_tk_891_);
lean_dec(v_attrKind_885_);
lean_dec(v_attrs_x3f_883_);
lean_dec(v___y_880_);
v_a_1031_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1029_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1029_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1025_, 10);
lean_dec(v___x_1005_);
lean_dec(v___x_984_);
lean_dec(v_kind_902_);
lean_dec(v_tk_891_);
lean_dec(v_attrKind_885_);
lean_dec(v_attrs_x3f_883_);
lean_dec(v___y_880_);
return v___x_1026_;
}
}
else
{
lean_dec_ref_known(v___x_1011_, 3);
lean_dec(v___x_1005_);
lean_dec(v___x_984_);
lean_dec(v_kind_902_);
lean_dec(v_tk_891_);
lean_dec(v_attrKind_885_);
lean_dec(v_attrs_x3f_883_);
lean_dec(v___y_880_);
return v___x_1012_;
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
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
lean_dec(v___x_893_);
v___x_1039_ = lean_unsigned_to_nat(5u);
v___x_1040_ = l_Lean_Syntax_getArg(v_stx_719_, v___x_1039_);
lean_dec(v_stx_719_);
v___x_1041_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9));
lean_inc(v___x_1040_);
v___x_1042_ = l_Lean_Syntax_isOfKind(v___x_1040_, v___x_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; 
lean_dec(v___x_1040_);
lean_dec(v_tk_891_);
lean_dec(v_attrKind_885_);
lean_dec(v_attrs_x3f_883_);
lean_dec(v___y_880_);
v___x_1043_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_1043_;
}
else
{
lean_object* v___f_1044_; lean_object* v___x_1045_; lean_object* v_alts_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___f_1044_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__5___boxed), 15, 10);
lean_closure_set(v___f_1044_, 0, v___x_1041_);
lean_closure_set(v___f_1044_, 1, v___x_726_);
lean_closure_set(v___f_1044_, 2, v_attrKind_885_);
lean_closure_set(v___f_1044_, 3, v___x_725_);
lean_closure_set(v___f_1044_, 4, v___x_794_);
lean_closure_set(v___f_1044_, 5, v_attrs_x3f_883_);
lean_closure_set(v___f_1044_, 6, v___x_723_);
lean_closure_set(v___f_1044_, 7, v___x_724_);
lean_closure_set(v___f_1044_, 8, v___x_886_);
lean_closure_set(v___f_1044_, 9, v___y_880_);
v___x_1045_ = l_Lean_Syntax_getArg(v___x_1040_, v___x_794_);
lean_dec(v___x_1040_);
v_alts_1046_ = l_Lean_Syntax_getArgs(v___x_1045_);
lean_dec(v___x_1045_);
v___x_1047_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__40));
v___x_1048_ = lean_box(2);
lean_inc_ref(v_alts_1046_);
v___x_1049_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v___x_1047_);
lean_ctor_set(v___x_1049_, 2, v_alts_1046_);
v___x_1050_ = lean_mk_empty_array_with_capacity(v___x_884_);
v___x_1051_ = lean_array_push(v___x_1050_, v_tk_891_);
v___x_1052_ = lean_array_push(v___x_1051_, v___x_1049_);
v___x_1053_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1048_);
lean_ctor_set(v___x_1053_, 1, v___x_1047_);
lean_ctor_set(v___x_1053_, 2, v___x_1052_);
v___x_1054_ = l_Lean_Elab_Command_getRef___redArg(v___y_881_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v_fileName_1056_; lean_object* v_fileMap_1057_; lean_object* v_currRecDepth_1058_; lean_object* v_cmdPos_1059_; lean_object* v_macroStack_1060_; lean_object* v_quotContext_x3f_1061_; lean_object* v_currMacroScope_1062_; lean_object* v_snap_x3f_1063_; lean_object* v_cancelTk_x3f_1064_; uint8_t v_suppressElabErrors_1065_; lean_object* v_ref_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1054_, 1);
v_fileName_1056_ = lean_ctor_get(v___y_881_, 0);
v_fileMap_1057_ = lean_ctor_get(v___y_881_, 1);
v_currRecDepth_1058_ = lean_ctor_get(v___y_881_, 2);
v_cmdPos_1059_ = lean_ctor_get(v___y_881_, 3);
v_macroStack_1060_ = lean_ctor_get(v___y_881_, 4);
v_quotContext_x3f_1061_ = lean_ctor_get(v___y_881_, 5);
v_currMacroScope_1062_ = lean_ctor_get(v___y_881_, 6);
v_snap_x3f_1063_ = lean_ctor_get(v___y_881_, 8);
v_cancelTk_x3f_1064_ = lean_ctor_get(v___y_881_, 9);
v_suppressElabErrors_1065_ = lean_ctor_get_uint8(v___y_881_, sizeof(void*)*10);
v_ref_1066_ = l_Lean_replaceRef(v___x_1053_, v_a_1055_);
lean_dec(v_a_1055_);
lean_dec_ref_known(v___x_1053_, 3);
lean_inc(v_cancelTk_x3f_1064_);
lean_inc(v_snap_x3f_1063_);
lean_inc(v_currMacroScope_1062_);
lean_inc(v_quotContext_x3f_1061_);
lean_inc(v_macroStack_1060_);
lean_inc(v_cmdPos_1059_);
lean_inc(v_currRecDepth_1058_);
lean_inc_ref(v_fileMap_1057_);
lean_inc_ref(v_fileName_1056_);
v___x_1067_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1067_, 0, v_fileName_1056_);
lean_ctor_set(v___x_1067_, 1, v_fileMap_1057_);
lean_ctor_set(v___x_1067_, 2, v_currRecDepth_1058_);
lean_ctor_set(v___x_1067_, 3, v_cmdPos_1059_);
lean_ctor_set(v___x_1067_, 4, v_macroStack_1060_);
lean_ctor_set(v___x_1067_, 5, v_quotContext_x3f_1061_);
lean_ctor_set(v___x_1067_, 6, v_currMacroScope_1062_);
lean_ctor_set(v___x_1067_, 7, v_ref_1066_);
lean_ctor_set(v___x_1067_, 8, v_snap_x3f_1063_);
lean_ctor_set(v___x_1067_, 9, v_cancelTk_x3f_1064_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*10, v_suppressElabErrors_1065_);
v___x_1068_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(v_alts_1046_, v___x_725_, v___f_1044_, v___x_1067_, v___y_879_);
lean_dec_ref_known(v___x_1067_, 10);
lean_dec_ref(v_alts_1046_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1068_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
v_a_1077_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1068_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1068_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1053_, 3);
lean_dec_ref(v_alts_1046_);
lean_dec_ref(v___f_1044_);
return v___x_1054_;
}
}
}
}
}
v___jp_1085_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1089_ = lean_unsigned_to_nat(1u);
v___x_1090_ = l_Lean_Syntax_getArg(v_stx_719_, v___x_1089_);
v___x_1091_ = l_Lean_Syntax_isNone(v___x_1090_);
if (v___x_1091_ == 0)
{
uint8_t v___x_1092_; 
lean_inc(v___x_1090_);
v___x_1092_ = l_Lean_Syntax_matchesNull(v___x_1090_, v___x_1089_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; 
lean_dec(v___x_1090_);
lean_dec(v_doc_x3f_1086_);
lean_dec(v_stx_719_);
v___x_1093_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_1093_;
}
else
{
lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1094_ = l_Lean_Syntax_getArg(v___x_1090_, v___x_794_);
lean_dec(v___x_1090_);
v___x_1095_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15));
lean_inc(v___x_1094_);
v___x_1096_ = l_Lean_Syntax_isOfKind(v___x_1094_, v___x_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; 
lean_dec(v___x_1094_);
lean_dec(v_doc_x3f_1086_);
lean_dec(v_stx_719_);
v___x_1097_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; lean_object* v_attrs_x3f_1099_; lean_object* v___x_1100_; 
v___x_1098_ = l_Lean_Syntax_getArg(v___x_1094_, v___x_1089_);
lean_dec(v___x_1094_);
v_attrs_x3f_1099_ = l_Lean_Syntax_getArgs(v___x_1098_);
lean_dec(v___x_1098_);
v___x_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1100_, 0, v_attrs_x3f_1099_);
v___y_879_ = v___y_1088_;
v___y_880_ = v_doc_x3f_1086_;
v___y_881_ = v___y_1087_;
v___y_882_ = v___x_1089_;
v_attrs_x3f_883_ = v___x_1100_;
goto v___jp_878_;
}
}
}
else
{
lean_object* v___x_1101_; 
lean_dec(v___x_1090_);
v___x_1101_ = lean_box(0);
v___y_879_ = v___y_1088_;
v___y_880_ = v_doc_x3f_1086_;
v___y_881_ = v___y_1087_;
v___y_882_ = v___x_1089_;
v_attrs_x3f_883_ = v___x_1101_;
goto v___jp_878_;
}
}
}
v___jp_728_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
lean_inc_ref_n(v___y_732_, 3);
v___x_744_ = l_Array_append___redArg(v___y_732_, v___y_743_);
lean_dec_ref(v___y_743_);
lean_inc_n(v___y_740_, 6);
lean_inc_n(v___y_734_, 17);
v___x_745_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_745_, 0, v___y_734_);
lean_ctor_set(v___x_745_, 1, v___y_740_);
lean_ctor_set(v___x_745_, 2, v___x_744_);
v___x_746_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
lean_inc_ref_n(v___y_741_, 2);
v___x_747_ = l_Lean_Name_mkStr4(v___x_723_, v___x_724_, v___y_741_, v___x_746_);
v___x_748_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__3));
v___x_749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_749_, 0, v___y_734_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = l_Array_append___redArg(v___y_732_, v___y_739_);
lean_dec_ref(v___y_739_);
v___x_751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_751_, 0, v___y_734_);
lean_ctor_set(v___x_751_, 1, v___y_740_);
lean_ctor_set(v___x_751_, 2, v___x_750_);
v___x_752_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__4));
v___x_753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_753_, 0, v___y_734_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = l_Lean_Syntax_node3(v___y_734_, v___x_747_, v___x_749_, v___x_751_, v___x_753_);
v___x_755_ = l_Lean_Syntax_node1(v___y_734_, v___y_740_, v___x_754_);
lean_inc_ref(v___y_738_);
v___x_756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_756_, 0, v___y_734_);
lean_ctor_set(v___x_756_, 1, v___y_738_);
v___x_757_ = l_Lean_TSyntax_getId(v___y_730_);
v___x_758_ = l_Lean_mkIdentFrom(v___y_731_, v___x_757_, v___x_727_);
lean_dec(v___y_731_);
v___x_759_ = l_Lean_Syntax_node2(v___y_734_, v___y_740_, v___x_758_, v___y_730_);
v___x_760_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__8));
v___x_761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_761_, 0, v___y_734_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__10, &l_Lean_Elab_Command_elabMacroRulesAux___closed__10_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__10);
v___x_763_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__11));
v___x_764_ = l_Lean_addMacroScope(v___y_742_, v___x_763_, v___y_729_);
v___x_765_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__5));
v___x_766_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_766_, 0, v___y_734_);
lean_ctor_set(v___x_766_, 1, v___x_762_);
lean_ctor_set(v___x_766_, 2, v___x_764_);
lean_ctor_set(v___x_766_, 3, v___x_765_);
v___x_767_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__12));
v___x_768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_768_, 0, v___y_734_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__13));
v___x_770_ = l_Lean_Name_mkStr4(v___x_723_, v___x_724_, v___y_741_, v___x_769_);
v___x_771_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_771_, 0, v___y_734_);
lean_ctor_set(v___x_771_, 1, v___x_769_);
v___x_772_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6));
v___x_773_ = l_Lean_Name_mkStr4(v___x_723_, v___x_724_, v___y_741_, v___x_772_);
v___x_774_ = l_Lean_Syntax_node1(v___y_734_, v___y_740_, v___y_736_);
v___x_775_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_775_, 0, v___y_734_);
lean_ctor_set(v___x_775_, 1, v___y_740_);
lean_ctor_set(v___x_775_, 2, v___y_732_);
v___x_776_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__19));
v___x_777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_777_, 0, v___y_734_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = l_Lean_Syntax_node4(v___y_734_, v___x_773_, v___x_774_, v___x_775_, v___x_777_, v___y_735_);
v___x_779_ = l_Lean_Syntax_node2(v___y_734_, v___x_770_, v___x_771_, v___x_778_);
v___x_780_ = lean_unsigned_to_nat(9u);
v___x_781_ = lean_mk_empty_array_with_capacity(v___x_780_);
v___x_782_ = lean_array_push(v___x_781_, v___x_745_);
v___x_783_ = lean_array_push(v___x_782_, v___x_755_);
v___x_784_ = lean_array_push(v___x_783_, v___y_733_);
v___x_785_ = lean_array_push(v___x_784_, v___x_756_);
v___x_786_ = lean_array_push(v___x_785_, v___x_759_);
v___x_787_ = lean_array_push(v___x_786_, v___x_761_);
v___x_788_ = lean_array_push(v___x_787_, v___x_766_);
v___x_789_ = lean_array_push(v___x_788_, v___x_768_);
v___x_790_ = lean_array_push(v___x_789_, v___x_779_);
lean_inc(v___y_737_);
v___x_791_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_791_, 0, v___y_734_);
lean_ctor_set(v___x_791_, 1, v___y_737_);
lean_ctor_set(v___x_791_, 2, v___x_790_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___boxed(lean_object* v_stx_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_Elab_Command_elabMacroRules___lam__1(v_stx_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules(lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v___f_1123_; lean_object* v___x_1124_; 
v___f_1123_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___closed__0));
v___x_1124_ = l_Lean_Elab_Command_adaptExpander(v___f_1123_, v_a_1119_, v_a_1120_, v_a_1121_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___boxed(lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_Elab_Command_elabMacroRules(v_a_1125_, v_a_1126_, v_a_1127_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1(){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1137_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1138_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0));
v___x_1139_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1));
v___x_1140_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___boxed), 4, 0);
v___x_1141_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1137_, v___x_1138_, v___x_1139_, v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___boxed(lean_object* v_a_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1();
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3(){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1));
v___x_1171_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6));
v___x_1172_ = l_Lean_addBuiltinDeclarationRanges(v___x_1170_, v___x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___boxed(lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3();
return v_res_1174_;
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
