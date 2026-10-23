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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Command_checkRuleAltKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkMacroRulesFun_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkMacroRulesFun_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkMacroRulesFun_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkMacroRulesFun_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_mkMacroRulesFun_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_mkMacroRulesFun_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__0 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__1 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__2 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__3 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__3_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__4 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__5 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__5_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__6 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__7 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__8 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Command_mkMacroRulesFun___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__9;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__10 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__10_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__11 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__11_value;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__12 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__13 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__13_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__14 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__14_value;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__15 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__15_value;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__16 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__16_value;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noErrorIfUnused"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__17 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__18_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__18_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__18_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__17_value),LEAN_SCALAR_PTR_LITERAL(161, 26, 252, 46, 47, 233, 154, 57)}};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__18 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__18_value;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "no_error_if_unused%"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__19 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__19_value;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__20 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__21_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__21_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__20_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__21 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__21_value;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "throw"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__22 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__22_value;
static lean_once_cell_t l_Lean_Elab_Command_mkMacroRulesFun___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__23;
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__22_value),LEAN_SCALAR_PTR_LITERAL(60, 81, 80, 209, 187, 239, 255, 113)}};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__24 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__24_value;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MonadExcept"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__25 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__25_value;
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__25_value),LEAN_SCALAR_PTR_LITERAL(162, 154, 253, 120, 110, 153, 103, 113)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__26_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__22_value),LEAN_SCALAR_PTR_LITERAL(121, 11, 61, 69, 62, 207, 229, 53)}};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__26 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__27 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__27_value;
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__28 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__28_value;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Macro.Exception.unsupportedSyntax"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__29 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__29_value;
static lean_once_cell_t l_Lean_Elab_Command_mkMacroRulesFun___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__30;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Macro"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__31 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__31_value;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Exception"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__32 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__32_value;
static const lean_string_object l_Lean_Elab_Command_mkMacroRulesFun___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "unsupportedSyntax"};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__33 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__33_value;
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__34_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__31_value),LEAN_SCALAR_PTR_LITERAL(168, 205, 218, 0, 241, 122, 66, 251)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__34_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__32_value),LEAN_SCALAR_PTR_LITERAL(215, 141, 7, 16, 63, 180, 3, 59)}};
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__34_value_aux_2),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__33_value),LEAN_SCALAR_PTR_LITERAL(110, 23, 159, 194, 88, 95, 49, 128)}};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__34 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__35 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__35_value;
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__34_value)}};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__36 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__36_value;
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__37 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__37_value;
static const lean_ctor_object l_Lean_Elab_Command_mkMacroRulesFun___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__35_value),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__37_value)}};
static const lean_object* l_Lean_Elab_Command_mkMacroRulesFun___closed__38 = (const lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__38_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkMacroRulesFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkMacroRulesFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "macro_rules"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__3_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "macroRules"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__4 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Command_elabMacroRulesAux___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__5;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__4_value),LEAN_SCALAR_PTR_LITERAL(6, 217, 176, 227, 245, 86, 100, 50)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__7 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__8;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__31_value),LEAN_SCALAR_PTR_LITERAL(153, 13, 84, 30, 172, 208, 133, 203)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__9_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__11_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "aux_def"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__11_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__12_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__13_value),LEAN_SCALAR_PTR_LITERAL(83, 33, 36, 212, 17, 187, 86, 94)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__14_value;
static const lean_array_object l_Lean_Elab_Command_elabMacroRulesAux___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__15 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__15_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__16 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__16_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__17 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__17_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__18 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__18_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "macro"};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__19 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__20_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__20_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__18_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRulesAux___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__20_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__19_value),LEAN_SCALAR_PTR_LITERAL(17, 202, 70, 6, 8, 133, 137, 74)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__20 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__20_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRulesAux___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__21 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__21_value;
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
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 80, 75, 5, 165, 87, 197, 1)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__31_value),LEAN_SCALAR_PTR_LITERAL(168, 205, 218, 0, 241, 122, 66, 251)}};
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
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(136, 104, 45, 91, 146, 14, 86, 4)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__1_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Command_elabMacroRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_elabMacroRules___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Command_elabMacroRules___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabMacroRules___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabMacroRules"};
static const lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_mkMacroRulesFun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__11_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabMacroRulesAux___closed__12_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
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
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkMacroRulesFun_spec__1___redArg(lean_object* v___y_1_){
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
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkMacroRulesFun_spec__1___redArg___boxed(lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkMacroRulesFun_spec__1___redArg(v___y_8_);
lean_dec(v___y_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkMacroRulesFun_spec__1(lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkMacroRulesFun_spec__1___redArg(v___y_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_Command_mkMacroRulesFun_spec__1___boxed(lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkMacroRulesFun_spec__1(v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_mkMacroRulesFun_spec__0(lean_object* v_cmdName_19_, lean_object* v_k_20_, size_t v_sz_21_, size_t v_i_22_, lean_object* v_bs_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
uint8_t v___x_27_; 
v___x_27_ = lean_usize_dec_lt(v_i_22_, v_sz_21_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; 
lean_dec(v_k_20_);
lean_dec_ref(v_cmdName_19_);
v___x_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_28_, 0, v_bs_23_);
return v___x_28_;
}
else
{
lean_object* v_v_29_; lean_object* v___x_30_; lean_object* v_bs_x27_31_; lean_object* v___x_32_; 
v_v_29_ = lean_array_uget(v_bs_23_, v_i_22_);
v___x_30_ = lean_unsigned_to_nat(0u);
v_bs_x27_31_ = lean_array_uset(v_bs_23_, v_i_22_, v___x_30_);
lean_inc(v_k_20_);
lean_inc_ref(v_cmdName_19_);
v___x_32_ = l_Lean_Elab_Command_checkRuleAltKind(v_cmdName_19_, v_k_20_, v_v_29_, v___y_24_, v___y_25_);
if (lean_obj_tag(v___x_32_) == 0)
{
lean_object* v_a_33_; size_t v___x_34_; size_t v___x_35_; lean_object* v___x_36_; 
v_a_33_ = lean_ctor_get(v___x_32_, 0);
lean_inc(v_a_33_);
lean_dec_ref_known(v___x_32_, 1);
v___x_34_ = ((size_t)1ULL);
v___x_35_ = lean_usize_add(v_i_22_, v___x_34_);
v___x_36_ = lean_array_uset(v_bs_x27_31_, v_i_22_, v_a_33_);
v_i_22_ = v___x_35_;
v_bs_23_ = v___x_36_;
goto _start;
}
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
lean_dec_ref(v_bs_x27_31_);
lean_dec(v_k_20_);
lean_dec_ref(v_cmdName_19_);
v_a_38_ = lean_ctor_get(v___x_32_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_32_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_32_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_mkMacroRulesFun_spec__0___boxed(lean_object* v_cmdName_46_, lean_object* v_k_47_, lean_object* v_sz_48_, lean_object* v_i_49_, lean_object* v_bs_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
size_t v_sz_boxed_54_; size_t v_i_boxed_55_; lean_object* v_res_56_; 
v_sz_boxed_54_ = lean_unbox_usize(v_sz_48_);
lean_dec(v_sz_48_);
v_i_boxed_55_ = lean_unbox_usize(v_i_49_);
lean_dec(v_i_49_);
v_res_56_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_mkMacroRulesFun_spec__0(v_cmdName_46_, v_k_47_, v_sz_boxed_54_, v_i_boxed_55_, v_bs_50_, v___y_51_, v___y_52_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
return v_res_56_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkMacroRulesFun___closed__9(void){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Array_mkArray0___redArg();
return v___x_75_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkMacroRulesFun___closed__23(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__22));
v___x_106_ = l_String_toRawSubstring_x27(v___x_105_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkMacroRulesFun___closed__30(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__29));
v___x_121_ = l_String_toRawSubstring_x27(v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkMacroRulesFun(lean_object* v_cmdName_141_, lean_object* v_k_142_, lean_object* v_alts_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
size_t v_sz_147_; size_t v___x_148_; lean_object* v___x_149_; 
v_sz_147_ = lean_array_size(v_alts_143_);
v___x_148_ = ((size_t)0ULL);
v___x_149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_mkMacroRulesFun_spec__0(v_cmdName_141_, v_k_142_, v_sz_147_, v___x_148_, v_alts_143_, v_a_144_, v_a_145_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_object* v_a_150_; lean_object* v___x_151_; 
v_a_150_ = lean_ctor_get(v___x_149_, 0);
lean_inc(v_a_150_);
lean_dec_ref_known(v___x_149_, 1);
v___x_151_ = l_Lean_Elab_Command_getRef___redArg(v_a_144_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; uint8_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v___x_151_, 1);
v___x_153_ = 0;
v___x_154_ = l_Lean_SourceInfo_fromRef(v_a_152_, v___x_153_);
lean_dec(v_a_152_);
v___x_155_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_144_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_209_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_209_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_209_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_209_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v_a_161_; lean_object* v_quotContext_x3f_205_; 
v_quotContext_x3f_205_ = lean_ctor_get(v_a_144_, 5);
if (lean_obj_tag(v_quotContext_x3f_205_) == 0)
{
lean_object* v___x_206_; lean_object* v_a_207_; 
v___x_206_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkMacroRulesFun_spec__1___redArg(v_a_145_);
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref(v___x_206_);
v_a_161_ = v_a_207_;
goto v___jp_160_;
}
else
{
lean_object* v_val_208_; 
v_val_208_ = lean_ctor_get(v_quotContext_x3f_205_, 0);
lean_inc(v_val_208_);
v_a_161_ = v_val_208_;
goto v___jp_160_;
}
v___jp_160_:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_162_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__3));
v___x_163_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__4));
lean_inc_n(v___x_154_, 16);
v___x_164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_154_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
v___x_165_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__6));
v___x_166_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__8));
v___x_167_ = lean_obj_once(&l_Lean_Elab_Command_mkMacroRulesFun___closed__9, &l_Lean_Elab_Command_mkMacroRulesFun___closed__9_once, _init_l_Lean_Elab_Command_mkMacroRulesFun___closed__9);
v___x_168_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__11));
v___x_169_ = l_Array_append___redArg(v___x_167_, v_a_150_);
lean_dec(v_a_150_);
v___x_170_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__12));
v___x_171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_154_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__14));
v___x_173_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__15));
v___x_174_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_154_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = l_Lean_Syntax_node1(v___x_154_, v___x_172_, v___x_174_);
v___x_176_ = l_Lean_Syntax_node1(v___x_154_, v___x_166_, v___x_175_);
v___x_177_ = l_Lean_Syntax_node1(v___x_154_, v___x_166_, v___x_176_);
v___x_178_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__16));
v___x_179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_154_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__18));
v___x_181_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__19));
v___x_182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_154_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__21));
v___x_184_ = lean_obj_once(&l_Lean_Elab_Command_mkMacroRulesFun___closed__23, &l_Lean_Elab_Command_mkMacroRulesFun___closed__23_once, _init_l_Lean_Elab_Command_mkMacroRulesFun___closed__23);
v___x_185_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__24));
lean_inc(v_a_156_);
lean_inc(v_a_161_);
v___x_186_ = l_Lean_addMacroScope(v_a_161_, v___x_185_, v_a_156_);
v___x_187_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__28));
v___x_188_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_188_, 0, v___x_154_);
lean_ctor_set(v___x_188_, 1, v___x_184_);
lean_ctor_set(v___x_188_, 2, v___x_186_);
lean_ctor_set(v___x_188_, 3, v___x_187_);
v___x_189_ = lean_obj_once(&l_Lean_Elab_Command_mkMacroRulesFun___closed__30, &l_Lean_Elab_Command_mkMacroRulesFun___closed__30_once, _init_l_Lean_Elab_Command_mkMacroRulesFun___closed__30);
v___x_190_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__34));
v___x_191_ = l_Lean_addMacroScope(v_a_161_, v___x_190_, v_a_156_);
v___x_192_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__38));
v___x_193_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_193_, 0, v___x_154_);
lean_ctor_set(v___x_193_, 1, v___x_189_);
lean_ctor_set(v___x_193_, 2, v___x_191_);
lean_ctor_set(v___x_193_, 3, v___x_192_);
v___x_194_ = l_Lean_Syntax_node1(v___x_154_, v___x_166_, v___x_193_);
v___x_195_ = l_Lean_Syntax_node2(v___x_154_, v___x_183_, v___x_188_, v___x_194_);
v___x_196_ = l_Lean_Syntax_node2(v___x_154_, v___x_180_, v___x_182_, v___x_195_);
v___x_197_ = l_Lean_Syntax_node4(v___x_154_, v___x_168_, v___x_171_, v___x_177_, v___x_179_, v___x_196_);
v___x_198_ = lean_array_push(v___x_169_, v___x_197_);
v___x_199_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_199_, 0, v___x_154_);
lean_ctor_set(v___x_199_, 1, v___x_166_);
lean_ctor_set(v___x_199_, 2, v___x_198_);
v___x_200_ = l_Lean_Syntax_node1(v___x_154_, v___x_165_, v___x_199_);
v___x_201_ = l_Lean_Syntax_node2(v___x_154_, v___x_163_, v___x_164_, v___x_200_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_201_);
v___x_203_ = v___x_158_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
lean_dec(v___x_154_);
lean_dec(v_a_150_);
v_a_210_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_155_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_155_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
else
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
lean_dec(v_a_150_);
v_a_218_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_151_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_151_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
else
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
v_a_226_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_233_ == 0)
{
v___x_228_ = v___x_149_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_149_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkMacroRulesFun___boxed(lean_object* v_cmdName_234_, lean_object* v_k_235_, lean_object* v_alts_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Elab_Command_mkMacroRulesFun(v_cmdName_234_, v_k_235_, v_alts_236_, v_a_237_, v_a_238_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
return v_res_240_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__5(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__4));
v___x_247_ = l_String_toRawSubstring_x27(v___x_246_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__31));
v___x_252_ = l_String_toRawSubstring_x27(v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux(lean_object* v_doc_x3f_280_, lean_object* v_attrs_x3f_281_, lean_object* v_attrKind_282_, lean_object* v_tk_283_, lean_object* v_k_284_, lean_object* v_alts_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
lean_inc(v_k_284_);
v___x_290_ = l_Lean_Elab_Command_mkMacroRulesFun(v___x_289_, v_k_284_, v_alts_285_, v_a_286_, v_a_287_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_427_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_427_ == 0)
{
v___x_293_ = v___x_290_;
v_isShared_294_ = v_isSharedCheck_427_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_427_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v_a_364_; lean_object* v___x_373_; 
v___x_373_ = l_Lean_Elab_Command_getRef___redArg(v_a_286_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; uint8_t v___x_375_; lean_object* v___y_377_; lean_object* v___x_397_; lean_object* v___x_416_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_374_);
lean_dec_ref_known(v___x_373_, 1);
v___x_375_ = 0;
v___x_397_ = l_Lean_SourceInfo_fromRef(v_a_374_, v___x_375_);
lean_dec(v_a_374_);
v___x_416_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_286_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_quotContext_x3f_417_; 
lean_dec_ref_known(v___x_416_, 1);
v_quotContext_x3f_417_ = lean_ctor_get(v_a_286_, 5);
if (lean_obj_tag(v_quotContext_x3f_417_) == 0)
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkMacroRulesFun_spec__1___redArg(v_a_287_);
lean_dec_ref(v___x_418_);
goto v___jp_398_;
}
else
{
goto v___jp_398_;
}
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec(v___x_397_);
lean_del_object(v___x_293_);
lean_dec(v_a_291_);
lean_dec(v_k_284_);
lean_dec(v_attrKind_282_);
lean_dec(v_doc_x3f_280_);
v_a_419_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_416_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_416_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
v___jp_376_:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_282_);
v___x_379_ = l_Lean_Elab_Command_getRef___redArg(v_a_286_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v___x_379_, 1);
v___x_381_ = l_Lean_SourceInfo_fromRef(v_a_380_, v___x_375_);
lean_dec(v_a_380_);
v___x_382_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_286_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_quotContext_x3f_383_; 
v_quotContext_x3f_383_ = lean_ctor_get(v_a_286_, 5);
if (lean_obj_tag(v_quotContext_x3f_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_385_; lean_object* v_a_386_; 
v_a_384_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_384_);
lean_dec_ref_known(v___x_382_, 1);
v___x_385_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkMacroRulesFun_spec__1___redArg(v_a_287_);
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref(v___x_385_);
v___y_360_ = v___y_377_;
v___y_361_ = v___x_378_;
v___y_362_ = v___x_381_;
v___y_363_ = v_a_384_;
v_a_364_ = v_a_386_;
goto v___jp_359_;
}
else
{
lean_object* v_a_387_; lean_object* v_val_388_; 
v_a_387_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_387_);
lean_dec_ref_known(v___x_382_, 1);
v_val_388_ = lean_ctor_get(v_quotContext_x3f_383_, 0);
lean_inc(v_val_388_);
v___y_360_ = v___y_377_;
v___y_361_ = v___x_378_;
v___y_362_ = v___x_381_;
v___y_363_ = v_a_387_;
v_a_364_ = v_val_388_;
goto v___jp_359_;
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec(v___x_381_);
lean_dec(v___x_378_);
lean_dec_ref(v___y_377_);
lean_del_object(v___x_293_);
lean_dec(v_a_291_);
lean_dec(v_k_284_);
lean_dec(v_doc_x3f_280_);
v_a_389_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_382_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_382_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
else
{
lean_dec(v___x_378_);
lean_dec_ref(v___y_377_);
lean_del_object(v___x_293_);
lean_dec(v_a_291_);
lean_dec(v_k_284_);
lean_dec(v_doc_x3f_280_);
return v___x_379_;
}
}
v___jp_398_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_399_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__17));
v___x_400_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__19));
v___x_401_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__20));
lean_inc_n(v___x_397_, 2);
v___x_402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_397_);
lean_ctor_set(v___x_402_, 1, v___x_400_);
lean_inc(v_k_284_);
v___x_403_ = l_Lean_mkIdent(v_k_284_);
v___x_404_ = l_Lean_Syntax_node2(v___x_397_, v___x_401_, v___x_402_, v___x_403_);
lean_inc(v_attrKind_282_);
v___x_405_ = l_Lean_Syntax_node2(v___x_397_, v___x_399_, v_attrKind_282_, v___x_404_);
if (lean_obj_tag(v_attrs_x3f_281_) == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_406_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__21));
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = lean_mk_empty_array_with_capacity(v___x_407_);
v___x_409_ = lean_array_push(v___x_408_, v___x_405_);
v___x_410_ = l_Lean_Syntax_SepArray_ofElems(v___x_406_, v___x_409_);
lean_dec_ref(v___x_409_);
v___y_377_ = v___x_410_;
goto v___jp_376_;
}
else
{
lean_object* v_val_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_val_411_ = lean_ctor_get(v_attrs_x3f_281_, 0);
v___x_412_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__21));
v___x_413_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_411_);
v___x_414_ = lean_array_push(v___x_413_, v___x_405_);
v___x_415_ = l_Lean_Syntax_SepArray_ofElems(v___x_412_, v___x_414_);
lean_dec_ref(v___x_414_);
v___y_377_ = v___x_415_;
goto v___jp_376_;
}
}
}
else
{
lean_del_object(v___x_293_);
lean_dec(v_a_291_);
lean_dec(v_k_284_);
lean_dec(v_attrKind_282_);
lean_dec(v_doc_x3f_280_);
return v___x_373_;
}
v___jp_295_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_357_; 
lean_inc_ref_n(v___y_296_, 2);
v___x_307_ = l_Array_append___redArg(v___y_296_, v___y_306_);
lean_dec_ref(v___y_306_);
lean_inc_n(v___y_299_, 4);
lean_inc_n(v___y_304_, 12);
v___x_308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_308_, 0, v___y_304_);
lean_ctor_set(v___x_308_, 1, v___y_299_);
lean_ctor_set(v___x_308_, 2, v___x_307_);
v___x_309_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__1));
v___x_310_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__2));
v___x_311_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
lean_inc_ref_n(v___y_298_, 2);
v___x_312_ = l_Lean_Name_mkStr4(v___y_298_, v___x_309_, v___x_310_, v___x_311_);
v___x_313_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
v___x_314_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_314_, 0, v___y_304_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = l_Array_append___redArg(v___y_296_, v___y_297_);
lean_dec_ref(v___y_297_);
v___x_316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_316_, 0, v___y_304_);
lean_ctor_set(v___x_316_, 1, v___y_299_);
lean_ctor_set(v___x_316_, 2, v___x_315_);
v___x_317_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__3));
v___x_318_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_318_, 0, v___y_304_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = l_Lean_Syntax_node3(v___y_304_, v___x_312_, v___x_314_, v___x_316_, v___x_318_);
v___x_320_ = l_Lean_Syntax_node1(v___y_304_, v___y_299_, v___x_319_);
lean_inc_ref(v___y_301_);
v___x_321_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_321_, 0, v___y_304_);
lean_ctor_set(v___x_321_, 1, v___y_301_);
v___x_322_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__5, &l_Lean_Elab_Command_elabMacroRulesAux___closed__5_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__5);
v___x_323_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__6));
lean_inc(v___y_305_);
lean_inc(v___y_303_);
v___x_324_ = l_Lean_addMacroScope(v___y_303_, v___x_323_, v___y_305_);
v___x_325_ = lean_box(0);
v___x_326_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_326_, 0, v___y_304_);
lean_ctor_set(v___x_326_, 1, v___x_322_);
lean_ctor_set(v___x_326_, 2, v___x_324_);
lean_ctor_set(v___x_326_, 3, v___x_325_);
v___x_327_ = 1;
v___x_328_ = l_Lean_mkIdentFrom(v_tk_283_, v_k_284_, v___x_327_);
v___x_329_ = l_Lean_Syntax_node2(v___y_304_, v___y_299_, v___x_326_, v___x_328_);
v___x_330_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__7));
v___x_331_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_331_, 0, v___y_304_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__31));
v___x_333_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__8, &l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8);
v___x_334_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__9));
v___x_335_ = l_Lean_addMacroScope(v___y_303_, v___x_334_, v___y_305_);
v___x_336_ = l_Lean_Name_mkStr2(v___y_298_, v___x_332_);
lean_inc(v___x_336_);
v___x_337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_325_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_336_);
v___x_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_325_);
v___x_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_337_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_341_, 0, v___y_304_);
lean_ctor_set(v___x_341_, 1, v___x_333_);
lean_ctor_set(v___x_341_, 2, v___x_335_);
lean_ctor_set(v___x_341_, 3, v___x_340_);
v___x_342_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
v___x_343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_343_, 0, v___y_304_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = lean_unsigned_to_nat(9u);
v___x_345_ = lean_mk_empty_array_with_capacity(v___x_344_);
v___x_346_ = lean_array_push(v___x_345_, v___x_308_);
v___x_347_ = lean_array_push(v___x_346_, v___x_320_);
v___x_348_ = lean_array_push(v___x_347_, v___y_300_);
v___x_349_ = lean_array_push(v___x_348_, v___x_321_);
v___x_350_ = lean_array_push(v___x_349_, v___x_329_);
v___x_351_ = lean_array_push(v___x_350_, v___x_331_);
v___x_352_ = lean_array_push(v___x_351_, v___x_341_);
v___x_353_ = lean_array_push(v___x_352_, v___x_343_);
v___x_354_ = lean_array_push(v___x_353_, v_a_291_);
lean_inc(v___y_302_);
v___x_355_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_355_, 0, v___y_304_);
lean_ctor_set(v___x_355_, 1, v___y_302_);
lean_ctor_set(v___x_355_, 2, v___x_354_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_355_);
v___x_357_ = v___x_293_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
v___jp_359_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_365_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__0));
v___x_366_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__13));
v___x_367_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__14));
v___x_368_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__8));
v___x_369_ = lean_obj_once(&l_Lean_Elab_Command_mkMacroRulesFun___closed__9, &l_Lean_Elab_Command_mkMacroRulesFun___closed__9_once, _init_l_Lean_Elab_Command_mkMacroRulesFun___closed__9);
if (lean_obj_tag(v_doc_x3f_280_) == 1)
{
lean_object* v_val_370_; lean_object* v___x_371_; 
v_val_370_ = lean_ctor_get(v_doc_x3f_280_, 0);
lean_inc(v_val_370_);
lean_dec_ref_known(v_doc_x3f_280_, 1);
v___x_371_ = l_Array_mkArray1___redArg(v_val_370_);
v___y_296_ = v___x_369_;
v___y_297_ = v___y_360_;
v___y_298_ = v___x_365_;
v___y_299_ = v___x_368_;
v___y_300_ = v___y_361_;
v___y_301_ = v___x_366_;
v___y_302_ = v___x_367_;
v___y_303_ = v_a_364_;
v___y_304_ = v___y_362_;
v___y_305_ = v___y_363_;
v___y_306_ = v___x_371_;
goto v___jp_295_;
}
else
{
lean_object* v___x_372_; 
lean_dec(v_doc_x3f_280_);
v___x_372_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__15));
v___y_296_ = v___x_369_;
v___y_297_ = v___y_360_;
v___y_298_ = v___x_365_;
v___y_299_ = v___x_368_;
v___y_300_ = v___y_361_;
v___y_301_ = v___x_366_;
v___y_302_ = v___x_367_;
v___y_303_ = v_a_364_;
v___y_304_ = v___y_362_;
v___y_305_ = v___y_363_;
v___y_306_ = v___x_372_;
goto v___jp_295_;
}
}
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec(v_k_284_);
lean_dec(v_attrKind_282_);
lean_dec(v_doc_x3f_280_);
v_a_428_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_290_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_290_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux___boxed(lean_object* v_doc_x3f_436_, lean_object* v_attrs_x3f_437_, lean_object* v_attrKind_438_, lean_object* v_tk_439_, lean_object* v_k_440_, lean_object* v_alts_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Elab_Command_elabMacroRulesAux(v_doc_x3f_436_, v_attrs_x3f_437_, v_attrKind_438_, v_tk_439_, v_k_440_, v_alts_441_, v_a_442_, v_a_443_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_tk_439_);
lean_dec(v_attrs_x3f_437_);
return v_res_445_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_box(0);
v___x_447_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v___x_446_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___closed__0);
v___x_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___boxed(lean_object* v___y_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0(lean_object* v_00_u03b1_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___boxed(lean_object* v_00_u03b1_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0(v_00_u03b1_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg___lam__0(lean_object* v___y_464_, uint8_t v_isExporting_465_, lean_object* v_a_x3f_466_){
_start:
{
lean_object* v___x_468_; lean_object* v_env_469_; lean_object* v_messages_470_; lean_object* v_scopes_471_; lean_object* v_usedQuotCtxts_472_; lean_object* v_nextMacroScope_473_; lean_object* v_maxRecDepth_474_; lean_object* v_ngen_475_; lean_object* v_auxDeclNGen_476_; lean_object* v_infoState_477_; lean_object* v_traceState_478_; lean_object* v_snapshotTasks_479_; lean_object* v_prevLinterStates_480_; lean_object* v_codeQualityEntryTasks_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_492_; 
v___x_468_ = lean_st_ref_take(v___y_464_);
v_env_469_ = lean_ctor_get(v___x_468_, 0);
v_messages_470_ = lean_ctor_get(v___x_468_, 1);
v_scopes_471_ = lean_ctor_get(v___x_468_, 2);
v_usedQuotCtxts_472_ = lean_ctor_get(v___x_468_, 3);
v_nextMacroScope_473_ = lean_ctor_get(v___x_468_, 4);
v_maxRecDepth_474_ = lean_ctor_get(v___x_468_, 5);
v_ngen_475_ = lean_ctor_get(v___x_468_, 6);
v_auxDeclNGen_476_ = lean_ctor_get(v___x_468_, 7);
v_infoState_477_ = lean_ctor_get(v___x_468_, 8);
v_traceState_478_ = lean_ctor_get(v___x_468_, 9);
v_snapshotTasks_479_ = lean_ctor_get(v___x_468_, 10);
v_prevLinterStates_480_ = lean_ctor_get(v___x_468_, 11);
v_codeQualityEntryTasks_481_ = lean_ctor_get(v___x_468_, 12);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_492_ == 0)
{
v___x_483_ = v___x_468_;
v_isShared_484_ = v_isSharedCheck_492_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_codeQualityEntryTasks_481_);
lean_inc(v_prevLinterStates_480_);
lean_inc(v_snapshotTasks_479_);
lean_inc(v_traceState_478_);
lean_inc(v_infoState_477_);
lean_inc(v_auxDeclNGen_476_);
lean_inc(v_ngen_475_);
lean_inc(v_maxRecDepth_474_);
lean_inc(v_nextMacroScope_473_);
lean_inc(v_usedQuotCtxts_472_);
lean_inc(v_scopes_471_);
lean_inc(v_messages_470_);
lean_inc(v_env_469_);
lean_dec(v___x_468_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_492_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_485_ = lean_box(0);
v___x_486_ = l_Lean_Environment_setExporting(v_env_469_, v_isExporting_465_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_486_);
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_messages_470_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_scopes_471_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_usedQuotCtxts_472_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v_nextMacroScope_473_);
lean_ctor_set(v_reuseFailAlloc_491_, 5, v_maxRecDepth_474_);
lean_ctor_set(v_reuseFailAlloc_491_, 6, v_ngen_475_);
lean_ctor_set(v_reuseFailAlloc_491_, 7, v_auxDeclNGen_476_);
lean_ctor_set(v_reuseFailAlloc_491_, 8, v_infoState_477_);
lean_ctor_set(v_reuseFailAlloc_491_, 9, v_traceState_478_);
lean_ctor_set(v_reuseFailAlloc_491_, 10, v_snapshotTasks_479_);
lean_ctor_set(v_reuseFailAlloc_491_, 11, v_prevLinterStates_480_);
lean_ctor_set(v_reuseFailAlloc_491_, 12, v_codeQualityEntryTasks_481_);
v___x_488_ = v_reuseFailAlloc_491_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_st_ref_put(v___y_464_, v___x_488_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_485_);
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg___lam__0___boxed(lean_object* v___y_493_, lean_object* v_isExporting_494_, lean_object* v_a_x3f_495_, lean_object* v___y_496_){
_start:
{
uint8_t v_isExporting_boxed_497_; lean_object* v_res_498_; 
v_isExporting_boxed_497_ = lean_unbox(v_isExporting_494_);
v_res_498_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg___lam__0(v___y_493_, v_isExporting_boxed_497_, v_a_x3f_495_);
lean_dec(v_a_x3f_495_);
lean_dec(v___y_493_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(lean_object* v_x_499_, uint8_t v_isExporting_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; lean_object* v_env_505_; lean_object* v___x_506_; uint8_t v_isModule_507_; 
v___x_504_ = lean_st_ref_get(v___y_502_);
v_env_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc_ref(v_env_505_);
lean_dec(v___x_504_);
v___x_506_ = l_Lean_Environment_header(v_env_505_);
v_isModule_507_ = lean_ctor_get_uint8(v___x_506_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_506_);
if (v_isModule_507_ == 0)
{
lean_object* v___x_508_; 
lean_dec_ref(v_env_505_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
v___x_508_ = lean_apply_3(v_x_499_, v___y_501_, v___y_502_, lean_box(0));
return v___x_508_;
}
else
{
uint8_t v_isExporting_509_; 
v_isExporting_509_ = lean_ctor_get_uint8(v_env_505_, sizeof(void*)*13);
lean_dec_ref(v_env_505_);
if (v_isExporting_500_ == 0)
{
if (v_isExporting_509_ == 0)
{
lean_object* v___x_563_; 
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
v___x_563_ = lean_apply_3(v_x_499_, v___y_501_, v___y_502_, lean_box(0));
return v___x_563_;
}
else
{
goto v___jp_510_;
}
}
else
{
if (v_isExporting_509_ == 0)
{
goto v___jp_510_;
}
else
{
lean_object* v___x_564_; 
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
v___x_564_ = lean_apply_3(v_x_499_, v___y_501_, v___y_502_, lean_box(0));
return v___x_564_;
}
}
v___jp_510_:
{
lean_object* v___x_511_; lean_object* v_env_512_; lean_object* v_messages_513_; lean_object* v_scopes_514_; lean_object* v_usedQuotCtxts_515_; lean_object* v_nextMacroScope_516_; lean_object* v_maxRecDepth_517_; lean_object* v_ngen_518_; lean_object* v_auxDeclNGen_519_; lean_object* v_infoState_520_; lean_object* v_traceState_521_; lean_object* v_snapshotTasks_522_; lean_object* v_prevLinterStates_523_; lean_object* v_codeQualityEntryTasks_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_562_; 
v___x_511_ = lean_st_ref_take(v___y_502_);
v_env_512_ = lean_ctor_get(v___x_511_, 0);
v_messages_513_ = lean_ctor_get(v___x_511_, 1);
v_scopes_514_ = lean_ctor_get(v___x_511_, 2);
v_usedQuotCtxts_515_ = lean_ctor_get(v___x_511_, 3);
v_nextMacroScope_516_ = lean_ctor_get(v___x_511_, 4);
v_maxRecDepth_517_ = lean_ctor_get(v___x_511_, 5);
v_ngen_518_ = lean_ctor_get(v___x_511_, 6);
v_auxDeclNGen_519_ = lean_ctor_get(v___x_511_, 7);
v_infoState_520_ = lean_ctor_get(v___x_511_, 8);
v_traceState_521_ = lean_ctor_get(v___x_511_, 9);
v_snapshotTasks_522_ = lean_ctor_get(v___x_511_, 10);
v_prevLinterStates_523_ = lean_ctor_get(v___x_511_, 11);
v_codeQualityEntryTasks_524_ = lean_ctor_get(v___x_511_, 12);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_562_ == 0)
{
v___x_526_ = v___x_511_;
v_isShared_527_ = v_isSharedCheck_562_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_codeQualityEntryTasks_524_);
lean_inc(v_prevLinterStates_523_);
lean_inc(v_snapshotTasks_522_);
lean_inc(v_traceState_521_);
lean_inc(v_infoState_520_);
lean_inc(v_auxDeclNGen_519_);
lean_inc(v_ngen_518_);
lean_inc(v_maxRecDepth_517_);
lean_inc(v_nextMacroScope_516_);
lean_inc(v_usedQuotCtxts_515_);
lean_inc(v_scopes_514_);
lean_inc(v_messages_513_);
lean_inc(v_env_512_);
lean_dec(v___x_511_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_562_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_528_ = l_Lean_Environment_setExporting(v_env_512_, v_isExporting_500_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_528_);
v___x_530_ = v___x_526_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_messages_513_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_scopes_514_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_usedQuotCtxts_515_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v_nextMacroScope_516_);
lean_ctor_set(v_reuseFailAlloc_561_, 5, v_maxRecDepth_517_);
lean_ctor_set(v_reuseFailAlloc_561_, 6, v_ngen_518_);
lean_ctor_set(v_reuseFailAlloc_561_, 7, v_auxDeclNGen_519_);
lean_ctor_set(v_reuseFailAlloc_561_, 8, v_infoState_520_);
lean_ctor_set(v_reuseFailAlloc_561_, 9, v_traceState_521_);
lean_ctor_set(v_reuseFailAlloc_561_, 10, v_snapshotTasks_522_);
lean_ctor_set(v_reuseFailAlloc_561_, 11, v_prevLinterStates_523_);
lean_ctor_set(v_reuseFailAlloc_561_, 12, v_codeQualityEntryTasks_524_);
v___x_530_ = v_reuseFailAlloc_561_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; lean_object* v_r_532_; 
v___x_531_ = lean_st_ref_put(v___y_502_, v___x_530_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
v_r_532_ = lean_apply_3(v_x_499_, v___y_501_, v___y_502_, lean_box(0));
if (lean_obj_tag(v_r_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_549_; 
v_a_533_ = lean_ctor_get(v_r_532_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v_r_532_);
if (v_isSharedCheck_549_ == 0)
{
v___x_535_ = v_r_532_;
v_isShared_536_ = v_isSharedCheck_549_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v_r_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_549_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
lean_inc(v_a_533_);
if (v_isShared_536_ == 0)
{
lean_ctor_set_tag(v___x_535_, 1);
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_548_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
v___x_539_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg___lam__0(v___y_502_, v_isExporting_509_, v___x_538_);
lean_dec_ref(v___x_538_);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; 
v_unused_547_ = lean_ctor_get(v___x_539_, 0);
lean_dec(v_unused_547_);
v___x_541_ = v___x_539_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_dec(v___x_539_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v_a_533_);
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_533_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
v_a_550_ = lean_ctor_get(v_r_532_, 0);
lean_inc(v_a_550_);
lean_dec_ref_known(v_r_532_, 1);
v___x_551_ = lean_box(0);
v___x_552_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg___lam__0(v___y_502_, v_isExporting_509_, v___x_551_);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v___x_552_, 0);
lean_dec(v_unused_560_);
v___x_554_ = v___x_552_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_dec(v___x_552_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
lean_ctor_set_tag(v___x_554_, 1);
lean_ctor_set(v___x_554_, 0, v_a_550_);
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_550_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg___boxed(lean_object* v_x_565_, lean_object* v_isExporting_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
uint8_t v_isExporting_boxed_570_; lean_object* v_res_571_; 
v_isExporting_boxed_570_ = lean_unbox(v_isExporting_566_);
v_res_571_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v_x_565_, v_isExporting_boxed_570_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1(lean_object* v_00_u03b1_572_, lean_object* v_x_573_, uint8_t v_isExporting_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v_x_573_, v_isExporting_574_, v___y_575_, v___y_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___boxed(lean_object* v_00_u03b1_579_, lean_object* v_x_580_, lean_object* v_isExporting_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
uint8_t v_isExporting_boxed_585_; lean_object* v_res_586_; 
v_isExporting_boxed_585_ = lean_unbox(v_isExporting_581_);
v_res_586_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1(v_00_u03b1_579_, v_x_580_, v_isExporting_boxed_585_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0(lean_object* v___x_587_, lean_object* v___x_588_, lean_object* v_doc_x3f_589_, lean_object* v_attrs_x3f_590_, lean_object* v_attrKind_591_, lean_object* v_tk_592_, lean_object* v_alts_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_Elab_Command_getRef___redArg(v___y_594_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v_fileName_599_; lean_object* v_fileMap_600_; lean_object* v_currRecDepth_601_; lean_object* v_cmdPos_602_; lean_object* v_macroStack_603_; lean_object* v_quotContext_x3f_604_; lean_object* v_currMacroScope_605_; lean_object* v_snap_x3f_606_; lean_object* v_cancelTk_x3f_607_; uint8_t v_suppressElabErrors_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_627_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref_known(v___x_597_, 1);
v_fileName_599_ = lean_ctor_get(v___y_594_, 0);
v_fileMap_600_ = lean_ctor_get(v___y_594_, 1);
v_currRecDepth_601_ = lean_ctor_get(v___y_594_, 2);
v_cmdPos_602_ = lean_ctor_get(v___y_594_, 3);
v_macroStack_603_ = lean_ctor_get(v___y_594_, 4);
v_quotContext_x3f_604_ = lean_ctor_get(v___y_594_, 5);
v_currMacroScope_605_ = lean_ctor_get(v___y_594_, 6);
v_snap_x3f_606_ = lean_ctor_get(v___y_594_, 8);
v_cancelTk_x3f_607_ = lean_ctor_get(v___y_594_, 9);
v_suppressElabErrors_608_ = lean_ctor_get_uint8(v___y_594_, sizeof(void*)*10);
v_isSharedCheck_627_ = !lean_is_exclusive(v___y_594_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v___y_594_, 7);
lean_dec(v_unused_628_);
v___x_610_ = v___y_594_;
v_isShared_611_ = v_isSharedCheck_627_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_cancelTk_x3f_607_);
lean_inc(v_snap_x3f_606_);
lean_inc(v_currMacroScope_605_);
lean_inc(v_quotContext_x3f_604_);
lean_inc(v_macroStack_603_);
lean_inc(v_cmdPos_602_);
lean_inc(v_currRecDepth_601_);
lean_inc(v_fileMap_600_);
lean_inc(v_fileName_599_);
lean_dec(v___y_594_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_627_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v_ref_612_; lean_object* v___x_614_; 
v_ref_612_ = l_Lean_replaceRef(v___x_587_, v_a_598_);
lean_dec(v_a_598_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 7, v_ref_612_);
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_fileName_599_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_fileMap_600_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_currRecDepth_601_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v_cmdPos_602_);
lean_ctor_set(v_reuseFailAlloc_626_, 4, v_macroStack_603_);
lean_ctor_set(v_reuseFailAlloc_626_, 5, v_quotContext_x3f_604_);
lean_ctor_set(v_reuseFailAlloc_626_, 6, v_currMacroScope_605_);
lean_ctor_set(v_reuseFailAlloc_626_, 7, v_ref_612_);
lean_ctor_set(v_reuseFailAlloc_626_, 8, v_snap_x3f_606_);
lean_ctor_set(v_reuseFailAlloc_626_, 9, v_cancelTk_x3f_607_);
lean_ctor_set_uint8(v_reuseFailAlloc_626_, sizeof(void*)*10, v_suppressElabErrors_608_);
v___x_614_ = v_reuseFailAlloc_626_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_Elab_Command_resolveSyntaxKind(v___x_588_, v___x_614_, v___y_595_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_617_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_615_, 1);
v___x_617_ = l_Lean_Elab_Command_elabMacroRulesAux(v_doc_x3f_589_, v_attrs_x3f_590_, v_attrKind_591_, v_tk_592_, v_a_616_, v_alts_593_, v___x_614_, v___y_595_);
lean_dec_ref(v___x_614_);
return v___x_617_;
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec_ref(v___x_614_);
lean_dec_ref(v_alts_593_);
lean_dec(v_attrKind_591_);
lean_dec(v_doc_x3f_589_);
v_a_618_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_615_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_615_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_594_);
lean_dec_ref(v_alts_593_);
lean_dec(v_attrKind_591_);
lean_dec(v_doc_x3f_589_);
lean_dec(v___x_588_);
return v___x_597_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__0___boxed(lean_object* v___x_629_, lean_object* v___x_630_, lean_object* v_doc_x3f_631_, lean_object* v_attrs_x3f_632_, lean_object* v_attrKind_633_, lean_object* v_tk_634_, lean_object* v_alts_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_Elab_Command_elabMacroRules___lam__0(v___x_629_, v___x_630_, v_doc_x3f_631_, v_attrs_x3f_632_, v_attrKind_633_, v_tk_634_, v_alts_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec(v_tk_634_);
lean_dec(v_attrs_x3f_632_);
lean_dec(v___x_629_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5(lean_object* v___x_643_, lean_object* v___x_644_, lean_object* v_attrKind_645_, lean_object* v___x_646_, lean_object* v___x_647_, lean_object* v_attrs_x3f_648_, lean_object* v___x_649_, lean_object* v___x_650_, lean_object* v___x_651_, lean_object* v_doc_x3f_652_, lean_object* v_kind_x3f_653_, lean_object* v_alts_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_Elab_Command_getRef___redArg(v___y_655_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_736_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_736_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_736_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_736_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
uint8_t v___x_663_; lean_object* v___x_664_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___x_725_; 
v___x_663_ = 0;
v___x_664_ = l_Lean_SourceInfo_fromRef(v_a_659_, v___x_663_);
lean_dec(v_a_659_);
v___x_725_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_655_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_quotContext_x3f_726_; 
lean_dec_ref_known(v___x_725_, 1);
v_quotContext_x3f_726_ = lean_ctor_get(v___y_655_, 5);
if (lean_obj_tag(v_quotContext_x3f_726_) == 0)
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkMacroRulesFun_spec__1___redArg(v___y_656_);
lean_dec_ref(v___x_727_);
goto v___jp_719_;
}
else
{
goto v___jp_719_;
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec(v___x_664_);
lean_del_object(v___x_661_);
lean_dec(v_kind_x3f_653_);
lean_dec(v_doc_x3f_652_);
lean_dec_ref(v___x_651_);
lean_dec_ref(v___x_650_);
lean_dec_ref(v___x_649_);
lean_dec_ref(v___x_646_);
lean_dec(v_attrKind_645_);
lean_dec(v___x_644_);
lean_dec(v___x_643_);
v_a_728_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_725_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_725_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
v___jp_665_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
lean_inc_ref_n(v___y_668_, 2);
v___x_672_ = l_Array_append___redArg(v___y_668_, v___y_671_);
lean_dec_ref(v___y_671_);
lean_inc_n(v___y_670_, 2);
lean_inc_n(v___x_664_, 3);
v___x_673_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_673_, 0, v___x_664_);
lean_ctor_set(v___x_673_, 1, v___y_670_);
lean_ctor_set(v___x_673_, 2, v___x_672_);
v___x_674_ = l_Array_append___redArg(v___y_668_, v_alts_654_);
v___x_675_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_675_, 0, v___x_664_);
lean_ctor_set(v___x_675_, 1, v___y_670_);
lean_ctor_set(v___x_675_, 2, v___x_674_);
v___x_676_ = l_Lean_Syntax_node1(v___x_664_, v___x_643_, v___x_675_);
v___x_677_ = l_Lean_Syntax_node6(v___x_664_, v___x_644_, v___y_669_, v___y_666_, v_attrKind_645_, v___y_667_, v___x_673_, v___x_676_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_677_);
v___x_679_ = v___x_661_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
v___jp_681_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
lean_inc_ref(v___y_682_);
v___x_686_ = l_Array_append___redArg(v___y_682_, v___y_685_);
lean_dec_ref(v___y_685_);
lean_inc(v___y_684_);
lean_inc_n(v___x_664_, 2);
v___x_687_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_687_, 0, v___x_664_);
lean_ctor_set(v___x_687_, 1, v___y_684_);
lean_ctor_set(v___x_687_, 2, v___x_686_);
v___x_688_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_664_);
lean_ctor_set(v___x_688_, 1, v___x_646_);
if (lean_obj_tag(v_kind_x3f_653_) == 0)
{
lean_object* v___x_689_; 
v___x_689_ = lean_mk_empty_array_with_capacity(v___x_647_);
v___y_666_ = v___x_687_;
v___y_667_ = v___x_688_;
v___y_668_ = v___y_682_;
v___y_669_ = v___y_683_;
v___y_670_ = v___y_684_;
v___y_671_ = v___x_689_;
goto v___jp_665_;
}
else
{
lean_object* v_val_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_val_690_ = lean_ctor_get(v_kind_x3f_653_, 0);
lean_inc(v_val_690_);
lean_dec_ref_known(v_kind_x3f_653_, 1);
v___x_691_ = l_Lean_mkIdent(v_val_690_);
v___x_692_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0));
lean_inc_n(v___x_664_, 4);
v___x_693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_664_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1));
v___x_695_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_664_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
v___x_697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_664_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2));
v___x_699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_664_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = l_Array_mkArray5___redArg(v___x_693_, v___x_695_, v___x_697_, v___x_691_, v___x_699_);
v___y_666_ = v___x_687_;
v___y_667_ = v___x_688_;
v___y_668_ = v___y_682_;
v___y_669_ = v___y_683_;
v___y_670_ = v___y_684_;
v___y_671_ = v___x_700_;
goto v___jp_665_;
}
}
v___jp_701_:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
lean_inc_ref(v___y_702_);
v___x_705_ = l_Array_append___redArg(v___y_702_, v___y_704_);
lean_dec_ref(v___y_704_);
lean_inc(v___y_703_);
lean_inc(v___x_664_);
v___x_706_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_706_, 0, v___x_664_);
lean_ctor_set(v___x_706_, 1, v___y_703_);
lean_ctor_set(v___x_706_, 2, v___x_705_);
if (lean_obj_tag(v_attrs_x3f_648_) == 1)
{
lean_object* v_val_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_val_707_ = lean_ctor_get(v_attrs_x3f_648_, 0);
v___x_708_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
v___x_709_ = l_Lean_Name_mkStr4(v___x_649_, v___x_650_, v___x_651_, v___x_708_);
v___x_710_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
lean_inc_n(v___x_664_, 4);
v___x_711_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_664_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
lean_inc_ref(v___y_702_);
v___x_712_ = l_Array_append___redArg(v___y_702_, v_val_707_);
lean_inc(v___y_703_);
v___x_713_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_713_, 0, v___x_664_);
lean_ctor_set(v___x_713_, 1, v___y_703_);
lean_ctor_set(v___x_713_, 2, v___x_712_);
v___x_714_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__3));
v___x_715_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_664_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = l_Lean_Syntax_node3(v___x_664_, v___x_709_, v___x_711_, v___x_713_, v___x_715_);
v___x_717_ = l_Array_mkArray1___redArg(v___x_716_);
v___y_682_ = v___y_702_;
v___y_683_ = v___x_706_;
v___y_684_ = v___y_703_;
v___y_685_ = v___x_717_;
goto v___jp_681_;
}
else
{
lean_object* v___x_718_; 
lean_dec_ref(v___x_651_);
lean_dec_ref(v___x_650_);
lean_dec_ref(v___x_649_);
v___x_718_ = lean_mk_empty_array_with_capacity(v___x_647_);
v___y_682_ = v___y_702_;
v___y_683_ = v___x_706_;
v___y_684_ = v___y_703_;
v___y_685_ = v___x_718_;
goto v___jp_681_;
}
}
v___jp_719_:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__8));
v___x_721_ = lean_obj_once(&l_Lean_Elab_Command_mkMacroRulesFun___closed__9, &l_Lean_Elab_Command_mkMacroRulesFun___closed__9_once, _init_l_Lean_Elab_Command_mkMacroRulesFun___closed__9);
if (lean_obj_tag(v_doc_x3f_652_) == 1)
{
lean_object* v_val_722_; lean_object* v___x_723_; 
v_val_722_ = lean_ctor_get(v_doc_x3f_652_, 0);
lean_inc(v_val_722_);
lean_dec_ref_known(v_doc_x3f_652_, 1);
v___x_723_ = l_Array_mkArray1___redArg(v_val_722_);
v___y_702_ = v___x_721_;
v___y_703_ = v___x_720_;
v___y_704_ = v___x_723_;
goto v___jp_701_;
}
else
{
lean_object* v___x_724_; 
lean_dec(v_doc_x3f_652_);
v___x_724_ = lean_mk_empty_array_with_capacity(v___x_647_);
v___y_702_ = v___x_721_;
v___y_703_ = v___x_720_;
v___y_704_ = v___x_724_;
goto v___jp_701_;
}
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v_kind_x3f_653_);
lean_dec(v_doc_x3f_652_);
lean_dec_ref(v___x_651_);
lean_dec_ref(v___x_650_);
lean_dec_ref(v___x_649_);
lean_dec_ref(v___x_646_);
lean_dec(v_attrKind_645_);
lean_dec(v___x_644_);
lean_dec(v___x_643_);
v_a_737_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_658_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_658_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__5___boxed(lean_object* v___x_745_, lean_object* v___x_746_, lean_object* v_attrKind_747_, lean_object* v___x_748_, lean_object* v___x_749_, lean_object* v_attrs_x3f_750_, lean_object* v___x_751_, lean_object* v___x_752_, lean_object* v___x_753_, lean_object* v_doc_x3f_754_, lean_object* v_kind_x3f_755_, lean_object* v_alts_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_Elab_Command_elabMacroRules___lam__5(v___x_745_, v___x_746_, v_attrKind_747_, v___x_748_, v___x_749_, v_attrs_x3f_750_, v___x_751_, v___x_752_, v___x_753_, v_doc_x3f_754_, v_kind_x3f_755_, v_alts_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec_ref(v_alts_756_);
lean_dec(v_attrs_x3f_750_);
lean_dec(v___x_749_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1(lean_object* v_stx_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; 
v___x_811_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__0));
v___x_812_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__1));
v___x_813_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__0));
v___x_814_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0));
lean_inc(v_stx_807_);
v___x_815_ = l_Lean_Syntax_isOfKind(v_stx_807_, v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_881_; 
lean_dec(v_stx_807_);
v___x_881_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_881_;
}
else
{
lean_object* v___x_882_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v_a_895_; lean_object* v___y_903_; lean_object* v___y_904_; uint8_t v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; uint8_t v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v_attrs_x3f_971_; lean_object* v_doc_x3f_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_1190_ = l_Lean_Syntax_getArg(v_stx_807_, v___x_882_);
v___x_1191_ = l_Lean_Syntax_isNone(v___x_1190_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1190_);
v___x_1193_ = l_Lean_Syntax_matchesNull(v___x_1190_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
lean_dec(v___x_1190_);
lean_dec(v_stx_807_);
v___x_1194_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_1194_;
}
else
{
lean_object* v_doc_x3f_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v_doc_x3f_1195_ = l_Lean_Syntax_getArg(v___x_1190_, v___x_882_);
lean_dec(v___x_1190_);
v___x_1196_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15));
lean_inc(v_doc_x3f_1195_);
v___x_1197_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1195_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; 
lean_dec(v_doc_x3f_1195_);
lean_dec(v_stx_807_);
v___x_1198_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_1198_;
}
else
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1199_, 0, v_doc_x3f_1195_);
v_doc_x3f_1174_ = v___x_1199_;
v___y_1175_ = v___y_808_;
v___y_1176_ = v___y_809_;
goto v___jp_1173_;
}
}
}
else
{
lean_object* v___x_1200_; 
lean_dec(v___x_1190_);
v___x_1200_ = lean_box(0);
v_doc_x3f_1174_ = v___x_1200_;
v___y_1175_ = v___y_808_;
v___y_1176_ = v___y_809_;
goto v___jp_1173_;
}
v___jp_883_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__13));
v___x_897_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__14));
v___x_898_ = lean_obj_once(&l_Lean_Elab_Command_mkMacroRulesFun___closed__9, &l_Lean_Elab_Command_mkMacroRulesFun___closed__9_once, _init_l_Lean_Elab_Command_mkMacroRulesFun___closed__9);
if (lean_obj_tag(v___y_889_) == 1)
{
lean_object* v_val_899_; lean_object* v___x_900_; 
v_val_899_ = lean_ctor_get(v___y_889_, 0);
lean_inc(v_val_899_);
lean_dec_ref_known(v___y_889_, 1);
v___x_900_ = l_Array_mkArray1___redArg(v_val_899_);
v___y_817_ = v___x_897_;
v___y_818_ = v___x_898_;
v___y_819_ = v___y_888_;
v___y_820_ = v_a_895_;
v___y_821_ = v___y_892_;
v___y_822_ = v___y_893_;
v___y_823_ = v___x_896_;
v___y_824_ = v___y_884_;
v___y_825_ = v___y_885_;
v___y_826_ = v___y_886_;
v___y_827_ = v___y_887_;
v___y_828_ = v___y_890_;
v___y_829_ = v___y_891_;
v___y_830_ = v___y_894_;
v___y_831_ = v___x_900_;
goto v___jp_816_;
}
else
{
lean_object* v___x_901_; 
lean_dec(v___y_889_);
v___x_901_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__15));
v___y_817_ = v___x_897_;
v___y_818_ = v___x_898_;
v___y_819_ = v___y_888_;
v___y_820_ = v_a_895_;
v___y_821_ = v___y_892_;
v___y_822_ = v___y_893_;
v___y_823_ = v___x_896_;
v___y_824_ = v___y_884_;
v___y_825_ = v___y_885_;
v___y_826_ = v___y_886_;
v___y_827_ = v___y_887_;
v___y_828_ = v___y_890_;
v___y_829_ = v___y_891_;
v___y_830_ = v___y_894_;
v___y_831_ = v___x_901_;
goto v___jp_816_;
}
}
v___jp_902_:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = l_Lean_Parser_Command_visibility_ofAttrKind(v___y_904_);
v___x_917_ = l_Lean_Elab_Command_getRef___redArg(v___y_911_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_917_, 1);
v___x_919_ = l_Lean_SourceInfo_fromRef(v_a_918_, v___y_905_);
lean_dec(v_a_918_);
v___x_920_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_911_);
lean_dec_ref(v___y_911_);
if (lean_obj_tag(v___x_920_) == 0)
{
if (lean_obj_tag(v___y_906_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_922_; lean_object* v_a_923_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
v___x_922_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkMacroRulesFun_spec__1___redArg(v___y_910_);
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref(v___x_922_);
v___y_884_ = v___y_908_;
v___y_885_ = v___x_919_;
v___y_886_ = v___y_909_;
v___y_887_ = v___y_915_;
v___y_888_ = v___y_903_;
v___y_889_ = v___y_912_;
v___y_890_ = v___y_913_;
v___y_891_ = v___y_914_;
v___y_892_ = v___x_916_;
v___y_893_ = v___y_907_;
v___y_894_ = v_a_921_;
v_a_895_ = v_a_923_;
goto v___jp_883_;
}
else
{
lean_object* v_a_924_; lean_object* v_val_925_; 
v_a_924_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_924_);
lean_dec_ref_known(v___x_920_, 1);
v_val_925_ = lean_ctor_get(v___y_906_, 0);
lean_inc(v_val_925_);
v___y_884_ = v___y_908_;
v___y_885_ = v___x_919_;
v___y_886_ = v___y_909_;
v___y_887_ = v___y_915_;
v___y_888_ = v___y_903_;
v___y_889_ = v___y_912_;
v___y_890_ = v___y_913_;
v___y_891_ = v___y_914_;
v___y_892_ = v___x_916_;
v___y_893_ = v___y_907_;
v___y_894_ = v_a_924_;
v_a_895_ = v_val_925_;
goto v___jp_883_;
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v___x_919_);
lean_dec(v___x_916_);
lean_dec_ref(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec(v___y_912_);
lean_dec(v___y_909_);
lean_dec(v___y_908_);
lean_dec(v___y_903_);
v_a_926_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_920_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_920_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_dec(v___x_916_);
lean_dec_ref(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_909_);
lean_dec(v___y_908_);
lean_dec(v___y_903_);
return v___x_917_;
}
}
v___jp_934_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_950_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__16));
lean_inc_ref(v___y_949_);
v___x_951_ = l_Lean_Name_mkStr4(v___x_811_, v___x_812_, v___y_949_, v___x_950_);
v___x_952_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__19));
v___x_953_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__20));
lean_inc_n(v___y_936_, 2);
v___x_954_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_954_, 0, v___y_936_);
lean_ctor_set(v___x_954_, 1, v___x_952_);
lean_inc(v___y_935_);
v___x_955_ = l_Lean_Syntax_node2(v___y_936_, v___x_953_, v___x_954_, v___y_935_);
lean_inc(v___y_937_);
v___x_956_ = l_Lean_Syntax_node2(v___y_936_, v___x_951_, v___y_937_, v___x_955_);
if (lean_obj_tag(v___y_946_) == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_957_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__21));
v___x_958_ = lean_mk_empty_array_with_capacity(v___y_942_);
v___x_959_ = lean_array_push(v___x_958_, v___x_956_);
v___x_960_ = l_Lean_Syntax_SepArray_ofElems(v___x_957_, v___x_959_);
lean_dec_ref(v___x_959_);
v___y_903_ = v___y_935_;
v___y_904_ = v___y_937_;
v___y_905_ = v___y_938_;
v___y_906_ = v___y_939_;
v___y_907_ = v___y_940_;
v___y_908_ = v___y_941_;
v___y_909_ = v___y_943_;
v___y_910_ = v___y_944_;
v___y_911_ = v___y_945_;
v___y_912_ = v___y_947_;
v___y_913_ = v___y_948_;
v___y_914_ = v___y_949_;
v___y_915_ = v___x_960_;
goto v___jp_902_;
}
else
{
lean_object* v_val_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_val_961_ = lean_ctor_get(v___y_946_, 0);
lean_inc(v_val_961_);
lean_dec_ref_known(v___y_946_, 1);
v___x_962_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__21));
v___x_963_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_961_);
lean_dec(v_val_961_);
v___x_964_ = lean_array_push(v___x_963_, v___x_956_);
v___x_965_ = l_Lean_Syntax_SepArray_ofElems(v___x_962_, v___x_964_);
lean_dec_ref(v___x_964_);
v___y_903_ = v___y_935_;
v___y_904_ = v___y_937_;
v___y_905_ = v___y_938_;
v___y_906_ = v___y_939_;
v___y_907_ = v___y_940_;
v___y_908_ = v___y_941_;
v___y_909_ = v___y_943_;
v___y_910_ = v___y_944_;
v___y_911_ = v___y_945_;
v___y_912_ = v___y_947_;
v___y_913_ = v___y_948_;
v___y_914_ = v___y_949_;
v___y_915_ = v___x_965_;
goto v___jp_902_;
}
}
v___jp_966_:
{
lean_object* v___x_972_; lean_object* v_attrKind_973_; lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_972_ = lean_unsigned_to_nat(2u);
v_attrKind_973_ = l_Lean_Syntax_getArg(v_stx_807_, v___x_972_);
v___x_974_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__2));
v___x_975_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8));
lean_inc(v_attrKind_973_);
v___x_976_ = l_Lean_Syntax_isOfKind(v_attrKind_973_, v___x_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; 
lean_dec(v_attrKind_973_);
lean_dec(v_attrs_x3f_971_);
lean_dec(v___y_969_);
lean_dec(v_stx_807_);
v___x_977_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_977_;
}
else
{
lean_object* v___x_978_; lean_object* v_tk_979_; lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_978_ = lean_unsigned_to_nat(3u);
v_tk_979_ = l_Lean_Syntax_getArg(v_stx_807_, v___x_978_);
v___x_980_ = lean_unsigned_to_nat(4u);
v___x_981_ = l_Lean_Syntax_getArg(v_stx_807_, v___x_980_);
lean_inc(v___x_981_);
v___x_982_ = l_Lean_Syntax_matchesNull(v___x_981_, v___x_882_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_983_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_981_);
v___x_984_ = l_Lean_Syntax_matchesNull(v___x_981_, v___x_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
lean_dec(v___x_981_);
lean_dec(v_tk_979_);
lean_dec(v_attrKind_973_);
lean_dec(v_attrs_x3f_971_);
lean_dec(v___y_969_);
lean_dec(v_stx_807_);
v___x_985_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_985_;
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_986_ = l_Lean_Syntax_getArg(v_stx_807_, v___x_983_);
lean_dec(v_stx_807_);
v___x_987_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__6));
lean_inc(v___x_986_);
v___x_988_ = l_Lean_Syntax_isOfKind(v___x_986_, v___x_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
lean_dec(v___x_986_);
lean_dec(v___x_981_);
lean_dec(v_tk_979_);
lean_dec(v_attrKind_973_);
lean_dec(v_attrs_x3f_971_);
lean_dec(v___y_969_);
v___x_989_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_989_;
}
else
{
lean_object* v_kind_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v_kind_990_ = l_Lean_Syntax_getArg(v___x_981_, v___x_978_);
lean_dec(v___x_981_);
v___x_991_ = l_Lean_Syntax_getArg(v___x_986_, v___x_882_);
lean_dec(v___x_986_);
lean_inc(v___x_991_);
v___x_992_ = l_Lean_Syntax_matchesNull(v___x_991_, v___y_970_);
if (v___x_992_ == 0)
{
lean_object* v_alts_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___f_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v_alts_993_ = l_Lean_Syntax_getArgs(v___x_991_);
lean_dec(v___x_991_);
v___x_994_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__8));
v___x_995_ = lean_box(2);
lean_inc_ref(v_alts_993_);
v___x_996_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v___x_994_);
lean_ctor_set(v___x_996_, 2, v_alts_993_);
v___x_997_ = lean_mk_empty_array_with_capacity(v___x_972_);
lean_inc(v_tk_979_);
v___x_998_ = lean_array_push(v___x_997_, v_tk_979_);
v___x_999_ = lean_array_push(v___x_998_, v___x_996_);
v___x_1000_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1000_, 0, v___x_995_);
lean_ctor_set(v___x_1000_, 1, v___x_994_);
lean_ctor_set(v___x_1000_, 2, v___x_999_);
v___x_1001_ = l_Lean_TSyntax_getId(v_kind_990_);
lean_dec(v_kind_990_);
lean_inc(v_attrKind_973_);
v___f_1002_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1002_, 0, v___x_1000_);
lean_closure_set(v___f_1002_, 1, v___x_1001_);
lean_closure_set(v___f_1002_, 2, v___y_969_);
lean_closure_set(v___f_1002_, 3, v_attrs_x3f_971_);
lean_closure_set(v___f_1002_, 4, v_attrKind_973_);
lean_closure_set(v___f_1002_, 5, v_tk_979_);
lean_closure_set(v___f_1002_, 6, v_alts_993_);
v___x_1003_ = l_Lean_Syntax_getArg(v_attrKind_973_, v___x_882_);
lean_dec(v_attrKind_973_);
lean_inc(v___x_1003_);
v___x_1004_ = l_Lean_Syntax_matchesNull(v___x_1003_, v___y_970_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; 
lean_dec(v___x_1003_);
v___x_1005_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_1002_, v___x_988_, v___y_968_, v___y_967_);
return v___x_1005_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1006_ = l_Lean_Syntax_getArg(v___x_1003_, v___x_882_);
lean_dec(v___x_1003_);
v___x_1007_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10));
v___x_1008_ = l_Lean_Syntax_isOfKind(v___x_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_1002_, v___x_988_, v___y_968_, v___y_967_);
return v___x_1009_;
}
else
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_1002_, v___x_992_, v___y_968_, v___y_967_);
return v___x_1010_;
}
}
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1011_ = l_Lean_Syntax_getArg(v___x_991_, v___x_882_);
v___x_1012_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__11));
lean_inc(v___x_1011_);
v___x_1013_ = l_Lean_Syntax_isOfKind(v___x_1011_, v___x_1012_);
if (v___x_1013_ == 0)
{
lean_object* v_alts_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___f_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
lean_dec(v___x_1011_);
v_alts_1014_ = l_Lean_Syntax_getArgs(v___x_991_);
lean_dec(v___x_991_);
v___x_1015_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__8));
v___x_1016_ = lean_box(2);
lean_inc_ref(v_alts_1014_);
v___x_1017_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v___x_1015_);
lean_ctor_set(v___x_1017_, 2, v_alts_1014_);
v___x_1018_ = lean_mk_empty_array_with_capacity(v___x_972_);
lean_inc(v_tk_979_);
v___x_1019_ = lean_array_push(v___x_1018_, v_tk_979_);
v___x_1020_ = lean_array_push(v___x_1019_, v___x_1017_);
v___x_1021_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1016_);
lean_ctor_set(v___x_1021_, 1, v___x_1015_);
lean_ctor_set(v___x_1021_, 2, v___x_1020_);
v___x_1022_ = l_Lean_TSyntax_getId(v_kind_990_);
lean_dec(v_kind_990_);
lean_inc(v_attrKind_973_);
v___f_1023_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1023_, 0, v___x_1021_);
lean_closure_set(v___f_1023_, 1, v___x_1022_);
lean_closure_set(v___f_1023_, 2, v___y_969_);
lean_closure_set(v___f_1023_, 3, v_attrs_x3f_971_);
lean_closure_set(v___f_1023_, 4, v_attrKind_973_);
lean_closure_set(v___f_1023_, 5, v_tk_979_);
lean_closure_set(v___f_1023_, 6, v_alts_1014_);
v___x_1024_ = l_Lean_Syntax_getArg(v_attrKind_973_, v___x_882_);
lean_dec(v_attrKind_973_);
lean_inc(v___x_1024_);
v___x_1025_ = l_Lean_Syntax_matchesNull(v___x_1024_, v___y_970_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; 
lean_dec(v___x_1024_);
v___x_1026_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_1023_, v___x_992_, v___y_968_, v___y_967_);
return v___x_1026_;
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1027_ = l_Lean_Syntax_getArg(v___x_1024_, v___x_882_);
lean_dec(v___x_1024_);
v___x_1028_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10));
v___x_1029_ = l_Lean_Syntax_isOfKind(v___x_1027_, v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_1023_, v___x_992_, v___y_968_, v___y_967_);
return v___x_1030_;
}
else
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_1023_, v___x_1013_, v___y_968_, v___y_967_);
return v___x_1031_;
}
}
}
else
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = l_Lean_Syntax_getArg(v___x_1011_, v___y_970_);
lean_inc(v___x_1032_);
v___x_1033_ = l_Lean_Syntax_matchesNull(v___x_1032_, v___y_970_);
if (v___x_1033_ == 0)
{
lean_object* v_alts_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___f_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
lean_dec(v___x_1032_);
lean_dec(v___x_1011_);
v_alts_1034_ = l_Lean_Syntax_getArgs(v___x_991_);
lean_dec(v___x_991_);
v___x_1035_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__8));
v___x_1036_ = lean_box(2);
lean_inc_ref(v_alts_1034_);
v___x_1037_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___x_1035_);
lean_ctor_set(v___x_1037_, 2, v_alts_1034_);
v___x_1038_ = lean_mk_empty_array_with_capacity(v___x_972_);
lean_inc(v_tk_979_);
v___x_1039_ = lean_array_push(v___x_1038_, v_tk_979_);
v___x_1040_ = lean_array_push(v___x_1039_, v___x_1037_);
v___x_1041_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1036_);
lean_ctor_set(v___x_1041_, 1, v___x_1035_);
lean_ctor_set(v___x_1041_, 2, v___x_1040_);
v___x_1042_ = l_Lean_TSyntax_getId(v_kind_990_);
lean_dec(v_kind_990_);
lean_inc(v_attrKind_973_);
v___f_1043_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1043_, 0, v___x_1041_);
lean_closure_set(v___f_1043_, 1, v___x_1042_);
lean_closure_set(v___f_1043_, 2, v___y_969_);
lean_closure_set(v___f_1043_, 3, v_attrs_x3f_971_);
lean_closure_set(v___f_1043_, 4, v_attrKind_973_);
lean_closure_set(v___f_1043_, 5, v_tk_979_);
lean_closure_set(v___f_1043_, 6, v_alts_1034_);
v___x_1044_ = l_Lean_Syntax_getArg(v_attrKind_973_, v___x_882_);
lean_dec(v_attrKind_973_);
lean_inc(v___x_1044_);
v___x_1045_ = l_Lean_Syntax_matchesNull(v___x_1044_, v___y_970_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; 
lean_dec(v___x_1044_);
v___x_1046_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_1043_, v___x_1013_, v___y_968_, v___y_967_);
return v___x_1046_;
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = l_Lean_Syntax_getArg(v___x_1044_, v___x_882_);
lean_dec(v___x_1044_);
v___x_1048_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10));
v___x_1049_ = l_Lean_Syntax_isOfKind(v___x_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_1043_, v___x_1013_, v___y_968_, v___y_967_);
return v___x_1050_;
}
else
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_1043_, v___x_1033_, v___y_968_, v___y_967_);
return v___x_1051_;
}
}
}
else
{
lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = l_Lean_Syntax_getArg(v___x_1032_, v___x_882_);
lean_dec(v___x_1032_);
lean_inc(v___x_1052_);
v___x_1053_ = l_Lean_Syntax_matchesNull(v___x_1052_, v___y_970_);
if (v___x_1053_ == 0)
{
lean_object* v_alts_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___f_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
lean_dec(v___x_1052_);
lean_dec(v___x_1011_);
v_alts_1054_ = l_Lean_Syntax_getArgs(v___x_991_);
lean_dec(v___x_991_);
v___x_1055_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__8));
v___x_1056_ = lean_box(2);
lean_inc_ref(v_alts_1054_);
v___x_1057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v___x_1055_);
lean_ctor_set(v___x_1057_, 2, v_alts_1054_);
v___x_1058_ = lean_mk_empty_array_with_capacity(v___x_972_);
lean_inc(v_tk_979_);
v___x_1059_ = lean_array_push(v___x_1058_, v_tk_979_);
v___x_1060_ = lean_array_push(v___x_1059_, v___x_1057_);
v___x_1061_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1056_);
lean_ctor_set(v___x_1061_, 1, v___x_1055_);
lean_ctor_set(v___x_1061_, 2, v___x_1060_);
v___x_1062_ = l_Lean_TSyntax_getId(v_kind_990_);
lean_dec(v_kind_990_);
lean_inc(v_attrKind_973_);
v___f_1063_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1063_, 0, v___x_1061_);
lean_closure_set(v___f_1063_, 1, v___x_1062_);
lean_closure_set(v___f_1063_, 2, v___y_969_);
lean_closure_set(v___f_1063_, 3, v_attrs_x3f_971_);
lean_closure_set(v___f_1063_, 4, v_attrKind_973_);
lean_closure_set(v___f_1063_, 5, v_tk_979_);
lean_closure_set(v___f_1063_, 6, v_alts_1054_);
v___x_1064_ = l_Lean_Syntax_getArg(v_attrKind_973_, v___x_882_);
lean_dec(v_attrKind_973_);
lean_inc(v___x_1064_);
v___x_1065_ = l_Lean_Syntax_matchesNull(v___x_1064_, v___y_970_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
lean_dec(v___x_1064_);
v___x_1066_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_1063_, v___x_1033_, v___y_968_, v___y_967_);
return v___x_1066_;
}
else
{
lean_object* v___x_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1067_ = l_Lean_Syntax_getArg(v___x_1064_, v___x_882_);
lean_dec(v___x_1064_);
v___x_1068_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10));
v___x_1069_ = l_Lean_Syntax_isOfKind(v___x_1067_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_1063_, v___x_1033_, v___y_968_, v___y_967_);
return v___x_1070_;
}
else
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_1063_, v___x_1053_, v___y_968_, v___y_967_);
return v___x_1071_;
}
}
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1072_ = l_Lean_Syntax_getArg(v___x_1052_, v___x_882_);
lean_dec(v___x_1052_);
v___x_1073_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12));
lean_inc(v___x_1072_);
v___x_1074_ = l_Lean_Syntax_isOfKind(v___x_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v_alts_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___f_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
lean_dec(v___x_1072_);
lean_dec(v___x_1011_);
v_alts_1075_ = l_Lean_Syntax_getArgs(v___x_991_);
lean_dec(v___x_991_);
v___x_1076_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__8));
v___x_1077_ = lean_box(2);
lean_inc_ref(v_alts_1075_);
v___x_1078_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___x_1076_);
lean_ctor_set(v___x_1078_, 2, v_alts_1075_);
v___x_1079_ = lean_mk_empty_array_with_capacity(v___x_972_);
lean_inc(v_tk_979_);
v___x_1080_ = lean_array_push(v___x_1079_, v_tk_979_);
v___x_1081_ = lean_array_push(v___x_1080_, v___x_1078_);
v___x_1082_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1077_);
lean_ctor_set(v___x_1082_, 1, v___x_1076_);
lean_ctor_set(v___x_1082_, 2, v___x_1081_);
v___x_1083_ = l_Lean_TSyntax_getId(v_kind_990_);
lean_dec(v_kind_990_);
lean_inc(v_attrKind_973_);
v___f_1084_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1084_, 0, v___x_1082_);
lean_closure_set(v___f_1084_, 1, v___x_1083_);
lean_closure_set(v___f_1084_, 2, v___y_969_);
lean_closure_set(v___f_1084_, 3, v_attrs_x3f_971_);
lean_closure_set(v___f_1084_, 4, v_attrKind_973_);
lean_closure_set(v___f_1084_, 5, v_tk_979_);
lean_closure_set(v___f_1084_, 6, v_alts_1075_);
v___x_1085_ = l_Lean_Syntax_getArg(v_attrKind_973_, v___x_882_);
lean_dec(v_attrKind_973_);
lean_inc(v___x_1085_);
v___x_1086_ = l_Lean_Syntax_matchesNull(v___x_1085_, v___y_970_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; 
lean_dec(v___x_1085_);
v___x_1087_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_1084_, v___x_1053_, v___y_968_, v___y_967_);
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1088_ = l_Lean_Syntax_getArg(v___x_1085_, v___x_882_);
lean_dec(v___x_1085_);
v___x_1089_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10));
v___x_1090_ = l_Lean_Syntax_isOfKind(v___x_1088_, v___x_1089_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_1084_, v___x_1053_, v___y_968_, v___y_967_);
return v___x_1091_;
}
else
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__1___redArg(v___f_1084_, v___x_982_, v___y_968_, v___y_967_);
return v___x_1092_;
}
}
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_dec(v___x_991_);
v___x_1093_ = l_Lean_Syntax_getArg(v___x_1011_, v___x_978_);
lean_dec(v___x_1011_);
v___x_1094_ = lean_mk_empty_array_with_capacity(v___x_972_);
lean_inc(v_tk_979_);
v___x_1095_ = lean_array_push(v___x_1094_, v_tk_979_);
lean_inc(v___x_1093_);
v___x_1096_ = lean_array_push(v___x_1095_, v___x_1093_);
v___x_1097_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__8));
v___x_1098_ = lean_box(2);
v___x_1099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v___x_1097_);
lean_ctor_set(v___x_1099_, 2, v___x_1096_);
v___x_1100_ = l_Lean_Elab_Command_getRef___redArg(v___y_968_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v_fileName_1102_; lean_object* v_fileMap_1103_; lean_object* v_currRecDepth_1104_; lean_object* v_cmdPos_1105_; lean_object* v_macroStack_1106_; lean_object* v_quotContext_x3f_1107_; lean_object* v_currMacroScope_1108_; lean_object* v_snap_x3f_1109_; lean_object* v_cancelTk_x3f_1110_; uint8_t v_suppressElabErrors_1111_; lean_object* v_ref_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1100_, 1);
v_fileName_1102_ = lean_ctor_get(v___y_968_, 0);
v_fileMap_1103_ = lean_ctor_get(v___y_968_, 1);
v_currRecDepth_1104_ = lean_ctor_get(v___y_968_, 2);
v_cmdPos_1105_ = lean_ctor_get(v___y_968_, 3);
v_macroStack_1106_ = lean_ctor_get(v___y_968_, 4);
v_quotContext_x3f_1107_ = lean_ctor_get(v___y_968_, 5);
v_currMacroScope_1108_ = lean_ctor_get(v___y_968_, 6);
v_snap_x3f_1109_ = lean_ctor_get(v___y_968_, 8);
v_cancelTk_x3f_1110_ = lean_ctor_get(v___y_968_, 9);
v_suppressElabErrors_1111_ = lean_ctor_get_uint8(v___y_968_, sizeof(void*)*10);
v_ref_1112_ = l_Lean_replaceRef(v___x_1099_, v_a_1101_);
lean_dec(v_a_1101_);
lean_dec_ref_known(v___x_1099_, 3);
lean_inc(v_cancelTk_x3f_1110_);
lean_inc(v_snap_x3f_1109_);
lean_inc(v_currMacroScope_1108_);
lean_inc(v_quotContext_x3f_1107_);
lean_inc(v_macroStack_1106_);
lean_inc(v_cmdPos_1105_);
lean_inc(v_currRecDepth_1104_);
lean_inc_ref(v_fileMap_1103_);
lean_inc_ref(v_fileName_1102_);
v___x_1113_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1113_, 0, v_fileName_1102_);
lean_ctor_set(v___x_1113_, 1, v_fileMap_1103_);
lean_ctor_set(v___x_1113_, 2, v_currRecDepth_1104_);
lean_ctor_set(v___x_1113_, 3, v_cmdPos_1105_);
lean_ctor_set(v___x_1113_, 4, v_macroStack_1106_);
lean_ctor_set(v___x_1113_, 5, v_quotContext_x3f_1107_);
lean_ctor_set(v___x_1113_, 6, v_currMacroScope_1108_);
lean_ctor_set(v___x_1113_, 7, v_ref_1112_);
lean_ctor_set(v___x_1113_, 8, v_snap_x3f_1109_);
lean_ctor_set(v___x_1113_, 9, v_cancelTk_x3f_1110_);
lean_ctor_set_uint8(v___x_1113_, sizeof(void*)*10, v_suppressElabErrors_1111_);
v___x_1114_ = l_Lean_Elab_Command_getRef___redArg(v___x_1113_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
v___x_1116_ = l_Lean_SourceInfo_fromRef(v_a_1115_, v___x_982_);
lean_dec(v_a_1115_);
v___x_1117_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_1113_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_dec_ref_known(v___x_1117_, 1);
if (lean_obj_tag(v_quotContext_x3f_1107_) == 0)
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_getMainModule___at___00Lean_Elab_Command_mkMacroRulesFun_spec__1___redArg(v___y_967_);
lean_dec_ref(v___x_1118_);
v___y_935_ = v_kind_990_;
v___y_936_ = v___x_1116_;
v___y_937_ = v_attrKind_973_;
v___y_938_ = v___x_982_;
v___y_939_ = v_quotContext_x3f_1107_;
v___y_940_ = v___x_1097_;
v___y_941_ = v_tk_979_;
v___y_942_ = v___y_970_;
v___y_943_ = v___x_1072_;
v___y_944_ = v___y_967_;
v___y_945_ = v___x_1113_;
v___y_946_ = v_attrs_x3f_971_;
v___y_947_ = v___y_969_;
v___y_948_ = v___x_1093_;
v___y_949_ = v___x_974_;
goto v___jp_934_;
}
else
{
v___y_935_ = v_kind_990_;
v___y_936_ = v___x_1116_;
v___y_937_ = v_attrKind_973_;
v___y_938_ = v___x_982_;
v___y_939_ = v_quotContext_x3f_1107_;
v___y_940_ = v___x_1097_;
v___y_941_ = v_tk_979_;
v___y_942_ = v___y_970_;
v___y_943_ = v___x_1072_;
v___y_944_ = v___y_967_;
v___y_945_ = v___x_1113_;
v___y_946_ = v_attrs_x3f_971_;
v___y_947_ = v___y_969_;
v___y_948_ = v___x_1093_;
v___y_949_ = v___x_974_;
goto v___jp_934_;
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v___x_1116_);
lean_dec_ref_known(v___x_1113_, 10);
lean_dec(v___x_1093_);
lean_dec(v___x_1072_);
lean_dec(v_kind_990_);
lean_dec(v_tk_979_);
lean_dec(v_attrKind_973_);
lean_dec(v_attrs_x3f_971_);
lean_dec(v___y_969_);
v_a_1119_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1117_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1117_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1113_, 10);
lean_dec(v___x_1093_);
lean_dec(v___x_1072_);
lean_dec(v_kind_990_);
lean_dec(v_tk_979_);
lean_dec(v_attrKind_973_);
lean_dec(v_attrs_x3f_971_);
lean_dec(v___y_969_);
return v___x_1114_;
}
}
else
{
lean_dec_ref_known(v___x_1099_, 3);
lean_dec(v___x_1093_);
lean_dec(v___x_1072_);
lean_dec(v_kind_990_);
lean_dec(v_tk_979_);
lean_dec(v_attrKind_973_);
lean_dec(v_attrs_x3f_971_);
lean_dec(v___y_969_);
return v___x_1100_;
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
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
lean_dec(v___x_981_);
v___x_1127_ = lean_unsigned_to_nat(5u);
v___x_1128_ = l_Lean_Syntax_getArg(v_stx_807_, v___x_1127_);
lean_dec(v_stx_807_);
v___x_1129_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__6));
lean_inc(v___x_1128_);
v___x_1130_ = l_Lean_Syntax_isOfKind(v___x_1128_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; 
lean_dec(v___x_1128_);
lean_dec(v_tk_979_);
lean_dec(v_attrKind_973_);
lean_dec(v_attrs_x3f_971_);
lean_dec(v___y_969_);
v___x_1131_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_1131_;
}
else
{
lean_object* v___f_1132_; lean_object* v___x_1133_; lean_object* v_alts_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___f_1132_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lam__5___boxed), 15, 10);
lean_closure_set(v___f_1132_, 0, v___x_1129_);
lean_closure_set(v___f_1132_, 1, v___x_814_);
lean_closure_set(v___f_1132_, 2, v_attrKind_973_);
lean_closure_set(v___f_1132_, 3, v___x_813_);
lean_closure_set(v___f_1132_, 4, v___x_882_);
lean_closure_set(v___f_1132_, 5, v_attrs_x3f_971_);
lean_closure_set(v___f_1132_, 6, v___x_811_);
lean_closure_set(v___f_1132_, 7, v___x_812_);
lean_closure_set(v___f_1132_, 8, v___x_974_);
lean_closure_set(v___f_1132_, 9, v___y_969_);
v___x_1133_ = l_Lean_Syntax_getArg(v___x_1128_, v___x_882_);
lean_dec(v___x_1128_);
v_alts_1134_ = l_Lean_Syntax_getArgs(v___x_1133_);
lean_dec(v___x_1133_);
v___x_1135_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__8));
v___x_1136_ = lean_box(2);
lean_inc_ref(v_alts_1134_);
v___x_1137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v___x_1135_);
lean_ctor_set(v___x_1137_, 2, v_alts_1134_);
v___x_1138_ = lean_mk_empty_array_with_capacity(v___x_972_);
v___x_1139_ = lean_array_push(v___x_1138_, v_tk_979_);
v___x_1140_ = lean_array_push(v___x_1139_, v___x_1137_);
v___x_1141_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1136_);
lean_ctor_set(v___x_1141_, 1, v___x_1135_);
lean_ctor_set(v___x_1141_, 2, v___x_1140_);
v___x_1142_ = l_Lean_Elab_Command_getRef___redArg(v___y_968_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v_fileName_1144_; lean_object* v_fileMap_1145_; lean_object* v_currRecDepth_1146_; lean_object* v_cmdPos_1147_; lean_object* v_macroStack_1148_; lean_object* v_quotContext_x3f_1149_; lean_object* v_currMacroScope_1150_; lean_object* v_snap_x3f_1151_; lean_object* v_cancelTk_x3f_1152_; uint8_t v_suppressElabErrors_1153_; lean_object* v_ref_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1142_, 1);
v_fileName_1144_ = lean_ctor_get(v___y_968_, 0);
v_fileMap_1145_ = lean_ctor_get(v___y_968_, 1);
v_currRecDepth_1146_ = lean_ctor_get(v___y_968_, 2);
v_cmdPos_1147_ = lean_ctor_get(v___y_968_, 3);
v_macroStack_1148_ = lean_ctor_get(v___y_968_, 4);
v_quotContext_x3f_1149_ = lean_ctor_get(v___y_968_, 5);
v_currMacroScope_1150_ = lean_ctor_get(v___y_968_, 6);
v_snap_x3f_1151_ = lean_ctor_get(v___y_968_, 8);
v_cancelTk_x3f_1152_ = lean_ctor_get(v___y_968_, 9);
v_suppressElabErrors_1153_ = lean_ctor_get_uint8(v___y_968_, sizeof(void*)*10);
v_ref_1154_ = l_Lean_replaceRef(v___x_1141_, v_a_1143_);
lean_dec(v_a_1143_);
lean_dec_ref_known(v___x_1141_, 3);
lean_inc(v_cancelTk_x3f_1152_);
lean_inc(v_snap_x3f_1151_);
lean_inc(v_currMacroScope_1150_);
lean_inc(v_quotContext_x3f_1149_);
lean_inc(v_macroStack_1148_);
lean_inc(v_cmdPos_1147_);
lean_inc(v_currRecDepth_1146_);
lean_inc_ref(v_fileMap_1145_);
lean_inc_ref(v_fileName_1144_);
v___x_1155_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1155_, 0, v_fileName_1144_);
lean_ctor_set(v___x_1155_, 1, v_fileMap_1145_);
lean_ctor_set(v___x_1155_, 2, v_currRecDepth_1146_);
lean_ctor_set(v___x_1155_, 3, v_cmdPos_1147_);
lean_ctor_set(v___x_1155_, 4, v_macroStack_1148_);
lean_ctor_set(v___x_1155_, 5, v_quotContext_x3f_1149_);
lean_ctor_set(v___x_1155_, 6, v_currMacroScope_1150_);
lean_ctor_set(v___x_1155_, 7, v_ref_1154_);
lean_ctor_set(v___x_1155_, 8, v_snap_x3f_1151_);
lean_ctor_set(v___x_1155_, 9, v_cancelTk_x3f_1152_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*10, v_suppressElabErrors_1153_);
v___x_1156_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(v_alts_1134_, v___x_813_, v___f_1132_, v___x_1155_, v___y_967_);
lean_dec_ref_known(v___x_1155_, 10);
lean_dec_ref(v_alts_1134_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v_a_1165_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1156_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1156_);
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
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1141_, 3);
lean_dec_ref(v_alts_1134_);
lean_dec_ref(v___f_1132_);
return v___x_1142_;
}
}
}
}
}
v___jp_1173_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1177_ = lean_unsigned_to_nat(1u);
v___x_1178_ = l_Lean_Syntax_getArg(v_stx_807_, v___x_1177_);
v___x_1179_ = l_Lean_Syntax_isNone(v___x_1178_);
if (v___x_1179_ == 0)
{
uint8_t v___x_1180_; 
lean_inc(v___x_1178_);
v___x_1180_ = l_Lean_Syntax_matchesNull(v___x_1178_, v___x_1177_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; 
lean_dec(v___x_1178_);
lean_dec(v_doc_x3f_1174_);
lean_dec(v_stx_807_);
v___x_1181_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_1181_;
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1182_ = l_Lean_Syntax_getArg(v___x_1178_, v___x_882_);
lean_dec(v___x_1178_);
v___x_1183_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13));
lean_inc(v___x_1182_);
v___x_1184_ = l_Lean_Syntax_isOfKind(v___x_1182_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; 
lean_dec(v___x_1182_);
lean_dec(v_doc_x3f_1174_);
lean_dec(v_stx_807_);
v___x_1185_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg();
return v___x_1185_;
}
else
{
lean_object* v___x_1186_; lean_object* v_attrs_x3f_1187_; lean_object* v___x_1188_; 
v___x_1186_ = l_Lean_Syntax_getArg(v___x_1182_, v___x_1177_);
lean_dec(v___x_1182_);
v_attrs_x3f_1187_ = l_Lean_Syntax_getArgs(v___x_1186_);
lean_dec(v___x_1186_);
v___x_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1188_, 0, v_attrs_x3f_1187_);
v___y_967_ = v___y_1176_;
v___y_968_ = v___y_1175_;
v___y_969_ = v_doc_x3f_1174_;
v___y_970_ = v___x_1177_;
v_attrs_x3f_971_ = v___x_1188_;
goto v___jp_966_;
}
}
}
else
{
lean_object* v___x_1189_; 
lean_dec(v___x_1178_);
v___x_1189_ = lean_box(0);
v___y_967_ = v___y_1176_;
v___y_968_ = v___y_1175_;
v___y_969_ = v_doc_x3f_1174_;
v___y_970_ = v___x_1177_;
v_attrs_x3f_971_ = v___x_1189_;
goto v___jp_966_;
}
}
}
v___jp_816_:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
lean_inc_ref_n(v___y_818_, 3);
v___x_832_ = l_Array_append___redArg(v___y_818_, v___y_831_);
lean_dec_ref(v___y_831_);
lean_inc_n(v___y_822_, 6);
lean_inc_n(v___y_825_, 17);
v___x_833_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_833_, 0, v___y_825_);
lean_ctor_set(v___x_833_, 1, v___y_822_);
lean_ctor_set(v___x_833_, 2, v___x_832_);
v___x_834_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__1));
lean_inc_ref_n(v___y_829_, 2);
v___x_835_ = l_Lean_Name_mkStr4(v___x_811_, v___x_812_, v___y_829_, v___x_834_);
v___x_836_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__2));
v___x_837_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_837_, 0, v___y_825_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = l_Array_append___redArg(v___y_818_, v___y_827_);
lean_dec_ref(v___y_827_);
v___x_839_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_839_, 0, v___y_825_);
lean_ctor_set(v___x_839_, 1, v___y_822_);
lean_ctor_set(v___x_839_, 2, v___x_838_);
v___x_840_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__3));
v___x_841_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_841_, 0, v___y_825_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = l_Lean_Syntax_node3(v___y_825_, v___x_835_, v___x_837_, v___x_839_, v___x_841_);
v___x_843_ = l_Lean_Syntax_node1(v___y_825_, v___y_822_, v___x_842_);
lean_inc_ref(v___y_823_);
v___x_844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_844_, 0, v___y_825_);
lean_ctor_set(v___x_844_, 1, v___y_823_);
v___x_845_ = l_Lean_TSyntax_getId(v___y_819_);
v___x_846_ = l_Lean_mkIdentFrom(v___y_824_, v___x_845_, v___x_815_);
lean_dec(v___y_824_);
v___x_847_ = l_Lean_Syntax_node2(v___y_825_, v___y_822_, v___x_846_, v___y_819_);
v___x_848_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__7));
v___x_849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_849_, 0, v___y_825_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = lean_obj_once(&l_Lean_Elab_Command_elabMacroRulesAux___closed__8, &l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once, _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8);
v___x_851_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__9));
v___x_852_ = l_Lean_addMacroScope(v___y_820_, v___x_851_, v___y_830_);
v___x_853_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__5));
v___x_854_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_854_, 0, v___y_825_);
lean_ctor_set(v___x_854_, 1, v___x_850_);
lean_ctor_set(v___x_854_, 2, v___x_852_);
lean_ctor_set(v___x_854_, 3, v___x_853_);
v___x_855_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRulesAux___closed__10));
v___x_856_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_856_, 0, v___y_825_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__3));
v___x_858_ = l_Lean_Name_mkStr4(v___x_811_, v___x_812_, v___y_829_, v___x_857_);
v___x_859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_859_, 0, v___y_825_);
lean_ctor_set(v___x_859_, 1, v___x_857_);
v___x_860_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6));
v___x_861_ = l_Lean_Name_mkStr4(v___x_811_, v___x_812_, v___y_829_, v___x_860_);
v___x_862_ = l_Lean_Syntax_node1(v___y_825_, v___y_822_, v___y_826_);
v___x_863_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_863_, 0, v___y_825_);
lean_ctor_set(v___x_863_, 1, v___y_822_);
lean_ctor_set(v___x_863_, 2, v___y_818_);
v___x_864_ = ((lean_object*)(l_Lean_Elab_Command_mkMacroRulesFun___closed__16));
v___x_865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_865_, 0, v___y_825_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = l_Lean_Syntax_node4(v___y_825_, v___x_861_, v___x_862_, v___x_863_, v___x_865_, v___y_828_);
v___x_867_ = l_Lean_Syntax_node2(v___y_825_, v___x_858_, v___x_859_, v___x_866_);
v___x_868_ = lean_unsigned_to_nat(9u);
v___x_869_ = lean_mk_empty_array_with_capacity(v___x_868_);
v___x_870_ = lean_array_push(v___x_869_, v___x_833_);
v___x_871_ = lean_array_push(v___x_870_, v___x_843_);
v___x_872_ = lean_array_push(v___x_871_, v___y_821_);
v___x_873_ = lean_array_push(v___x_872_, v___x_844_);
v___x_874_ = lean_array_push(v___x_873_, v___x_847_);
v___x_875_ = lean_array_push(v___x_874_, v___x_849_);
v___x_876_ = lean_array_push(v___x_875_, v___x_854_);
v___x_877_ = lean_array_push(v___x_876_, v___x_856_);
v___x_878_ = lean_array_push(v___x_877_, v___x_867_);
lean_inc(v___y_817_);
v___x_879_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_879_, 0, v___y_825_);
lean_ctor_set(v___x_879_, 1, v___y_817_);
lean_ctor_set(v___x_879_, 2, v___x_878_);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lam__1___boxed(lean_object* v_stx_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Elab_Command_elabMacroRules___lam__1(v_stx_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules(lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v___f_1211_; lean_object* v___x_1212_; 
v___f_1211_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___closed__0));
v___x_1212_ = l_Lean_Elab_Command_adaptExpander(v___f_1211_, v_a_1207_, v_a_1208_, v_a_1209_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___boxed(lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_Elab_Command_elabMacroRules(v_a_1213_, v_a_1214_, v_a_1215_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1(){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1225_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1226_ = ((lean_object*)(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0));
v___x_1227_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1));
v___x_1228_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___boxed), 4, 0);
v___x_1229_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1225_, v___x_1226_, v___x_1227_, v___x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___boxed(lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1();
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3(){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1));
v___x_1259_ = ((lean_object*)(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6));
v___x_1260_ = l_Lean_addBuiltinDeclarationRanges(v___x_1258_, v___x_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___boxed(lean_object* v_a_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3();
return v_res_1262_;
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
