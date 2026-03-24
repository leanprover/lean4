// Lean compiler output
// Module: Lake.DSL.Script
// Imports: public import Init.Prelude import Lake.Config.Package import Lake.DSL.Attributes import Lake.DSL.Syntax
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
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lake_DSL_expandOptSimpleBinder(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_DSL_expandIdentOrStrAsIdent(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lake_DSL_expandAttrs(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scriptDecl"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__2 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3_value_aux_0),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3_value_aux_1),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(131, 18, 40, 229, 14, 216, 222, 158)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "ill-formed script declaration"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__5 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__5_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__6 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__6_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__7 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__7_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__8 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__8_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__9 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__9_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__10 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__10_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__11 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__11_value;
static const lean_array_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__13 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__13_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__14 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__14_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__15 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__15_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ScriptFn"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16_value;
static lean_once_cell_t l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16_value),LEAN_SCALAR_PTR_LITERAL(165, 12, 188, 107, 238, 45, 212, 138)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__18 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__18_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__19_value_aux_0),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16_value),LEAN_SCALAR_PTR_LITERAL(233, 20, 53, 85, 81, 66, 33, 235)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__19 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__19_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__20 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__20_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__22 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__22_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__23 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__23_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__24 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__24_value;
static const lean_array_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__27 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__27_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__28 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__28_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__29 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__29_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__29_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30_value;
static lean_once_cell_t l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 8, .m_data = "«script»"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__34 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__34_value;
static lean_once_cell_t l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "script"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__36 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__36_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__36_value),LEAN_SCALAR_PTR_LITERAL(148, 36, 101, 0, 21, 164, 81, 12)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__37 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__37_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__38 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__38_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__39 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__39_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__41 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__41_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__42 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__42_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__43 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__43_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "declValDo"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__44 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__44_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45_value_aux_0),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45_value_aux_1),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__44_value),LEAN_SCALAR_PTR_LITERAL(253, 210, 120, 194, 116, 135, 247, 152)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value_aux_0),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value_aux_1),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value_aux_2),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__41_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value_aux_0),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value_aux_1),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__42_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value_aux_2),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__43_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "whereDecls"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__50 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__50_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value_aux_0),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value_aux_1),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value_aux_2),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__50_value),LEAN_SCALAR_PTR_LITERAL(51, 156, 180, 247, 37, 30, 126, 62)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__52 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__52_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value_aux_0),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value_aux_1),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value_aux_2),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__52_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "scriptDeclSpec"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__54 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__54_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55_value_aux_0),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 13, 75, 143, 104, 166, 231, 81)}};
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55_value_aux_1),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__54_value),LEAN_SCALAR_PTR_LITERAL(106, 145, 50, 108, 63, 62, 118, 110)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__1 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__1_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__1_value),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 223, 152, 205, 91, 21, 95, 180)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__2 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__2_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__2_value),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(20, 230, 244, 102, 183, 225, 161, 156)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__3 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__3_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Script"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__4 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__4_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__3_value),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 177, 130, 119, 20, 187, 87)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__5 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__5_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(149, 105, 124, 53, 231, 234, 215, 21)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__6 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__6_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__6_value),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 83, 187, 127, 129, 64, 205, 210)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__7 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__7_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__7_value),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(22, 30, 50, 150, 17, 15, 93, 22)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__8 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__8_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "expandScriptDecl"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__9 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__9_value;
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__8_value),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(229, 166, 205, 152, 227, 63, 7, 154)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__10 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___boxed(lean_object*);
static lean_object* _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16));
v___x_23_ = l_String_toRawSubstring_x27(v___x_22_);
return v___x_23_;
}
}
static lean_object* _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31(void){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Array_mkArray0(lean_box(0));
return v___x_44_;
}
}
static lean_object* _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__34));
v___x_49_ = l_String_toRawSubstring_x27(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl(lean_object* v_x_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v___y_97_; lean_object* v___y_98_; lean_object* v___y_99_; lean_object* v___y_100_; lean_object* v___y_101_; lean_object* v___y_102_; lean_object* v___y_103_; lean_object* v___y_104_; lean_object* v___y_105_; lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v___x_119_; lean_object* v___y_121_; lean_object* v___y_122_; lean_object* v___y_123_; lean_object* v___y_124_; lean_object* v___y_125_; lean_object* v___y_126_; lean_object* v___y_127_; lean_object* v___y_128_; lean_object* v___y_129_; lean_object* v___y_130_; lean_object* v___y_131_; lean_object* v___y_132_; lean_object* v___y_133_; lean_object* v___y_134_; lean_object* v___y_135_; uint8_t v___x_142_; 
v___x_119_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3));
lean_inc(v_x_93_);
v___x_142_ = l_Lean_Syntax_isOfKind(v_x_93_, v___x_119_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_144_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_143_, v_a_94_, v_a_95_);
lean_dec(v_x_93_);
return v___x_144_;
}
else
{
lean_object* v___x_145_; lean_object* v___y_147_; lean_object* v___y_148_; lean_object* v___y_149_; lean_object* v___y_150_; lean_object* v___y_151_; lean_object* v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v___y_161_; lean_object* v___y_162_; lean_object* v___y_163_; lean_object* v___y_164_; lean_object* v___y_165_; lean_object* v___y_166_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___y_230_; uint8_t v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v_wds_x3f_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v_wds_x3f_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v_args_x3f_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v_attrs_x3f_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v_doc_x3f_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_509_ = l_Lean_Syntax_getArg(v_x_93_, v___x_145_);
v___x_510_ = l_Lean_Syntax_isNone(v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_509_);
v___x_512_ = l_Lean_Syntax_matchesNull(v___x_509_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v___x_509_);
v___x_513_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_514_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_513_, v_a_94_, v_a_95_);
lean_dec(v_x_93_);
return v___x_514_;
}
else
{
lean_object* v_doc_x3f_515_; lean_object* v___x_516_; 
v_doc_x3f_515_ = l_Lean_Syntax_getArg(v___x_509_, v___x_145_);
lean_dec(v___x_509_);
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v_doc_x3f_515_);
v_doc_x3f_497_ = v___x_516_;
v___y_498_ = v_a_94_;
v___y_499_ = v_a_95_;
goto v___jp_496_;
}
}
else
{
lean_object* v___x_517_; 
lean_dec(v___x_509_);
v___x_517_ = lean_box(0);
v_doc_x3f_497_ = v___x_517_;
v___y_498_ = v_a_94_;
v___y_499_ = v_a_95_;
goto v___jp_496_;
}
v___jp_146_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
lean_inc_ref(v___y_161_);
v___x_170_ = l_Array_append___redArg(v___y_161_, v___y_169_);
lean_dec_ref(v___y_169_);
lean_inc(v___y_148_);
lean_inc(v___y_149_);
v___x_171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_171_, 0, v___y_149_);
lean_ctor_set(v___x_171_, 1, v___y_148_);
lean_ctor_set(v___x_171_, 2, v___x_170_);
v___x_172_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__5));
lean_inc_ref(v___y_155_);
lean_inc_ref(v___y_166_);
lean_inc_ref(v___y_167_);
v___x_173_ = l_Lean_Name_mkStr4(v___y_167_, v___y_166_, v___y_155_, v___x_172_);
v___x_174_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__6));
lean_inc(v___y_149_);
v___x_175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_175_, 0, v___y_149_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
v___x_176_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__7));
v___x_177_ = l_Lean_Syntax_SepArray_ofElems(v___x_176_, v___y_165_);
lean_dec_ref(v___y_165_);
lean_inc_ref(v___y_161_);
v___x_178_ = l_Array_append___redArg(v___y_161_, v___x_177_);
lean_dec_ref(v___x_177_);
lean_inc(v___y_148_);
lean_inc(v___y_149_);
v___x_179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_179_, 0, v___y_149_);
lean_ctor_set(v___x_179_, 1, v___y_148_);
lean_ctor_set(v___x_179_, 2, v___x_178_);
v___x_180_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__8));
lean_inc(v___y_149_);
v___x_181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_181_, 0, v___y_149_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
lean_inc(v___y_149_);
v___x_182_ = l_Lean_Syntax_node3(v___y_149_, v___x_173_, v___x_175_, v___x_179_, v___x_181_);
lean_inc(v___y_148_);
lean_inc(v___y_149_);
v___x_183_ = l_Lean_Syntax_node1(v___y_149_, v___y_148_, v___x_182_);
lean_inc_n(v___y_151_, 5);
lean_inc(v___y_149_);
v___x_184_ = l_Lean_Syntax_node7(v___y_149_, v___y_168_, v___x_171_, v___x_183_, v___y_151_, v___y_151_, v___y_151_, v___y_151_, v___y_151_);
v___x_185_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__9));
lean_inc_ref(v___y_156_);
lean_inc_ref(v___y_166_);
lean_inc_ref(v___y_167_);
v___x_186_ = l_Lean_Name_mkStr4(v___y_167_, v___y_166_, v___y_156_, v___x_185_);
v___x_187_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__10));
lean_inc(v___y_149_);
v___x_188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_188_, 0, v___y_149_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__11));
lean_inc_ref(v___y_156_);
lean_inc_ref(v___y_166_);
lean_inc_ref(v___y_167_);
v___x_190_ = l_Lean_Name_mkStr4(v___y_167_, v___y_166_, v___y_156_, v___x_189_);
v___x_191_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12));
v___x_192_ = lean_box(2);
lean_inc(v___y_148_);
v___x_193_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v___y_148_);
lean_ctor_set(v___x_193_, 2, v___x_191_);
v___x_194_ = lean_mk_empty_array_with_capacity(v___y_163_);
v___x_195_ = lean_array_push(v___x_194_, v___y_162_);
v___x_196_ = lean_array_push(v___x_195_, v___x_193_);
v___x_197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_197_, 0, v___x_192_);
lean_ctor_set(v___x_197_, 1, v___x_190_);
lean_ctor_set(v___x_197_, 2, v___x_196_);
v___x_198_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__13));
lean_inc_ref(v___y_166_);
lean_inc_ref(v___y_167_);
v___x_199_ = l_Lean_Name_mkStr4(v___y_167_, v___y_166_, v___y_156_, v___x_198_);
v___x_200_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__14));
lean_inc_ref(v___y_155_);
lean_inc_ref(v___y_166_);
lean_inc_ref(v___y_167_);
v___x_201_ = l_Lean_Name_mkStr4(v___y_167_, v___y_166_, v___y_155_, v___x_200_);
v___x_202_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__15));
lean_inc(v___y_149_);
v___x_203_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_203_, 0, v___y_149_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = lean_obj_once(&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17, &l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17_once, _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17);
v___x_205_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__18));
v___x_206_ = l_Lean_addMacroScope(v___y_150_, v___x_205_, v___y_154_);
v___x_207_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__20));
v___x_208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___y_164_);
lean_inc(v___y_149_);
v___x_209_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_209_, 0, v___y_149_);
lean_ctor_set(v___x_209_, 1, v___x_204_);
lean_ctor_set(v___x_209_, 2, v___x_206_);
lean_ctor_set(v___x_209_, 3, v___x_208_);
lean_inc(v___y_149_);
v___x_210_ = l_Lean_Syntax_node2(v___y_149_, v___x_201_, v___x_203_, v___x_209_);
lean_inc(v___y_148_);
lean_inc(v___y_149_);
v___x_211_ = l_Lean_Syntax_node1(v___y_149_, v___y_148_, v___x_210_);
lean_inc(v___y_151_);
lean_inc(v___y_149_);
v___x_212_ = l_Lean_Syntax_node2(v___y_149_, v___x_199_, v___y_151_, v___x_211_);
v___x_213_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21));
lean_inc(v___y_149_);
v___x_214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_214_, 0, v___y_149_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__22));
lean_inc_ref(v___y_155_);
lean_inc_ref(v___y_166_);
lean_inc_ref(v___y_167_);
v___x_216_ = l_Lean_Name_mkStr4(v___y_167_, v___y_166_, v___y_155_, v___x_215_);
lean_inc(v___y_149_);
v___x_217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_217_, 0, v___y_149_);
lean_ctor_set(v___x_217_, 1, v___x_215_);
v___x_218_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__23));
v___x_219_ = l_Lean_Name_mkStr4(v___y_167_, v___y_166_, v___y_155_, v___x_218_);
lean_inc(v___y_148_);
lean_inc(v___y_149_);
v___x_220_ = l_Lean_Syntax_node1(v___y_149_, v___y_148_, v___y_153_);
v___x_221_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__24));
lean_inc(v___y_149_);
v___x_222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_222_, 0, v___y_149_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
lean_inc(v___y_151_);
lean_inc(v___y_149_);
v___x_223_ = l_Lean_Syntax_node4(v___y_149_, v___x_219_, v___x_220_, v___y_151_, v___x_222_, v___y_159_);
lean_inc(v___y_149_);
v___x_224_ = l_Lean_Syntax_node2(v___y_149_, v___x_216_, v___x_217_, v___x_223_);
lean_inc_n(v___y_151_, 2);
lean_inc(v___y_149_);
v___x_225_ = l_Lean_Syntax_node2(v___y_149_, v___y_147_, v___y_151_, v___y_151_);
if (lean_obj_tag(v___y_157_) == 1)
{
lean_object* v_val_226_; lean_object* v___x_227_; 
v_val_226_ = lean_ctor_get(v___y_157_, 0);
lean_inc(v_val_226_);
lean_dec_ref(v___y_157_);
v___x_227_ = l_Array_mkArray1___redArg(v_val_226_);
v___y_97_ = v___x_184_;
v___y_98_ = v___y_148_;
v___y_99_ = v___x_225_;
v___y_100_ = v___x_214_;
v___y_101_ = v___y_149_;
v___y_102_ = v___y_151_;
v___y_103_ = v___y_152_;
v___y_104_ = v___x_197_;
v___y_105_ = v___x_224_;
v___y_106_ = v___x_212_;
v___y_107_ = v___y_158_;
v___y_108_ = v___y_160_;
v___y_109_ = v___y_161_;
v___y_110_ = v___x_188_;
v___y_111_ = v___x_186_;
v___y_112_ = v___x_227_;
goto v___jp_96_;
}
else
{
lean_object* v___x_228_; 
lean_dec(v___y_157_);
v___x_228_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25));
v___y_97_ = v___x_184_;
v___y_98_ = v___y_148_;
v___y_99_ = v___x_225_;
v___y_100_ = v___x_214_;
v___y_101_ = v___y_149_;
v___y_102_ = v___y_151_;
v___y_103_ = v___y_152_;
v___y_104_ = v___x_197_;
v___y_105_ = v___x_224_;
v___y_106_ = v___x_212_;
v___y_107_ = v___y_158_;
v___y_108_ = v___y_160_;
v___y_109_ = v___y_161_;
v___y_110_ = v___x_188_;
v___y_111_ = v___x_186_;
v___y_112_ = v___x_228_;
goto v___jp_96_;
}
}
v___jp_229_:
{
lean_object* v_methods_247_; lean_object* v_quotContext_248_; lean_object* v_currMacroScope_249_; lean_object* v_currRecDepth_250_; lean_object* v_maxRecDepth_251_; lean_object* v_ref_252_; lean_object* v_ref_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v_methods_247_ = lean_ctor_get(v___y_245_, 0);
lean_inc(v_methods_247_);
v_quotContext_248_ = lean_ctor_get(v___y_245_, 1);
lean_inc(v_quotContext_248_);
v_currMacroScope_249_ = lean_ctor_get(v___y_245_, 2);
lean_inc(v_currMacroScope_249_);
v_currRecDepth_250_ = lean_ctor_get(v___y_245_, 3);
lean_inc(v_currRecDepth_250_);
v_maxRecDepth_251_ = lean_ctor_get(v___y_245_, 4);
lean_inc(v_maxRecDepth_251_);
v_ref_252_ = lean_ctor_get(v___y_245_, 5);
lean_inc(v_ref_252_);
lean_dec_ref(v___y_245_);
v_ref_253_ = l_Lean_replaceRef(v___y_240_, v_ref_252_);
lean_dec(v_ref_252_);
lean_dec(v___y_240_);
lean_inc(v_ref_253_);
lean_inc(v_currMacroScope_249_);
lean_inc(v_quotContext_248_);
v___x_254_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_254_, 0, v_methods_247_);
lean_ctor_set(v___x_254_, 1, v_quotContext_248_);
lean_ctor_set(v___x_254_, 2, v_currMacroScope_249_);
lean_ctor_set(v___x_254_, 3, v_currRecDepth_250_);
lean_ctor_set(v___x_254_, 4, v_maxRecDepth_251_);
lean_ctor_set(v___x_254_, 5, v_ref_253_);
v___x_255_ = l_Lake_DSL_expandOptSimpleBinder(v___y_230_, v___x_254_, v___y_246_);
lean_dec_ref(v___x_254_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v_a_257_; lean_object* v_id_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
v_a_257_ = lean_ctor_get(v___x_255_, 1);
lean_inc(v_a_257_);
lean_dec_ref(v___x_255_);
v_id_258_ = l_Lake_DSL_expandIdentOrStrAsIdent(v___y_233_);
v___x_259_ = l_Lean_SourceInfo_fromRef(v_ref_253_, v___y_231_);
lean_dec(v_ref_253_);
v___x_260_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26));
v___x_261_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__27));
lean_inc_ref(v___y_242_);
lean_inc_ref(v___y_243_);
v___x_262_ = l_Lean_Name_mkStr4(v___y_243_, v___y_242_, v___x_260_, v___x_261_);
v___x_263_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__28));
lean_inc_ref(v___y_242_);
lean_inc_ref(v___y_243_);
v___x_264_ = l_Lean_Name_mkStr4(v___y_243_, v___y_242_, v___x_260_, v___x_263_);
v___x_265_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30));
v___x_266_ = lean_obj_once(&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31, &l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31_once, _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31);
lean_inc(v___x_259_);
v___x_267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_267_, 0, v___x_259_);
lean_ctor_set(v___x_267_, 1, v___x_265_);
lean_ctor_set(v___x_267_, 2, v___x_266_);
lean_inc_ref(v___x_267_);
lean_inc(v___x_259_);
v___x_268_ = l_Lean_Syntax_node1(v___x_259_, v___x_264_, v___x_267_);
v___x_269_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32));
v___x_270_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33));
lean_inc_ref(v___y_242_);
lean_inc_ref(v___y_243_);
v___x_271_ = l_Lean_Name_mkStr4(v___y_243_, v___y_242_, v___x_269_, v___x_270_);
v___x_272_ = lean_obj_once(&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35, &l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35_once, _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35);
v___x_273_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__37));
lean_inc(v_currMacroScope_249_);
lean_inc(v_quotContext_248_);
v___x_274_ = l_Lean_addMacroScope(v_quotContext_248_, v___x_273_, v_currMacroScope_249_);
v___x_275_ = lean_box(0);
lean_inc(v___x_259_);
v___x_276_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_276_, 0, v___x_259_);
lean_ctor_set(v___x_276_, 1, v___x_272_);
lean_ctor_set(v___x_276_, 2, v___x_274_);
lean_ctor_set(v___x_276_, 3, v___x_275_);
lean_inc_ref(v___x_267_);
lean_inc(v___x_259_);
v___x_277_ = l_Lean_Syntax_node2(v___x_259_, v___x_271_, v___x_276_, v___x_267_);
lean_inc(v___x_259_);
v___x_278_ = l_Lean_Syntax_node2(v___x_259_, v___x_262_, v___x_268_, v___x_277_);
v___x_279_ = lean_mk_empty_array_with_capacity(v___y_241_);
v___x_280_ = lean_array_push(v___x_279_, v___x_278_);
v___x_281_ = l_Lake_DSL_expandAttrs(v___y_236_);
v___x_282_ = l_Array_append___redArg(v___x_280_, v___x_281_);
lean_dec_ref(v___x_281_);
v___x_283_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__38));
lean_inc_ref(v___y_235_);
lean_inc_ref(v___y_242_);
lean_inc_ref(v___y_243_);
v___x_284_ = l_Lean_Name_mkStr4(v___y_243_, v___y_242_, v___y_235_, v___x_283_);
v___x_285_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__39));
lean_inc_ref(v___y_235_);
lean_inc_ref(v___y_242_);
lean_inc_ref(v___y_243_);
v___x_286_ = l_Lean_Name_mkStr4(v___y_243_, v___y_242_, v___y_235_, v___x_285_);
if (lean_obj_tag(v___y_238_) == 1)
{
lean_object* v_val_287_; lean_object* v___x_288_; 
v_val_287_ = lean_ctor_get(v___y_238_, 0);
lean_inc(v_val_287_);
lean_dec_ref(v___y_238_);
v___x_288_ = l_Array_mkArray1___redArg(v_val_287_);
v___y_147_ = v___y_232_;
v___y_148_ = v___x_265_;
v___y_149_ = v___x_259_;
v___y_150_ = v_quotContext_248_;
v___y_151_ = v___x_267_;
v___y_152_ = v___y_234_;
v___y_153_ = v_a_256_;
v___y_154_ = v_currMacroScope_249_;
v___y_155_ = v___x_260_;
v___y_156_ = v___y_235_;
v___y_157_ = v_wds_x3f_244_;
v___y_158_ = v___x_284_;
v___y_159_ = v___y_237_;
v___y_160_ = v_a_257_;
v___y_161_ = v___x_266_;
v___y_162_ = v_id_258_;
v___y_163_ = v___y_239_;
v___y_164_ = v___x_275_;
v___y_165_ = v___x_282_;
v___y_166_ = v___y_242_;
v___y_167_ = v___y_243_;
v___y_168_ = v___x_286_;
v___y_169_ = v___x_288_;
goto v___jp_146_;
}
else
{
lean_object* v___x_289_; 
lean_dec(v___y_238_);
v___x_289_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25));
v___y_147_ = v___y_232_;
v___y_148_ = v___x_265_;
v___y_149_ = v___x_259_;
v___y_150_ = v_quotContext_248_;
v___y_151_ = v___x_267_;
v___y_152_ = v___y_234_;
v___y_153_ = v_a_256_;
v___y_154_ = v_currMacroScope_249_;
v___y_155_ = v___x_260_;
v___y_156_ = v___y_235_;
v___y_157_ = v_wds_x3f_244_;
v___y_158_ = v___x_284_;
v___y_159_ = v___y_237_;
v___y_160_ = v_a_257_;
v___y_161_ = v___x_266_;
v___y_162_ = v_id_258_;
v___y_163_ = v___y_239_;
v___y_164_ = v___x_275_;
v___y_165_ = v___x_282_;
v___y_166_ = v___y_242_;
v___y_167_ = v___y_243_;
v___y_168_ = v___x_286_;
v___y_169_ = v___x_289_;
goto v___jp_146_;
}
}
else
{
lean_object* v_a_290_; lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec(v_ref_253_);
lean_dec(v_currMacroScope_249_);
lean_dec(v_quotContext_248_);
lean_dec(v_wds_x3f_244_);
lean_dec_ref(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_238_);
lean_dec(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec(v___y_233_);
lean_dec(v___y_232_);
v_a_290_ = lean_ctor_get(v___x_255_, 0);
v_a_291_ = lean_ctor_get(v___x_255_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_255_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_inc(v_a_290_);
lean_dec(v___x_255_);
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
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_290_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_a_291_);
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
v___jp_299_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_inc_ref(v___y_307_);
v___x_316_ = l_Array_append___redArg(v___y_307_, v___y_315_);
lean_dec_ref(v___y_315_);
lean_inc(v___y_301_);
lean_inc(v___y_303_);
v___x_317_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_317_, 0, v___y_303_);
lean_ctor_set(v___x_317_, 1, v___y_301_);
lean_ctor_set(v___x_317_, 2, v___x_316_);
v___x_318_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40));
v___x_319_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__41));
lean_inc_ref(v___y_311_);
lean_inc_ref(v___y_312_);
v___x_320_ = l_Lean_Name_mkStr4(v___y_312_, v___y_311_, v___x_318_, v___x_319_);
v___x_321_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21));
lean_inc(v___y_303_);
v___x_322_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_322_, 0, v___y_303_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
lean_inc(v___y_303_);
v___x_323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_323_, 0, v___y_303_);
lean_ctor_set(v___x_323_, 1, v___y_314_);
lean_inc(v___y_303_);
v___x_324_ = l_Lean_Syntax_node2(v___y_303_, v___y_310_, v___x_323_, v___y_302_);
v___x_325_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__42));
v___x_326_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__43));
v___x_327_ = l_Lean_Name_mkStr4(v___y_312_, v___y_311_, v___x_325_, v___x_326_);
lean_inc_ref(v___y_307_);
lean_inc(v___y_301_);
lean_inc(v___y_303_);
v___x_328_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_328_, 0, v___y_303_);
lean_ctor_set(v___x_328_, 1, v___y_301_);
lean_ctor_set(v___x_328_, 2, v___y_307_);
lean_inc_ref(v___x_328_);
lean_inc(v___y_303_);
v___x_329_ = l_Lean_Syntax_node2(v___y_303_, v___x_327_, v___x_328_, v___x_328_);
if (lean_obj_tag(v___y_300_) == 1)
{
lean_object* v_val_330_; lean_object* v___x_331_; 
v_val_330_ = lean_ctor_get(v___y_300_, 0);
lean_inc(v_val_330_);
lean_dec_ref(v___y_300_);
v___x_331_ = l_Array_mkArray1___redArg(v_val_330_);
v___y_121_ = v___y_301_;
v___y_122_ = v___y_303_;
v___y_123_ = v___x_322_;
v___y_124_ = v___y_304_;
v___y_125_ = v___y_305_;
v___y_126_ = v___y_306_;
v___y_127_ = v___y_307_;
v___y_128_ = v___x_324_;
v___y_129_ = v___x_329_;
v___y_130_ = v___x_317_;
v___y_131_ = v___y_308_;
v___y_132_ = v___y_309_;
v___y_133_ = v___x_320_;
v___y_134_ = v___y_313_;
v___y_135_ = v___x_331_;
goto v___jp_120_;
}
else
{
lean_object* v___x_332_; 
lean_dec(v___y_300_);
v___x_332_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25));
v___y_121_ = v___y_301_;
v___y_122_ = v___y_303_;
v___y_123_ = v___x_322_;
v___y_124_ = v___y_304_;
v___y_125_ = v___y_305_;
v___y_126_ = v___y_306_;
v___y_127_ = v___y_307_;
v___y_128_ = v___x_324_;
v___y_129_ = v___x_329_;
v___y_130_ = v___x_317_;
v___y_131_ = v___y_308_;
v___y_132_ = v___y_309_;
v___y_133_ = v___x_320_;
v___y_134_ = v___y_313_;
v___y_135_ = v___x_332_;
goto v___jp_120_;
}
}
v___jp_333_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
lean_inc_ref(v___y_341_);
v___x_350_ = l_Array_append___redArg(v___y_341_, v___y_349_);
lean_dec_ref(v___y_349_);
lean_inc(v___y_335_);
lean_inc(v___y_338_);
v___x_351_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_351_, 0, v___y_338_);
lean_ctor_set(v___x_351_, 1, v___y_335_);
lean_ctor_set(v___x_351_, 2, v___x_350_);
v___x_352_ = l_Lean_SourceInfo_fromRef(v___y_345_, v___x_142_);
lean_dec(v___y_345_);
v___x_353_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__36));
v___x_354_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_352_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
if (lean_obj_tag(v___y_334_) == 1)
{
lean_object* v_val_355_; lean_object* v___x_356_; 
v_val_355_ = lean_ctor_get(v___y_334_, 0);
lean_inc(v_val_355_);
lean_dec_ref(v___y_334_);
v___x_356_ = l_Array_mkArray1___redArg(v_val_355_);
v___y_300_ = v___y_336_;
v___y_301_ = v___y_335_;
v___y_302_ = v___y_337_;
v___y_303_ = v___y_338_;
v___y_304_ = v___y_339_;
v___y_305_ = v___y_340_;
v___y_306_ = v___x_351_;
v___y_307_ = v___y_341_;
v___y_308_ = v___y_342_;
v___y_309_ = v___y_343_;
v___y_310_ = v___y_344_;
v___y_311_ = v___y_346_;
v___y_312_ = v___y_347_;
v___y_313_ = v___x_354_;
v___y_314_ = v___y_348_;
v___y_315_ = v___x_356_;
goto v___jp_299_;
}
else
{
lean_object* v___x_357_; 
lean_dec(v___y_334_);
v___x_357_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25));
v___y_300_ = v___y_336_;
v___y_301_ = v___y_335_;
v___y_302_ = v___y_337_;
v___y_303_ = v___y_338_;
v___y_304_ = v___y_339_;
v___y_305_ = v___y_340_;
v___y_306_ = v___x_351_;
v___y_307_ = v___y_341_;
v___y_308_ = v___y_342_;
v___y_309_ = v___y_343_;
v___y_310_ = v___y_344_;
v___y_311_ = v___y_346_;
v___y_312_ = v___y_347_;
v___y_313_ = v___x_354_;
v___y_314_ = v___y_348_;
v___y_315_ = v___x_357_;
goto v___jp_299_;
}
}
v___jp_358_:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
lean_inc_ref(v___y_366_);
v___x_375_ = l_Array_append___redArg(v___y_366_, v___y_374_);
lean_dec_ref(v___y_374_);
lean_inc(v___y_360_);
lean_inc(v___y_363_);
v___x_376_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_376_, 0, v___y_363_);
lean_ctor_set(v___x_376_, 1, v___y_360_);
lean_ctor_set(v___x_376_, 2, v___x_375_);
if (lean_obj_tag(v___y_365_) == 1)
{
lean_object* v_val_377_; lean_object* v___x_378_; 
v_val_377_ = lean_ctor_get(v___y_365_, 0);
lean_inc(v_val_377_);
lean_dec_ref(v___y_365_);
v___x_378_ = l_Array_mkArray1___redArg(v_val_377_);
v___y_334_ = v___y_359_;
v___y_335_ = v___y_360_;
v___y_336_ = v___y_361_;
v___y_337_ = v___y_362_;
v___y_338_ = v___y_363_;
v___y_339_ = v___y_364_;
v___y_340_ = v___x_376_;
v___y_341_ = v___y_366_;
v___y_342_ = v___y_367_;
v___y_343_ = v___y_368_;
v___y_344_ = v___y_369_;
v___y_345_ = v___y_370_;
v___y_346_ = v___y_371_;
v___y_347_ = v___y_372_;
v___y_348_ = v___y_373_;
v___y_349_ = v___x_378_;
goto v___jp_333_;
}
else
{
lean_object* v___x_379_; 
lean_dec(v___y_365_);
v___x_379_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25));
v___y_334_ = v___y_359_;
v___y_335_ = v___y_360_;
v___y_336_ = v___y_361_;
v___y_337_ = v___y_362_;
v___y_338_ = v___y_363_;
v___y_339_ = v___y_364_;
v___y_340_ = v___x_376_;
v___y_341_ = v___y_366_;
v___y_342_ = v___y_367_;
v___y_343_ = v___y_368_;
v___y_344_ = v___y_369_;
v___y_345_ = v___y_370_;
v___y_346_ = v___y_371_;
v___y_347_ = v___y_372_;
v___y_348_ = v___y_373_;
v___y_349_ = v___x_379_;
goto v___jp_333_;
}
}
v___jp_380_:
{
lean_object* v_ref_395_; uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_ref_395_ = lean_ctor_get(v___y_393_, 5);
v___x_396_ = 0;
v___x_397_ = l_Lean_SourceInfo_fromRef(v_ref_395_, v___x_396_);
v___x_398_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30));
v___x_399_ = lean_obj_once(&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31, &l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31_once, _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31);
if (lean_obj_tag(v___y_383_) == 1)
{
lean_object* v_val_400_; lean_object* v___x_401_; 
v_val_400_ = lean_ctor_get(v___y_383_, 0);
lean_inc(v_val_400_);
lean_dec_ref(v___y_383_);
v___x_401_ = l_Array_mkArray1___redArg(v_val_400_);
v___y_359_ = v___y_381_;
v___y_360_ = v___x_398_;
v___y_361_ = v_wds_x3f_392_;
v___y_362_ = v___y_382_;
v___y_363_ = v___x_397_;
v___y_364_ = v___y_385_;
v___y_365_ = v___y_389_;
v___y_366_ = v___x_399_;
v___y_367_ = v___y_384_;
v___y_368_ = v___y_394_;
v___y_369_ = v___y_386_;
v___y_370_ = v___y_387_;
v___y_371_ = v___y_388_;
v___y_372_ = v___y_390_;
v___y_373_ = v___y_391_;
v___y_374_ = v___x_401_;
goto v___jp_358_;
}
else
{
lean_object* v___x_402_; 
lean_dec(v___y_383_);
v___x_402_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25));
v___y_359_ = v___y_381_;
v___y_360_ = v___x_398_;
v___y_361_ = v_wds_x3f_392_;
v___y_362_ = v___y_382_;
v___y_363_ = v___x_397_;
v___y_364_ = v___y_385_;
v___y_365_ = v___y_389_;
v___y_366_ = v___x_399_;
v___y_367_ = v___y_384_;
v___y_368_ = v___y_394_;
v___y_369_ = v___y_386_;
v___y_370_ = v___y_387_;
v___y_371_ = v___y_388_;
v___y_372_ = v___y_390_;
v___y_373_ = v___y_391_;
v___y_374_ = v___x_402_;
goto v___jp_358_;
}
}
v___jp_403_:
{
lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_416_ = l_Lean_Syntax_getArg(v___y_411_, v___y_408_);
lean_dec(v___y_411_);
v___x_417_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45));
lean_inc(v___x_416_);
v___x_418_ = l_Lean_Syntax_isOfKind(v___x_416_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
lean_dec(v___y_406_);
v___x_419_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46));
v___x_420_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47));
v___x_421_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40));
v___x_422_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48));
lean_inc(v___x_416_);
v___x_423_ = l_Lean_Syntax_isOfKind(v___x_416_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec(v___x_416_);
lean_dec(v_args_x3f_413_);
lean_dec(v___y_412_);
lean_dec(v___y_409_);
lean_dec(v___y_407_);
lean_dec(v___y_405_);
v___x_424_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_425_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_424_, v___y_414_, v___y_415_);
lean_dec(v_x_93_);
return v___x_425_;
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_426_ = l_Lean_Syntax_getArg(v___x_416_, v___y_408_);
v___x_427_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49));
lean_inc(v___x_426_);
v___x_428_ = l_Lean_Syntax_isOfKind(v___x_426_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec(v___x_426_);
lean_dec(v___x_416_);
lean_dec(v_args_x3f_413_);
lean_dec(v___y_412_);
lean_dec(v___y_409_);
lean_dec(v___y_407_);
lean_dec(v___y_405_);
v___x_429_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_430_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_429_, v___y_414_, v___y_415_);
lean_dec(v_x_93_);
return v___x_430_;
}
else
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = l_Lean_Syntax_getArg(v___x_426_, v___x_145_);
v___x_432_ = l_Lean_Syntax_matchesNull(v___x_431_, v___x_145_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec(v___x_426_);
lean_dec(v___x_416_);
lean_dec(v_args_x3f_413_);
lean_dec(v___y_412_);
lean_dec(v___y_409_);
lean_dec(v___y_407_);
lean_dec(v___y_405_);
v___x_433_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_434_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_433_, v___y_414_, v___y_415_);
lean_dec(v_x_93_);
return v___x_434_;
}
else
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = l_Lean_Syntax_getArg(v___x_426_, v___y_410_);
lean_dec(v___x_426_);
v___x_436_ = l_Lean_Syntax_matchesNull(v___x_435_, v___x_145_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec(v___x_416_);
lean_dec(v_args_x3f_413_);
lean_dec(v___y_412_);
lean_dec(v___y_409_);
lean_dec(v___y_407_);
lean_dec(v___y_405_);
v___x_437_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_438_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_437_, v___y_414_, v___y_415_);
lean_dec(v_x_93_);
return v___x_438_;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_439_ = l_Lean_Syntax_getArg(v___x_416_, v___y_410_);
v___x_440_ = l_Lean_Syntax_getArg(v___x_416_, v___y_404_);
lean_dec(v___x_416_);
v___x_441_ = l_Lean_Syntax_isNone(v___x_440_);
if (v___x_441_ == 0)
{
uint8_t v___x_442_; 
lean_inc(v___x_440_);
v___x_442_ = l_Lean_Syntax_matchesNull(v___x_440_, v___y_410_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec(v___x_440_);
lean_dec(v___x_439_);
lean_dec(v_args_x3f_413_);
lean_dec(v___y_412_);
lean_dec(v___y_409_);
lean_dec(v___y_407_);
lean_dec(v___y_405_);
v___x_443_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_444_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_443_, v___y_414_, v___y_415_);
lean_dec(v_x_93_);
return v___x_444_;
}
else
{
lean_object* v_wds_x3f_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v_wds_x3f_445_ = l_Lean_Syntax_getArg(v___x_440_, v___x_145_);
lean_dec(v___x_440_);
v___x_446_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51));
lean_inc(v_wds_x3f_445_);
v___x_447_ = l_Lean_Syntax_isOfKind(v_wds_x3f_445_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec(v_wds_x3f_445_);
lean_dec(v___x_439_);
lean_dec(v_args_x3f_413_);
lean_dec(v___y_412_);
lean_dec(v___y_409_);
lean_dec(v___y_407_);
lean_dec(v___y_405_);
v___x_448_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_449_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_448_, v___y_414_, v___y_415_);
lean_dec(v_x_93_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; 
lean_dec(v_x_93_);
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v_wds_x3f_445_);
lean_inc_ref(v___y_414_);
v___y_230_ = v_args_x3f_413_;
v___y_231_ = v___x_418_;
v___y_232_ = v___x_427_;
v___y_233_ = v___y_407_;
v___y_234_ = v___x_422_;
v___y_235_ = v___x_421_;
v___y_236_ = v___y_412_;
v___y_237_ = v___x_439_;
v___y_238_ = v___y_405_;
v___y_239_ = v___y_408_;
v___y_240_ = v___y_409_;
v___y_241_ = v___y_410_;
v___y_242_ = v___x_420_;
v___y_243_ = v___x_419_;
v_wds_x3f_244_ = v___x_450_;
v___y_245_ = v___y_414_;
v___y_246_ = v___y_415_;
goto v___jp_229_;
}
}
}
else
{
lean_object* v___x_451_; 
lean_dec(v___x_440_);
lean_dec(v_x_93_);
v___x_451_ = lean_box(0);
lean_inc_ref(v___y_414_);
v___y_230_ = v_args_x3f_413_;
v___y_231_ = v___x_418_;
v___y_232_ = v___x_427_;
v___y_233_ = v___y_407_;
v___y_234_ = v___x_422_;
v___y_235_ = v___x_421_;
v___y_236_ = v___y_412_;
v___y_237_ = v___x_439_;
v___y_238_ = v___y_405_;
v___y_239_ = v___y_408_;
v___y_240_ = v___y_409_;
v___y_241_ = v___y_410_;
v___y_242_ = v___x_420_;
v___y_243_ = v___x_419_;
v_wds_x3f_244_ = v___x_451_;
v___y_245_ = v___y_414_;
v___y_246_ = v___y_415_;
goto v___jp_229_;
}
}
}
}
}
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_452_ = l_Lean_Syntax_getArg(v___x_416_, v___x_145_);
v___x_453_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46));
v___x_454_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47));
v___x_455_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__52));
v___x_456_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53));
lean_inc(v___x_452_);
v___x_457_ = l_Lean_Syntax_isOfKind(v___x_452_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec(v___x_452_);
lean_dec(v___x_416_);
lean_dec(v_args_x3f_413_);
lean_dec(v___y_412_);
lean_dec(v___y_409_);
lean_dec(v___y_407_);
lean_dec(v___y_406_);
lean_dec(v___y_405_);
v___x_458_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_459_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_458_, v___y_414_, v___y_415_);
lean_dec(v_x_93_);
return v___x_459_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_460_ = l_Lean_Syntax_getArg(v___x_452_, v___y_410_);
lean_dec(v___x_452_);
v___x_461_ = l_Lean_Syntax_getArg(v___x_416_, v___y_410_);
lean_dec(v___x_416_);
v___x_462_ = l_Lean_Syntax_isNone(v___x_461_);
if (v___x_462_ == 0)
{
uint8_t v___x_463_; 
lean_inc(v___x_461_);
v___x_463_ = l_Lean_Syntax_matchesNull(v___x_461_, v___y_410_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec(v___x_461_);
lean_dec(v___x_460_);
lean_dec(v_args_x3f_413_);
lean_dec(v___y_412_);
lean_dec(v___y_409_);
lean_dec(v___y_407_);
lean_dec(v___y_406_);
lean_dec(v___y_405_);
v___x_464_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_465_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_464_, v___y_414_, v___y_415_);
lean_dec(v_x_93_);
return v___x_465_;
}
else
{
lean_object* v_wds_x3f_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v_wds_x3f_466_ = l_Lean_Syntax_getArg(v___x_461_, v___x_145_);
lean_dec(v___x_461_);
v___x_467_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51));
lean_inc(v_wds_x3f_466_);
v___x_468_ = l_Lean_Syntax_isOfKind(v_wds_x3f_466_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v_wds_x3f_466_);
lean_dec(v___x_460_);
lean_dec(v_args_x3f_413_);
lean_dec(v___y_412_);
lean_dec(v___y_409_);
lean_dec(v___y_407_);
lean_dec(v___y_406_);
lean_dec(v___y_405_);
v___x_469_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_470_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_469_, v___y_414_, v___y_415_);
lean_dec(v_x_93_);
return v___x_470_;
}
else
{
lean_object* v___x_471_; 
lean_dec(v_x_93_);
v___x_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_471_, 0, v_wds_x3f_466_);
v___y_381_ = v_args_x3f_413_;
v___y_382_ = v___x_460_;
v___y_383_ = v___y_405_;
v___y_384_ = v___y_406_;
v___y_385_ = v___y_407_;
v___y_386_ = v___x_456_;
v___y_387_ = v___y_409_;
v___y_388_ = v___x_454_;
v___y_389_ = v___y_412_;
v___y_390_ = v___x_453_;
v___y_391_ = v___x_455_;
v_wds_x3f_392_ = v___x_471_;
v___y_393_ = v___y_414_;
v___y_394_ = v___y_415_;
goto v___jp_380_;
}
}
}
else
{
lean_object* v___x_472_; 
lean_dec(v___x_461_);
lean_dec(v_x_93_);
v___x_472_ = lean_box(0);
v___y_381_ = v_args_x3f_413_;
v___y_382_ = v___x_460_;
v___y_383_ = v___y_405_;
v___y_384_ = v___y_406_;
v___y_385_ = v___y_407_;
v___y_386_ = v___x_456_;
v___y_387_ = v___y_409_;
v___y_388_ = v___x_454_;
v___y_389_ = v___y_412_;
v___y_390_ = v___x_453_;
v___y_391_ = v___x_455_;
v_wds_x3f_392_ = v___x_472_;
v___y_393_ = v___y_414_;
v___y_394_ = v___y_415_;
goto v___jp_380_;
}
}
}
}
v___jp_473_:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_479_ = lean_unsigned_to_nat(3u);
v___x_480_ = l_Lean_Syntax_getArg(v_x_93_, v___x_479_);
v___x_481_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55));
lean_inc(v___x_480_);
v___x_482_ = l_Lean_Syntax_isOfKind(v___x_480_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
lean_dec(v___x_480_);
lean_dec(v_attrs_x3f_476_);
lean_dec(v___y_474_);
v___x_483_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_484_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_483_, v___y_477_, v___y_478_);
lean_dec(v_x_93_);
return v___x_484_;
}
else
{
lean_object* v___x_485_; lean_object* v_kw_486_; lean_object* v_name_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_485_ = lean_unsigned_to_nat(2u);
v_kw_486_ = l_Lean_Syntax_getArg(v_x_93_, v___x_485_);
v_name_487_ = l_Lean_Syntax_getArg(v___x_480_, v___x_145_);
v___x_488_ = l_Lean_Syntax_getArg(v___x_480_, v___y_475_);
v___x_489_ = l_Lean_Syntax_isNone(v___x_488_);
if (v___x_489_ == 0)
{
uint8_t v___x_490_; 
lean_inc(v___x_488_);
v___x_490_ = l_Lean_Syntax_matchesNull(v___x_488_, v___y_475_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v___x_488_);
lean_dec(v_name_487_);
lean_dec(v_kw_486_);
lean_dec(v___x_480_);
lean_dec(v_attrs_x3f_476_);
lean_dec(v___y_474_);
v___x_491_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_492_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_491_, v___y_477_, v___y_478_);
lean_dec(v_x_93_);
return v___x_492_;
}
else
{
lean_object* v_args_x3f_493_; lean_object* v___x_494_; 
v_args_x3f_493_ = l_Lean_Syntax_getArg(v___x_488_, v___x_145_);
lean_dec(v___x_488_);
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v_args_x3f_493_);
v___y_404_ = v___x_479_;
v___y_405_ = v___y_474_;
v___y_406_ = v___x_481_;
v___y_407_ = v_name_487_;
v___y_408_ = v___x_485_;
v___y_409_ = v_kw_486_;
v___y_410_ = v___y_475_;
v___y_411_ = v___x_480_;
v___y_412_ = v_attrs_x3f_476_;
v_args_x3f_413_ = v___x_494_;
v___y_414_ = v___y_477_;
v___y_415_ = v___y_478_;
goto v___jp_403_;
}
}
else
{
lean_object* v___x_495_; 
lean_dec(v___x_488_);
v___x_495_ = lean_box(0);
v___y_404_ = v___x_479_;
v___y_405_ = v___y_474_;
v___y_406_ = v___x_481_;
v___y_407_ = v_name_487_;
v___y_408_ = v___x_485_;
v___y_409_ = v_kw_486_;
v___y_410_ = v___y_475_;
v___y_411_ = v___x_480_;
v___y_412_ = v_attrs_x3f_476_;
v_args_x3f_413_ = v___x_495_;
v___y_414_ = v___y_477_;
v___y_415_ = v___y_478_;
goto v___jp_403_;
}
}
}
v___jp_496_:
{
lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_500_ = lean_unsigned_to_nat(1u);
v___x_501_ = l_Lean_Syntax_getArg(v_x_93_, v___x_500_);
v___x_502_ = l_Lean_Syntax_isNone(v___x_501_);
if (v___x_502_ == 0)
{
uint8_t v___x_503_; 
lean_inc(v___x_501_);
v___x_503_ = l_Lean_Syntax_matchesNull(v___x_501_, v___x_500_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec(v___x_501_);
lean_dec(v_doc_x3f_497_);
v___x_504_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_505_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_504_, v___y_498_, v___y_499_);
lean_dec(v_x_93_);
return v___x_505_;
}
else
{
lean_object* v_attrs_x3f_506_; lean_object* v___x_507_; 
v_attrs_x3f_506_ = l_Lean_Syntax_getArg(v___x_501_, v___x_145_);
lean_dec(v___x_501_);
v___x_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_507_, 0, v_attrs_x3f_506_);
v___y_474_ = v_doc_x3f_497_;
v___y_475_ = v___x_500_;
v_attrs_x3f_476_ = v___x_507_;
v___y_477_ = v___y_498_;
v___y_478_ = v___y_499_;
goto v___jp_473_;
}
}
else
{
lean_object* v___x_508_; 
lean_dec(v___x_501_);
v___x_508_ = lean_box(0);
v___y_474_ = v_doc_x3f_497_;
v___y_475_ = v___x_500_;
v_attrs_x3f_476_ = v___x_508_;
v___y_477_ = v___y_498_;
v___y_478_ = v___y_499_;
goto v___jp_473_;
}
}
}
v___jp_96_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_113_ = l_Array_append___redArg(v___y_109_, v___y_112_);
lean_dec_ref(v___y_112_);
lean_inc(v___y_101_);
v___x_114_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_114_, 0, v___y_101_);
lean_ctor_set(v___x_114_, 1, v___y_98_);
lean_ctor_set(v___x_114_, 2, v___x_113_);
lean_inc(v___y_101_);
v___x_115_ = l_Lean_Syntax_node4(v___y_101_, v___y_103_, v___y_100_, v___y_105_, v___y_99_, v___x_114_);
lean_inc(v___y_101_);
v___x_116_ = l_Lean_Syntax_node5(v___y_101_, v___y_111_, v___y_110_, v___y_104_, v___y_106_, v___x_115_, v___y_102_);
v___x_117_ = l_Lean_Syntax_node2(v___y_101_, v___y_107_, v___y_97_, v___x_116_);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v___y_108_);
return v___x_118_;
}
v___jp_120_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_136_ = l_Array_append___redArg(v___y_127_, v___y_135_);
lean_dec_ref(v___y_135_);
lean_inc(v___y_122_);
v___x_137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_137_, 0, v___y_122_);
lean_ctor_set(v___x_137_, 1, v___y_121_);
lean_ctor_set(v___x_137_, 2, v___x_136_);
lean_inc(v___y_122_);
v___x_138_ = l_Lean_Syntax_node4(v___y_122_, v___y_133_, v___y_123_, v___y_128_, v___y_129_, v___x_137_);
lean_inc(v___y_122_);
v___x_139_ = l_Lean_Syntax_node3(v___y_122_, v___y_131_, v___y_124_, v___y_130_, v___x_138_);
v___x_140_ = l_Lean_Syntax_node4(v___y_122_, v___x_119_, v___y_125_, v___y_126_, v___y_134_, v___x_139_);
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v___y_132_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___boxed(lean_object* v_x_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl(v_x_518_, v_a_519_, v_a_520_);
lean_dec_ref(v_a_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1(){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_550_ = l_Lean_Elab_macroAttribute;
v___x_551_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3));
v___x_552_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__10));
v___x_553_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___boxed), 3, 0);
v___x_554_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_550_, v___x_551_, v___x_552_, v___x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___boxed(lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1();
return v_res_556_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Attributes(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_Script(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_DSL_Script(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Lake_Config_Package(uint8_t builtin);
lean_object* initialize_Lake_DSL_Attributes(uint8_t builtin);
lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Script(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Script(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_DSL_Script(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_DSL_Script(builtin);
}
#ifdef __cplusplus
}
#endif
