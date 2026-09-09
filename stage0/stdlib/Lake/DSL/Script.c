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
lean_object* v___x_145_; lean_object* v___y_147_; lean_object* v___y_148_; lean_object* v___y_149_; lean_object* v___y_150_; lean_object* v___y_151_; lean_object* v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v___y_161_; lean_object* v___y_162_; lean_object* v___y_163_; lean_object* v___y_164_; lean_object* v___y_165_; lean_object* v___y_166_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_234_; uint8_t v___y_235_; lean_object* v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v_wds_x3f_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; uint8_t v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v_wds_x3f_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v___y_441_; lean_object* v___y_442_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v_args_x3f_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v_attrs_x3f_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v_doc_x3f_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_542_ = l_Lean_Syntax_getArg(v_x_93_, v___x_145_);
v___x_543_ = l_Lean_Syntax_isNone(v___x_542_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_542_);
v___x_545_ = l_Lean_Syntax_matchesNull(v___x_542_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; 
lean_dec(v___x_542_);
v___x_546_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_547_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_546_, v_a_94_, v_a_95_);
lean_dec(v_x_93_);
return v___x_547_;
}
else
{
lean_object* v_doc_x3f_548_; lean_object* v___x_549_; 
v_doc_x3f_548_ = l_Lean_Syntax_getArg(v___x_542_, v___x_145_);
lean_dec(v___x_542_);
v___x_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_549_, 0, v_doc_x3f_548_);
v_doc_x3f_530_ = v___x_549_;
v___y_531_ = v_a_94_;
v___y_532_ = v_a_95_;
goto v___jp_529_;
}
}
else
{
lean_object* v___x_550_; 
lean_dec(v___x_542_);
v___x_550_ = lean_box(0);
v_doc_x3f_530_ = v___x_550_;
v___y_531_ = v_a_94_;
v___y_532_ = v_a_95_;
goto v___jp_529_;
}
v___jp_146_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
lean_inc_ref_n(v___y_167_, 2);
v___x_170_ = l_Array_append___redArg(v___y_167_, v___y_169_);
lean_dec_ref(v___y_169_);
lean_inc_n(v___y_160_, 6);
lean_inc_n(v___y_152_, 20);
v___x_171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_171_, 0, v___y_152_);
lean_ctor_set(v___x_171_, 1, v___y_160_);
lean_ctor_set(v___x_171_, 2, v___x_170_);
v___x_172_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__5));
lean_inc_ref_n(v___y_155_, 3);
lean_inc_ref_n(v___y_150_, 7);
lean_inc_ref_n(v___y_153_, 7);
v___x_173_ = l_Lean_Name_mkStr4(v___y_153_, v___y_150_, v___y_155_, v___x_172_);
v___x_174_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__6));
v___x_175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_175_, 0, v___y_152_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
v___x_176_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__7));
v___x_177_ = l_Lean_Syntax_SepArray_ofElems(v___x_176_, v___y_168_);
lean_dec_ref(v___y_168_);
v___x_178_ = l_Array_append___redArg(v___y_167_, v___x_177_);
lean_dec_ref(v___x_177_);
v___x_179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_179_, 0, v___y_152_);
lean_ctor_set(v___x_179_, 1, v___y_160_);
lean_ctor_set(v___x_179_, 2, v___x_178_);
v___x_180_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__8));
v___x_181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_181_, 0, v___y_152_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = l_Lean_Syntax_node3(v___y_152_, v___x_173_, v___x_175_, v___x_179_, v___x_181_);
v___x_183_ = l_Lean_Syntax_node1(v___y_152_, v___y_160_, v___x_182_);
lean_inc_n(v___y_164_, 9);
v___x_184_ = l_Lean_Syntax_node7(v___y_152_, v___y_163_, v___x_171_, v___x_183_, v___y_164_, v___y_164_, v___y_164_, v___y_164_, v___y_164_);
v___x_185_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__9));
lean_inc_ref_n(v___y_166_, 3);
v___x_186_ = l_Lean_Name_mkStr4(v___y_153_, v___y_150_, v___y_166_, v___x_185_);
v___x_187_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__10));
v___x_188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_188_, 0, v___y_152_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__11));
v___x_190_ = l_Lean_Name_mkStr4(v___y_153_, v___y_150_, v___y_166_, v___x_189_);
v___x_191_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12));
v___x_192_ = lean_box(2);
v___x_193_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v___y_160_);
lean_ctor_set(v___x_193_, 2, v___x_191_);
v___x_194_ = lean_mk_empty_array_with_capacity(v___y_151_);
v___x_195_ = lean_array_push(v___x_194_, v___y_148_);
v___x_196_ = lean_array_push(v___x_195_, v___x_193_);
v___x_197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_197_, 0, v___x_192_);
lean_ctor_set(v___x_197_, 1, v___x_190_);
lean_ctor_set(v___x_197_, 2, v___x_196_);
v___x_198_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__13));
v___x_199_ = l_Lean_Name_mkStr4(v___y_153_, v___y_150_, v___y_166_, v___x_198_);
v___x_200_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__14));
v___x_201_ = l_Lean_Name_mkStr4(v___y_153_, v___y_150_, v___y_155_, v___x_200_);
v___x_202_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__15));
v___x_203_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_203_, 0, v___y_152_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = lean_obj_once(&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17, &l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17_once, _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17);
v___x_205_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__18));
v___x_206_ = l_Lean_addMacroScope(v___y_165_, v___x_205_, v___y_162_);
v___x_207_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__20));
lean_inc(v___y_156_);
v___x_208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___y_156_);
v___x_209_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_209_, 0, v___y_152_);
lean_ctor_set(v___x_209_, 1, v___x_204_);
lean_ctor_set(v___x_209_, 2, v___x_206_);
lean_ctor_set(v___x_209_, 3, v___x_208_);
v___x_210_ = l_Lean_Syntax_node2(v___y_152_, v___x_201_, v___x_203_, v___x_209_);
v___x_211_ = l_Lean_Syntax_node1(v___y_152_, v___y_160_, v___x_210_);
v___x_212_ = l_Lean_Syntax_node2(v___y_152_, v___x_199_, v___y_164_, v___x_211_);
v___x_213_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21));
v___x_214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_214_, 0, v___y_152_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__22));
v___x_216_ = l_Lean_Name_mkStr4(v___y_153_, v___y_150_, v___y_155_, v___x_215_);
v___x_217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_217_, 0, v___y_152_);
lean_ctor_set(v___x_217_, 1, v___x_215_);
v___x_218_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__23));
v___x_219_ = l_Lean_Name_mkStr4(v___y_153_, v___y_150_, v___y_155_, v___x_218_);
v___x_220_ = l_Lean_Syntax_node1(v___y_152_, v___y_160_, v___y_161_);
v___x_221_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__24));
v___x_222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_222_, 0, v___y_152_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = l_Lean_Syntax_node4(v___y_152_, v___x_219_, v___x_220_, v___y_164_, v___x_222_, v___y_147_);
v___x_224_ = l_Lean_Syntax_node2(v___y_152_, v___x_216_, v___x_217_, v___x_223_);
lean_inc(v___y_149_);
v___x_225_ = l_Lean_Syntax_node2(v___y_152_, v___y_149_, v___y_164_, v___y_164_);
if (lean_obj_tag(v___y_157_) == 1)
{
lean_object* v_val_226_; lean_object* v___x_227_; 
v_val_226_ = lean_ctor_get(v___y_157_, 0);
lean_inc(v_val_226_);
lean_dec_ref_known(v___y_157_, 1);
v___x_227_ = l_Array_mkArray1___redArg(v_val_226_);
v___y_97_ = v___x_184_;
v___y_98_ = v___x_186_;
v___y_99_ = v___x_188_;
v___y_100_ = v___x_224_;
v___y_101_ = v___x_212_;
v___y_102_ = v___x_197_;
v___y_103_ = v___y_152_;
v___y_104_ = v___x_225_;
v___y_105_ = v___x_214_;
v___y_106_ = v___y_154_;
v___y_107_ = v___y_158_;
v___y_108_ = v___y_160_;
v___y_109_ = v___y_159_;
v___y_110_ = v___y_164_;
v___y_111_ = v___y_167_;
v___y_112_ = v___x_227_;
goto v___jp_96_;
}
else
{
lean_object* v___x_228_; 
lean_dec(v___y_157_);
v___x_228_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25));
v___y_97_ = v___x_184_;
v___y_98_ = v___x_186_;
v___y_99_ = v___x_188_;
v___y_100_ = v___x_224_;
v___y_101_ = v___x_212_;
v___y_102_ = v___x_197_;
v___y_103_ = v___y_152_;
v___y_104_ = v___x_225_;
v___y_105_ = v___x_214_;
v___y_106_ = v___y_154_;
v___y_107_ = v___y_158_;
v___y_108_ = v___y_160_;
v___y_109_ = v___y_159_;
v___y_110_ = v___y_164_;
v___y_111_ = v___y_167_;
v___y_112_ = v___x_228_;
goto v___jp_96_;
}
}
v___jp_229_:
{
lean_object* v_methods_247_; lean_object* v_quotContext_248_; lean_object* v_currMacroScope_249_; lean_object* v_currRecDepth_250_; lean_object* v_maxRecDepth_251_; lean_object* v_ref_252_; lean_object* v_ref_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v_methods_247_ = lean_ctor_get(v___y_245_, 0);
v_quotContext_248_ = lean_ctor_get(v___y_245_, 1);
v_currMacroScope_249_ = lean_ctor_get(v___y_245_, 2);
v_currRecDepth_250_ = lean_ctor_get(v___y_245_, 3);
v_maxRecDepth_251_ = lean_ctor_get(v___y_245_, 4);
v_ref_252_ = lean_ctor_get(v___y_245_, 5);
v_ref_253_ = l_Lean_replaceRef(v___y_243_, v_ref_252_);
lean_dec(v___y_243_);
lean_inc(v_ref_253_);
lean_inc(v_maxRecDepth_251_);
lean_inc(v_currRecDepth_250_);
lean_inc(v_currMacroScope_249_);
lean_inc(v_quotContext_248_);
lean_inc(v_methods_247_);
v___x_254_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_254_, 0, v_methods_247_);
lean_ctor_set(v___x_254_, 1, v_quotContext_248_);
lean_ctor_set(v___x_254_, 2, v_currMacroScope_249_);
lean_ctor_set(v___x_254_, 3, v_currRecDepth_250_);
lean_ctor_set(v___x_254_, 4, v_maxRecDepth_251_);
lean_ctor_set(v___x_254_, 5, v_ref_253_);
v___x_255_ = l_Lake_DSL_expandOptSimpleBinder(v___y_234_, v___x_254_, v___y_246_);
lean_dec_ref_known(v___x_254_, 6);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v_a_257_; lean_object* v_id_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
v_a_257_ = lean_ctor_get(v___x_255_, 1);
lean_inc(v_a_257_);
lean_dec_ref_known(v___x_255_, 2);
v_id_258_ = l_Lake_DSL_expandIdentOrStrAsIdent(v___y_231_);
v___x_259_ = l_Lean_SourceInfo_fromRef(v_ref_253_, v___y_235_);
lean_dec(v_ref_253_);
v___x_260_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26));
v___x_261_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__27));
lean_inc_ref_n(v___y_232_, 5);
lean_inc_ref_n(v___y_237_, 5);
v___x_262_ = l_Lean_Name_mkStr4(v___y_237_, v___y_232_, v___x_260_, v___x_261_);
v___x_263_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__28));
v___x_264_ = l_Lean_Name_mkStr4(v___y_237_, v___y_232_, v___x_260_, v___x_263_);
v___x_265_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30));
v___x_266_ = lean_obj_once(&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31, &l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31_once, _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31);
lean_inc_n(v___x_259_, 5);
v___x_267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_267_, 0, v___x_259_);
lean_ctor_set(v___x_267_, 1, v___x_265_);
lean_ctor_set(v___x_267_, 2, v___x_266_);
lean_inc_ref_n(v___x_267_, 2);
v___x_268_ = l_Lean_Syntax_node1(v___x_259_, v___x_264_, v___x_267_);
v___x_269_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32));
v___x_270_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33));
v___x_271_ = l_Lean_Name_mkStr4(v___y_237_, v___y_232_, v___x_269_, v___x_270_);
v___x_272_ = lean_obj_once(&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35, &l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35_once, _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35);
v___x_273_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__37));
lean_inc(v_currMacroScope_249_);
lean_inc(v_quotContext_248_);
v___x_274_ = l_Lean_addMacroScope(v_quotContext_248_, v___x_273_, v_currMacroScope_249_);
v___x_275_ = lean_box(0);
v___x_276_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_276_, 0, v___x_259_);
lean_ctor_set(v___x_276_, 1, v___x_272_);
lean_ctor_set(v___x_276_, 2, v___x_274_);
lean_ctor_set(v___x_276_, 3, v___x_275_);
v___x_277_ = l_Lean_Syntax_node2(v___x_259_, v___x_271_, v___x_276_, v___x_267_);
v___x_278_ = l_Lean_Syntax_node2(v___x_259_, v___x_262_, v___x_268_, v___x_277_);
v___x_279_ = lean_mk_empty_array_with_capacity(v___y_241_);
v___x_280_ = lean_array_push(v___x_279_, v___x_278_);
v___x_281_ = l_Lake_DSL_expandAttrs(v___y_238_);
v___x_282_ = l_Array_append___redArg(v___x_280_, v___x_281_);
lean_dec_ref(v___x_281_);
v___x_283_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__38));
lean_inc_ref_n(v___y_242_, 2);
v___x_284_ = l_Lean_Name_mkStr4(v___y_237_, v___y_232_, v___y_242_, v___x_283_);
v___x_285_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__39));
v___x_286_ = l_Lean_Name_mkStr4(v___y_237_, v___y_232_, v___y_242_, v___x_285_);
if (lean_obj_tag(v___y_240_) == 1)
{
lean_object* v_val_287_; lean_object* v___x_288_; 
v_val_287_ = lean_ctor_get(v___y_240_, 0);
lean_inc(v_val_287_);
lean_dec_ref_known(v___y_240_, 1);
v___x_288_ = l_Array_mkArray1___redArg(v_val_287_);
lean_inc(v_quotContext_248_);
lean_inc(v_currMacroScope_249_);
v___y_147_ = v___y_230_;
v___y_148_ = v_id_258_;
v___y_149_ = v___y_233_;
v___y_150_ = v___y_232_;
v___y_151_ = v___y_236_;
v___y_152_ = v___x_259_;
v___y_153_ = v___y_237_;
v___y_154_ = v___y_239_;
v___y_155_ = v___x_260_;
v___y_156_ = v___x_275_;
v___y_157_ = v_wds_x3f_244_;
v___y_158_ = v_a_257_;
v___y_159_ = v___x_284_;
v___y_160_ = v___x_265_;
v___y_161_ = v_a_256_;
v___y_162_ = v_currMacroScope_249_;
v___y_163_ = v___x_286_;
v___y_164_ = v___x_267_;
v___y_165_ = v_quotContext_248_;
v___y_166_ = v___y_242_;
v___y_167_ = v___x_266_;
v___y_168_ = v___x_282_;
v___y_169_ = v___x_288_;
goto v___jp_146_;
}
else
{
lean_object* v___x_289_; 
lean_dec(v___y_240_);
v___x_289_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25));
lean_inc(v_quotContext_248_);
lean_inc(v_currMacroScope_249_);
v___y_147_ = v___y_230_;
v___y_148_ = v_id_258_;
v___y_149_ = v___y_233_;
v___y_150_ = v___y_232_;
v___y_151_ = v___y_236_;
v___y_152_ = v___x_259_;
v___y_153_ = v___y_237_;
v___y_154_ = v___y_239_;
v___y_155_ = v___x_260_;
v___y_156_ = v___x_275_;
v___y_157_ = v_wds_x3f_244_;
v___y_158_ = v_a_257_;
v___y_159_ = v___x_284_;
v___y_160_ = v___x_265_;
v___y_161_ = v_a_256_;
v___y_162_ = v_currMacroScope_249_;
v___y_163_ = v___x_286_;
v___y_164_ = v___x_267_;
v___y_165_ = v_quotContext_248_;
v___y_166_ = v___y_242_;
v___y_167_ = v___x_266_;
v___y_168_ = v___x_282_;
v___y_169_ = v___x_289_;
goto v___jp_146_;
}
}
else
{
lean_object* v_a_290_; lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec(v_ref_253_);
lean_dec(v_wds_x3f_244_);
lean_dec(v___y_240_);
lean_dec(v___y_238_);
lean_dec(v___y_231_);
lean_dec(v___y_230_);
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
lean_object* v___x_317_; 
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v___y_315_);
v___y_230_ = v___y_300_;
v___y_231_ = v___y_301_;
v___y_232_ = v___y_303_;
v___y_233_ = v___y_304_;
v___y_234_ = v___y_305_;
v___y_235_ = v___y_306_;
v___y_236_ = v___y_307_;
v___y_237_ = v___y_309_;
v___y_238_ = v___y_310_;
v___y_239_ = v___y_311_;
v___y_240_ = v___y_313_;
v___y_241_ = v___y_312_;
v___y_242_ = v___y_314_;
v___y_243_ = v___y_316_;
v_wds_x3f_244_ = v___x_317_;
v___y_245_ = v___y_308_;
v___y_246_ = v___y_302_;
goto v___jp_229_;
}
v___jp_318_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
lean_inc_ref_n(v___y_320_, 2);
v___x_335_ = l_Array_append___redArg(v___y_320_, v___y_334_);
lean_dec_ref(v___y_334_);
lean_inc_n(v___y_333_, 2);
lean_inc_n(v___y_324_, 6);
v___x_336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_336_, 0, v___y_324_);
lean_ctor_set(v___x_336_, 1, v___y_333_);
lean_ctor_set(v___x_336_, 2, v___x_335_);
v___x_337_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40));
v___x_338_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__41));
lean_inc_ref_n(v___y_331_, 2);
lean_inc_ref_n(v___y_329_, 2);
v___x_339_ = l_Lean_Name_mkStr4(v___y_329_, v___y_331_, v___x_337_, v___x_338_);
v___x_340_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21));
v___x_341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_341_, 0, v___y_324_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
lean_inc_ref(v___y_332_);
v___x_342_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_342_, 0, v___y_324_);
lean_ctor_set(v___x_342_, 1, v___y_332_);
lean_inc(v___y_319_);
v___x_343_ = l_Lean_Syntax_node2(v___y_324_, v___y_319_, v___x_342_, v___y_325_);
v___x_344_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__42));
v___x_345_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__43));
v___x_346_ = l_Lean_Name_mkStr4(v___y_329_, v___y_331_, v___x_344_, v___x_345_);
v___x_347_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_347_, 0, v___y_324_);
lean_ctor_set(v___x_347_, 1, v___y_333_);
lean_ctor_set(v___x_347_, 2, v___y_320_);
lean_inc_ref(v___x_347_);
v___x_348_ = l_Lean_Syntax_node2(v___y_324_, v___x_346_, v___x_347_, v___x_347_);
if (lean_obj_tag(v___y_330_) == 1)
{
lean_object* v_val_349_; lean_object* v___x_350_; 
v_val_349_ = lean_ctor_get(v___y_330_, 0);
lean_inc(v_val_349_);
lean_dec_ref_known(v___y_330_, 1);
v___x_350_ = l_Array_mkArray1___redArg(v_val_349_);
v___y_121_ = v___y_320_;
v___y_122_ = v___x_343_;
v___y_123_ = v___y_321_;
v___y_124_ = v___x_348_;
v___y_125_ = v___y_322_;
v___y_126_ = v___y_323_;
v___y_127_ = v___x_336_;
v___y_128_ = v___y_324_;
v___y_129_ = v___y_326_;
v___y_130_ = v___y_327_;
v___y_131_ = v___y_328_;
v___y_132_ = v___x_341_;
v___y_133_ = v___y_333_;
v___y_134_ = v___x_339_;
v___y_135_ = v___x_350_;
goto v___jp_120_;
}
else
{
lean_object* v___x_351_; 
lean_dec(v___y_330_);
v___x_351_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25));
v___y_121_ = v___y_320_;
v___y_122_ = v___x_343_;
v___y_123_ = v___y_321_;
v___y_124_ = v___x_348_;
v___y_125_ = v___y_322_;
v___y_126_ = v___y_323_;
v___y_127_ = v___x_336_;
v___y_128_ = v___y_324_;
v___y_129_ = v___y_326_;
v___y_130_ = v___y_327_;
v___y_131_ = v___y_328_;
v___y_132_ = v___x_341_;
v___y_133_ = v___y_333_;
v___y_134_ = v___x_339_;
v___y_135_ = v___x_351_;
goto v___jp_120_;
}
}
v___jp_352_:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
lean_inc_ref(v___y_354_);
v___x_369_ = l_Array_append___redArg(v___y_354_, v___y_368_);
lean_dec_ref(v___y_368_);
lean_inc(v___y_366_);
lean_inc(v___y_358_);
v___x_370_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_370_, 0, v___y_358_);
lean_ctor_set(v___x_370_, 1, v___y_366_);
lean_ctor_set(v___x_370_, 2, v___x_369_);
v___x_371_ = l_Lean_SourceInfo_fromRef(v___y_367_, v___x_142_);
lean_dec(v___y_367_);
v___x_372_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__36));
v___x_373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
if (lean_obj_tag(v___y_356_) == 1)
{
lean_object* v_val_374_; lean_object* v___x_375_; 
v_val_374_ = lean_ctor_get(v___y_356_, 0);
lean_inc(v_val_374_);
lean_dec_ref_known(v___y_356_, 1);
v___x_375_ = l_Array_mkArray1___redArg(v_val_374_);
v___y_319_ = v___y_353_;
v___y_320_ = v___y_354_;
v___y_321_ = v___y_355_;
v___y_322_ = v___y_357_;
v___y_323_ = v___x_373_;
v___y_324_ = v___y_358_;
v___y_325_ = v___y_359_;
v___y_326_ = v___y_360_;
v___y_327_ = v___y_361_;
v___y_328_ = v___x_370_;
v___y_329_ = v___y_362_;
v___y_330_ = v___y_363_;
v___y_331_ = v___y_364_;
v___y_332_ = v___y_365_;
v___y_333_ = v___y_366_;
v___y_334_ = v___x_375_;
goto v___jp_318_;
}
else
{
lean_object* v___x_376_; 
lean_dec(v___y_356_);
v___x_376_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25));
v___y_319_ = v___y_353_;
v___y_320_ = v___y_354_;
v___y_321_ = v___y_355_;
v___y_322_ = v___y_357_;
v___y_323_ = v___x_373_;
v___y_324_ = v___y_358_;
v___y_325_ = v___y_359_;
v___y_326_ = v___y_360_;
v___y_327_ = v___y_361_;
v___y_328_ = v___x_370_;
v___y_329_ = v___y_362_;
v___y_330_ = v___y_363_;
v___y_331_ = v___y_364_;
v___y_332_ = v___y_365_;
v___y_333_ = v___y_366_;
v___y_334_ = v___x_376_;
goto v___jp_318_;
}
}
v___jp_377_:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
lean_inc_ref(v___y_379_);
v___x_394_ = l_Array_append___redArg(v___y_379_, v___y_393_);
lean_dec_ref(v___y_393_);
lean_inc(v___y_391_);
lean_inc(v___y_383_);
v___x_395_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_395_, 0, v___y_383_);
lean_ctor_set(v___x_395_, 1, v___y_391_);
lean_ctor_set(v___x_395_, 2, v___x_394_);
if (lean_obj_tag(v___y_382_) == 1)
{
lean_object* v_val_396_; lean_object* v___x_397_; 
v_val_396_ = lean_ctor_get(v___y_382_, 0);
lean_inc(v_val_396_);
lean_dec_ref_known(v___y_382_, 1);
v___x_397_ = l_Array_mkArray1___redArg(v_val_396_);
v___y_353_ = v___y_378_;
v___y_354_ = v___y_379_;
v___y_355_ = v___y_380_;
v___y_356_ = v___y_381_;
v___y_357_ = v___x_395_;
v___y_358_ = v___y_383_;
v___y_359_ = v___y_384_;
v___y_360_ = v___y_385_;
v___y_361_ = v___y_386_;
v___y_362_ = v___y_387_;
v___y_363_ = v___y_388_;
v___y_364_ = v___y_389_;
v___y_365_ = v___y_390_;
v___y_366_ = v___y_391_;
v___y_367_ = v___y_392_;
v___y_368_ = v___x_397_;
goto v___jp_352_;
}
else
{
lean_object* v___x_398_; 
lean_dec(v___y_382_);
v___x_398_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25));
v___y_353_ = v___y_378_;
v___y_354_ = v___y_379_;
v___y_355_ = v___y_380_;
v___y_356_ = v___y_381_;
v___y_357_ = v___x_395_;
v___y_358_ = v___y_383_;
v___y_359_ = v___y_384_;
v___y_360_ = v___y_385_;
v___y_361_ = v___y_386_;
v___y_362_ = v___y_387_;
v___y_363_ = v___y_388_;
v___y_364_ = v___y_389_;
v___y_365_ = v___y_390_;
v___y_366_ = v___y_391_;
v___y_367_ = v___y_392_;
v___y_368_ = v___x_398_;
goto v___jp_352_;
}
}
v___jp_399_:
{
lean_object* v_ref_414_; uint8_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_ref_414_ = lean_ctor_get(v___y_412_, 5);
v___x_415_ = 0;
v___x_416_ = l_Lean_SourceInfo_fromRef(v_ref_414_, v___x_415_);
v___x_417_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30));
v___x_418_ = lean_obj_once(&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31, &l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31_once, _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31);
if (lean_obj_tag(v___y_405_) == 1)
{
lean_object* v_val_419_; lean_object* v___x_420_; 
v_val_419_ = lean_ctor_get(v___y_405_, 0);
lean_inc(v_val_419_);
lean_dec_ref_known(v___y_405_, 1);
v___x_420_ = l_Array_mkArray1___redArg(v_val_419_);
v___y_378_ = v___y_401_;
v___y_379_ = v___x_418_;
v___y_380_ = v___y_403_;
v___y_381_ = v___y_404_;
v___y_382_ = v___y_408_;
v___y_383_ = v___x_416_;
v___y_384_ = v___y_409_;
v___y_385_ = v___y_413_;
v___y_386_ = v___y_400_;
v___y_387_ = v___y_402_;
v___y_388_ = v_wds_x3f_411_;
v___y_389_ = v___y_406_;
v___y_390_ = v___y_407_;
v___y_391_ = v___x_417_;
v___y_392_ = v___y_410_;
v___y_393_ = v___x_420_;
goto v___jp_377_;
}
else
{
lean_object* v___x_421_; 
lean_dec(v___y_405_);
v___x_421_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25));
v___y_378_ = v___y_401_;
v___y_379_ = v___x_418_;
v___y_380_ = v___y_403_;
v___y_381_ = v___y_404_;
v___y_382_ = v___y_408_;
v___y_383_ = v___x_416_;
v___y_384_ = v___y_409_;
v___y_385_ = v___y_413_;
v___y_386_ = v___y_400_;
v___y_387_ = v___y_402_;
v___y_388_ = v_wds_x3f_411_;
v___y_389_ = v___y_406_;
v___y_390_ = v___y_407_;
v___y_391_ = v___x_417_;
v___y_392_ = v___y_410_;
v___y_393_ = v___x_421_;
goto v___jp_377_;
}
}
v___jp_422_:
{
lean_object* v___x_437_; 
v___x_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_437_, 0, v___y_430_);
v___y_400_ = v___y_431_;
v___y_401_ = v___y_423_;
v___y_402_ = v___y_432_;
v___y_403_ = v___y_424_;
v___y_404_ = v___y_426_;
v___y_405_ = v___y_433_;
v___y_406_ = v___y_434_;
v___y_407_ = v___y_435_;
v___y_408_ = v___y_428_;
v___y_409_ = v___y_429_;
v___y_410_ = v___y_436_;
v_wds_x3f_411_ = v___x_437_;
v___y_412_ = v___y_427_;
v___y_413_ = v___y_425_;
goto v___jp_399_;
}
v___jp_438_:
{
lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_451_ = l_Lean_Syntax_getArg(v___y_443_, v___y_444_);
lean_dec(v___y_443_);
v___x_452_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45));
lean_inc(v___x_451_);
v___x_453_ = l_Lean_Syntax_isOfKind(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_454_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46));
v___x_455_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47));
v___x_456_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40));
v___x_457_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48));
lean_inc(v___x_451_);
v___x_458_ = l_Lean_Syntax_isOfKind(v___x_451_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec(v___x_451_);
lean_dec(v_args_x3f_448_);
lean_dec(v___y_447_);
lean_dec(v___y_446_);
lean_dec(v___y_441_);
lean_dec(v___y_440_);
v___x_459_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_460_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_459_, v___y_449_, v___y_450_);
lean_dec(v_x_93_);
return v___x_460_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_461_ = l_Lean_Syntax_getArg(v___x_451_, v___y_444_);
v___x_462_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49));
lean_inc(v___x_461_);
v___x_463_ = l_Lean_Syntax_isOfKind(v___x_461_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec(v___x_461_);
lean_dec(v___x_451_);
lean_dec(v_args_x3f_448_);
lean_dec(v___y_447_);
lean_dec(v___y_446_);
lean_dec(v___y_441_);
lean_dec(v___y_440_);
v___x_464_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_465_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_464_, v___y_449_, v___y_450_);
lean_dec(v_x_93_);
return v___x_465_;
}
else
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = l_Lean_Syntax_getArg(v___x_461_, v___x_145_);
v___x_467_ = l_Lean_Syntax_matchesNull(v___x_466_, v___x_145_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec(v___x_461_);
lean_dec(v___x_451_);
lean_dec(v_args_x3f_448_);
lean_dec(v___y_447_);
lean_dec(v___y_446_);
lean_dec(v___y_441_);
lean_dec(v___y_440_);
v___x_468_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_469_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_468_, v___y_449_, v___y_450_);
lean_dec(v_x_93_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = l_Lean_Syntax_getArg(v___x_461_, v___y_442_);
lean_dec(v___x_461_);
v___x_471_ = l_Lean_Syntax_matchesNull(v___x_470_, v___x_145_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec(v___x_451_);
lean_dec(v_args_x3f_448_);
lean_dec(v___y_447_);
lean_dec(v___y_446_);
lean_dec(v___y_441_);
lean_dec(v___y_440_);
v___x_472_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_473_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_472_, v___y_449_, v___y_450_);
lean_dec(v_x_93_);
return v___x_473_;
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_474_ = l_Lean_Syntax_getArg(v___x_451_, v___y_442_);
v___x_475_ = l_Lean_Syntax_getArg(v___x_451_, v___y_445_);
lean_dec(v___x_451_);
v___x_476_ = l_Lean_Syntax_isNone(v___x_475_);
if (v___x_476_ == 0)
{
uint8_t v___x_477_; 
lean_inc(v___x_475_);
v___x_477_ = l_Lean_Syntax_matchesNull(v___x_475_, v___y_442_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v___x_475_);
lean_dec(v___x_474_);
lean_dec(v_args_x3f_448_);
lean_dec(v___y_447_);
lean_dec(v___y_446_);
lean_dec(v___y_441_);
lean_dec(v___y_440_);
v___x_478_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_479_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_478_, v___y_449_, v___y_450_);
lean_dec(v_x_93_);
return v___x_479_;
}
else
{
lean_object* v_wds_x3f_480_; 
v_wds_x3f_480_ = l_Lean_Syntax_getArg(v___x_475_, v___x_145_);
lean_dec(v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51));
lean_inc(v_wds_x3f_480_);
v___x_482_ = l_Lean_Syntax_isOfKind(v_wds_x3f_480_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
lean_dec(v_wds_x3f_480_);
lean_dec(v___x_474_);
lean_dec(v_args_x3f_448_);
lean_dec(v___y_447_);
lean_dec(v___y_446_);
lean_dec(v___y_441_);
lean_dec(v___y_440_);
v___x_483_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_484_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_483_, v___y_449_, v___y_450_);
lean_dec(v_x_93_);
return v___x_484_;
}
else
{
lean_dec(v_x_93_);
v___y_300_ = v___x_474_;
v___y_301_ = v___y_440_;
v___y_302_ = v___y_450_;
v___y_303_ = v___x_455_;
v___y_304_ = v___x_462_;
v___y_305_ = v_args_x3f_448_;
v___y_306_ = v___x_453_;
v___y_307_ = v___y_444_;
v___y_308_ = v___y_449_;
v___y_309_ = v___x_454_;
v___y_310_ = v___y_446_;
v___y_311_ = v___x_457_;
v___y_312_ = v___y_442_;
v___y_313_ = v___y_441_;
v___y_314_ = v___x_456_;
v___y_315_ = v_wds_x3f_480_;
v___y_316_ = v___y_447_;
goto v___jp_299_;
}
}
else
{
lean_dec(v_x_93_);
v___y_300_ = v___x_474_;
v___y_301_ = v___y_440_;
v___y_302_ = v___y_450_;
v___y_303_ = v___x_455_;
v___y_304_ = v___x_462_;
v___y_305_ = v_args_x3f_448_;
v___y_306_ = v___x_453_;
v___y_307_ = v___y_444_;
v___y_308_ = v___y_449_;
v___y_309_ = v___x_454_;
v___y_310_ = v___y_446_;
v___y_311_ = v___x_457_;
v___y_312_ = v___y_442_;
v___y_313_ = v___y_441_;
v___y_314_ = v___x_456_;
v___y_315_ = v_wds_x3f_480_;
v___y_316_ = v___y_447_;
goto v___jp_299_;
}
}
}
else
{
lean_object* v___x_485_; 
lean_dec(v___x_475_);
lean_dec(v_x_93_);
v___x_485_ = lean_box(0);
v___y_230_ = v___x_474_;
v___y_231_ = v___y_440_;
v___y_232_ = v___x_455_;
v___y_233_ = v___x_462_;
v___y_234_ = v_args_x3f_448_;
v___y_235_ = v___x_453_;
v___y_236_ = v___y_444_;
v___y_237_ = v___x_454_;
v___y_238_ = v___y_446_;
v___y_239_ = v___x_457_;
v___y_240_ = v___y_441_;
v___y_241_ = v___y_442_;
v___y_242_ = v___x_456_;
v___y_243_ = v___y_447_;
v_wds_x3f_244_ = v___x_485_;
v___y_245_ = v___y_449_;
v___y_246_ = v___y_450_;
goto v___jp_229_;
}
}
}
}
}
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_486_ = l_Lean_Syntax_getArg(v___x_451_, v___x_145_);
v___x_487_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46));
v___x_488_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47));
v___x_489_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__52));
v___x_490_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53));
lean_inc(v___x_486_);
v___x_491_ = l_Lean_Syntax_isOfKind(v___x_486_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
lean_dec(v___x_486_);
lean_dec(v___x_451_);
lean_dec(v_args_x3f_448_);
lean_dec(v___y_447_);
lean_dec(v___y_446_);
lean_dec(v___y_441_);
lean_dec(v___y_440_);
v___x_492_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_493_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_492_, v___y_449_, v___y_450_);
lean_dec(v_x_93_);
return v___x_493_;
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_494_ = l_Lean_Syntax_getArg(v___x_486_, v___y_442_);
lean_dec(v___x_486_);
v___x_495_ = l_Lean_Syntax_getArg(v___x_451_, v___y_442_);
lean_dec(v___x_451_);
v___x_496_ = l_Lean_Syntax_isNone(v___x_495_);
if (v___x_496_ == 0)
{
uint8_t v___x_497_; 
lean_inc(v___x_495_);
v___x_497_ = l_Lean_Syntax_matchesNull(v___x_495_, v___y_442_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; 
lean_dec(v___x_495_);
lean_dec(v___x_494_);
lean_dec(v_args_x3f_448_);
lean_dec(v___y_447_);
lean_dec(v___y_446_);
lean_dec(v___y_441_);
lean_dec(v___y_440_);
v___x_498_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_499_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_498_, v___y_449_, v___y_450_);
lean_dec(v_x_93_);
return v___x_499_;
}
else
{
lean_object* v_wds_x3f_500_; 
v_wds_x3f_500_ = l_Lean_Syntax_getArg(v___x_495_, v___x_145_);
lean_dec(v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51));
lean_inc(v_wds_x3f_500_);
v___x_502_ = l_Lean_Syntax_isOfKind(v_wds_x3f_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec(v_wds_x3f_500_);
lean_dec(v___x_494_);
lean_dec(v_args_x3f_448_);
lean_dec(v___y_447_);
lean_dec(v___y_446_);
lean_dec(v___y_441_);
lean_dec(v___y_440_);
v___x_503_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_504_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_503_, v___y_449_, v___y_450_);
lean_dec(v_x_93_);
return v___x_504_;
}
else
{
lean_dec(v_x_93_);
v___y_423_ = v___x_490_;
v___y_424_ = v___y_440_;
v___y_425_ = v___y_450_;
v___y_426_ = v_args_x3f_448_;
v___y_427_ = v___y_449_;
v___y_428_ = v___y_446_;
v___y_429_ = v___x_494_;
v___y_430_ = v_wds_x3f_500_;
v___y_431_ = v___y_439_;
v___y_432_ = v___x_487_;
v___y_433_ = v___y_441_;
v___y_434_ = v___x_488_;
v___y_435_ = v___x_489_;
v___y_436_ = v___y_447_;
goto v___jp_422_;
}
}
else
{
lean_dec(v_x_93_);
v___y_423_ = v___x_490_;
v___y_424_ = v___y_440_;
v___y_425_ = v___y_450_;
v___y_426_ = v_args_x3f_448_;
v___y_427_ = v___y_449_;
v___y_428_ = v___y_446_;
v___y_429_ = v___x_494_;
v___y_430_ = v_wds_x3f_500_;
v___y_431_ = v___y_439_;
v___y_432_ = v___x_487_;
v___y_433_ = v___y_441_;
v___y_434_ = v___x_488_;
v___y_435_ = v___x_489_;
v___y_436_ = v___y_447_;
goto v___jp_422_;
}
}
}
else
{
lean_object* v___x_505_; 
lean_dec(v___x_495_);
lean_dec(v_x_93_);
v___x_505_ = lean_box(0);
v___y_400_ = v___y_439_;
v___y_401_ = v___x_490_;
v___y_402_ = v___x_487_;
v___y_403_ = v___y_440_;
v___y_404_ = v_args_x3f_448_;
v___y_405_ = v___y_441_;
v___y_406_ = v___x_488_;
v___y_407_ = v___x_489_;
v___y_408_ = v___y_446_;
v___y_409_ = v___x_494_;
v___y_410_ = v___y_447_;
v_wds_x3f_411_ = v___x_505_;
v___y_412_ = v___y_449_;
v___y_413_ = v___y_450_;
goto v___jp_399_;
}
}
}
}
v___jp_506_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_512_ = lean_unsigned_to_nat(3u);
v___x_513_ = l_Lean_Syntax_getArg(v_x_93_, v___x_512_);
v___x_514_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55));
lean_inc(v___x_513_);
v___x_515_ = l_Lean_Syntax_isOfKind(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec(v___x_513_);
lean_dec(v_attrs_x3f_509_);
lean_dec(v___y_508_);
v___x_516_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_517_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_516_, v___y_510_, v___y_511_);
lean_dec(v_x_93_);
return v___x_517_;
}
else
{
lean_object* v___x_518_; lean_object* v_kw_519_; lean_object* v_name_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_518_ = lean_unsigned_to_nat(2u);
v_kw_519_ = l_Lean_Syntax_getArg(v_x_93_, v___x_518_);
v_name_520_ = l_Lean_Syntax_getArg(v___x_513_, v___x_145_);
v___x_521_ = l_Lean_Syntax_getArg(v___x_513_, v___y_507_);
v___x_522_ = l_Lean_Syntax_isNone(v___x_521_);
if (v___x_522_ == 0)
{
uint8_t v___x_523_; 
lean_inc(v___x_521_);
v___x_523_ = l_Lean_Syntax_matchesNull(v___x_521_, v___y_507_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; 
lean_dec(v___x_521_);
lean_dec(v_name_520_);
lean_dec(v_kw_519_);
lean_dec(v___x_513_);
lean_dec(v_attrs_x3f_509_);
lean_dec(v___y_508_);
v___x_524_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_525_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_524_, v___y_510_, v___y_511_);
lean_dec(v_x_93_);
return v___x_525_;
}
else
{
lean_object* v_args_x3f_526_; lean_object* v___x_527_; 
v_args_x3f_526_ = l_Lean_Syntax_getArg(v___x_521_, v___x_145_);
lean_dec(v___x_521_);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v_args_x3f_526_);
v___y_439_ = v___x_514_;
v___y_440_ = v_name_520_;
v___y_441_ = v___y_508_;
v___y_442_ = v___y_507_;
v___y_443_ = v___x_513_;
v___y_444_ = v___x_518_;
v___y_445_ = v___x_512_;
v___y_446_ = v_attrs_x3f_509_;
v___y_447_ = v_kw_519_;
v_args_x3f_448_ = v___x_527_;
v___y_449_ = v___y_510_;
v___y_450_ = v___y_511_;
goto v___jp_438_;
}
}
else
{
lean_object* v___x_528_; 
lean_dec(v___x_521_);
v___x_528_ = lean_box(0);
v___y_439_ = v___x_514_;
v___y_440_ = v_name_520_;
v___y_441_ = v___y_508_;
v___y_442_ = v___y_507_;
v___y_443_ = v___x_513_;
v___y_444_ = v___x_518_;
v___y_445_ = v___x_512_;
v___y_446_ = v_attrs_x3f_509_;
v___y_447_ = v_kw_519_;
v_args_x3f_448_ = v___x_528_;
v___y_449_ = v___y_510_;
v___y_450_ = v___y_511_;
goto v___jp_438_;
}
}
}
v___jp_529_:
{
lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = l_Lean_Syntax_getArg(v_x_93_, v___x_533_);
v___x_535_ = l_Lean_Syntax_isNone(v___x_534_);
if (v___x_535_ == 0)
{
uint8_t v___x_536_; 
lean_inc(v___x_534_);
v___x_536_ = l_Lean_Syntax_matchesNull(v___x_534_, v___x_533_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec(v___x_534_);
lean_dec(v_doc_x3f_530_);
v___x_537_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
v___x_538_ = l_Lean_Macro_throwErrorAt___redArg(v_x_93_, v___x_537_, v___y_531_, v___y_532_);
lean_dec(v_x_93_);
return v___x_538_;
}
else
{
lean_object* v_attrs_x3f_539_; lean_object* v___x_540_; 
v_attrs_x3f_539_ = l_Lean_Syntax_getArg(v___x_534_, v___x_145_);
lean_dec(v___x_534_);
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v_attrs_x3f_539_);
v___y_507_ = v___x_533_;
v___y_508_ = v_doc_x3f_530_;
v_attrs_x3f_509_ = v___x_540_;
v___y_510_ = v___y_531_;
v___y_511_ = v___y_532_;
goto v___jp_506_;
}
}
else
{
lean_object* v___x_541_; 
lean_dec(v___x_534_);
v___x_541_ = lean_box(0);
v___y_507_ = v___x_533_;
v___y_508_ = v_doc_x3f_530_;
v_attrs_x3f_509_ = v___x_541_;
v___y_510_ = v___y_531_;
v___y_511_ = v___y_532_;
goto v___jp_506_;
}
}
}
v___jp_96_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
lean_inc_ref(v___y_111_);
v___x_113_ = l_Array_append___redArg(v___y_111_, v___y_112_);
lean_dec_ref(v___y_112_);
lean_inc(v___y_108_);
lean_inc_n(v___y_103_, 3);
v___x_114_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_114_, 0, v___y_103_);
lean_ctor_set(v___x_114_, 1, v___y_108_);
lean_ctor_set(v___x_114_, 2, v___x_113_);
lean_inc(v___y_106_);
v___x_115_ = l_Lean_Syntax_node4(v___y_103_, v___y_106_, v___y_105_, v___y_100_, v___y_104_, v___x_114_);
v___x_116_ = l_Lean_Syntax_node5(v___y_103_, v___y_98_, v___y_99_, v___y_102_, v___y_101_, v___x_115_, v___y_110_);
v___x_117_ = l_Lean_Syntax_node2(v___y_103_, v___y_109_, v___y_97_, v___x_116_);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v___y_107_);
return v___x_118_;
}
v___jp_120_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
lean_inc_ref(v___y_121_);
v___x_136_ = l_Array_append___redArg(v___y_121_, v___y_135_);
lean_dec_ref(v___y_135_);
lean_inc(v___y_133_);
lean_inc_n(v___y_128_, 3);
v___x_137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_137_, 0, v___y_128_);
lean_ctor_set(v___x_137_, 1, v___y_133_);
lean_ctor_set(v___x_137_, 2, v___x_136_);
v___x_138_ = l_Lean_Syntax_node4(v___y_128_, v___y_134_, v___y_132_, v___y_122_, v___y_124_, v___x_137_);
lean_inc(v___y_130_);
v___x_139_ = l_Lean_Syntax_node3(v___y_128_, v___y_130_, v___y_123_, v___y_127_, v___x_138_);
v___x_140_ = l_Lean_Syntax_node4(v___y_128_, v___x_119_, v___y_125_, v___y_131_, v___y_126_, v___x_139_);
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v___y_129_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___boxed(lean_object* v_x_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl(v_x_551_, v_a_552_, v_a_553_);
lean_dec_ref(v_a_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1(){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_583_ = l_Lean_Elab_macroAttribute;
v___x_584_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3));
v___x_585_ = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__10));
v___x_586_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___boxed), 3, 0);
v___x_587_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_583_, v___x_584_, v___x_585_, v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___boxed(lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1();
return v_res_589_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Attributes(uint8_t builtin);
lean_object* runtime_initialize_Lake_DSL_Syntax(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_Script(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
