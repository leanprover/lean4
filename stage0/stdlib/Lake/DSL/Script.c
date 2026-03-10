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
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__0_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__1_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scriptDecl"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__2 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16_value),LEAN_SCALAR_PTR_LITERAL(165, 12, 188, 107, 238, 45, 212, 138)}};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__18 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__18_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Array_mkArray0(lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lake_DSL_expandOptSimpleBinder(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_DSL_expandIdentOrStrAsIdent(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lake_DSL_expandAttrs(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__0 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__0_value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___boxed(lean_object*);
static lean_object* _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__34));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_50; 
x_27 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3));
lean_inc(x_1);
x_50 = l_Lean_Syntax_isOfKind(x_1, x_27);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_52 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_51, x_2, x_3);
lean_dec(x_1);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_423; uint8_t x_424; 
x_53 = lean_unsigned_to_nat(0u);
x_423 = l_Lean_Syntax_getArg(x_1, x_53);
x_424 = l_Lean_Syntax_isNone(x_423);
if (x_424 == 0)
{
lean_object* x_425; uint8_t x_426; 
x_425 = lean_unsigned_to_nat(1u);
lean_inc(x_423);
x_426 = l_Lean_Syntax_matchesNull(x_423, x_425);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; 
lean_dec(x_423);
x_427 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_428 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_427, x_2, x_3);
lean_dec(x_1);
return x_428;
}
else
{
lean_object* x_429; lean_object* x_430; 
x_429 = l_Lean_Syntax_getArg(x_423, x_53);
lean_dec(x_423);
x_430 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_430, 0, x_429);
x_410 = x_430;
x_411 = x_2;
x_412 = x_3;
goto block_422;
}
}
else
{
lean_object* x_431; 
lean_dec(x_423);
x_431 = lean_box(0);
x_410 = x_431;
x_411 = x_2;
x_412 = x_3;
goto block_422;
}
block_136:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_inc_ref(x_67);
x_77 = l_Array_append___redArg(x_67, x_76);
lean_dec_ref(x_76);
lean_inc(x_62);
lean_inc(x_64);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_64);
lean_ctor_set(x_78, 1, x_62);
lean_ctor_set(x_78, 2, x_77);
x_79 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__5));
lean_inc_ref(x_54);
lean_inc_ref(x_61);
lean_inc_ref(x_70);
x_80 = l_Lean_Name_mkStr4(x_70, x_61, x_54, x_79);
x_81 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__6));
lean_inc(x_64);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_64);
lean_ctor_set(x_82, 1, x_81);
x_83 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__7));
x_84 = l_Lean_Syntax_SepArray_ofElems(x_83, x_58);
lean_dec_ref(x_58);
lean_inc_ref(x_67);
x_85 = l_Array_append___redArg(x_67, x_84);
lean_dec_ref(x_84);
lean_inc(x_62);
lean_inc(x_64);
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_64);
lean_ctor_set(x_86, 1, x_62);
lean_ctor_set(x_86, 2, x_85);
x_87 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__8));
lean_inc(x_64);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_64);
lean_ctor_set(x_88, 1, x_87);
lean_inc(x_64);
x_89 = l_Lean_Syntax_node3(x_64, x_80, x_82, x_86, x_88);
lean_inc(x_62);
lean_inc(x_64);
x_90 = l_Lean_Syntax_node1(x_64, x_62, x_89);
lean_inc_n(x_55, 5);
lean_inc(x_64);
x_91 = l_Lean_Syntax_node7(x_64, x_63, x_78, x_90, x_55, x_55, x_55, x_55, x_55);
x_92 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__9));
lean_inc_ref(x_73);
lean_inc_ref(x_61);
lean_inc_ref(x_70);
x_93 = l_Lean_Name_mkStr4(x_70, x_61, x_73, x_92);
x_94 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__10));
lean_inc(x_64);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_64);
lean_ctor_set(x_95, 1, x_94);
x_96 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__11));
lean_inc_ref(x_73);
lean_inc_ref(x_61);
lean_inc_ref(x_70);
x_97 = l_Lean_Name_mkStr4(x_70, x_61, x_73, x_96);
x_98 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12));
x_99 = lean_box(2);
lean_inc(x_62);
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_62);
lean_ctor_set(x_100, 2, x_98);
x_101 = lean_mk_empty_array_with_capacity(x_59);
x_102 = lean_array_push(x_101, x_65);
x_103 = lean_array_push(x_102, x_100);
x_104 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_97);
lean_ctor_set(x_104, 2, x_103);
x_105 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__13));
lean_inc_ref(x_61);
lean_inc_ref(x_70);
x_106 = l_Lean_Name_mkStr4(x_70, x_61, x_73, x_105);
x_107 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__14));
lean_inc_ref(x_54);
lean_inc_ref(x_61);
lean_inc_ref(x_70);
x_108 = l_Lean_Name_mkStr4(x_70, x_61, x_54, x_107);
x_109 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__15));
lean_inc(x_64);
x_110 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_110, 0, x_64);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_obj_once(&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17, &l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17_once, _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17);
x_112 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__18));
x_113 = l_Lean_addMacroScope(x_66, x_112, x_56);
x_114 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__20));
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_57);
lean_inc(x_64);
x_116 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_116, 0, x_64);
lean_ctor_set(x_116, 1, x_111);
lean_ctor_set(x_116, 2, x_113);
lean_ctor_set(x_116, 3, x_115);
lean_inc(x_64);
x_117 = l_Lean_Syntax_node2(x_64, x_108, x_110, x_116);
lean_inc(x_62);
lean_inc(x_64);
x_118 = l_Lean_Syntax_node1(x_64, x_62, x_117);
lean_inc(x_55);
lean_inc(x_64);
x_119 = l_Lean_Syntax_node2(x_64, x_106, x_55, x_118);
x_120 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21));
lean_inc(x_64);
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_64);
lean_ctor_set(x_121, 1, x_120);
x_122 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__22));
lean_inc_ref(x_54);
lean_inc_ref(x_61);
lean_inc_ref(x_70);
x_123 = l_Lean_Name_mkStr4(x_70, x_61, x_54, x_122);
lean_inc(x_64);
x_124 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_124, 0, x_64);
lean_ctor_set(x_124, 1, x_122);
x_125 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__23));
x_126 = l_Lean_Name_mkStr4(x_70, x_61, x_54, x_125);
lean_inc(x_62);
lean_inc(x_64);
x_127 = l_Lean_Syntax_node1(x_64, x_62, x_71);
x_128 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__24));
lean_inc(x_64);
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_64);
lean_ctor_set(x_129, 1, x_128);
lean_inc(x_55);
lean_inc(x_64);
x_130 = l_Lean_Syntax_node4(x_64, x_126, x_127, x_55, x_129, x_75);
lean_inc(x_64);
x_131 = l_Lean_Syntax_node2(x_64, x_123, x_124, x_130);
lean_inc_n(x_55, 2);
lean_inc(x_64);
x_132 = l_Lean_Syntax_node2(x_64, x_72, x_55, x_55);
if (lean_obj_tag(x_68) == 1)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_68, 0);
lean_inc(x_133);
lean_dec_ref(x_68);
x_134 = l_Array_mkArray1___redArg(x_133);
x_4 = x_93;
x_5 = x_55;
x_6 = x_132;
x_7 = x_91;
x_8 = x_131;
x_9 = x_60;
x_10 = x_119;
x_11 = x_121;
x_12 = x_62;
x_13 = x_104;
x_14 = x_64;
x_15 = x_67;
x_16 = x_95;
x_17 = x_69;
x_18 = x_74;
x_19 = x_134;
goto block_26;
}
else
{
lean_object* x_135; 
lean_dec(x_68);
x_135 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25));
x_4 = x_93;
x_5 = x_55;
x_6 = x_132;
x_7 = x_91;
x_8 = x_131;
x_9 = x_60;
x_10 = x_119;
x_11 = x_121;
x_12 = x_62;
x_13 = x_104;
x_14 = x_64;
x_15 = x_67;
x_16 = x_95;
x_17 = x_69;
x_18 = x_74;
x_19 = x_135;
goto block_26;
}
}
block_212:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_211; 
x_154 = lean_ctor_get(x_152, 0);
x_155 = lean_ctor_get(x_152, 1);
x_156 = lean_ctor_get(x_152, 2);
x_157 = lean_ctor_get(x_152, 3);
x_158 = lean_ctor_get(x_152, 4);
x_159 = lean_ctor_get(x_152, 5);
x_211 = !lean_is_exclusive(x_152);
if (x_211 == 0)
{
x_160 = x_152;
x_161 = x_211;
goto block_210;
}
else
{
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_152);
x_160 = lean_box(0);
x_161 = x_211;
goto block_210;
}
block_210:
{
lean_object* x_162; lean_object* x_163; 
x_162 = l_Lean_replaceRef(x_143, x_159);
lean_dec(x_159);
lean_dec(x_143);
lean_inc(x_162);
lean_inc(x_156);
lean_inc(x_155);
if (x_161 == 0)
{
lean_ctor_set(x_160, 5, x_162);
x_163 = x_160;
goto block_208;
}
else
{
lean_object* x_209; 
x_209 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_209, 0, x_154);
lean_ctor_set(x_209, 1, x_155);
lean_ctor_set(x_209, 2, x_156);
lean_ctor_set(x_209, 3, x_157);
lean_ctor_set(x_209, 4, x_158);
lean_ctor_set(x_209, 5, x_162);
x_163 = x_209;
goto block_208;
}
block_208:
{
lean_object* x_164; 
x_164 = l_Lake_DSL_expandOptSimpleBinder(x_144, x_163, x_153);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec_ref(x_164);
x_167 = l_Lake_DSL_expandIdentOrStrAsIdent(x_141);
x_168 = l_Lean_SourceInfo_fromRef(x_162, x_149);
lean_dec(x_162);
x_169 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26));
x_170 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__27));
lean_inc_ref(x_140);
lean_inc_ref(x_145);
x_171 = l_Lean_Name_mkStr4(x_145, x_140, x_169, x_170);
x_172 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__28));
lean_inc_ref(x_140);
lean_inc_ref(x_145);
x_173 = l_Lean_Name_mkStr4(x_145, x_140, x_169, x_172);
x_174 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30));
x_175 = lean_obj_once(&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31, &l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31_once, _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31);
lean_inc(x_168);
x_176 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_176, 0, x_168);
lean_ctor_set(x_176, 1, x_174);
lean_ctor_set(x_176, 2, x_175);
lean_inc_ref(x_176);
lean_inc(x_168);
x_177 = l_Lean_Syntax_node1(x_168, x_173, x_176);
x_178 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32));
x_179 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33));
lean_inc_ref(x_140);
lean_inc_ref(x_145);
x_180 = l_Lean_Name_mkStr4(x_145, x_140, x_178, x_179);
x_181 = lean_obj_once(&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35, &l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35_once, _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35);
x_182 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__37));
lean_inc(x_156);
lean_inc(x_155);
x_183 = l_Lean_addMacroScope(x_155, x_182, x_156);
x_184 = lean_box(0);
lean_inc(x_168);
x_185 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_185, 0, x_168);
lean_ctor_set(x_185, 1, x_181);
lean_ctor_set(x_185, 2, x_183);
lean_ctor_set(x_185, 3, x_184);
lean_inc_ref(x_176);
lean_inc(x_168);
x_186 = l_Lean_Syntax_node2(x_168, x_180, x_185, x_176);
lean_inc(x_168);
x_187 = l_Lean_Syntax_node2(x_168, x_171, x_177, x_186);
x_188 = lean_mk_empty_array_with_capacity(x_142);
x_189 = lean_array_push(x_188, x_187);
x_190 = l_Lake_DSL_expandAttrs(x_137);
x_191 = l_Array_append___redArg(x_189, x_190);
lean_dec_ref(x_190);
x_192 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__38));
lean_inc_ref(x_147);
lean_inc_ref(x_140);
lean_inc_ref(x_145);
x_193 = l_Lean_Name_mkStr4(x_145, x_140, x_147, x_192);
x_194 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__39));
lean_inc_ref(x_147);
lean_inc_ref(x_140);
lean_inc_ref(x_145);
x_195 = l_Lean_Name_mkStr4(x_145, x_140, x_147, x_194);
if (lean_obj_tag(x_146) == 1)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_146, 0);
lean_inc(x_196);
lean_dec_ref(x_146);
x_197 = l_Array_mkArray1___redArg(x_196);
x_54 = x_169;
x_55 = x_176;
x_56 = x_156;
x_57 = x_184;
x_58 = x_191;
x_59 = x_138;
x_60 = x_139;
x_61 = x_140;
x_62 = x_174;
x_63 = x_195;
x_64 = x_168;
x_65 = x_167;
x_66 = x_155;
x_67 = x_175;
x_68 = x_151;
x_69 = x_166;
x_70 = x_145;
x_71 = x_165;
x_72 = x_148;
x_73 = x_147;
x_74 = x_193;
x_75 = x_150;
x_76 = x_197;
goto block_136;
}
else
{
lean_object* x_198; 
lean_dec(x_146);
x_198 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25));
x_54 = x_169;
x_55 = x_176;
x_56 = x_156;
x_57 = x_184;
x_58 = x_191;
x_59 = x_138;
x_60 = x_139;
x_61 = x_140;
x_62 = x_174;
x_63 = x_195;
x_64 = x_168;
x_65 = x_167;
x_66 = x_155;
x_67 = x_175;
x_68 = x_151;
x_69 = x_166;
x_70 = x_145;
x_71 = x_165;
x_72 = x_148;
x_73 = x_147;
x_74 = x_193;
x_75 = x_150;
x_76 = x_198;
goto block_136;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; uint8_t x_207; 
lean_dec(x_162);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_148);
lean_dec_ref(x_147);
lean_dec(x_146);
lean_dec_ref(x_145);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec(x_137);
x_199 = lean_ctor_get(x_164, 0);
x_200 = lean_ctor_get(x_164, 1);
x_207 = !lean_is_exclusive(x_164);
if (x_207 == 0)
{
x_201 = x_164;
x_202 = x_207;
goto block_206;
}
else
{
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_164);
x_201 = lean_box(0);
x_202 = x_207;
goto block_206;
}
block_206:
{
lean_object* x_203; 
if (x_202 == 0)
{
x_203 = x_201;
goto block_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_199);
lean_ctor_set(x_205, 1, x_200);
x_203 = x_205;
goto block_204;
}
block_204:
{
return x_203;
}
}
}
}
}
}
block_246:
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_inc_ref(x_219);
x_229 = l_Array_append___redArg(x_219, x_228);
lean_dec_ref(x_228);
lean_inc(x_217);
lean_inc(x_220);
x_230 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_230, 0, x_220);
lean_ctor_set(x_230, 1, x_217);
lean_ctor_set(x_230, 2, x_229);
x_231 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40));
x_232 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__41));
lean_inc_ref(x_213);
lean_inc_ref(x_222);
x_233 = l_Lean_Name_mkStr4(x_222, x_213, x_231, x_232);
x_234 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21));
lean_inc(x_220);
x_235 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_235, 0, x_220);
lean_ctor_set(x_235, 1, x_234);
lean_inc(x_220);
x_236 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_236, 0, x_220);
lean_ctor_set(x_236, 1, x_225);
lean_inc(x_220);
x_237 = l_Lean_Syntax_node2(x_220, x_218, x_236, x_224);
x_238 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__42));
x_239 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__43));
x_240 = l_Lean_Name_mkStr4(x_222, x_213, x_238, x_239);
lean_inc_ref(x_219);
lean_inc(x_217);
lean_inc(x_220);
x_241 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_241, 0, x_220);
lean_ctor_set(x_241, 1, x_217);
lean_ctor_set(x_241, 2, x_219);
lean_inc_ref(x_241);
lean_inc(x_220);
x_242 = l_Lean_Syntax_node2(x_220, x_240, x_241, x_241);
if (lean_obj_tag(x_215) == 1)
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_215, 0);
lean_inc(x_243);
lean_dec_ref(x_215);
x_244 = l_Array_mkArray1___redArg(x_243);
x_28 = x_242;
x_29 = x_214;
x_30 = x_216;
x_31 = x_217;
x_32 = x_233;
x_33 = x_237;
x_34 = x_230;
x_35 = x_219;
x_36 = x_220;
x_37 = x_221;
x_38 = x_223;
x_39 = x_235;
x_40 = x_226;
x_41 = x_227;
x_42 = x_244;
goto block_49;
}
else
{
lean_object* x_245; 
lean_dec(x_215);
x_245 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25));
x_28 = x_242;
x_29 = x_214;
x_30 = x_216;
x_31 = x_217;
x_32 = x_233;
x_33 = x_237;
x_34 = x_230;
x_35 = x_219;
x_36 = x_220;
x_37 = x_221;
x_38 = x_223;
x_39 = x_235;
x_40 = x_226;
x_41 = x_227;
x_42 = x_245;
goto block_49;
}
}
block_271:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_inc_ref(x_252);
x_263 = l_Array_append___redArg(x_252, x_262);
lean_dec_ref(x_262);
lean_inc(x_250);
lean_inc(x_253);
x_264 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_264, 0, x_253);
lean_ctor_set(x_264, 1, x_250);
lean_ctor_set(x_264, 2, x_263);
x_265 = l_Lean_SourceInfo_fromRef(x_257, x_50);
lean_dec(x_257);
x_266 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__36));
x_267 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
if (lean_obj_tag(x_258) == 1)
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_ctor_get(x_258, 0);
lean_inc(x_268);
lean_dec_ref(x_258);
x_269 = l_Array_mkArray1___redArg(x_268);
x_213 = x_247;
x_214 = x_248;
x_215 = x_249;
x_216 = x_267;
x_217 = x_250;
x_218 = x_251;
x_219 = x_252;
x_220 = x_253;
x_221 = x_254;
x_222 = x_255;
x_223 = x_256;
x_224 = x_259;
x_225 = x_261;
x_226 = x_260;
x_227 = x_264;
x_228 = x_269;
goto block_246;
}
else
{
lean_object* x_270; 
lean_dec(x_258);
x_270 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25));
x_213 = x_247;
x_214 = x_248;
x_215 = x_249;
x_216 = x_267;
x_217 = x_250;
x_218 = x_251;
x_219 = x_252;
x_220 = x_253;
x_221 = x_254;
x_222 = x_255;
x_223 = x_256;
x_224 = x_259;
x_225 = x_261;
x_226 = x_260;
x_227 = x_264;
x_228 = x_270;
goto block_246;
}
}
block_293:
{
lean_object* x_288; lean_object* x_289; 
lean_inc_ref(x_278);
x_288 = l_Array_append___redArg(x_278, x_287);
lean_dec_ref(x_287);
lean_inc(x_275);
lean_inc(x_279);
x_289 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_289, 0, x_279);
lean_ctor_set(x_289, 1, x_275);
lean_ctor_set(x_289, 2, x_288);
if (lean_obj_tag(x_276) == 1)
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_276, 0);
lean_inc(x_290);
lean_dec_ref(x_276);
x_291 = l_Array_mkArray1___redArg(x_290);
x_247 = x_272;
x_248 = x_273;
x_249 = x_274;
x_250 = x_275;
x_251 = x_277;
x_252 = x_278;
x_253 = x_279;
x_254 = x_280;
x_255 = x_281;
x_256 = x_289;
x_257 = x_282;
x_258 = x_283;
x_259 = x_284;
x_260 = x_286;
x_261 = x_285;
x_262 = x_291;
goto block_271;
}
else
{
lean_object* x_292; 
lean_dec(x_276);
x_292 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25));
x_247 = x_272;
x_248 = x_273;
x_249 = x_274;
x_250 = x_275;
x_251 = x_277;
x_252 = x_278;
x_253 = x_279;
x_254 = x_280;
x_255 = x_281;
x_256 = x_289;
x_257 = x_282;
x_258 = x_283;
x_259 = x_284;
x_260 = x_286;
x_261 = x_285;
x_262 = x_292;
goto block_271;
}
}
block_316:
{
lean_object* x_308; uint8_t x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_308 = lean_ctor_get(x_306, 5);
lean_inc(x_308);
lean_dec_ref(x_306);
x_309 = 0;
x_310 = l_Lean_SourceInfo_fromRef(x_308, x_309);
lean_dec(x_308);
x_311 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30));
x_312 = lean_obj_once(&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31, &l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31_once, _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31);
if (lean_obj_tag(x_304) == 1)
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_304, 0);
lean_inc(x_313);
lean_dec_ref(x_304);
x_314 = l_Array_mkArray1___redArg(x_313);
x_272 = x_295;
x_273 = x_307;
x_274 = x_305;
x_275 = x_311;
x_276 = x_299;
x_277 = x_303;
x_278 = x_312;
x_279 = x_310;
x_280 = x_294;
x_281 = x_296;
x_282 = x_297;
x_283 = x_298;
x_284 = x_300;
x_285 = x_302;
x_286 = x_301;
x_287 = x_314;
goto block_293;
}
else
{
lean_object* x_315; 
lean_dec(x_304);
x_315 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25));
x_272 = x_295;
x_273 = x_307;
x_274 = x_305;
x_275 = x_311;
x_276 = x_299;
x_277 = x_303;
x_278 = x_312;
x_279 = x_310;
x_280 = x_294;
x_281 = x_296;
x_282 = x_297;
x_283 = x_298;
x_284 = x_300;
x_285 = x_302;
x_286 = x_301;
x_287 = x_315;
goto block_293;
}
}
block_386:
{
lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_329 = l_Lean_Syntax_getArg(x_323, x_322);
lean_dec(x_323);
x_330 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45));
lean_inc(x_329);
x_331 = l_Lean_Syntax_isOfKind(x_329, x_330);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; 
lean_dec(x_324);
x_332 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46));
x_333 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47));
x_334 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40));
x_335 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48));
lean_inc(x_329);
x_336 = l_Lean_Syntax_isOfKind(x_329, x_335);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; 
lean_dec(x_329);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_321);
lean_dec(x_319);
lean_dec(x_317);
x_337 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_338 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_337, x_327, x_328);
lean_dec(x_1);
return x_338;
}
else
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_339 = l_Lean_Syntax_getArg(x_329, x_322);
x_340 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49));
lean_inc(x_339);
x_341 = l_Lean_Syntax_isOfKind(x_339, x_340);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; 
lean_dec(x_339);
lean_dec(x_329);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_321);
lean_dec(x_319);
lean_dec(x_317);
x_342 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_343 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_342, x_327, x_328);
lean_dec(x_1);
return x_343;
}
else
{
lean_object* x_344; uint8_t x_345; 
x_344 = l_Lean_Syntax_getArg(x_339, x_53);
x_345 = l_Lean_Syntax_matchesNull(x_344, x_53);
if (x_345 == 0)
{
lean_object* x_346; lean_object* x_347; 
lean_dec(x_339);
lean_dec(x_329);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_321);
lean_dec(x_319);
lean_dec(x_317);
x_346 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_347 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_346, x_327, x_328);
lean_dec(x_1);
return x_347;
}
else
{
lean_object* x_348; uint8_t x_349; 
x_348 = l_Lean_Syntax_getArg(x_339, x_318);
lean_dec(x_339);
x_349 = l_Lean_Syntax_matchesNull(x_348, x_53);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; 
lean_dec(x_329);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_321);
lean_dec(x_319);
lean_dec(x_317);
x_350 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_351 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_350, x_327, x_328);
lean_dec(x_1);
return x_351;
}
else
{
lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_352 = l_Lean_Syntax_getArg(x_329, x_318);
x_353 = l_Lean_Syntax_getArg(x_329, x_320);
lean_dec(x_329);
x_354 = l_Lean_Syntax_isNone(x_353);
if (x_354 == 0)
{
uint8_t x_355; 
lean_inc(x_353);
x_355 = l_Lean_Syntax_matchesNull(x_353, x_318);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; 
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_321);
lean_dec(x_319);
lean_dec(x_317);
x_356 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_357 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_356, x_327, x_328);
lean_dec(x_1);
return x_357;
}
else
{
lean_object* x_358; lean_object* x_359; uint8_t x_360; 
x_358 = l_Lean_Syntax_getArg(x_353, x_53);
lean_dec(x_353);
x_359 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51));
lean_inc(x_358);
x_360 = l_Lean_Syntax_isOfKind(x_358, x_359);
if (x_360 == 0)
{
lean_object* x_361; lean_object* x_362; 
lean_dec(x_358);
lean_dec(x_352);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_321);
lean_dec(x_319);
lean_dec(x_317);
x_361 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_362 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_361, x_327, x_328);
lean_dec(x_1);
return x_362;
}
else
{
lean_object* x_363; 
lean_dec(x_1);
x_363 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_363, 0, x_358);
x_137 = x_321;
x_138 = x_322;
x_139 = x_335;
x_140 = x_333;
x_141 = x_317;
x_142 = x_318;
x_143 = x_319;
x_144 = x_326;
x_145 = x_332;
x_146 = x_325;
x_147 = x_334;
x_148 = x_340;
x_149 = x_331;
x_150 = x_352;
x_151 = x_363;
x_152 = x_327;
x_153 = x_328;
goto block_212;
}
}
}
else
{
lean_object* x_364; 
lean_dec(x_353);
lean_dec(x_1);
x_364 = lean_box(0);
x_137 = x_321;
x_138 = x_322;
x_139 = x_335;
x_140 = x_333;
x_141 = x_317;
x_142 = x_318;
x_143 = x_319;
x_144 = x_326;
x_145 = x_332;
x_146 = x_325;
x_147 = x_334;
x_148 = x_340;
x_149 = x_331;
x_150 = x_352;
x_151 = x_364;
x_152 = x_327;
x_153 = x_328;
goto block_212;
}
}
}
}
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; 
x_365 = l_Lean_Syntax_getArg(x_329, x_53);
x_366 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46));
x_367 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47));
x_368 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__52));
x_369 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53));
lean_inc(x_365);
x_370 = l_Lean_Syntax_isOfKind(x_365, x_369);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; 
lean_dec(x_365);
lean_dec(x_329);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_321);
lean_dec(x_319);
lean_dec(x_317);
x_371 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_372 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_371, x_327, x_328);
lean_dec(x_1);
return x_372;
}
else
{
lean_object* x_373; lean_object* x_374; uint8_t x_375; 
x_373 = l_Lean_Syntax_getArg(x_365, x_318);
lean_dec(x_365);
x_374 = l_Lean_Syntax_getArg(x_329, x_318);
lean_dec(x_329);
x_375 = l_Lean_Syntax_isNone(x_374);
if (x_375 == 0)
{
uint8_t x_376; 
lean_inc(x_374);
x_376 = l_Lean_Syntax_matchesNull(x_374, x_318);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; 
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_321);
lean_dec(x_319);
lean_dec(x_317);
x_377 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_378 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_377, x_327, x_328);
lean_dec(x_1);
return x_378;
}
else
{
lean_object* x_379; lean_object* x_380; uint8_t x_381; 
x_379 = l_Lean_Syntax_getArg(x_374, x_53);
lean_dec(x_374);
x_380 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51));
lean_inc(x_379);
x_381 = l_Lean_Syntax_isOfKind(x_379, x_380);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; 
lean_dec(x_379);
lean_dec(x_373);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_321);
lean_dec(x_319);
lean_dec(x_317);
x_382 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_383 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_382, x_327, x_328);
lean_dec(x_1);
return x_383;
}
else
{
lean_object* x_384; 
lean_dec(x_1);
x_384 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_384, 0, x_379);
x_294 = x_317;
x_295 = x_367;
x_296 = x_366;
x_297 = x_319;
x_298 = x_326;
x_299 = x_321;
x_300 = x_373;
x_301 = x_324;
x_302 = x_368;
x_303 = x_369;
x_304 = x_325;
x_305 = x_384;
x_306 = x_327;
x_307 = x_328;
goto block_316;
}
}
}
else
{
lean_object* x_385; 
lean_dec(x_374);
lean_dec(x_1);
x_385 = lean_box(0);
x_294 = x_317;
x_295 = x_367;
x_296 = x_366;
x_297 = x_319;
x_298 = x_326;
x_299 = x_321;
x_300 = x_373;
x_301 = x_324;
x_302 = x_368;
x_303 = x_369;
x_304 = x_325;
x_305 = x_385;
x_306 = x_327;
x_307 = x_328;
goto block_316;
}
}
}
}
block_409:
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; 
x_392 = lean_unsigned_to_nat(3u);
x_393 = l_Lean_Syntax_getArg(x_1, x_392);
x_394 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55));
lean_inc(x_393);
x_395 = l_Lean_Syntax_isOfKind(x_393, x_394);
if (x_395 == 0)
{
lean_object* x_396; lean_object* x_397; 
lean_dec(x_393);
lean_dec(x_389);
lean_dec(x_388);
x_396 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_397 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_396, x_390, x_391);
lean_dec(x_1);
return x_397;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; 
x_398 = lean_unsigned_to_nat(2u);
x_399 = l_Lean_Syntax_getArg(x_1, x_398);
x_400 = l_Lean_Syntax_getArg(x_393, x_53);
x_401 = l_Lean_Syntax_getArg(x_393, x_387);
x_402 = l_Lean_Syntax_isNone(x_401);
if (x_402 == 0)
{
uint8_t x_403; 
lean_inc(x_401);
x_403 = l_Lean_Syntax_matchesNull(x_401, x_387);
if (x_403 == 0)
{
lean_object* x_404; lean_object* x_405; 
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_399);
lean_dec(x_393);
lean_dec(x_389);
lean_dec(x_388);
x_404 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_405 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_404, x_390, x_391);
lean_dec(x_1);
return x_405;
}
else
{
lean_object* x_406; lean_object* x_407; 
x_406 = l_Lean_Syntax_getArg(x_401, x_53);
lean_dec(x_401);
x_407 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_407, 0, x_406);
x_317 = x_400;
x_318 = x_387;
x_319 = x_399;
x_320 = x_392;
x_321 = x_389;
x_322 = x_398;
x_323 = x_393;
x_324 = x_394;
x_325 = x_388;
x_326 = x_407;
x_327 = x_390;
x_328 = x_391;
goto block_386;
}
}
else
{
lean_object* x_408; 
lean_dec(x_401);
x_408 = lean_box(0);
x_317 = x_400;
x_318 = x_387;
x_319 = x_399;
x_320 = x_392;
x_321 = x_389;
x_322 = x_398;
x_323 = x_393;
x_324 = x_394;
x_325 = x_388;
x_326 = x_408;
x_327 = x_390;
x_328 = x_391;
goto block_386;
}
}
}
block_422:
{
lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_413 = lean_unsigned_to_nat(1u);
x_414 = l_Lean_Syntax_getArg(x_1, x_413);
x_415 = l_Lean_Syntax_isNone(x_414);
if (x_415 == 0)
{
uint8_t x_416; 
lean_inc(x_414);
x_416 = l_Lean_Syntax_matchesNull(x_414, x_413);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; 
lean_dec(x_414);
lean_dec(x_410);
x_417 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_418 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_417, x_411, x_412);
lean_dec(x_1);
return x_418;
}
else
{
lean_object* x_419; lean_object* x_420; 
x_419 = l_Lean_Syntax_getArg(x_414, x_53);
lean_dec(x_414);
x_420 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_420, 0, x_419);
x_387 = x_413;
x_388 = x_410;
x_389 = x_420;
x_390 = x_411;
x_391 = x_412;
goto block_409;
}
}
else
{
lean_object* x_421; 
lean_dec(x_414);
x_421 = lean_box(0);
x_387 = x_413;
x_388 = x_410;
x_389 = x_421;
x_390 = x_411;
x_391 = x_412;
goto block_409;
}
}
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = l_Array_append___redArg(x_15, x_19);
lean_dec_ref(x_19);
lean_inc(x_14);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 2, x_20);
lean_inc(x_14);
x_22 = l_Lean_Syntax_node4(x_14, x_9, x_11, x_8, x_6, x_21);
lean_inc(x_14);
x_23 = l_Lean_Syntax_node5(x_14, x_4, x_16, x_13, x_10, x_22, x_5);
x_24 = l_Lean_Syntax_node2(x_14, x_18, x_7, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
block_49:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = l_Array_append___redArg(x_35, x_42);
lean_dec_ref(x_42);
lean_inc(x_36);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_31);
lean_ctor_set(x_44, 2, x_43);
lean_inc(x_36);
x_45 = l_Lean_Syntax_node4(x_36, x_32, x_39, x_33, x_28, x_44);
lean_inc(x_36);
x_46 = l_Lean_Syntax_node3(x_36, x_40, x_37, x_34, x_45);
x_47 = l_Lean_Syntax_node4(x_36, x_27, x_38, x_41, x_30, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_29);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__3));
x_4 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___closed__10));
x_5 = lean_alloc_closure((void*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl), 3, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1();
return x_2;
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
res = runtime_initialize_Init_Prelude(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Package(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Attributes(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Syntax(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1()
;
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
res = initialize_Init_Prelude(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Attributes(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Syntax(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Script(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_DSL_Script(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_DSL_Script(builtin);
}
#ifdef __cplusplus
}
#endif
