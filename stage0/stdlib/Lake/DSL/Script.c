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
static lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__13 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__13_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__14 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__14_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__15 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__15_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ScriptFn"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
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
static lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25;
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
static lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33_value;
static const lean_string_object l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 8, .m_data = "«script»"};
static const lean_object* l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__34 = (const lean_object*)&l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__34_value;
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
static lean_object* _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__16));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35() {
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
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_456; uint8_t x_457; 
x_53 = lean_unsigned_to_nat(0u);
x_456 = l_Lean_Syntax_getArg(x_1, x_53);
x_457 = l_Lean_Syntax_isNone(x_456);
if (x_457 == 0)
{
lean_object* x_458; uint8_t x_459; 
x_458 = lean_unsigned_to_nat(1u);
lean_inc(x_456);
x_459 = l_Lean_Syntax_matchesNull(x_456, x_458);
if (x_459 == 0)
{
lean_object* x_460; lean_object* x_461; 
lean_dec(x_456);
x_460 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_461 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_460, x_2, x_3);
lean_dec(x_1);
return x_461;
}
else
{
lean_object* x_462; lean_object* x_463; 
x_462 = l_Lean_Syntax_getArg(x_456, x_53);
lean_dec(x_456);
x_463 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_463, 0, x_462);
x_443 = x_463;
x_444 = x_2;
x_445 = x_3;
goto block_455;
}
}
else
{
lean_object* x_464; 
lean_dec(x_456);
x_464 = lean_box(0);
x_443 = x_464;
x_444 = x_2;
x_445 = x_3;
goto block_455;
}
block_136:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_inc_ref(x_70);
x_77 = l_Array_append___redArg(x_70, x_76);
lean_dec_ref(x_76);
lean_inc(x_73);
lean_inc(x_57);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_57);
lean_ctor_set(x_78, 1, x_73);
lean_ctor_set(x_78, 2, x_77);
x_79 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__5));
lean_inc_ref(x_66);
lean_inc_ref(x_54);
lean_inc_ref(x_67);
x_80 = l_Lean_Name_mkStr4(x_67, x_54, x_66, x_79);
x_81 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__6));
lean_inc(x_57);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_57);
lean_ctor_set(x_82, 1, x_81);
x_83 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__7));
x_84 = l_Lean_Syntax_SepArray_ofElems(x_83, x_58);
lean_dec_ref(x_58);
lean_inc_ref(x_70);
x_85 = l_Array_append___redArg(x_70, x_84);
lean_dec_ref(x_84);
lean_inc(x_73);
lean_inc(x_57);
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_57);
lean_ctor_set(x_86, 1, x_73);
lean_ctor_set(x_86, 2, x_85);
x_87 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__8));
lean_inc(x_57);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_57);
lean_ctor_set(x_88, 1, x_87);
lean_inc(x_57);
x_89 = l_Lean_Syntax_node3(x_57, x_80, x_82, x_86, x_88);
lean_inc(x_73);
lean_inc(x_57);
x_90 = l_Lean_Syntax_node1(x_57, x_73, x_89);
lean_inc_n(x_63, 5);
lean_inc(x_57);
x_91 = l_Lean_Syntax_node7(x_57, x_60, x_78, x_90, x_63, x_63, x_63, x_63, x_63);
x_92 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__9));
lean_inc_ref(x_56);
lean_inc_ref(x_54);
lean_inc_ref(x_67);
x_93 = l_Lean_Name_mkStr4(x_67, x_54, x_56, x_92);
x_94 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__10));
lean_inc(x_57);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_57);
lean_ctor_set(x_95, 1, x_94);
x_96 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__11));
lean_inc_ref(x_56);
lean_inc_ref(x_54);
lean_inc_ref(x_67);
x_97 = l_Lean_Name_mkStr4(x_67, x_54, x_56, x_96);
x_98 = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12;
x_99 = lean_box(2);
lean_inc(x_73);
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_73);
lean_ctor_set(x_100, 2, x_98);
x_101 = lean_mk_empty_array_with_capacity(x_68);
x_102 = lean_array_push(x_101, x_69);
x_103 = lean_array_push(x_102, x_100);
x_104 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_97);
lean_ctor_set(x_104, 2, x_103);
x_105 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__13));
lean_inc_ref(x_54);
lean_inc_ref(x_67);
x_106 = l_Lean_Name_mkStr4(x_67, x_54, x_56, x_105);
x_107 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__14));
lean_inc_ref(x_66);
lean_inc_ref(x_54);
lean_inc_ref(x_67);
x_108 = l_Lean_Name_mkStr4(x_67, x_54, x_66, x_107);
x_109 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__15));
lean_inc(x_57);
x_110 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_110, 0, x_57);
lean_ctor_set(x_110, 1, x_109);
x_111 = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17;
x_112 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__18));
x_113 = l_Lean_addMacroScope(x_75, x_112, x_65);
x_114 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__20));
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_72);
lean_inc(x_57);
x_116 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_116, 0, x_57);
lean_ctor_set(x_116, 1, x_111);
lean_ctor_set(x_116, 2, x_113);
lean_ctor_set(x_116, 3, x_115);
lean_inc(x_57);
x_117 = l_Lean_Syntax_node2(x_57, x_108, x_110, x_116);
lean_inc(x_73);
lean_inc(x_57);
x_118 = l_Lean_Syntax_node1(x_57, x_73, x_117);
lean_inc(x_63);
lean_inc(x_57);
x_119 = l_Lean_Syntax_node2(x_57, x_106, x_63, x_118);
x_120 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21));
lean_inc(x_57);
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_57);
lean_ctor_set(x_121, 1, x_120);
x_122 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__22));
lean_inc_ref(x_66);
lean_inc_ref(x_54);
lean_inc_ref(x_67);
x_123 = l_Lean_Name_mkStr4(x_67, x_54, x_66, x_122);
lean_inc(x_57);
x_124 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_124, 0, x_57);
lean_ctor_set(x_124, 1, x_122);
x_125 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__23));
x_126 = l_Lean_Name_mkStr4(x_67, x_54, x_66, x_125);
lean_inc(x_73);
lean_inc(x_57);
x_127 = l_Lean_Syntax_node1(x_57, x_73, x_74);
x_128 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__24));
lean_inc(x_57);
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_57);
lean_ctor_set(x_129, 1, x_128);
lean_inc(x_63);
lean_inc(x_57);
x_130 = l_Lean_Syntax_node4(x_57, x_126, x_127, x_63, x_129, x_62);
lean_inc(x_57);
x_131 = l_Lean_Syntax_node2(x_57, x_123, x_124, x_130);
lean_inc_n(x_63, 2);
lean_inc(x_57);
x_132 = l_Lean_Syntax_node2(x_57, x_55, x_63, x_63);
if (lean_obj_tag(x_71) == 1)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_71, 0);
lean_inc(x_133);
lean_dec_ref(x_71);
x_134 = l_Array_mkArray1___redArg(x_133);
x_4 = x_91;
x_5 = x_57;
x_6 = x_95;
x_7 = x_59;
x_8 = x_61;
x_9 = x_132;
x_10 = x_63;
x_11 = x_64;
x_12 = x_119;
x_13 = x_121;
x_14 = x_104;
x_15 = x_70;
x_16 = x_73;
x_17 = x_131;
x_18 = x_93;
x_19 = x_134;
goto block_26;
}
else
{
lean_object* x_135; 
lean_dec(x_71);
x_135 = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25;
x_4 = x_91;
x_5 = x_57;
x_6 = x_95;
x_7 = x_59;
x_8 = x_61;
x_9 = x_132;
x_10 = x_63;
x_11 = x_64;
x_12 = x_119;
x_13 = x_121;
x_14 = x_104;
x_15 = x_70;
x_16 = x_73;
x_17 = x_131;
x_18 = x_93;
x_19 = x_135;
goto block_26;
}
}
block_245:
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_152);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_155 = lean_ctor_get(x_152, 1);
x_156 = lean_ctor_get(x_152, 2);
x_157 = lean_ctor_get(x_152, 5);
x_158 = l_Lean_replaceRef(x_138, x_157);
lean_dec(x_157);
lean_dec(x_138);
lean_inc(x_158);
lean_inc(x_156);
lean_inc(x_155);
lean_ctor_set(x_152, 5, x_158);
x_159 = l_Lake_DSL_expandOptSimpleBinder(x_149, x_152, x_153);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec_ref(x_159);
x_162 = l_Lake_DSL_expandIdentOrStrAsIdent(x_150);
x_163 = l_Lean_SourceInfo_fromRef(x_158, x_143);
lean_dec(x_158);
x_164 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26));
x_165 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__27));
lean_inc_ref(x_137);
lean_inc_ref(x_145);
x_166 = l_Lean_Name_mkStr4(x_145, x_137, x_164, x_165);
x_167 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__28));
lean_inc_ref(x_137);
lean_inc_ref(x_145);
x_168 = l_Lean_Name_mkStr4(x_145, x_137, x_164, x_167);
x_169 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30));
x_170 = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31;
lean_inc(x_163);
x_171 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_171, 0, x_163);
lean_ctor_set(x_171, 1, x_169);
lean_ctor_set(x_171, 2, x_170);
lean_inc_ref(x_171);
lean_inc(x_163);
x_172 = l_Lean_Syntax_node1(x_163, x_168, x_171);
x_173 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32));
x_174 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33));
lean_inc_ref(x_137);
lean_inc_ref(x_145);
x_175 = l_Lean_Name_mkStr4(x_145, x_137, x_173, x_174);
x_176 = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35;
x_177 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__37));
lean_inc(x_156);
lean_inc(x_155);
x_178 = l_Lean_addMacroScope(x_155, x_177, x_156);
x_179 = lean_box(0);
lean_inc(x_163);
x_180 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_180, 0, x_163);
lean_ctor_set(x_180, 1, x_176);
lean_ctor_set(x_180, 2, x_178);
lean_ctor_set(x_180, 3, x_179);
lean_inc_ref(x_171);
lean_inc(x_163);
x_181 = l_Lean_Syntax_node2(x_163, x_175, x_180, x_171);
lean_inc(x_163);
x_182 = l_Lean_Syntax_node2(x_163, x_166, x_172, x_181);
x_183 = lean_mk_empty_array_with_capacity(x_141);
x_184 = lean_array_push(x_183, x_182);
x_185 = l_Lake_DSL_expandAttrs(x_147);
x_186 = l_Array_append___redArg(x_184, x_185);
lean_dec_ref(x_185);
x_187 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__38));
lean_inc_ref(x_139);
lean_inc_ref(x_137);
lean_inc_ref(x_145);
x_188 = l_Lean_Name_mkStr4(x_145, x_137, x_139, x_187);
x_189 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__39));
lean_inc_ref(x_139);
lean_inc_ref(x_137);
lean_inc_ref(x_145);
x_190 = l_Lean_Name_mkStr4(x_145, x_137, x_139, x_189);
if (lean_obj_tag(x_148) == 1)
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_148, 0);
lean_inc(x_191);
lean_dec_ref(x_148);
x_192 = l_Array_mkArray1___redArg(x_191);
x_54 = x_137;
x_55 = x_140;
x_56 = x_139;
x_57 = x_163;
x_58 = x_186;
x_59 = x_188;
x_60 = x_190;
x_61 = x_161;
x_62 = x_142;
x_63 = x_171;
x_64 = x_144;
x_65 = x_156;
x_66 = x_164;
x_67 = x_145;
x_68 = x_146;
x_69 = x_162;
x_70 = x_170;
x_71 = x_151;
x_72 = x_179;
x_73 = x_169;
x_74 = x_160;
x_75 = x_155;
x_76 = x_192;
goto block_136;
}
else
{
lean_object* x_193; 
lean_dec(x_148);
x_193 = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25;
x_54 = x_137;
x_55 = x_140;
x_56 = x_139;
x_57 = x_163;
x_58 = x_186;
x_59 = x_188;
x_60 = x_190;
x_61 = x_161;
x_62 = x_142;
x_63 = x_171;
x_64 = x_144;
x_65 = x_156;
x_66 = x_164;
x_67 = x_145;
x_68 = x_146;
x_69 = x_162;
x_70 = x_170;
x_71 = x_151;
x_72 = x_179;
x_73 = x_169;
x_74 = x_160;
x_75 = x_155;
x_76 = x_193;
goto block_136;
}
}
else
{
uint8_t x_194; 
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_148);
lean_dec(x_147);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_140);
lean_dec_ref(x_139);
lean_dec_ref(x_137);
x_194 = !lean_is_exclusive(x_159);
if (x_194 == 0)
{
return x_159;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_159, 0);
x_196 = lean_ctor_get(x_159, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_159);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_198 = lean_ctor_get(x_152, 0);
x_199 = lean_ctor_get(x_152, 1);
x_200 = lean_ctor_get(x_152, 2);
x_201 = lean_ctor_get(x_152, 3);
x_202 = lean_ctor_get(x_152, 4);
x_203 = lean_ctor_get(x_152, 5);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_152);
x_204 = l_Lean_replaceRef(x_138, x_203);
lean_dec(x_203);
lean_dec(x_138);
lean_inc(x_204);
lean_inc(x_200);
lean_inc(x_199);
x_205 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_205, 0, x_198);
lean_ctor_set(x_205, 1, x_199);
lean_ctor_set(x_205, 2, x_200);
lean_ctor_set(x_205, 3, x_201);
lean_ctor_set(x_205, 4, x_202);
lean_ctor_set(x_205, 5, x_204);
x_206 = l_Lake_DSL_expandOptSimpleBinder(x_149, x_205, x_153);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec_ref(x_206);
x_209 = l_Lake_DSL_expandIdentOrStrAsIdent(x_150);
x_210 = l_Lean_SourceInfo_fromRef(x_204, x_143);
lean_dec(x_204);
x_211 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__26));
x_212 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__27));
lean_inc_ref(x_137);
lean_inc_ref(x_145);
x_213 = l_Lean_Name_mkStr4(x_145, x_137, x_211, x_212);
x_214 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__28));
lean_inc_ref(x_137);
lean_inc_ref(x_145);
x_215 = l_Lean_Name_mkStr4(x_145, x_137, x_211, x_214);
x_216 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30));
x_217 = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31;
lean_inc(x_210);
x_218 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_218, 0, x_210);
lean_ctor_set(x_218, 1, x_216);
lean_ctor_set(x_218, 2, x_217);
lean_inc_ref(x_218);
lean_inc(x_210);
x_219 = l_Lean_Syntax_node1(x_210, x_215, x_218);
x_220 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__32));
x_221 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__33));
lean_inc_ref(x_137);
lean_inc_ref(x_145);
x_222 = l_Lean_Name_mkStr4(x_145, x_137, x_220, x_221);
x_223 = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35;
x_224 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__37));
lean_inc(x_200);
lean_inc(x_199);
x_225 = l_Lean_addMacroScope(x_199, x_224, x_200);
x_226 = lean_box(0);
lean_inc(x_210);
x_227 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_227, 0, x_210);
lean_ctor_set(x_227, 1, x_223);
lean_ctor_set(x_227, 2, x_225);
lean_ctor_set(x_227, 3, x_226);
lean_inc_ref(x_218);
lean_inc(x_210);
x_228 = l_Lean_Syntax_node2(x_210, x_222, x_227, x_218);
lean_inc(x_210);
x_229 = l_Lean_Syntax_node2(x_210, x_213, x_219, x_228);
x_230 = lean_mk_empty_array_with_capacity(x_141);
x_231 = lean_array_push(x_230, x_229);
x_232 = l_Lake_DSL_expandAttrs(x_147);
x_233 = l_Array_append___redArg(x_231, x_232);
lean_dec_ref(x_232);
x_234 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__38));
lean_inc_ref(x_139);
lean_inc_ref(x_137);
lean_inc_ref(x_145);
x_235 = l_Lean_Name_mkStr4(x_145, x_137, x_139, x_234);
x_236 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__39));
lean_inc_ref(x_139);
lean_inc_ref(x_137);
lean_inc_ref(x_145);
x_237 = l_Lean_Name_mkStr4(x_145, x_137, x_139, x_236);
if (lean_obj_tag(x_148) == 1)
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_148, 0);
lean_inc(x_238);
lean_dec_ref(x_148);
x_239 = l_Array_mkArray1___redArg(x_238);
x_54 = x_137;
x_55 = x_140;
x_56 = x_139;
x_57 = x_210;
x_58 = x_233;
x_59 = x_235;
x_60 = x_237;
x_61 = x_208;
x_62 = x_142;
x_63 = x_218;
x_64 = x_144;
x_65 = x_200;
x_66 = x_211;
x_67 = x_145;
x_68 = x_146;
x_69 = x_209;
x_70 = x_217;
x_71 = x_151;
x_72 = x_226;
x_73 = x_216;
x_74 = x_207;
x_75 = x_199;
x_76 = x_239;
goto block_136;
}
else
{
lean_object* x_240; 
lean_dec(x_148);
x_240 = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25;
x_54 = x_137;
x_55 = x_140;
x_56 = x_139;
x_57 = x_210;
x_58 = x_233;
x_59 = x_235;
x_60 = x_237;
x_61 = x_208;
x_62 = x_142;
x_63 = x_218;
x_64 = x_144;
x_65 = x_200;
x_66 = x_211;
x_67 = x_145;
x_68 = x_146;
x_69 = x_209;
x_70 = x_217;
x_71 = x_151;
x_72 = x_226;
x_73 = x_216;
x_74 = x_207;
x_75 = x_199;
x_76 = x_240;
goto block_136;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_204);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_148);
lean_dec(x_147);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_140);
lean_dec_ref(x_139);
lean_dec_ref(x_137);
x_241 = lean_ctor_get(x_206, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_206, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_243 = x_206;
} else {
 lean_dec_ref(x_206);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
}
block_279:
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_inc_ref(x_255);
x_262 = l_Array_append___redArg(x_255, x_261);
lean_dec_ref(x_261);
lean_inc(x_247);
lean_inc(x_260);
x_263 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_247);
lean_ctor_set(x_263, 2, x_262);
x_264 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40));
x_265 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__41));
lean_inc_ref(x_250);
lean_inc_ref(x_253);
x_266 = l_Lean_Name_mkStr4(x_253, x_250, x_264, x_265);
x_267 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__21));
lean_inc(x_260);
x_268 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_268, 0, x_260);
lean_ctor_set(x_268, 1, x_267);
lean_inc(x_260);
x_269 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_269, 0, x_260);
lean_ctor_set(x_269, 1, x_256);
lean_inc(x_260);
x_270 = l_Lean_Syntax_node2(x_260, x_248, x_269, x_252);
x_271 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__42));
x_272 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__43));
x_273 = l_Lean_Name_mkStr4(x_253, x_250, x_271, x_272);
lean_inc_ref(x_255);
lean_inc(x_247);
lean_inc(x_260);
x_274 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_274, 0, x_260);
lean_ctor_set(x_274, 1, x_247);
lean_ctor_set(x_274, 2, x_255);
lean_inc_ref(x_274);
lean_inc(x_260);
x_275 = l_Lean_Syntax_node2(x_260, x_273, x_274, x_274);
if (lean_obj_tag(x_254) == 1)
{
lean_object* x_276; lean_object* x_277; 
x_276 = lean_ctor_get(x_254, 0);
lean_inc(x_276);
lean_dec_ref(x_254);
x_277 = l_Array_mkArray1___redArg(x_276);
x_28 = x_268;
x_29 = x_246;
x_30 = x_247;
x_31 = x_263;
x_32 = x_275;
x_33 = x_249;
x_34 = x_266;
x_35 = x_251;
x_36 = x_255;
x_37 = x_270;
x_38 = x_257;
x_39 = x_258;
x_40 = x_260;
x_41 = x_259;
x_42 = x_277;
goto block_49;
}
else
{
lean_object* x_278; 
lean_dec(x_254);
x_278 = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25;
x_28 = x_268;
x_29 = x_246;
x_30 = x_247;
x_31 = x_263;
x_32 = x_275;
x_33 = x_249;
x_34 = x_266;
x_35 = x_251;
x_36 = x_255;
x_37 = x_270;
x_38 = x_257;
x_39 = x_258;
x_40 = x_260;
x_41 = x_259;
x_42 = x_278;
goto block_49;
}
}
block_304:
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_inc_ref(x_288);
x_296 = l_Array_append___redArg(x_288, x_295);
lean_dec_ref(x_295);
lean_inc(x_282);
lean_inc(x_294);
x_297 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_282);
lean_ctor_set(x_297, 2, x_296);
x_298 = l_Lean_SourceInfo_fromRef(x_280, x_50);
lean_dec(x_280);
x_299 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__36));
x_300 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
if (lean_obj_tag(x_290) == 1)
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_290, 0);
lean_inc(x_301);
lean_dec_ref(x_290);
x_302 = l_Array_mkArray1___redArg(x_301);
x_246 = x_281;
x_247 = x_282;
x_248 = x_283;
x_249 = x_284;
x_250 = x_285;
x_251 = x_297;
x_252 = x_286;
x_253 = x_287;
x_254 = x_289;
x_255 = x_288;
x_256 = x_291;
x_257 = x_292;
x_258 = x_300;
x_259 = x_293;
x_260 = x_294;
x_261 = x_302;
goto block_279;
}
else
{
lean_object* x_303; 
lean_dec(x_290);
x_303 = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25;
x_246 = x_281;
x_247 = x_282;
x_248 = x_283;
x_249 = x_284;
x_250 = x_285;
x_251 = x_297;
x_252 = x_286;
x_253 = x_287;
x_254 = x_289;
x_255 = x_288;
x_256 = x_291;
x_257 = x_292;
x_258 = x_300;
x_259 = x_293;
x_260 = x_294;
x_261 = x_303;
goto block_279;
}
}
block_326:
{
lean_object* x_321; lean_object* x_322; 
lean_inc_ref(x_314);
x_321 = l_Array_append___redArg(x_314, x_320);
lean_dec_ref(x_320);
lean_inc(x_307);
lean_inc(x_319);
x_322 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_322, 0, x_319);
lean_ctor_set(x_322, 1, x_307);
lean_ctor_set(x_322, 2, x_321);
if (lean_obj_tag(x_312) == 1)
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_ctor_get(x_312, 0);
lean_inc(x_323);
lean_dec_ref(x_312);
x_324 = l_Array_mkArray1___redArg(x_323);
x_280 = x_305;
x_281 = x_306;
x_282 = x_307;
x_283 = x_308;
x_284 = x_309;
x_285 = x_310;
x_286 = x_311;
x_287 = x_313;
x_288 = x_314;
x_289 = x_315;
x_290 = x_316;
x_291 = x_317;
x_292 = x_322;
x_293 = x_318;
x_294 = x_319;
x_295 = x_324;
goto block_304;
}
else
{
lean_object* x_325; 
lean_dec(x_312);
x_325 = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25;
x_280 = x_305;
x_281 = x_306;
x_282 = x_307;
x_283 = x_308;
x_284 = x_309;
x_285 = x_310;
x_286 = x_311;
x_287 = x_313;
x_288 = x_314;
x_289 = x_315;
x_290 = x_316;
x_291 = x_317;
x_292 = x_322;
x_293 = x_318;
x_294 = x_319;
x_295 = x_325;
goto block_304;
}
}
block_349:
{
lean_object* x_341; uint8_t x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_341 = lean_ctor_get(x_339, 5);
lean_inc(x_341);
lean_dec_ref(x_339);
x_342 = 0;
x_343 = l_Lean_SourceInfo_fromRef(x_341, x_342);
lean_dec(x_341);
x_344 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__30));
x_345 = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31;
if (lean_obj_tag(x_333) == 1)
{
lean_object* x_346; lean_object* x_347; 
x_346 = lean_ctor_get(x_333, 0);
lean_inc(x_346);
lean_dec_ref(x_333);
x_347 = l_Array_mkArray1___redArg(x_346);
x_305 = x_327;
x_306 = x_340;
x_307 = x_344;
x_308 = x_331;
x_309 = x_332;
x_310 = x_334;
x_311 = x_328;
x_312 = x_329;
x_313 = x_330;
x_314 = x_345;
x_315 = x_338;
x_316 = x_336;
x_317 = x_335;
x_318 = x_337;
x_319 = x_343;
x_320 = x_347;
goto block_326;
}
else
{
lean_object* x_348; 
lean_dec(x_333);
x_348 = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25;
x_305 = x_327;
x_306 = x_340;
x_307 = x_344;
x_308 = x_331;
x_309 = x_332;
x_310 = x_334;
x_311 = x_328;
x_312 = x_329;
x_313 = x_330;
x_314 = x_345;
x_315 = x_338;
x_316 = x_336;
x_317 = x_335;
x_318 = x_337;
x_319 = x_343;
x_320 = x_348;
goto block_326;
}
}
block_419:
{
lean_object* x_362; lean_object* x_363; uint8_t x_364; 
x_362 = l_Lean_Syntax_getArg(x_357, x_352);
lean_dec(x_357);
x_363 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__45));
lean_inc(x_362);
x_364 = l_Lean_Syntax_isOfKind(x_362, x_363);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
lean_dec(x_355);
x_365 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46));
x_366 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47));
x_367 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__40));
x_368 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__48));
lean_inc(x_362);
x_369 = l_Lean_Syntax_isOfKind(x_362, x_368);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; 
lean_dec(x_362);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_356);
lean_dec(x_353);
lean_dec(x_351);
x_370 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_371 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_370, x_360, x_361);
lean_dec(x_1);
return x_371;
}
else
{
lean_object* x_372; lean_object* x_373; uint8_t x_374; 
x_372 = l_Lean_Syntax_getArg(x_362, x_352);
x_373 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__49));
lean_inc(x_372);
x_374 = l_Lean_Syntax_isOfKind(x_372, x_373);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; 
lean_dec(x_372);
lean_dec(x_362);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_356);
lean_dec(x_353);
lean_dec(x_351);
x_375 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_376 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_375, x_360, x_361);
lean_dec(x_1);
return x_376;
}
else
{
lean_object* x_377; uint8_t x_378; 
x_377 = l_Lean_Syntax_getArg(x_372, x_53);
x_378 = l_Lean_Syntax_matchesNull(x_377, x_53);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; 
lean_dec(x_372);
lean_dec(x_362);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_356);
lean_dec(x_353);
lean_dec(x_351);
x_379 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_380 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_379, x_360, x_361);
lean_dec(x_1);
return x_380;
}
else
{
lean_object* x_381; uint8_t x_382; 
x_381 = l_Lean_Syntax_getArg(x_372, x_354);
lean_dec(x_372);
x_382 = l_Lean_Syntax_matchesNull(x_381, x_53);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; 
lean_dec(x_362);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_356);
lean_dec(x_353);
lean_dec(x_351);
x_383 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_384 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_383, x_360, x_361);
lean_dec(x_1);
return x_384;
}
else
{
lean_object* x_385; lean_object* x_386; uint8_t x_387; 
x_385 = l_Lean_Syntax_getArg(x_362, x_354);
x_386 = l_Lean_Syntax_getArg(x_362, x_350);
lean_dec(x_362);
x_387 = l_Lean_Syntax_isNone(x_386);
if (x_387 == 0)
{
uint8_t x_388; 
lean_inc(x_386);
x_388 = l_Lean_Syntax_matchesNull(x_386, x_354);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; 
lean_dec(x_386);
lean_dec(x_385);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_356);
lean_dec(x_353);
lean_dec(x_351);
x_389 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_390 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_389, x_360, x_361);
lean_dec(x_1);
return x_390;
}
else
{
lean_object* x_391; lean_object* x_392; uint8_t x_393; 
x_391 = l_Lean_Syntax_getArg(x_386, x_53);
lean_dec(x_386);
x_392 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51));
lean_inc(x_391);
x_393 = l_Lean_Syntax_isOfKind(x_391, x_392);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; 
lean_dec(x_391);
lean_dec(x_385);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_356);
lean_dec(x_353);
lean_dec(x_351);
x_394 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_395 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_394, x_360, x_361);
lean_dec(x_1);
return x_395;
}
else
{
lean_object* x_396; 
lean_dec(x_1);
x_396 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_396, 0, x_391);
x_137 = x_366;
x_138 = x_351;
x_139 = x_367;
x_140 = x_373;
x_141 = x_354;
x_142 = x_385;
x_143 = x_364;
x_144 = x_368;
x_145 = x_365;
x_146 = x_352;
x_147 = x_353;
x_148 = x_356;
x_149 = x_359;
x_150 = x_358;
x_151 = x_396;
x_152 = x_360;
x_153 = x_361;
goto block_245;
}
}
}
else
{
lean_object* x_397; 
lean_dec(x_386);
lean_dec(x_1);
x_397 = lean_box(0);
x_137 = x_366;
x_138 = x_351;
x_139 = x_367;
x_140 = x_373;
x_141 = x_354;
x_142 = x_385;
x_143 = x_364;
x_144 = x_368;
x_145 = x_365;
x_146 = x_352;
x_147 = x_353;
x_148 = x_356;
x_149 = x_359;
x_150 = x_358;
x_151 = x_397;
x_152 = x_360;
x_153 = x_361;
goto block_245;
}
}
}
}
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; 
x_398 = l_Lean_Syntax_getArg(x_362, x_53);
x_399 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__46));
x_400 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__47));
x_401 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__52));
x_402 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__53));
lean_inc(x_398);
x_403 = l_Lean_Syntax_isOfKind(x_398, x_402);
if (x_403 == 0)
{
lean_object* x_404; lean_object* x_405; 
lean_dec(x_398);
lean_dec(x_362);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_353);
lean_dec(x_351);
x_404 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_405 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_404, x_360, x_361);
lean_dec(x_1);
return x_405;
}
else
{
lean_object* x_406; lean_object* x_407; uint8_t x_408; 
x_406 = l_Lean_Syntax_getArg(x_398, x_354);
lean_dec(x_398);
x_407 = l_Lean_Syntax_getArg(x_362, x_354);
lean_dec(x_362);
x_408 = l_Lean_Syntax_isNone(x_407);
if (x_408 == 0)
{
uint8_t x_409; 
lean_inc(x_407);
x_409 = l_Lean_Syntax_matchesNull(x_407, x_354);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; 
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_353);
lean_dec(x_351);
x_410 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_411 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_410, x_360, x_361);
lean_dec(x_1);
return x_411;
}
else
{
lean_object* x_412; lean_object* x_413; uint8_t x_414; 
x_412 = l_Lean_Syntax_getArg(x_407, x_53);
lean_dec(x_407);
x_413 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__51));
lean_inc(x_412);
x_414 = l_Lean_Syntax_isOfKind(x_412, x_413);
if (x_414 == 0)
{
lean_object* x_415; lean_object* x_416; 
lean_dec(x_412);
lean_dec(x_406);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_353);
lean_dec(x_351);
x_415 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_416 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_415, x_360, x_361);
lean_dec(x_1);
return x_416;
}
else
{
lean_object* x_417; 
lean_dec(x_1);
x_417 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_417, 0, x_412);
x_327 = x_351;
x_328 = x_406;
x_329 = x_353;
x_330 = x_399;
x_331 = x_402;
x_332 = x_355;
x_333 = x_356;
x_334 = x_400;
x_335 = x_401;
x_336 = x_359;
x_337 = x_358;
x_338 = x_417;
x_339 = x_360;
x_340 = x_361;
goto block_349;
}
}
}
else
{
lean_object* x_418; 
lean_dec(x_407);
lean_dec(x_1);
x_418 = lean_box(0);
x_327 = x_351;
x_328 = x_406;
x_329 = x_353;
x_330 = x_399;
x_331 = x_402;
x_332 = x_355;
x_333 = x_356;
x_334 = x_400;
x_335 = x_401;
x_336 = x_359;
x_337 = x_358;
x_338 = x_418;
x_339 = x_360;
x_340 = x_361;
goto block_349;
}
}
}
}
block_442:
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; 
x_425 = lean_unsigned_to_nat(3u);
x_426 = l_Lean_Syntax_getArg(x_1, x_425);
x_427 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__55));
lean_inc(x_426);
x_428 = l_Lean_Syntax_isOfKind(x_426, x_427);
if (x_428 == 0)
{
lean_object* x_429; lean_object* x_430; 
lean_dec(x_426);
lean_dec(x_422);
lean_dec(x_421);
x_429 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_430 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_429, x_423, x_424);
lean_dec(x_1);
return x_430;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; 
x_431 = lean_unsigned_to_nat(2u);
x_432 = l_Lean_Syntax_getArg(x_1, x_431);
x_433 = l_Lean_Syntax_getArg(x_426, x_53);
x_434 = l_Lean_Syntax_getArg(x_426, x_420);
x_435 = l_Lean_Syntax_isNone(x_434);
if (x_435 == 0)
{
uint8_t x_436; 
lean_inc(x_434);
x_436 = l_Lean_Syntax_matchesNull(x_434, x_420);
if (x_436 == 0)
{
lean_object* x_437; lean_object* x_438; 
lean_dec(x_434);
lean_dec(x_433);
lean_dec(x_432);
lean_dec(x_426);
lean_dec(x_422);
lean_dec(x_421);
x_437 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_438 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_437, x_423, x_424);
lean_dec(x_1);
return x_438;
}
else
{
lean_object* x_439; lean_object* x_440; 
x_439 = l_Lean_Syntax_getArg(x_434, x_53);
lean_dec(x_434);
x_440 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_440, 0, x_439);
x_350 = x_425;
x_351 = x_432;
x_352 = x_431;
x_353 = x_422;
x_354 = x_420;
x_355 = x_427;
x_356 = x_421;
x_357 = x_426;
x_358 = x_433;
x_359 = x_440;
x_360 = x_423;
x_361 = x_424;
goto block_419;
}
}
else
{
lean_object* x_441; 
lean_dec(x_434);
x_441 = lean_box(0);
x_350 = x_425;
x_351 = x_432;
x_352 = x_431;
x_353 = x_422;
x_354 = x_420;
x_355 = x_427;
x_356 = x_421;
x_357 = x_426;
x_358 = x_433;
x_359 = x_441;
x_360 = x_423;
x_361 = x_424;
goto block_419;
}
}
}
block_455:
{
lean_object* x_446; lean_object* x_447; uint8_t x_448; 
x_446 = lean_unsigned_to_nat(1u);
x_447 = l_Lean_Syntax_getArg(x_1, x_446);
x_448 = l_Lean_Syntax_isNone(x_447);
if (x_448 == 0)
{
uint8_t x_449; 
lean_inc(x_447);
x_449 = l_Lean_Syntax_matchesNull(x_447, x_446);
if (x_449 == 0)
{
lean_object* x_450; lean_object* x_451; 
lean_dec(x_447);
lean_dec(x_443);
x_450 = ((lean_object*)(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__4));
x_451 = l_Lean_Macro_throwErrorAt___redArg(x_1, x_450, x_444, x_445);
lean_dec(x_1);
return x_451;
}
else
{
lean_object* x_452; lean_object* x_453; 
x_452 = l_Lean_Syntax_getArg(x_447, x_53);
lean_dec(x_447);
x_453 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_453, 0, x_452);
x_420 = x_446;
x_421 = x_443;
x_422 = x_453;
x_423 = x_444;
x_424 = x_445;
goto block_442;
}
}
else
{
lean_object* x_454; 
lean_dec(x_447);
x_454 = lean_box(0);
x_420 = x_446;
x_421 = x_443;
x_422 = x_454;
x_423 = x_444;
x_424 = x_445;
goto block_442;
}
}
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = l_Array_append___redArg(x_15, x_19);
lean_dec_ref(x_19);
lean_inc(x_5);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 2, x_20);
lean_inc(x_5);
x_22 = l_Lean_Syntax_node4(x_5, x_11, x_13, x_17, x_9, x_21);
lean_inc(x_5);
x_23 = l_Lean_Syntax_node5(x_5, x_18, x_6, x_14, x_12, x_22, x_10);
x_24 = l_Lean_Syntax_node2(x_5, x_7, x_4, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
block_49:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = l_Array_append___redArg(x_36, x_42);
lean_dec_ref(x_42);
lean_inc(x_40);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_30);
lean_ctor_set(x_44, 2, x_43);
lean_inc(x_40);
x_45 = l_Lean_Syntax_node4(x_40, x_34, x_28, x_37, x_32, x_44);
lean_inc(x_40);
x_46 = l_Lean_Syntax_node3(x_40, x_33, x_41, x_31, x_45);
x_47 = l_Lean_Syntax_node4(x_40, x_27, x_38, x_35, x_39, x_46);
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
l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12 = _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12();
lean_mark_persistent(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__12);
l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17 = _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17();
lean_mark_persistent(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__17);
l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25 = _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25();
lean_mark_persistent(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__25);
l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31 = _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31();
lean_mark_persistent(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__31);
l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35 = _init_l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35();
lean_mark_persistent(l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___closed__35);
if (builtin) {res = l___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl___regBuiltin___private_Lake_DSL_Script_0__Lake_DSL_expandScriptDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
