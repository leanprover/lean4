// Lean compiler output
// Module: Init.Data.Format.Macro
// Imports: public meta import Init.Meta public import Init.Notation
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_termF_x21___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_termF_x21___00__closed__0 = (const lean_object*)&l_Std_termF_x21___00__closed__0_value;
static const lean_string_object l_Std_termF_x21___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termF!_"};
static const lean_object* l_Std_termF_x21___00__closed__1 = (const lean_object*)&l_Std_termF_x21___00__closed__1_value;
static const lean_ctor_object l_Std_termF_x21___00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_termF_x21___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_termF_x21___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_termF_x21___00__closed__2_value_aux_0),((lean_object*)&l_Std_termF_x21___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(236, 216, 133, 36, 148, 218, 11, 227)}};
static const lean_object* l_Std_termF_x21___00__closed__2 = (const lean_object*)&l_Std_termF_x21___00__closed__2_value;
static const lean_string_object l_Std_termF_x21___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_termF_x21___00__closed__3 = (const lean_object*)&l_Std_termF_x21___00__closed__3_value;
static const lean_ctor_object l_Std_termF_x21___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_termF_x21___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_termF_x21___00__closed__4 = (const lean_object*)&l_Std_termF_x21___00__closed__4_value;
static const lean_string_object l_Std_termF_x21___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "f!"};
static const lean_object* l_Std_termF_x21___00__closed__5 = (const lean_object*)&l_Std_termF_x21___00__closed__5_value;
static const lean_ctor_object l_Std_termF_x21___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_termF_x21___00__closed__5_value)}};
static const lean_object* l_Std_termF_x21___00__closed__6 = (const lean_object*)&l_Std_termF_x21___00__closed__6_value;
static const lean_string_object l_Std_termF_x21___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "interpolatedStr"};
static const lean_object* l_Std_termF_x21___00__closed__7 = (const lean_object*)&l_Std_termF_x21___00__closed__7_value;
static const lean_ctor_object l_Std_termF_x21___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_termF_x21___00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(156, 58, 177, 246, 99, 11, 16, 252)}};
static const lean_object* l_Std_termF_x21___00__closed__8 = (const lean_object*)&l_Std_termF_x21___00__closed__8_value;
static const lean_string_object l_Std_termF_x21___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_termF_x21___00__closed__9 = (const lean_object*)&l_Std_termF_x21___00__closed__9_value;
static const lean_ctor_object l_Std_termF_x21___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_termF_x21___00__closed__9_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_termF_x21___00__closed__10 = (const lean_object*)&l_Std_termF_x21___00__closed__10_value;
static const lean_ctor_object l_Std_termF_x21___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_termF_x21___00__closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_termF_x21___00__closed__11 = (const lean_object*)&l_Std_termF_x21___00__closed__11_value;
static const lean_ctor_object l_Std_termF_x21___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_termF_x21___00__closed__8_value),((lean_object*)&l_Std_termF_x21___00__closed__11_value)}};
static const lean_object* l_Std_termF_x21___00__closed__12 = (const lean_object*)&l_Std_termF_x21___00__closed__12_value;
static const lean_ctor_object l_Std_termF_x21___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_termF_x21___00__closed__4_value),((lean_object*)&l_Std_termF_x21___00__closed__6_value),((lean_object*)&l_Std_termF_x21___00__closed__12_value)}};
static const lean_object* l_Std_termF_x21___00__closed__13 = (const lean_object*)&l_Std_termF_x21___00__closed__13_value;
static const lean_ctor_object l_Std_termF_x21___00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_termF_x21___00__closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_termF_x21___00__closed__13_value)}};
static const lean_object* l_Std_termF_x21___00__closed__14 = (const lean_object*)&l_Std_termF_x21___00__closed__14_value;
LEAN_EXPORT const lean_object* l_Std_termF_x21__ = (const lean_object*)&l_Std_termF_x21___00__closed__14_value;
static const lean_string_object l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Format"};
static const lean_object* l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__0 = (const lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__0_value;
static lean_once_cell_t l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__1;
static const lean_ctor_object l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_object* l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__2 = (const lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__2_value;
static const lean_ctor_object l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_termF_x21___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__3_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_object* l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__3 = (const lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__3_value;
static const lean_ctor_object l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__4 = (const lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__4_value;
static const lean_ctor_object l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__3_value)}};
static const lean_object* l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__5 = (const lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__5_value;
static const lean_ctor_object l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__6 = (const lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__6_value;
static const lean_ctor_object l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__4_value),((lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__6_value)}};
static const lean_object* l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__7 = (const lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__7_value;
static const lean_string_object l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Std.format"};
static const lean_object* l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__8 = (const lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__8_value;
static lean_once_cell_t l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__9;
static const lean_string_object l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "format"};
static const lean_object* l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__10 = (const lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__10_value;
static const lean_ctor_object l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_termF_x21___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__11_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(230, 83, 123, 122, 108, 199, 223, 228)}};
static const lean_object* l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__11 = (const lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__11_value;
static const lean_string_object l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ToFormat"};
static const lean_object* l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__12 = (const lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__12_value;
static const lean_ctor_object l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_termF_x21___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__13_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(62, 155, 59, 53, 87, 215, 169, 107)}};
static const lean_ctor_object l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__13_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(192, 160, 229, 53, 40, 251, 21, 121)}};
static const lean_object* l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__13 = (const lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__13_value;
static const lean_ctor_object l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__14 = (const lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__14_value;
static const lean_ctor_object l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__15 = (const lean_object*)&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__15_value;
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__1(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = ((lean_object*)(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__0));
v___x_35_ = l_String_toRawSubstring_x27(v___x_34_);
return v___x_35_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__9(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = ((lean_object*)(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__8));
v___x_54_ = l_String_toRawSubstring_x27(v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1(lean_object* v_x_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = ((lean_object*)(l_Std_termF_x21___00__closed__2));
lean_inc(v_x_70_);
v___x_74_ = l_Lean_Syntax_isOfKind(v_x_70_, v___x_73_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec_ref(v_a_71_);
lean_dec(v_x_70_);
v___x_75_ = lean_box(1);
v___x_76_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v_a_72_);
return v___x_76_;
}
else
{
lean_object* v_quotContext_77_; lean_object* v_currMacroScope_78_; lean_object* v_ref_79_; lean_object* v___x_80_; lean_object* v_interpStr_81_; uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v_quotContext_77_ = lean_ctor_get(v_a_71_, 1);
v_currMacroScope_78_ = lean_ctor_get(v_a_71_, 2);
v_ref_79_ = lean_ctor_get(v_a_71_, 5);
v___x_80_ = lean_unsigned_to_nat(1u);
v_interpStr_81_ = l_Lean_Syntax_getArg(v_x_70_, v___x_80_);
lean_dec(v_x_70_);
v___x_82_ = 0;
v___x_83_ = l_Lean_SourceInfo_fromRef(v_ref_79_, v___x_82_);
v___x_84_ = lean_obj_once(&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__1, &l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__1_once, _init_l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__1);
v___x_85_ = ((lean_object*)(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__2));
lean_inc(v_currMacroScope_78_);
lean_inc(v_quotContext_77_);
v___x_86_ = l_Lean_addMacroScope(v_quotContext_77_, v___x_85_, v_currMacroScope_78_);
v___x_87_ = ((lean_object*)(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__7));
lean_inc(v___x_83_);
v___x_88_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_88_, 0, v___x_83_);
lean_ctor_set(v___x_88_, 1, v___x_84_);
lean_ctor_set(v___x_88_, 2, v___x_86_);
lean_ctor_set(v___x_88_, 3, v___x_87_);
v___x_89_ = lean_obj_once(&l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__9, &l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__9_once, _init_l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__9);
v___x_90_ = ((lean_object*)(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__11));
lean_inc(v_currMacroScope_78_);
lean_inc(v_quotContext_77_);
v___x_91_ = l_Lean_addMacroScope(v_quotContext_77_, v___x_90_, v_currMacroScope_78_);
v___x_92_ = ((lean_object*)(l_Std___aux__Init__Data__Format__Macro______macroRules__Std__termF_x21____1___closed__15));
v___x_93_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_93_, 0, v___x_83_);
lean_ctor_set(v___x_93_, 1, v___x_89_);
lean_ctor_set(v___x_93_, 2, v___x_91_);
lean_ctor_set(v___x_93_, 3, v___x_92_);
lean_inc_ref(v___x_93_);
v___x_94_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_81_, v___x_88_, v___x_93_, v___x_93_, v_a_71_, v_a_72_);
lean_dec(v_interpStr_81_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
v_a_96_ = lean_ctor_get(v___x_94_, 1);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_94_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_inc(v_a_95_);
lean_dec(v___x_94_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_95_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
else
{
lean_object* v_a_104_; lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
v_a_104_ = lean_ctor_get(v___x_94_, 0);
v_a_105_ = lean_ctor_get(v___x_94_, 1);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v___x_94_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_inc(v_a_104_);
lean_dec(v___x_94_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_104_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v_a_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Meta(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Format_Macro(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Meta(uint8_t builtin);
lean_object* initialize_Init_Notation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Format_Macro(builtin);
}
#ifdef __cplusplus
}
#endif
