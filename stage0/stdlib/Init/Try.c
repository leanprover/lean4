// Lean compiler output
// Module: Init.Try
// Imports: public import Init.Tactics
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
extern lean_object* l_Lean_Parser_Tactic_optConfig;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Try_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(8) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 1, 0, 1, 0)}};
static const lean_object* l_Lean_Try_instInhabitedConfig_default___closed__0 = (const lean_object*)&l_Lean_Try_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Try_instInhabitedConfig_default = (const lean_object*)&l_Lean_Try_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Try_instInhabitedConfig = (const lean_object*)&l_Lean_Try_instInhabitedConfig_default___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_tryTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_Tactic_tryTrace___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_tryTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_Tactic_tryTrace___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_tryTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Parser_Tactic_tryTrace___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_tryTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "tryTrace"};
static const lean_object* l_Lean_Parser_Tactic_tryTrace___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tryTrace___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tryTrace___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tryTrace___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tryTrace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__3_value),LEAN_SCALAR_PTR_LITERAL(222, 128, 230, 128, 87, 180, 97, 21)}};
static const lean_object* l_Lean_Parser_Tactic_tryTrace___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_tryTrace___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Parser_Tactic_tryTrace___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tryTrace___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Parser_Tactic_tryTrace___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_tryTrace___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "try\?"};
static const lean_object* l_Lean_Parser_Tactic_tryTrace___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tryTrace___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__7_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_tryTrace___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__8_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tryTrace___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tryTrace___closed__9;
static lean_once_cell_t l_Lean_Parser_Tactic_tryTrace___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tryTrace___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tryTrace;
static const lean_string_object l_Lean_Parser_Tactic_attemptAll___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attemptAll"};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 233, 242, 37, 159, 125, 179, 213)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_attemptAll___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attempt_all "};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_attemptAll___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withPosition"};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__4_value),LEAN_SCALAR_PTR_LITERAL(246, 171, 180, 145, 132, 143, 108, 238)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_attemptAll___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "many1"};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__6_value),LEAN_SCALAR_PTR_LITERAL(55, 136, 52, 6, 12, 19, 78, 239)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic_attemptAll___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__8_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__9_value;
static const lean_string_object l_Lean_Parser_Tactic_attemptAll___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ppDedent"};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__10_value),LEAN_SCALAR_PTR_LITERAL(242, 37, 230, 124, 106, 100, 159, 37)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__11_value;
static const lean_string_object l_Lean_Parser_Tactic_attemptAll___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ppLine"};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__12_value),LEAN_SCALAR_PTR_LITERAL(117, 61, 38, 245, 158, 59, 171, 58)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__11_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__14_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__15_value;
static const lean_string_object l_Lean_Parser_Tactic_attemptAll___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGe"};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__16_value),LEAN_SCALAR_PTR_LITERAL(119, 36, 80, 74, 173, 106, 150, 68)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__17_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__18 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__18_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__15_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__18_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__19 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__19_value;
static const lean_string_object l_Lean_Parser_Tactic_attemptAll___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "| "};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__20 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__20_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__20_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__21 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__21_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__19_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__21_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__22 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__22_value;
static const lean_string_object l_Lean_Parser_Tactic_attemptAll___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__23 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__23_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__23_value),LEAN_SCALAR_PTR_LITERAL(13, 106, 54, 236, 164, 218, 24, 154)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__24 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__24_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__24_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__25 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__25_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__22_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__25_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__26 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__26_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__26_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__27 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__27_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__27_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__28 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__28_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__28_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__29 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__29_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__29_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__30 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__30_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__30_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__31 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__31_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_attemptAll = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__31_value;
static const lean_string_object l_Lean_Parser_Tactic_attemptAllPar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "attemptAllPar"};
static const lean_object* l_Lean_Parser_Tactic_attemptAllPar___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAllPar___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAllPar___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAllPar___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAllPar___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAllPar___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAllPar___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAllPar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAllPar___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_attemptAllPar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 73, 192, 8, 247, 249, 123, 255)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAllPar___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAllPar___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_attemptAllPar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "attempt_all_par "};
static const lean_object* l_Lean_Parser_Tactic_attemptAllPar___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAllPar___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAllPar___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAllPar___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAllPar___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAllPar___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAllPar___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAllPar___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__29_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAllPar___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAllPar___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAllPar___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAllPar___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_attemptAllPar___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAllPar___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAllPar___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_attemptAllPar = (const lean_object*)&l_Lean_Parser_Tactic_attemptAllPar___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_firstPar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "firstPar"};
static const lean_object* l_Lean_Parser_Tactic_firstPar___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_firstPar___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_firstPar___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_firstPar___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_firstPar___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_firstPar___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_firstPar___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_firstPar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_firstPar___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_firstPar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 43, 83, 229, 83, 112, 229, 7)}};
static const lean_object* l_Lean_Parser_Tactic_firstPar___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_firstPar___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_firstPar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "first_par "};
static const lean_object* l_Lean_Parser_Tactic_firstPar___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_firstPar___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_firstPar___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_firstPar___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_firstPar___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_firstPar___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_firstPar___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_firstPar___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__29_value)}};
static const lean_object* l_Lean_Parser_Tactic_firstPar___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_firstPar___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_firstPar___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_firstPar___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_firstPar___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_firstPar___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_firstPar___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_firstPar = (const lean_object*)&l_Lean_Parser_Tactic_firstPar___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_tryResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tryResult"};
static const lean_object* l_Lean_Parser_Tactic_tryResult___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tryResult___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tryResult___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tryResult___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tryResult___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 153, 96, 187, 124, 208, 140, 174)}};
static const lean_object* l_Lean_Parser_Tactic_tryResult___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_tryResult___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "try_suggestions "};
static const lean_object* l_Lean_Parser_Tactic_tryResult___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tryResult___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_tryResult___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_tryResult___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Lean_Parser_Tactic_tryResult___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tryResult___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__4_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Lean_Parser_Tactic_tryResult___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_tryResult___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Parser_Tactic_tryResult___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tryResult___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__6_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Parser_Tactic_tryResult___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tryResult___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_tryResult___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tryResult___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_tryResult___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tryResult___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_tryResult___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tryResult___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_tryResult___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_tryResult = (const lean_object*)&l_Lean_Parser_Tactic_tryResult___closed__11_value;
static const lean_string_object l_Lean_Parser_Command_registerTryTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__0 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__0_value;
static const lean_string_object l_Lean_Parser_Command_registerTryTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "registerTryTactic"};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__1 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__1_value),LEAN_SCALAR_PTR_LITERAL(64, 133, 180, 171, 152, 84, 222, 30)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__2 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__2_value;
static const lean_string_object l_Lean_Parser_Command_registerTryTactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__3 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__3_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__4 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__4_value;
static const lean_string_object l_Lean_Parser_Command_registerTryTactic___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__5 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__5_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__6 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__6_value)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__7 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__4_value),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__7_value)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__8 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__8_value;
static const lean_string_object l_Lean_Parser_Command_registerTryTactic___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "register_try\?_tactic"};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__9 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__9_value)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__10 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__8_value),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__10_value)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__11 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__11_value;
static const lean_string_object l_Lean_Parser_Command_registerTryTactic___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__12 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__12_value)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__13 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__13_value;
static const lean_string_object l_Lean_Parser_Command_registerTryTactic___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "priority"};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__14 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__14_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__15 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__15_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__13_value),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__15_value)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__16 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__16_value;
static const lean_string_object l_Lean_Parser_Command_registerTryTactic___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__17 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__17_value)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__18 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__18_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__16_value),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__18_value)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__19 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__19_value;
static const lean_string_object l_Lean_Parser_Command_registerTryTactic___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__20 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__20_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__20_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__21 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__21_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__21_value)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__22 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__22_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__19_value),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__22_value)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__23 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__23_value;
static const lean_string_object l_Lean_Parser_Command_registerTryTactic___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__24 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__24_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__24_value)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__25 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__25_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__23_value),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__25_value)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__26 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__26_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__4_value),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__26_value)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__27 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__27_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__11_value),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__27_value)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__28 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__28_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__28_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__25_value)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__29 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__29_value;
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__2_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__29_value)}};
static const lean_object* l_Lean_Parser_Command_registerTryTactic___closed__30 = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__30_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Command_registerTryTactic = (const lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__30_value;
static const lean_string_object l_tactic_u220e___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "tactic∎"};
static const lean_object* l_tactic_u220e___closed__0 = (const lean_object*)&l_tactic_u220e___closed__0_value;
static const lean_ctor_object l_tactic_u220e___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tactic_u220e___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 148, 242, 87, 185, 4, 228, 246)}};
static const lean_object* l_tactic_u220e___closed__1 = (const lean_object*)&l_tactic_u220e___closed__1_value;
static const lean_string_object l_tactic_u220e___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∎"};
static const lean_object* l_tactic_u220e___closed__2 = (const lean_object*)&l_tactic_u220e___closed__2_value;
static const lean_ctor_object l_tactic_u220e___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_tactic_u220e___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_tactic_u220e___closed__3 = (const lean_object*)&l_tactic_u220e___closed__3_value;
static const lean_ctor_object l_tactic_u220e___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_tactic_u220e___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_tactic_u220e___closed__3_value)}};
static const lean_object* l_tactic_u220e___closed__4 = (const lean_object*)&l_tactic_u220e___closed__4_value;
LEAN_EXPORT const lean_object* l_tactic_u220e = (const lean_object*)&l_tactic_u220e___closed__4_value;
static const lean_string_object l___aux__Init__Try______macroRules__tactic_u220e__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___aux__Init__Try______macroRules__tactic_u220e__1___closed__0 = (const lean_object*)&l___aux__Init__Try______macroRules__tactic_u220e__1___closed__0_value;
static const lean_ctor_object l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1_value_aux_2),((lean_object*)&l___aux__Init__Try______macroRules__tactic_u220e__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1 = (const lean_object*)&l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1_value;
static const lean_string_object l___aux__Init__Try______macroRules__tactic_u220e__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___aux__Init__Try______macroRules__tactic_u220e__1___closed__2 = (const lean_object*)&l___aux__Init__Try______macroRules__tactic_u220e__1___closed__2_value;
static const lean_ctor_object l___aux__Init__Try______macroRules__tactic_u220e__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Try______macroRules__tactic_u220e__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___aux__Init__Try______macroRules__tactic_u220e__1___closed__3 = (const lean_object*)&l___aux__Init__Try______macroRules__tactic_u220e__1___closed__3_value;
static lean_once_cell_t l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4;
LEAN_EXPORT lean_object* l___aux__Init__Try______macroRules__tactic_u220e__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Try______macroRules__tactic_u220e__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term_u220e___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 5, .m_data = "term∎"};
static const lean_object* l_term_u220e___closed__0 = (const lean_object*)&l_term_u220e___closed__0_value;
static const lean_ctor_object l_term_u220e___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_u220e___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 217, 62, 40, 148, 144, 169, 117)}};
static const lean_object* l_term_u220e___closed__1 = (const lean_object*)&l_term_u220e___closed__1_value;
static const lean_ctor_object l_term_u220e___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_tactic_u220e___closed__2_value)}};
static const lean_object* l_term_u220e___closed__2 = (const lean_object*)&l_term_u220e___closed__2_value;
static const lean_ctor_object l_term_u220e___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_term_u220e___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_term_u220e___closed__2_value)}};
static const lean_object* l_term_u220e___closed__3 = (const lean_object*)&l_term_u220e___closed__3_value;
LEAN_EXPORT const lean_object* l_term_u220e = (const lean_object*)&l_term_u220e___closed__3_value;
static const lean_string_object l___aux__Init__Try______macroRules__term_u220e__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__0 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__0_value;
static const lean_string_object l___aux__Init__Try______macroRules__term_u220e__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__1 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__1_value;
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__2_value_aux_1),((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__2_value_aux_2),((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__2 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__2_value;
static const lean_string_object l___aux__Init__Try______macroRules__term_u220e__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__3 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__3_value;
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__23_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__4 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__4_value;
static const lean_string_object l___aux__Init__Try______macroRules__term_u220e__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__5 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__5_value;
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__6_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__6_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__6_value_aux_2),((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__6 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__6_value;
static const lean_string_object l___aux__Init__Try______macroRules__term_u220e__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__7 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__7_value;
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__8_value_aux_2),((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(205, 9, 236, 192, 59, 252, 178, 140)}};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__8 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__8_value;
static const lean_string_object l___aux__Init__Try______macroRules__term_u220e__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "valConfigItem"};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__9 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__9_value;
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__10_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__10_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__10_value_aux_2),((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(135, 67, 19, 169, 17, 95, 109, 188)}};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__10 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__10_value;
static const lean_string_object l___aux__Init__Try______macroRules__term_u220e__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "wrapWithBy"};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__11 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__11_value;
static lean_once_cell_t l___aux__Init__Try______macroRules__term_u220e__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__12;
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(182, 142, 241, 227, 132, 208, 208, 14)}};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__13 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__13_value;
static const lean_string_object l___aux__Init__Try______macroRules__term_u220e__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__14 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__14_value;
static lean_once_cell_t l___aux__Init__Try______macroRules__term_u220e__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__15;
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(235, 97, 249, 134, 197, 220, 12, 91)}};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__16 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__16_value;
static const lean_string_object l___aux__Init__Try______macroRules__term_u220e__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__17 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__17_value;
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__18_value_aux_0),((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__18 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__18_value;
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__19 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__19_value;
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Try______macroRules__term_u220e__1___closed__20 = (const lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__20_value;
LEAN_EXPORT lean_object* l___aux__Init__Try______macroRules__term_u220e__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Try______macroRules__term_u220e__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Try_Marker___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Try_Marker___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Try_Marker(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Try_Marker___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Try_markerUnexpander___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Try_markerUnexpander___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Try_markerUnexpander(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Try_markerUnexpander___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Parser_Tactic_tryTrace___closed__9(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_23_ = l_Lean_Parser_Tactic_optConfig;
v___x_24_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTrace___closed__8));
v___x_25_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTrace___closed__6));
v___x_26_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
lean_ctor_set(v___x_26_, 1, v___x_24_);
lean_ctor_set(v___x_26_, 2, v___x_23_);
return v___x_26_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tryTrace___closed__10(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_27_ = lean_obj_once(&l_Lean_Parser_Tactic_tryTrace___closed__9, &l_Lean_Parser_Tactic_tryTrace___closed__9_once, _init_l_Lean_Parser_Tactic_tryTrace___closed__9);
v___x_28_ = lean_unsigned_to_nat(1022u);
v___x_29_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTrace___closed__4));
v___x_30_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v___x_28_);
lean_ctor_set(v___x_30_, 2, v___x_27_);
return v___x_30_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tryTrace(void){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_obj_once(&l_Lean_Parser_Tactic_tryTrace___closed__10, &l_Lean_Parser_Tactic_tryTrace___closed__10_once, _init_l_Lean_Parser_Tactic_tryTrace___closed__10);
return v___x_31_;
}
}
static lean_object* _init_l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4(void){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Array_mkArray0(lean_box(0));
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Try______macroRules__tactic_u220e__1(lean_object* v_x_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = ((lean_object*)(l_tactic_u220e___closed__1));
v___x_275_ = l_Lean_Syntax_isOfKind(v_x_271_, v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_box(1);
v___x_277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v_a_273_);
return v___x_277_;
}
else
{
lean_object* v_ref_278_; uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_ref_278_ = lean_ctor_get(v_a_272_, 5);
v___x_279_ = 0;
v___x_280_ = l_Lean_SourceInfo_fromRef(v_ref_278_, v___x_279_);
v___x_281_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTrace___closed__4));
v___x_282_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTrace___closed__7));
lean_inc_n(v___x_280_, 3);
v___x_283_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_280_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = ((lean_object*)(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1));
v___x_285_ = ((lean_object*)(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__3));
v___x_286_ = lean_obj_once(&l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4, &l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4_once, _init_l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4);
v___x_287_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_287_, 0, v___x_280_);
lean_ctor_set(v___x_287_, 1, v___x_285_);
lean_ctor_set(v___x_287_, 2, v___x_286_);
v___x_288_ = l_Lean_Syntax_node1(v___x_280_, v___x_284_, v___x_287_);
v___x_289_ = l_Lean_Syntax_node2(v___x_280_, v___x_281_, v___x_283_, v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v_a_273_);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Try______macroRules__tactic_u220e__1___boxed(lean_object* v_x_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___aux__Init__Try______macroRules__tactic_u220e__1(v_x_291_, v_a_292_, v_a_293_);
lean_dec_ref(v_a_292_);
return v_res_294_;
}
}
static lean_object* _init_l___aux__Init__Try______macroRules__term_u220e__1___closed__12(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__11));
v___x_338_ = l_String_toRawSubstring_x27(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l___aux__Init__Try______macroRules__term_u220e__1___closed__15(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__14));
v___x_343_ = l_String_toRawSubstring_x27(v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Try______macroRules__term_u220e__1(lean_object* v_x_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = ((lean_object*)(l_term_u220e___closed__1));
v___x_360_ = l_Lean_Syntax_isOfKind(v_x_356_, v___x_359_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_box(1);
v___x_362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v_a_358_);
return v___x_362_;
}
else
{
lean_object* v_quotContext_363_; lean_object* v_currMacroScope_364_; lean_object* v_ref_365_; uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v_quotContext_363_ = lean_ctor_get(v_a_357_, 1);
v_currMacroScope_364_ = lean_ctor_get(v_a_357_, 2);
v_ref_365_ = lean_ctor_get(v_a_357_, 5);
v___x_366_ = 0;
v___x_367_ = l_Lean_SourceInfo_fromRef(v_ref_365_, v___x_366_);
v___x_368_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__2));
v___x_369_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__3));
lean_inc_n(v___x_367_, 15);
v___x_370_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_367_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__4));
v___x_372_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__6));
v___x_373_ = ((lean_object*)(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__3));
v___x_374_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTrace___closed__4));
v___x_375_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTrace___closed__7));
v___x_376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_367_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = ((lean_object*)(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1));
v___x_378_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__8));
v___x_379_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__10));
v___x_380_ = ((lean_object*)(l_Lean_Parser_Command_registerTryTactic___closed__12));
v___x_381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_367_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
v___x_382_ = lean_obj_once(&l___aux__Init__Try______macroRules__term_u220e__1___closed__12, &l___aux__Init__Try______macroRules__term_u220e__1___closed__12_once, _init_l___aux__Init__Try______macroRules__term_u220e__1___closed__12);
v___x_383_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__13));
lean_inc_n(v_currMacroScope_364_, 2);
lean_inc_n(v_quotContext_363_, 2);
v___x_384_ = l_Lean_addMacroScope(v_quotContext_363_, v___x_383_, v_currMacroScope_364_);
v___x_385_ = lean_box(0);
v___x_386_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_386_, 0, v___x_367_);
lean_ctor_set(v___x_386_, 1, v___x_382_);
lean_ctor_set(v___x_386_, 2, v___x_384_);
lean_ctor_set(v___x_386_, 3, v___x_385_);
v___x_387_ = ((lean_object*)(l_Lean_Parser_Command_registerTryTactic___closed__17));
v___x_388_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_367_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = lean_obj_once(&l___aux__Init__Try______macroRules__term_u220e__1___closed__15, &l___aux__Init__Try______macroRules__term_u220e__1___closed__15_once, _init_l___aux__Init__Try______macroRules__term_u220e__1___closed__15);
v___x_390_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__16));
v___x_391_ = l_Lean_addMacroScope(v_quotContext_363_, v___x_390_, v_currMacroScope_364_);
v___x_392_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__20));
v___x_393_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_393_, 0, v___x_367_);
lean_ctor_set(v___x_393_, 1, v___x_389_);
lean_ctor_set(v___x_393_, 2, v___x_391_);
lean_ctor_set(v___x_393_, 3, v___x_392_);
v___x_394_ = ((lean_object*)(l_Lean_Parser_Command_registerTryTactic___closed__24));
v___x_395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_367_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = l_Lean_Syntax_node5(v___x_367_, v___x_379_, v___x_381_, v___x_386_, v___x_388_, v___x_393_, v___x_395_);
v___x_397_ = l_Lean_Syntax_node1(v___x_367_, v___x_378_, v___x_396_);
v___x_398_ = l_Lean_Syntax_node1(v___x_367_, v___x_373_, v___x_397_);
v___x_399_ = l_Lean_Syntax_node1(v___x_367_, v___x_377_, v___x_398_);
v___x_400_ = l_Lean_Syntax_node2(v___x_367_, v___x_374_, v___x_376_, v___x_399_);
v___x_401_ = l_Lean_Syntax_node1(v___x_367_, v___x_373_, v___x_400_);
v___x_402_ = l_Lean_Syntax_node1(v___x_367_, v___x_372_, v___x_401_);
v___x_403_ = l_Lean_Syntax_node1(v___x_367_, v___x_371_, v___x_402_);
v___x_404_ = l_Lean_Syntax_node2(v___x_367_, v___x_368_, v___x_370_, v___x_403_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v_a_358_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Try______macroRules__term_u220e__1___boxed(lean_object* v_x_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___aux__Init__Try______macroRules__term_u220e__1(v_x_406_, v_a_407_, v_a_408_);
lean_dec_ref(v_a_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Try_Marker___redArg(lean_object* v_a_410_){
_start:
{
lean_inc(v_a_410_);
return v_a_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Try_Marker___redArg___boxed(lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Try_Marker___redArg(v_a_411_);
lean_dec(v_a_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Try_Marker(lean_object* v_00_u03b1_413_, lean_object* v_a_414_){
_start:
{
lean_inc(v_a_414_);
return v_a_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Try_Marker___boxed(lean_object* v_00_u03b1_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Try_Marker(v_00_u03b1_415_, v_a_416_);
lean_dec(v_a_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Try_markerUnexpander___redArg(lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
uint8_t v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_420_ = 0;
v___x_421_ = l_Lean_SourceInfo_fromRef(v_a_418_, v___x_420_);
v___x_422_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__2));
v___x_423_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__3));
lean_inc_n(v___x_421_, 8);
v___x_424_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_421_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__4));
v___x_426_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__6));
v___x_427_ = ((lean_object*)(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__3));
v___x_428_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTrace___closed__4));
v___x_429_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTrace___closed__7));
v___x_430_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_421_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
v___x_431_ = ((lean_object*)(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1));
v___x_432_ = lean_obj_once(&l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4, &l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4_once, _init_l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4);
v___x_433_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_433_, 0, v___x_421_);
lean_ctor_set(v___x_433_, 1, v___x_427_);
lean_ctor_set(v___x_433_, 2, v___x_432_);
v___x_434_ = l_Lean_Syntax_node1(v___x_421_, v___x_431_, v___x_433_);
v___x_435_ = l_Lean_Syntax_node2(v___x_421_, v___x_428_, v___x_430_, v___x_434_);
v___x_436_ = l_Lean_Syntax_node1(v___x_421_, v___x_427_, v___x_435_);
v___x_437_ = l_Lean_Syntax_node1(v___x_421_, v___x_426_, v___x_436_);
v___x_438_ = l_Lean_Syntax_node1(v___x_421_, v___x_425_, v___x_437_);
v___x_439_ = l_Lean_Syntax_node2(v___x_421_, v___x_422_, v___x_424_, v___x_438_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v_a_419_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Try_markerUnexpander___redArg___boxed(lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Try_markerUnexpander___redArg(v_a_441_, v_a_442_);
lean_dec(v_a_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Try_markerUnexpander(lean_object* v_x_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Try_markerUnexpander___redArg(v_a_445_, v_a_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Try_markerUnexpander___boxed(lean_object* v_x_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_Try_markerUnexpander(v_x_448_, v_a_449_, v_a_450_);
lean_dec(v_a_449_);
lean_dec(v_x_448_);
return v_res_451_;
}
}
lean_object* runtime_initialize_Init_Tactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Try(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Try(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Parser_Tactic_tryTrace = _init_l_Lean_Parser_Tactic_tryTrace();
lean_mark_persistent(l_Lean_Parser_Tactic_tryTrace);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Tactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Try(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Try(builtin);
}
#ifdef __cplusplus
}
#endif
