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
static const lean_string_object l_Lean_Parser_Tactic_tryTraceWith___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "tryTraceWith"};
static const lean_object* l_Lean_Parser_Tactic_tryTraceWith___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tryTraceWith___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tryTraceWith___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tryTraceWith___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTraceWith___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tryTraceWith___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTraceWith___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tryTraceWith___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTraceWith___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tryTraceWith___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 89, 220, 7, 252, 66, 194, 105)}};
static const lean_object* l_Lean_Parser_Tactic_tryTraceWith___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tryTraceWith___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_tryTraceWith___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l_Lean_Parser_Tactic_tryTraceWith___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tryTraceWith___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tryTraceWith___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTraceWith___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_tryTraceWith___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_tryTraceWith___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tryTraceWith___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tryTraceWith___closed__4;
static const lean_string_object l_Lean_Parser_Tactic_tryTraceWith___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Parser_Tactic_tryTraceWith___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_tryTraceWith___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tryTraceWith___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tryTraceWith___closed__5_value),LEAN_SCALAR_PTR_LITERAL(13, 106, 54, 236, 164, 218, 24, 154)}};
static const lean_object* l_Lean_Parser_Tactic_tryTraceWith___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_tryTraceWith___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tryTraceWith___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTraceWith___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_tryTraceWith___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_tryTraceWith___closed__7_value;
static lean_once_cell_t l_Lean_Parser_Tactic_tryTraceWith___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tryTraceWith___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_tryTraceWith___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_tryTraceWith___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_tryTraceWith;
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
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__22_value),((lean_object*)&l_Lean_Parser_Tactic_tryTraceWith___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__23 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__23_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__23_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__24 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__24_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__24_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__25 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__25_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__25_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__26 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__26_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__26_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__27 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__27_value;
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAll___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__27_value)}};
static const lean_object* l_Lean_Parser_Tactic_attemptAll___closed__28 = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__28_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_attemptAll = (const lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__28_value;
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
static const lean_ctor_object l_Lean_Parser_Tactic_attemptAllPar___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAllPar___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__26_value)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_firstPar___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_firstPar___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_attemptAll___closed__26_value)}};
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
static const lean_ctor_object l_Lean_Parser_Command_registerTryTactic___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tryTrace___closed__6_value),((lean_object*)&l_Lean_Parser_Command_registerTryTactic___closed__28_value),((lean_object*)&l_Lean_Parser_Tactic_tryTraceWith___closed__7_value)}};
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
static const lean_ctor_object l___aux__Init__Try______macroRules__term_u220e__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Try______macroRules__term_u220e__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tryTraceWith___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
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
static lean_object* _init_l_Lean_Parser_Tactic_tryTraceWith___closed__4(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_41_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTraceWith___closed__3));
v___x_42_ = lean_obj_once(&l_Lean_Parser_Tactic_tryTrace___closed__9, &l_Lean_Parser_Tactic_tryTrace___closed__9_once, _init_l_Lean_Parser_Tactic_tryTrace___closed__9);
v___x_43_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTrace___closed__6));
v___x_44_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v___x_42_);
lean_ctor_set(v___x_44_, 2, v___x_41_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tryTraceWith___closed__8(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_50_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTraceWith___closed__7));
v___x_51_ = lean_obj_once(&l_Lean_Parser_Tactic_tryTraceWith___closed__4, &l_Lean_Parser_Tactic_tryTraceWith___closed__4_once, _init_l_Lean_Parser_Tactic_tryTraceWith___closed__4);
v___x_52_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTrace___closed__6));
v___x_53_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
lean_ctor_set(v___x_53_, 2, v___x_50_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tryTraceWith___closed__9(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_obj_once(&l_Lean_Parser_Tactic_tryTraceWith___closed__8, &l_Lean_Parser_Tactic_tryTraceWith___closed__8_once, _init_l_Lean_Parser_Tactic_tryTraceWith___closed__8);
v___x_55_ = lean_unsigned_to_nat(1022u);
v___x_56_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTraceWith___closed__1));
v___x_57_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_54_);
return v___x_57_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_tryTraceWith(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_obj_once(&l_Lean_Parser_Tactic_tryTraceWith___closed__9, &l_Lean_Parser_Tactic_tryTraceWith___closed__9_once, _init_l_Lean_Parser_Tactic_tryTraceWith___closed__9);
return v___x_58_;
}
}
static lean_object* _init_l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4(void){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Array_mkArray0(lean_box(0));
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Try______macroRules__tactic_u220e__1(lean_object* v_x_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = ((lean_object*)(l_tactic_u220e___closed__1));
v___x_297_ = l_Lean_Syntax_isOfKind(v_x_293_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_box(1);
v___x_299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v_a_295_);
return v___x_299_;
}
else
{
lean_object* v_ref_300_; uint8_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_ref_300_ = lean_ctor_get(v_a_294_, 5);
v___x_301_ = 0;
v___x_302_ = l_Lean_SourceInfo_fromRef(v_ref_300_, v___x_301_);
v___x_303_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTrace___closed__4));
v___x_304_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTrace___closed__7));
lean_inc_n(v___x_302_, 3);
v___x_305_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_302_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = ((lean_object*)(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1));
v___x_307_ = ((lean_object*)(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__3));
v___x_308_ = lean_obj_once(&l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4, &l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4_once, _init_l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4);
v___x_309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_309_, 0, v___x_302_);
lean_ctor_set(v___x_309_, 1, v___x_307_);
lean_ctor_set(v___x_309_, 2, v___x_308_);
v___x_310_ = l_Lean_Syntax_node1(v___x_302_, v___x_306_, v___x_309_);
v___x_311_ = l_Lean_Syntax_node2(v___x_302_, v___x_303_, v___x_305_, v___x_310_);
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v_a_295_);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Try______macroRules__tactic_u220e__1___boxed(lean_object* v_x_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___aux__Init__Try______macroRules__tactic_u220e__1(v_x_313_, v_a_314_, v_a_315_);
lean_dec_ref(v_a_314_);
return v_res_316_;
}
}
static lean_object* _init_l___aux__Init__Try______macroRules__term_u220e__1___closed__12(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__11));
v___x_360_ = l_String_toRawSubstring_x27(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l___aux__Init__Try______macroRules__term_u220e__1___closed__15(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__14));
v___x_365_ = l_String_toRawSubstring_x27(v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Try______macroRules__term_u220e__1(lean_object* v_x_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = ((lean_object*)(l_term_u220e___closed__1));
v___x_382_ = l_Lean_Syntax_isOfKind(v_x_378_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_box(1);
v___x_384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v_a_380_);
return v___x_384_;
}
else
{
lean_object* v_quotContext_385_; lean_object* v_currMacroScope_386_; lean_object* v_ref_387_; uint8_t v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_quotContext_385_ = lean_ctor_get(v_a_379_, 1);
v_currMacroScope_386_ = lean_ctor_get(v_a_379_, 2);
v_ref_387_ = lean_ctor_get(v_a_379_, 5);
v___x_388_ = 0;
v___x_389_ = l_Lean_SourceInfo_fromRef(v_ref_387_, v___x_388_);
v___x_390_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__2));
v___x_391_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__3));
lean_inc_n(v___x_389_, 15);
v___x_392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_389_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__4));
v___x_394_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__6));
v___x_395_ = ((lean_object*)(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__3));
v___x_396_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTrace___closed__4));
v___x_397_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTrace___closed__7));
v___x_398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_389_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = ((lean_object*)(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1));
v___x_400_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__8));
v___x_401_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__10));
v___x_402_ = ((lean_object*)(l_Lean_Parser_Command_registerTryTactic___closed__12));
v___x_403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_389_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = lean_obj_once(&l___aux__Init__Try______macroRules__term_u220e__1___closed__12, &l___aux__Init__Try______macroRules__term_u220e__1___closed__12_once, _init_l___aux__Init__Try______macroRules__term_u220e__1___closed__12);
v___x_405_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__13));
lean_inc_n(v_currMacroScope_386_, 2);
lean_inc_n(v_quotContext_385_, 2);
v___x_406_ = l_Lean_addMacroScope(v_quotContext_385_, v___x_405_, v_currMacroScope_386_);
v___x_407_ = lean_box(0);
v___x_408_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_408_, 0, v___x_389_);
lean_ctor_set(v___x_408_, 1, v___x_404_);
lean_ctor_set(v___x_408_, 2, v___x_406_);
lean_ctor_set(v___x_408_, 3, v___x_407_);
v___x_409_ = ((lean_object*)(l_Lean_Parser_Command_registerTryTactic___closed__17));
v___x_410_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_389_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = lean_obj_once(&l___aux__Init__Try______macroRules__term_u220e__1___closed__15, &l___aux__Init__Try______macroRules__term_u220e__1___closed__15_once, _init_l___aux__Init__Try______macroRules__term_u220e__1___closed__15);
v___x_412_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__16));
v___x_413_ = l_Lean_addMacroScope(v_quotContext_385_, v___x_412_, v_currMacroScope_386_);
v___x_414_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__20));
v___x_415_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_415_, 0, v___x_389_);
lean_ctor_set(v___x_415_, 1, v___x_411_);
lean_ctor_set(v___x_415_, 2, v___x_413_);
lean_ctor_set(v___x_415_, 3, v___x_414_);
v___x_416_ = ((lean_object*)(l_Lean_Parser_Command_registerTryTactic___closed__24));
v___x_417_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_389_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = l_Lean_Syntax_node5(v___x_389_, v___x_401_, v___x_403_, v___x_408_, v___x_410_, v___x_415_, v___x_417_);
v___x_419_ = l_Lean_Syntax_node1(v___x_389_, v___x_400_, v___x_418_);
v___x_420_ = l_Lean_Syntax_node1(v___x_389_, v___x_395_, v___x_419_);
v___x_421_ = l_Lean_Syntax_node1(v___x_389_, v___x_399_, v___x_420_);
v___x_422_ = l_Lean_Syntax_node2(v___x_389_, v___x_396_, v___x_398_, v___x_421_);
v___x_423_ = l_Lean_Syntax_node1(v___x_389_, v___x_395_, v___x_422_);
v___x_424_ = l_Lean_Syntax_node1(v___x_389_, v___x_394_, v___x_423_);
v___x_425_ = l_Lean_Syntax_node1(v___x_389_, v___x_393_, v___x_424_);
v___x_426_ = l_Lean_Syntax_node2(v___x_389_, v___x_390_, v___x_392_, v___x_425_);
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v_a_380_);
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Try______macroRules__term_u220e__1___boxed(lean_object* v_x_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___aux__Init__Try______macroRules__term_u220e__1(v_x_428_, v_a_429_, v_a_430_);
lean_dec_ref(v_a_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Try_Marker___redArg(lean_object* v_a_432_){
_start:
{
lean_inc(v_a_432_);
return v_a_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Try_Marker___redArg___boxed(lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Try_Marker___redArg(v_a_433_);
lean_dec(v_a_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Try_Marker(lean_object* v_00_u03b1_435_, lean_object* v_a_436_){
_start:
{
lean_inc(v_a_436_);
return v_a_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Try_Marker___boxed(lean_object* v_00_u03b1_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Try_Marker(v_00_u03b1_437_, v_a_438_);
lean_dec(v_a_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Try_markerUnexpander___redArg(lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_442_ = 0;
v___x_443_ = l_Lean_SourceInfo_fromRef(v_a_440_, v___x_442_);
v___x_444_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__2));
v___x_445_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__3));
lean_inc_n(v___x_443_, 8);
v___x_446_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_443_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__4));
v___x_448_ = ((lean_object*)(l___aux__Init__Try______macroRules__term_u220e__1___closed__6));
v___x_449_ = ((lean_object*)(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__3));
v___x_450_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTrace___closed__4));
v___x_451_ = ((lean_object*)(l_Lean_Parser_Tactic_tryTrace___closed__7));
v___x_452_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_443_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = ((lean_object*)(l___aux__Init__Try______macroRules__tactic_u220e__1___closed__1));
v___x_454_ = lean_obj_once(&l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4, &l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4_once, _init_l___aux__Init__Try______macroRules__tactic_u220e__1___closed__4);
v___x_455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_455_, 0, v___x_443_);
lean_ctor_set(v___x_455_, 1, v___x_449_);
lean_ctor_set(v___x_455_, 2, v___x_454_);
v___x_456_ = l_Lean_Syntax_node1(v___x_443_, v___x_453_, v___x_455_);
v___x_457_ = l_Lean_Syntax_node2(v___x_443_, v___x_450_, v___x_452_, v___x_456_);
v___x_458_ = l_Lean_Syntax_node1(v___x_443_, v___x_449_, v___x_457_);
v___x_459_ = l_Lean_Syntax_node1(v___x_443_, v___x_448_, v___x_458_);
v___x_460_ = l_Lean_Syntax_node1(v___x_443_, v___x_447_, v___x_459_);
v___x_461_ = l_Lean_Syntax_node2(v___x_443_, v___x_444_, v___x_446_, v___x_460_);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v_a_441_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Try_markerUnexpander___redArg___boxed(lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Try_markerUnexpander___redArg(v_a_463_, v_a_464_);
lean_dec(v_a_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Try_markerUnexpander(lean_object* v_x_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_Try_markerUnexpander___redArg(v_a_467_, v_a_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Try_markerUnexpander___boxed(lean_object* v_x_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Try_markerUnexpander(v_x_470_, v_a_471_, v_a_472_);
lean_dec(v_a_471_);
lean_dec(v_x_470_);
return v_res_473_;
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
l_Lean_Parser_Tactic_tryTraceWith = _init_l_Lean_Parser_Tactic_tryTraceWith();
lean_mark_persistent(l_Lean_Parser_Tactic_tryTraceWith);
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
