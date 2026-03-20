// Lean compiler output
// Module: Init.Data.Range.Basic
// Imports: public import Init.Control.Basic public import Init.Grind.Tactics public meta import Init.Grind.Tactics import Init.Omega import Init.WFTactics
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_instMembershipNatRange;
LEAN_EXPORT lean_object* l_Std_Legacy_Range_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_size___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__3 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4_value;
static const lean_array_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__6 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__8 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__10 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(138, 49, 229, 237, 137, 52, 176, 206)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__12;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__13;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__14 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value_aux_2),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9_value),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5_value)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__16 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__16_value;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__17;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__18;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__19;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__20;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__21;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__22;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__23;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__24;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__25;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__26;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_forIn_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_forIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_forM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForMNatOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForMNatOfMonad(lean_object*, lean_object*);
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Legacy"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Range"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term[:_]"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__3 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__3_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value_aux_0),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value_aux_1),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value_aux_2),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 247, 114, 105, 22, 2, 212, 24)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__5 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__5_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__7 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__7_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__7_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__9 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__9_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__9_value),LEAN_SCALAR_PTR_LITERAL(69, 6, 27, 142, 141, 165, 41, 16)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__13 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__13_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__13_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__14 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__14_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__16 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__16_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__16_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__17 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__17_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__17_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__18 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__18_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__19 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__19_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__19_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__18_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__21 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__21_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__21_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__22 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__22_value;
LEAN_EXPORT const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x5d = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__22_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term[_:_]"};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__0 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__0_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value_aux_0),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value_aux_1),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value_aux_2),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 227, 143, 95, 3, 88, 200, 110)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__2 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__2_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__2_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__3 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__3_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10_value),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__3_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__4 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__4_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8_value),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__4_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__5 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__5_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__5_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__6 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__6_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__6_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__7 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__7_value;
LEAN_EXPORT const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x5d = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__7_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term[:_:_]"};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__0 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__0_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value_aux_0),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value_aux_1),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value_aux_2),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 39, 16, 99, 27, 138, 138, 190)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__16_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__2 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__2_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__2_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__3 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__3_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__3_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__4 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__4_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__4_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__5 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__5_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__5_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__6 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__6_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__6_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__7 = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__7_value;
LEAN_EXPORT const lean_object* l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d = (const lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__7_value;
static const lean_string_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term[_:_:_]"};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__0 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__0_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value_aux_0),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value_aux_1),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value_aux_2),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 172, 42, 253, 230, 203, 52, 54)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__3_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__12_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__2 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__2_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__2_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__15_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__3 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__3_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__10_value),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__3_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__4 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__4_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__8_value),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__4_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__5 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__5_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__6_value),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__5_value),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__20_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__6 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__6_value;
static const lean_ctor_object l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__6_value)}};
static const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__7 = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__7_value;
LEAN_EXPORT const lean_object* l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d = (const lean_object*)&l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__7_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__1 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__1_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value_aux_1),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3_value;
static lean_once_cell_t l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__5 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__5_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value_aux_1),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__7 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__7_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value_aux_1),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__9 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__9_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value_aux_1),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "stop"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__11 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__11_value;
static lean_once_cell_t l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(73, 89, 146, 127, 39, 212, 171, 73)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value_aux_0),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value_aux_1),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(244, 244, 197, 195, 27, 244, 67, 26)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__15 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__15_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__17 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__17_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value_aux_1),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 39, 227, 176, 252, 65, 103)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "step_pos"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__21 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__21_value;
static lean_once_cell_t l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(245, 121, 239, 198, 116, 70, 162, 77)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value_aux_0),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value_aux_1),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(160, 87, 147, 8, 30, 205, 161, 86)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__25 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__25_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Nat.zero_lt_one"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__27 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__27_value;
static lean_once_cell_t l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__29 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__29_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "zero_lt_one"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__30 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__30_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31_value_aux_0),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(185, 8, 170, 47, 200, 94, 239, 254)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__32 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__32_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__33 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__33_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__34 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__34_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value_aux_1),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35_value;
static lean_once_cell_t l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 104, 217, 143, 145, 181, 232, 169)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value_aux_0),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value_aux_1),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__39 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__39_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__38_value)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__40 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__40_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__40_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__41 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__41_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__39_value),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__41_value)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43_value;
LEAN_EXPORT lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "start"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__0 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__0_value;
static lean_once_cell_t l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 129, 58, 248, 205, 160, 234, 176)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__2 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__2_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value_aux_0),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value_aux_1),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 7, 44, 103, 11, 200, 166, 88)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__4 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__4_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__5 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "step"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__0 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__0_value;
static lean_once_cell_t l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 177, 97, 197, 78, 128, 65, 7)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__2 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__2_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value_aux_0),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 172, 96, 137, 71, 84, 13, 161)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value_aux_1),((lean_object*)&l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2_value),LEAN_SCALAR_PTR_LITERAL(122, 161, 58, 164, 116, 78, 126, 170)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 65, 241, 97, 173, 114, 37, 17)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__4 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__4_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__5 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__5_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__6 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__6_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value_aux_1),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__8 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__8_value;
static const lean_string_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__9 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__9_value;
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value_aux_2),((lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10 = (const lean_object*)&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10_value;
LEAN_EXPORT lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x3a___x5d__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "tacticGet_elem_tactic_extensible"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value;
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 80, 20, 121, 148, 193, 237, 106)}};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1_value;
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "seq1"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value;
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 140, 137, 56, 141, 11, 143, 117)}};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3_value;
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value;
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5_value;
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Membership.get_elem_helper"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6_value;
static lean_once_cell_t l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7;
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Membership"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value;
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "get_elem_helper"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value;
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(205, 217, 109, 94, 255, 55, 82, 109)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value_aux_0),((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(137, 97, 88, 79, 176, 40, 72, 204)}};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value;
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value;
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12_value;
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13_value;
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "assumption"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value;
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(240, 50, 167, 190, 65, 82, 149, 231)}};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15_value;
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value;
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value_aux_2),((lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17_value;
static const lean_string_object l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18 = (const lean_object*)&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18_value;
LEAN_EXPORT lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_Legacy_instMembershipNatRange(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_size(lean_object* v_r_2_){
_start:
{
lean_object* v_start_3_; lean_object* v_stop_4_; lean_object* v_step_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_start_3_ = lean_ctor_get(v_r_2_, 0);
v_stop_4_ = lean_ctor_get(v_r_2_, 1);
v_step_5_ = lean_ctor_get(v_r_2_, 2);
v___x_6_ = lean_nat_sub(v_stop_4_, v_start_3_);
v___x_7_ = lean_nat_add(v___x_6_, v_step_5_);
lean_dec(v___x_6_);
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = lean_nat_sub(v___x_7_, v___x_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_nat_div(v___x_9_, v_step_5_);
lean_dec(v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_size___boxed(lean_object* v_r_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_Legacy_Range_size(v_r_11_);
lean_dec_ref(v_r_11_);
return v_res_12_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__12(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__10));
v___x_40_ = l_Lean_mkAtom(v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__13(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__12, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__12_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__12);
v___x_42_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5));
v___x_43_ = lean_array_push(v___x_42_, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__17(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__16));
v___x_55_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5));
v___x_56_ = lean_array_push(v___x_55_, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__18(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__17, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__17_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__17);
v___x_58_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15));
v___x_59_ = lean_box(2);
v___x_60_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___x_58_);
lean_ctor_set(v___x_60_, 2, v___x_57_);
return v___x_60_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__19(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__18, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__18_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__18);
v___x_62_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__13, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__13_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__13);
v___x_63_ = lean_array_push(v___x_62_, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__20(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_64_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__19, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__19_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__19);
v___x_65_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__11));
v___x_66_ = lean_box(2);
v___x_67_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
lean_ctor_set(v___x_67_, 2, v___x_64_);
return v___x_67_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__21(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__20, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__20_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__20);
v___x_69_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5));
v___x_70_ = lean_array_push(v___x_69_, v___x_68_);
return v___x_70_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__22(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_71_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__21, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__21_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__21);
v___x_72_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9));
v___x_73_ = lean_box(2);
v___x_74_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___x_72_);
lean_ctor_set(v___x_74_, 2, v___x_71_);
return v___x_74_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__23(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__22, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__22_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__22);
v___x_76_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5));
v___x_77_ = lean_array_push(v___x_76_, v___x_75_);
return v___x_77_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__24(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__23, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__23_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__23);
v___x_79_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7));
v___x_80_ = lean_box(2);
v___x_81_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_79_);
lean_ctor_set(v___x_81_, 2, v___x_78_);
return v___x_81_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__25(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__24, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__24_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__24);
v___x_83_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__5));
v___x_84_ = lean_array_push(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__26(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_85_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__25, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__25_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__25);
v___x_86_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4));
v___x_87_ = lean_box(2);
v___x_88_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_86_);
lean_ctor_set(v___x_88_, 2, v___x_85_);
return v___x_88_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1(void){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__26, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__26_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__26);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg___lam__0___boxed(lean_object* v_toApplicative_90_, lean_object* v_i_91_, lean_object* v_step_92_, lean_object* v_inst_93_, lean_object* v_range_94_, lean_object* v_f_95_, lean_object* v_____do__lift_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg___lam__0(v_toApplicative_90_, v_i_91_, v_step_92_, v_inst_93_, v_range_94_, v_f_95_, v_____do__lift_96_);
lean_dec(v_step_92_);
lean_dec(v_i_91_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(lean_object* v_inst_98_, lean_object* v_range_99_, lean_object* v_f_100_, lean_object* v_b_101_, lean_object* v_i_102_){
_start:
{
lean_object* v_stop_103_; lean_object* v_step_104_; uint8_t v___x_105_; 
v_stop_103_ = lean_ctor_get(v_range_99_, 1);
v_step_104_ = lean_ctor_get(v_range_99_, 2);
lean_inc(v_step_104_);
v___x_105_ = lean_nat_dec_lt(v_i_102_, v_stop_103_);
if (v___x_105_ == 0)
{
lean_object* v_toApplicative_106_; lean_object* v_toPure_107_; lean_object* v___x_108_; 
lean_dec(v_step_104_);
lean_dec(v_i_102_);
lean_dec(v_f_100_);
lean_dec_ref(v_range_99_);
v_toApplicative_106_ = lean_ctor_get(v_inst_98_, 0);
lean_inc_ref(v_toApplicative_106_);
lean_dec_ref(v_inst_98_);
v_toPure_107_ = lean_ctor_get(v_toApplicative_106_, 1);
lean_inc(v_toPure_107_);
lean_dec_ref(v_toApplicative_106_);
v___x_108_ = lean_apply_2(v_toPure_107_, lean_box(0), v_b_101_);
return v___x_108_;
}
else
{
lean_object* v_toApplicative_109_; lean_object* v_toBind_110_; lean_object* v___f_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_toApplicative_109_ = lean_ctor_get(v_inst_98_, 0);
lean_inc_ref(v_toApplicative_109_);
v_toBind_110_ = lean_ctor_get(v_inst_98_, 1);
lean_inc(v_toBind_110_);
lean_inc(v_f_100_);
lean_inc(v_i_102_);
v___f_111_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_111_, 0, v_toApplicative_109_);
lean_closure_set(v___f_111_, 1, v_i_102_);
lean_closure_set(v___f_111_, 2, v_step_104_);
lean_closure_set(v___f_111_, 3, v_inst_98_);
lean_closure_set(v___f_111_, 4, v_range_99_);
lean_closure_set(v___f_111_, 5, v_f_100_);
v___x_112_ = lean_apply_3(v_f_100_, v_i_102_, lean_box(0), v_b_101_);
v___x_113_ = lean_apply_4(v_toBind_110_, lean_box(0), lean_box(0), v___x_112_, v___f_111_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg___lam__0(lean_object* v_toApplicative_114_, lean_object* v_i_115_, lean_object* v_step_116_, lean_object* v_inst_117_, lean_object* v_range_118_, lean_object* v_f_119_, lean_object* v_____do__lift_120_){
_start:
{
if (lean_obj_tag(v_____do__lift_120_) == 0)
{
lean_object* v_a_121_; lean_object* v_toPure_122_; lean_object* v___x_123_; 
lean_dec(v_f_119_);
lean_dec_ref(v_range_118_);
lean_dec_ref(v_inst_117_);
v_a_121_ = lean_ctor_get(v_____do__lift_120_, 0);
lean_inc(v_a_121_);
lean_dec_ref(v_____do__lift_120_);
v_toPure_122_ = lean_ctor_get(v_toApplicative_114_, 1);
lean_inc(v_toPure_122_);
lean_dec_ref(v_toApplicative_114_);
v___x_123_ = lean_apply_2(v_toPure_122_, lean_box(0), v_a_121_);
return v___x_123_;
}
else
{
lean_object* v_a_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
lean_dec_ref(v_toApplicative_114_);
v_a_124_ = lean_ctor_get(v_____do__lift_120_, 0);
lean_inc(v_a_124_);
lean_dec_ref(v_____do__lift_120_);
v___x_125_ = lean_nat_add(v_i_115_, v_step_116_);
v___x_126_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(v_inst_117_, v_range_118_, v_f_119_, v_a_124_, v___x_125_);
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_object* v_m_127_, lean_object* v_00_u03b2_128_, lean_object* v_inst_129_, lean_object* v_range_130_, lean_object* v_f_131_, lean_object* v_b_132_, lean_object* v_i_133_, lean_object* v_hs_134_, lean_object* v_hl_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(v_inst_129_, v_range_130_, v_f_131_, v_b_132_, v_i_133_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop_match__1_splitter___redArg(lean_object* v_____do__lift_137_, lean_object* v_h__1_138_, lean_object* v_h__2_139_){
_start:
{
if (lean_obj_tag(v_____do__lift_137_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_141_; 
lean_dec(v_h__2_139_);
v_a_140_ = lean_ctor_get(v_____do__lift_137_, 0);
lean_inc(v_a_140_);
lean_dec_ref(v_____do__lift_137_);
v___x_141_ = lean_apply_1(v_h__1_138_, v_a_140_);
return v___x_141_;
}
else
{
lean_object* v_a_142_; lean_object* v___x_143_; 
lean_dec(v_h__1_138_);
v_a_142_ = lean_ctor_get(v_____do__lift_137_, 0);
lean_inc(v_a_142_);
lean_dec_ref(v_____do__lift_137_);
v___x_143_ = lean_apply_1(v_h__2_139_, v_a_142_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop_match__1_splitter(lean_object* v_00_u03b2_144_, lean_object* v_motive_145_, lean_object* v_____do__lift_146_, lean_object* v_h__1_147_, lean_object* v_h__2_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop_match__1_splitter___redArg(v_____do__lift_146_, v_h__1_147_, v_h__2_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_forIn_x27___redArg(lean_object* v_inst_150_, lean_object* v_range_151_, lean_object* v_init_152_, lean_object* v_f_153_){
_start:
{
lean_object* v_start_154_; lean_object* v___x_155_; 
v_start_154_ = lean_ctor_get(v_range_151_, 0);
lean_inc(v_start_154_);
v___x_155_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(v_inst_150_, v_range_151_, v_f_153_, v_init_152_, v_start_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_forIn_x27(lean_object* v_m_156_, lean_object* v_00_u03b2_157_, lean_object* v_inst_158_, lean_object* v_range_159_, lean_object* v_init_160_, lean_object* v_f_161_){
_start:
{
lean_object* v_start_162_; lean_object* v___x_163_; 
v_start_162_ = lean_ctor_get(v_range_159_, 0);
lean_inc(v_start_162_);
v___x_163_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(v_inst_158_, v_range_159_, v_f_161_, v_init_160_, v_start_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_inst_164_, lean_object* v_00_u03b2_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_start_169_; lean_object* v___x_170_; 
v_start_169_ = lean_ctor_get(v___y_166_, 0);
lean_inc(v_start_169_);
v___x_170_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___redArg(v_inst_164_, v___y_166_, v___y_168_, v___y_167_, v_start_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad___redArg(lean_object* v_inst_171_){
_start:
{
lean_object* v___f_172_; 
v___f_172_ = lean_alloc_closure((void*)(l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_172_, 0, v_inst_171_);
return v___f_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad(lean_object* v_m_173_, lean_object* v_inst_174_){
_start:
{
lean_object* v___f_175_; 
v___f_175_ = lean_alloc_closure((void*)(l_Std_Legacy_Range_instForIn_x27NatInferInstanceMembershipOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_175_, 0, v_inst_174_);
return v___f_175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg___lam__0___boxed(lean_object* v_i_176_, lean_object* v_step_177_, lean_object* v_inst_178_, lean_object* v_range_179_, lean_object* v_f_180_, lean_object* v_____r_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg___lam__0(v_i_176_, v_step_177_, v_inst_178_, v_range_179_, v_f_180_, v_____r_181_);
lean_dec(v_step_177_);
lean_dec(v_i_176_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg(lean_object* v_inst_183_, lean_object* v_range_184_, lean_object* v_f_185_, lean_object* v_i_186_){
_start:
{
lean_object* v_stop_187_; lean_object* v_step_188_; uint8_t v___x_189_; 
v_stop_187_ = lean_ctor_get(v_range_184_, 1);
v_step_188_ = lean_ctor_get(v_range_184_, 2);
lean_inc(v_step_188_);
v___x_189_ = lean_nat_dec_lt(v_i_186_, v_stop_187_);
if (v___x_189_ == 0)
{
lean_object* v_toApplicative_190_; lean_object* v_toPure_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
lean_dec(v_step_188_);
lean_dec(v_i_186_);
lean_dec(v_f_185_);
lean_dec_ref(v_range_184_);
v_toApplicative_190_ = lean_ctor_get(v_inst_183_, 0);
lean_inc_ref(v_toApplicative_190_);
lean_dec_ref(v_inst_183_);
v_toPure_191_ = lean_ctor_get(v_toApplicative_190_, 1);
lean_inc(v_toPure_191_);
lean_dec_ref(v_toApplicative_190_);
v___x_192_ = lean_box(0);
v___x_193_ = lean_apply_2(v_toPure_191_, lean_box(0), v___x_192_);
return v___x_193_;
}
else
{
lean_object* v_toBind_194_; lean_object* v___f_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_toBind_194_ = lean_ctor_get(v_inst_183_, 1);
lean_inc(v_toBind_194_);
lean_inc(v_f_185_);
lean_inc(v_i_186_);
v___f_195_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_195_, 0, v_i_186_);
lean_closure_set(v___f_195_, 1, v_step_188_);
lean_closure_set(v___f_195_, 2, v_inst_183_);
lean_closure_set(v___f_195_, 3, v_range_184_);
lean_closure_set(v___f_195_, 4, v_f_185_);
v___x_196_ = lean_apply_1(v_f_185_, v_i_186_);
v___x_197_ = lean_apply_4(v_toBind_194_, lean_box(0), lean_box(0), v___x_196_, v___f_195_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg___lam__0(lean_object* v_i_198_, lean_object* v_step_199_, lean_object* v_inst_200_, lean_object* v_range_201_, lean_object* v_f_202_, lean_object* v_____r_203_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_nat_add(v_i_198_, v_step_199_);
v___x_205_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg(v_inst_200_, v_range_201_, v_f_202_, v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop(lean_object* v_m_206_, lean_object* v_inst_207_, lean_object* v_range_208_, lean_object* v_f_209_, lean_object* v_i_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg(v_inst_207_, v_range_208_, v_f_209_, v_i_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_forM___redArg(lean_object* v_inst_212_, lean_object* v_range_213_, lean_object* v_f_214_){
_start:
{
lean_object* v_start_215_; lean_object* v___x_216_; 
v_start_215_ = lean_ctor_get(v_range_213_, 0);
lean_inc(v_start_215_);
v___x_216_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg(v_inst_212_, v_range_213_, v_f_214_, v_start_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_forM(lean_object* v_m_217_, lean_object* v_inst_218_, lean_object* v_range_219_, lean_object* v_f_220_){
_start:
{
lean_object* v_start_221_; lean_object* v___x_222_; 
v_start_221_ = lean_ctor_get(v_range_219_, 0);
lean_inc(v_start_221_);
v___x_222_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forM_loop___redArg(v_inst_218_, v_range_219_, v_f_220_, v_start_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForMNatOfMonad___redArg(lean_object* v_inst_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = lean_alloc_closure((void*)(l_Std_Legacy_Range_forM), 4, 2);
lean_closure_set(v___x_224_, 0, lean_box(0));
lean_closure_set(v___x_224_, 1, v_inst_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range_instForMNatOfMonad(lean_object* v_m_225_, lean_object* v_inst_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = lean_alloc_closure((void*)(l_Std_Legacy_Range_forM), 4, 2);
lean_closure_set(v___x_227_, 0, lean_box(0));
lean_closure_set(v___x_227_, 1, v_inst_226_);
return v___x_227_;
}
}
static lean_object* _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4(void){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Array_mkArray0(lean_box(0));
return v___x_376_;
}
}
static lean_object* _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__11));
v___x_397_ = l_String_toRawSubstring_x27(v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__21));
v___x_421_ = l_String_toRawSubstring_x27(v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__27));
v___x_437_ = l_String_toRawSubstring_x27(v___x_436_);
return v___x_437_;
}
}
static lean_object* _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__2));
v___x_456_ = l_String_toRawSubstring_x27(v___x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1(lean_object* v_x_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = ((lean_object*)(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__4));
lean_inc(v_x_475_);
v___x_479_ = l_Lean_Syntax_isOfKind(v_x_475_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec_ref(v_a_476_);
lean_dec(v_x_475_);
v___x_480_ = lean_box(1);
v___x_481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v_a_477_);
return v___x_481_;
}
else
{
lean_object* v_quotContext_482_; lean_object* v_currMacroScope_483_; lean_object* v_ref_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_quotContext_482_ = lean_ctor_get(v_a_476_, 1);
lean_inc(v_quotContext_482_);
v_currMacroScope_483_ = lean_ctor_get(v_a_476_, 2);
lean_inc(v_currMacroScope_483_);
v_ref_484_ = lean_ctor_get(v_a_476_, 5);
lean_inc(v_ref_484_);
lean_dec_ref(v_a_476_);
v___x_485_ = lean_unsigned_to_nat(2u);
v___x_486_ = l_Lean_Syntax_getArg(v_x_475_, v___x_485_);
lean_dec(v_x_475_);
v___x_487_ = 0;
v___x_488_ = l_Lean_SourceInfo_fromRef(v_ref_484_, v___x_487_);
lean_dec(v_ref_484_);
v___x_489_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2));
v___x_490_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3));
lean_inc(v___x_488_);
v___x_491_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_488_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9));
v___x_493_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4);
lean_inc(v___x_488_);
v___x_494_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_494_, 0, v___x_488_);
lean_ctor_set(v___x_494_, 1, v___x_492_);
lean_ctor_set(v___x_494_, 2, v___x_493_);
v___x_495_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6));
v___x_496_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8));
v___x_497_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10));
v___x_498_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12);
v___x_499_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13));
lean_inc(v_currMacroScope_483_);
lean_inc(v_quotContext_482_);
v___x_500_ = l_Lean_addMacroScope(v_quotContext_482_, v___x_499_, v_currMacroScope_483_);
v___x_501_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16));
lean_inc(v___x_488_);
v___x_502_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_502_, 0, v___x_488_);
lean_ctor_set(v___x_502_, 1, v___x_498_);
lean_ctor_set(v___x_502_, 2, v___x_500_);
lean_ctor_set(v___x_502_, 3, v___x_501_);
lean_inc_ref(v___x_494_);
lean_inc(v___x_488_);
v___x_503_ = l_Lean_Syntax_node2(v___x_488_, v___x_497_, v___x_502_, v___x_494_);
v___x_504_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18));
v___x_505_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19));
lean_inc(v___x_488_);
v___x_506_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_488_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
lean_inc_ref(v___x_494_);
lean_inc_ref(v___x_506_);
lean_inc(v___x_488_);
v___x_507_ = l_Lean_Syntax_node3(v___x_488_, v___x_504_, v___x_506_, v___x_494_, v___x_486_);
lean_inc_ref_n(v___x_494_, 2);
lean_inc(v___x_488_);
v___x_508_ = l_Lean_Syntax_node3(v___x_488_, v___x_492_, v___x_494_, v___x_494_, v___x_507_);
lean_inc(v___x_488_);
v___x_509_ = l_Lean_Syntax_node2(v___x_488_, v___x_496_, v___x_503_, v___x_508_);
v___x_510_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20));
lean_inc(v___x_488_);
v___x_511_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_488_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22);
v___x_513_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23));
lean_inc(v_currMacroScope_483_);
lean_inc(v_quotContext_482_);
v___x_514_ = l_Lean_addMacroScope(v_quotContext_482_, v___x_513_, v_currMacroScope_483_);
v___x_515_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26));
lean_inc(v___x_488_);
v___x_516_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_516_, 0, v___x_488_);
lean_ctor_set(v___x_516_, 1, v___x_512_);
lean_ctor_set(v___x_516_, 2, v___x_514_);
lean_ctor_set(v___x_516_, 3, v___x_515_);
lean_inc_ref(v___x_494_);
lean_inc(v___x_488_);
v___x_517_ = l_Lean_Syntax_node2(v___x_488_, v___x_497_, v___x_516_, v___x_494_);
v___x_518_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28);
v___x_519_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31));
lean_inc(v_currMacroScope_483_);
lean_inc(v_quotContext_482_);
v___x_520_ = l_Lean_addMacroScope(v_quotContext_482_, v___x_519_, v_currMacroScope_483_);
v___x_521_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__33));
lean_inc(v___x_488_);
v___x_522_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_522_, 0, v___x_488_);
lean_ctor_set(v___x_522_, 1, v___x_518_);
lean_ctor_set(v___x_522_, 2, v___x_520_);
lean_ctor_set(v___x_522_, 3, v___x_521_);
lean_inc_ref(v___x_494_);
lean_inc(v___x_488_);
v___x_523_ = l_Lean_Syntax_node3(v___x_488_, v___x_504_, v___x_506_, v___x_494_, v___x_522_);
lean_inc_ref_n(v___x_494_, 2);
lean_inc(v___x_488_);
v___x_524_ = l_Lean_Syntax_node3(v___x_488_, v___x_492_, v___x_494_, v___x_494_, v___x_523_);
lean_inc(v___x_488_);
v___x_525_ = l_Lean_Syntax_node2(v___x_488_, v___x_496_, v___x_517_, v___x_524_);
lean_inc(v___x_488_);
v___x_526_ = l_Lean_Syntax_node3(v___x_488_, v___x_492_, v___x_509_, v___x_511_, v___x_525_);
lean_inc(v___x_488_);
v___x_527_ = l_Lean_Syntax_node1(v___x_488_, v___x_495_, v___x_526_);
v___x_528_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35));
lean_inc_ref(v___x_494_);
lean_inc(v___x_488_);
v___x_529_ = l_Lean_Syntax_node1(v___x_488_, v___x_528_, v___x_494_);
v___x_530_ = ((lean_object*)(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11));
lean_inc(v___x_488_);
v___x_531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_488_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36);
v___x_533_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37));
v___x_534_ = l_Lean_addMacroScope(v_quotContext_482_, v___x_533_, v_currMacroScope_483_);
v___x_535_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42));
lean_inc(v___x_488_);
v___x_536_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_536_, 0, v___x_488_);
lean_ctor_set(v___x_536_, 1, v___x_532_);
lean_ctor_set(v___x_536_, 2, v___x_534_);
lean_ctor_set(v___x_536_, 3, v___x_535_);
lean_inc(v___x_488_);
v___x_537_ = l_Lean_Syntax_node2(v___x_488_, v___x_492_, v___x_531_, v___x_536_);
v___x_538_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43));
lean_inc(v___x_488_);
v___x_539_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_488_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = l_Lean_Syntax_node6(v___x_488_, v___x_489_, v___x_491_, v___x_494_, v___x_527_, v___x_529_, v___x_537_, v___x_539_);
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v_a_477_);
return v___x_541_;
}
}
}
static lean_object* _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__0));
v___x_544_ = l_String_toRawSubstring_x27(v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1(lean_object* v_x_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_561_ = ((lean_object*)(l_Std_Legacy_Range_term_x5b___x3a___x5d___closed__1));
lean_inc(v_x_558_);
v___x_562_ = l_Lean_Syntax_isOfKind(v_x_558_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec_ref(v_a_559_);
lean_dec(v_x_558_);
v___x_563_ = lean_box(1);
v___x_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v_a_560_);
return v___x_564_;
}
else
{
lean_object* v_quotContext_565_; lean_object* v_currMacroScope_566_; lean_object* v_ref_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_quotContext_565_ = lean_ctor_get(v_a_559_, 1);
lean_inc(v_quotContext_565_);
v_currMacroScope_566_ = lean_ctor_get(v_a_559_, 2);
lean_inc(v_currMacroScope_566_);
v_ref_567_ = lean_ctor_get(v_a_559_, 5);
lean_inc(v_ref_567_);
lean_dec_ref(v_a_559_);
v___x_568_ = lean_unsigned_to_nat(1u);
v___x_569_ = l_Lean_Syntax_getArg(v_x_558_, v___x_568_);
v___x_570_ = lean_unsigned_to_nat(3u);
v___x_571_ = l_Lean_Syntax_getArg(v_x_558_, v___x_570_);
lean_dec(v_x_558_);
v___x_572_ = 0;
v___x_573_ = l_Lean_SourceInfo_fromRef(v_ref_567_, v___x_572_);
lean_dec(v_ref_567_);
v___x_574_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2));
v___x_575_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3));
lean_inc(v___x_573_);
v___x_576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_573_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9));
v___x_578_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4);
lean_inc(v___x_573_);
v___x_579_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_579_, 0, v___x_573_);
lean_ctor_set(v___x_579_, 1, v___x_577_);
lean_ctor_set(v___x_579_, 2, v___x_578_);
v___x_580_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6));
v___x_581_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8));
v___x_582_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10));
v___x_583_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1);
v___x_584_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__2));
lean_inc(v_currMacroScope_566_);
lean_inc(v_quotContext_565_);
v___x_585_ = l_Lean_addMacroScope(v_quotContext_565_, v___x_584_, v_currMacroScope_566_);
v___x_586_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__5));
lean_inc(v___x_573_);
v___x_587_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_587_, 0, v___x_573_);
lean_ctor_set(v___x_587_, 1, v___x_583_);
lean_ctor_set(v___x_587_, 2, v___x_585_);
lean_ctor_set(v___x_587_, 3, v___x_586_);
lean_inc_ref(v___x_579_);
lean_inc(v___x_573_);
v___x_588_ = l_Lean_Syntax_node2(v___x_573_, v___x_582_, v___x_587_, v___x_579_);
v___x_589_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18));
v___x_590_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19));
lean_inc(v___x_573_);
v___x_591_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_573_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
lean_inc_ref(v___x_579_);
lean_inc_ref(v___x_591_);
lean_inc(v___x_573_);
v___x_592_ = l_Lean_Syntax_node3(v___x_573_, v___x_589_, v___x_591_, v___x_579_, v___x_569_);
lean_inc_ref_n(v___x_579_, 2);
lean_inc(v___x_573_);
v___x_593_ = l_Lean_Syntax_node3(v___x_573_, v___x_577_, v___x_579_, v___x_579_, v___x_592_);
lean_inc(v___x_573_);
v___x_594_ = l_Lean_Syntax_node2(v___x_573_, v___x_581_, v___x_588_, v___x_593_);
v___x_595_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20));
lean_inc(v___x_573_);
v___x_596_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_573_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12);
v___x_598_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13));
lean_inc(v_currMacroScope_566_);
lean_inc(v_quotContext_565_);
v___x_599_ = l_Lean_addMacroScope(v_quotContext_565_, v___x_598_, v_currMacroScope_566_);
v___x_600_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16));
lean_inc(v___x_573_);
v___x_601_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_601_, 0, v___x_573_);
lean_ctor_set(v___x_601_, 1, v___x_597_);
lean_ctor_set(v___x_601_, 2, v___x_599_);
lean_ctor_set(v___x_601_, 3, v___x_600_);
lean_inc_ref(v___x_579_);
lean_inc(v___x_573_);
v___x_602_ = l_Lean_Syntax_node2(v___x_573_, v___x_582_, v___x_601_, v___x_579_);
lean_inc_ref(v___x_579_);
lean_inc_ref(v___x_591_);
lean_inc(v___x_573_);
v___x_603_ = l_Lean_Syntax_node3(v___x_573_, v___x_589_, v___x_591_, v___x_579_, v___x_571_);
lean_inc_ref_n(v___x_579_, 2);
lean_inc(v___x_573_);
v___x_604_ = l_Lean_Syntax_node3(v___x_573_, v___x_577_, v___x_579_, v___x_579_, v___x_603_);
lean_inc(v___x_573_);
v___x_605_ = l_Lean_Syntax_node2(v___x_573_, v___x_581_, v___x_602_, v___x_604_);
v___x_606_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22);
v___x_607_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23));
lean_inc(v_currMacroScope_566_);
lean_inc(v_quotContext_565_);
v___x_608_ = l_Lean_addMacroScope(v_quotContext_565_, v___x_607_, v_currMacroScope_566_);
v___x_609_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26));
lean_inc(v___x_573_);
v___x_610_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_610_, 0, v___x_573_);
lean_ctor_set(v___x_610_, 1, v___x_606_);
lean_ctor_set(v___x_610_, 2, v___x_608_);
lean_ctor_set(v___x_610_, 3, v___x_609_);
lean_inc_ref(v___x_579_);
lean_inc(v___x_573_);
v___x_611_ = l_Lean_Syntax_node2(v___x_573_, v___x_582_, v___x_610_, v___x_579_);
v___x_612_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__28);
v___x_613_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__31));
lean_inc(v_currMacroScope_566_);
lean_inc(v_quotContext_565_);
v___x_614_ = l_Lean_addMacroScope(v_quotContext_565_, v___x_613_, v_currMacroScope_566_);
v___x_615_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__33));
lean_inc(v___x_573_);
v___x_616_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_616_, 0, v___x_573_);
lean_ctor_set(v___x_616_, 1, v___x_612_);
lean_ctor_set(v___x_616_, 2, v___x_614_);
lean_ctor_set(v___x_616_, 3, v___x_615_);
lean_inc_ref(v___x_579_);
lean_inc(v___x_573_);
v___x_617_ = l_Lean_Syntax_node3(v___x_573_, v___x_589_, v___x_591_, v___x_579_, v___x_616_);
lean_inc_ref_n(v___x_579_, 2);
lean_inc(v___x_573_);
v___x_618_ = l_Lean_Syntax_node3(v___x_573_, v___x_577_, v___x_579_, v___x_579_, v___x_617_);
lean_inc(v___x_573_);
v___x_619_ = l_Lean_Syntax_node2(v___x_573_, v___x_581_, v___x_611_, v___x_618_);
lean_inc_ref(v___x_596_);
lean_inc(v___x_573_);
v___x_620_ = l_Lean_Syntax_node5(v___x_573_, v___x_577_, v___x_594_, v___x_596_, v___x_605_, v___x_596_, v___x_619_);
lean_inc(v___x_573_);
v___x_621_ = l_Lean_Syntax_node1(v___x_573_, v___x_580_, v___x_620_);
v___x_622_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35));
lean_inc_ref(v___x_579_);
lean_inc(v___x_573_);
v___x_623_ = l_Lean_Syntax_node1(v___x_573_, v___x_622_, v___x_579_);
v___x_624_ = ((lean_object*)(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11));
lean_inc(v___x_573_);
v___x_625_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_573_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36);
v___x_627_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37));
v___x_628_ = l_Lean_addMacroScope(v_quotContext_565_, v___x_627_, v_currMacroScope_566_);
v___x_629_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42));
lean_inc(v___x_573_);
v___x_630_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_630_, 0, v___x_573_);
lean_ctor_set(v___x_630_, 1, v___x_626_);
lean_ctor_set(v___x_630_, 2, v___x_628_);
lean_ctor_set(v___x_630_, 3, v___x_629_);
lean_inc(v___x_573_);
v___x_631_ = l_Lean_Syntax_node2(v___x_573_, v___x_577_, v___x_625_, v___x_630_);
v___x_632_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43));
lean_inc(v___x_573_);
v___x_633_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_573_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = l_Lean_Syntax_node6(v___x_573_, v___x_574_, v___x_576_, v___x_579_, v___x_621_, v___x_623_, v___x_631_, v___x_633_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v_a_560_);
return v___x_635_;
}
}
}
static lean_object* _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__0));
v___x_638_ = l_String_toRawSubstring_x27(v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1(lean_object* v_x_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = ((lean_object*)(l_Std_Legacy_Range_term_x5b___x3a___x3a___x5d___closed__1));
lean_inc(v_x_665_);
v___x_669_ = l_Lean_Syntax_isOfKind(v_x_665_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; 
lean_dec_ref(v_a_666_);
lean_dec(v_x_665_);
v___x_670_ = lean_box(1);
v___x_671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v_a_667_);
return v___x_671_;
}
else
{
lean_object* v_quotContext_672_; lean_object* v_currMacroScope_673_; lean_object* v_ref_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_quotContext_672_ = lean_ctor_get(v_a_666_, 1);
lean_inc(v_quotContext_672_);
v_currMacroScope_673_ = lean_ctor_get(v_a_666_, 2);
lean_inc(v_currMacroScope_673_);
v_ref_674_ = lean_ctor_get(v_a_666_, 5);
lean_inc(v_ref_674_);
lean_dec_ref(v_a_666_);
v___x_675_ = lean_unsigned_to_nat(1u);
v___x_676_ = l_Lean_Syntax_getArg(v_x_665_, v___x_675_);
v___x_677_ = lean_unsigned_to_nat(3u);
v___x_678_ = l_Lean_Syntax_getArg(v_x_665_, v___x_677_);
v___x_679_ = lean_unsigned_to_nat(5u);
v___x_680_ = l_Lean_Syntax_getArg(v_x_665_, v___x_679_);
lean_dec(v_x_665_);
v___x_681_ = 0;
v___x_682_ = l_Lean_SourceInfo_fromRef(v_ref_674_, v___x_681_);
lean_dec(v_ref_674_);
v___x_683_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2));
v___x_684_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3));
lean_inc(v___x_682_);
v___x_685_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_682_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9));
v___x_687_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4);
lean_inc(v___x_682_);
v___x_688_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_688_, 0, v___x_682_);
lean_ctor_set(v___x_688_, 1, v___x_686_);
lean_ctor_set(v___x_688_, 2, v___x_687_);
v___x_689_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6));
v___x_690_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8));
v___x_691_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10));
v___x_692_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__1);
v___x_693_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__2));
lean_inc(v_currMacroScope_673_);
lean_inc(v_quotContext_672_);
v___x_694_ = l_Lean_addMacroScope(v_quotContext_672_, v___x_693_, v_currMacroScope_673_);
v___x_695_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x5d__1___closed__5));
lean_inc(v___x_682_);
v___x_696_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_696_, 0, v___x_682_);
lean_ctor_set(v___x_696_, 1, v___x_692_);
lean_ctor_set(v___x_696_, 2, v___x_694_);
lean_ctor_set(v___x_696_, 3, v___x_695_);
lean_inc_ref(v___x_688_);
lean_inc(v___x_682_);
v___x_697_ = l_Lean_Syntax_node2(v___x_682_, v___x_691_, v___x_696_, v___x_688_);
v___x_698_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18));
v___x_699_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19));
lean_inc(v___x_682_);
v___x_700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_682_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
lean_inc_ref(v___x_688_);
lean_inc_ref(v___x_700_);
lean_inc(v___x_682_);
v___x_701_ = l_Lean_Syntax_node3(v___x_682_, v___x_698_, v___x_700_, v___x_688_, v___x_676_);
lean_inc_ref_n(v___x_688_, 2);
lean_inc(v___x_682_);
v___x_702_ = l_Lean_Syntax_node3(v___x_682_, v___x_686_, v___x_688_, v___x_688_, v___x_701_);
lean_inc(v___x_682_);
v___x_703_ = l_Lean_Syntax_node2(v___x_682_, v___x_690_, v___x_697_, v___x_702_);
v___x_704_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20));
lean_inc(v___x_682_);
v___x_705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_682_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12);
v___x_707_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13));
lean_inc(v_currMacroScope_673_);
lean_inc(v_quotContext_672_);
v___x_708_ = l_Lean_addMacroScope(v_quotContext_672_, v___x_707_, v_currMacroScope_673_);
v___x_709_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16));
lean_inc(v___x_682_);
v___x_710_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_710_, 0, v___x_682_);
lean_ctor_set(v___x_710_, 1, v___x_706_);
lean_ctor_set(v___x_710_, 2, v___x_708_);
lean_ctor_set(v___x_710_, 3, v___x_709_);
lean_inc_ref(v___x_688_);
lean_inc(v___x_682_);
v___x_711_ = l_Lean_Syntax_node2(v___x_682_, v___x_691_, v___x_710_, v___x_688_);
lean_inc_ref(v___x_688_);
lean_inc_ref(v___x_700_);
lean_inc(v___x_682_);
v___x_712_ = l_Lean_Syntax_node3(v___x_682_, v___x_698_, v___x_700_, v___x_688_, v___x_678_);
lean_inc_ref_n(v___x_688_, 2);
lean_inc(v___x_682_);
v___x_713_ = l_Lean_Syntax_node3(v___x_682_, v___x_686_, v___x_688_, v___x_688_, v___x_712_);
lean_inc(v___x_682_);
v___x_714_ = l_Lean_Syntax_node2(v___x_682_, v___x_690_, v___x_711_, v___x_713_);
v___x_715_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1);
v___x_716_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__2));
lean_inc(v_currMacroScope_673_);
lean_inc(v_quotContext_672_);
v___x_717_ = l_Lean_addMacroScope(v_quotContext_672_, v___x_716_, v_currMacroScope_673_);
v___x_718_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__5));
lean_inc(v___x_682_);
v___x_719_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_719_, 0, v___x_682_);
lean_ctor_set(v___x_719_, 1, v___x_715_);
lean_ctor_set(v___x_719_, 2, v___x_717_);
lean_ctor_set(v___x_719_, 3, v___x_718_);
lean_inc_ref(v___x_688_);
lean_inc(v___x_682_);
v___x_720_ = l_Lean_Syntax_node2(v___x_682_, v___x_691_, v___x_719_, v___x_688_);
lean_inc_ref(v___x_688_);
lean_inc_ref(v___x_700_);
lean_inc(v___x_682_);
v___x_721_ = l_Lean_Syntax_node3(v___x_682_, v___x_698_, v___x_700_, v___x_688_, v___x_680_);
lean_inc_ref_n(v___x_688_, 2);
lean_inc(v___x_682_);
v___x_722_ = l_Lean_Syntax_node3(v___x_682_, v___x_686_, v___x_688_, v___x_688_, v___x_721_);
lean_inc(v___x_682_);
v___x_723_ = l_Lean_Syntax_node2(v___x_682_, v___x_690_, v___x_720_, v___x_722_);
v___x_724_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22);
v___x_725_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23));
lean_inc(v_currMacroScope_673_);
lean_inc(v_quotContext_672_);
v___x_726_ = l_Lean_addMacroScope(v_quotContext_672_, v___x_725_, v_currMacroScope_673_);
v___x_727_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26));
lean_inc(v___x_682_);
v___x_728_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_728_, 0, v___x_682_);
lean_ctor_set(v___x_728_, 1, v___x_724_);
lean_ctor_set(v___x_728_, 2, v___x_726_);
lean_ctor_set(v___x_728_, 3, v___x_727_);
lean_inc_ref(v___x_688_);
lean_inc(v___x_682_);
v___x_729_ = l_Lean_Syntax_node2(v___x_682_, v___x_691_, v___x_728_, v___x_688_);
v___x_730_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7));
v___x_731_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__8));
lean_inc(v___x_682_);
v___x_732_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_682_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4));
v___x_734_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7));
v___x_735_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__9));
v___x_736_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10));
lean_inc(v___x_682_);
v___x_737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_682_);
lean_ctor_set(v___x_737_, 1, v___x_735_);
v___x_738_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15));
lean_inc_ref(v___x_688_);
lean_inc(v___x_682_);
v___x_739_ = l_Lean_Syntax_node1(v___x_682_, v___x_738_, v___x_688_);
lean_inc(v___x_682_);
v___x_740_ = l_Lean_Syntax_node2(v___x_682_, v___x_736_, v___x_737_, v___x_739_);
lean_inc(v___x_682_);
v___x_741_ = l_Lean_Syntax_node1(v___x_682_, v___x_686_, v___x_740_);
lean_inc(v___x_682_);
v___x_742_ = l_Lean_Syntax_node1(v___x_682_, v___x_734_, v___x_741_);
lean_inc(v___x_682_);
v___x_743_ = l_Lean_Syntax_node1(v___x_682_, v___x_733_, v___x_742_);
lean_inc(v___x_682_);
v___x_744_ = l_Lean_Syntax_node2(v___x_682_, v___x_730_, v___x_732_, v___x_743_);
lean_inc_ref(v___x_688_);
lean_inc(v___x_682_);
v___x_745_ = l_Lean_Syntax_node3(v___x_682_, v___x_698_, v___x_700_, v___x_688_, v___x_744_);
lean_inc_ref_n(v___x_688_, 2);
lean_inc(v___x_682_);
v___x_746_ = l_Lean_Syntax_node3(v___x_682_, v___x_686_, v___x_688_, v___x_688_, v___x_745_);
lean_inc(v___x_682_);
v___x_747_ = l_Lean_Syntax_node2(v___x_682_, v___x_690_, v___x_729_, v___x_746_);
lean_inc_ref_n(v___x_705_, 2);
lean_inc(v___x_682_);
v___x_748_ = l_Lean_Syntax_node7(v___x_682_, v___x_686_, v___x_703_, v___x_705_, v___x_714_, v___x_705_, v___x_723_, v___x_705_, v___x_747_);
lean_inc(v___x_682_);
v___x_749_ = l_Lean_Syntax_node1(v___x_682_, v___x_689_, v___x_748_);
v___x_750_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35));
lean_inc_ref(v___x_688_);
lean_inc(v___x_682_);
v___x_751_ = l_Lean_Syntax_node1(v___x_682_, v___x_750_, v___x_688_);
v___x_752_ = ((lean_object*)(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11));
lean_inc(v___x_682_);
v___x_753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_682_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36);
v___x_755_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37));
v___x_756_ = l_Lean_addMacroScope(v_quotContext_672_, v___x_755_, v_currMacroScope_673_);
v___x_757_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42));
lean_inc(v___x_682_);
v___x_758_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_758_, 0, v___x_682_);
lean_ctor_set(v___x_758_, 1, v___x_754_);
lean_ctor_set(v___x_758_, 2, v___x_756_);
lean_ctor_set(v___x_758_, 3, v___x_757_);
lean_inc(v___x_682_);
v___x_759_ = l_Lean_Syntax_node2(v___x_682_, v___x_686_, v___x_753_, v___x_758_);
v___x_760_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43));
lean_inc(v___x_682_);
v___x_761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_682_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = l_Lean_Syntax_node6(v___x_682_, v___x_683_, v___x_685_, v___x_688_, v___x_749_, v___x_751_, v___x_759_, v___x_761_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v_a_667_);
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x3a___x5d__1(lean_object* v_x_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = ((lean_object*)(l_Std_Legacy_Range_term_x5b_x3a___x3a___x5d___closed__1));
lean_inc(v_x_764_);
v___x_768_ = l_Lean_Syntax_isOfKind(v_x_764_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec_ref(v_a_765_);
lean_dec(v_x_764_);
v___x_769_ = lean_box(1);
v___x_770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v_a_766_);
return v___x_770_;
}
else
{
lean_object* v_quotContext_771_; lean_object* v_currMacroScope_772_; lean_object* v_ref_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_quotContext_771_ = lean_ctor_get(v_a_765_, 1);
lean_inc(v_quotContext_771_);
v_currMacroScope_772_ = lean_ctor_get(v_a_765_, 2);
lean_inc(v_currMacroScope_772_);
v_ref_773_ = lean_ctor_get(v_a_765_, 5);
lean_inc(v_ref_773_);
lean_dec_ref(v_a_765_);
v___x_774_ = lean_unsigned_to_nat(2u);
v___x_775_ = l_Lean_Syntax_getArg(v_x_764_, v___x_774_);
v___x_776_ = lean_unsigned_to_nat(4u);
v___x_777_ = l_Lean_Syntax_getArg(v_x_764_, v___x_776_);
lean_dec(v_x_764_);
v___x_778_ = 0;
v___x_779_ = l_Lean_SourceInfo_fromRef(v_ref_773_, v___x_778_);
lean_dec(v_ref_773_);
v___x_780_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__2));
v___x_781_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__3));
lean_inc(v___x_779_);
v___x_782_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_779_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9));
v___x_784_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__4);
lean_inc(v___x_779_);
v___x_785_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_785_, 0, v___x_779_);
lean_ctor_set(v___x_785_, 1, v___x_783_);
lean_ctor_set(v___x_785_, 2, v___x_784_);
v___x_786_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__6));
v___x_787_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__8));
v___x_788_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__10));
v___x_789_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__12);
v___x_790_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__13));
lean_inc(v_currMacroScope_772_);
lean_inc(v_quotContext_771_);
v___x_791_ = l_Lean_addMacroScope(v_quotContext_771_, v___x_790_, v_currMacroScope_772_);
v___x_792_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__16));
lean_inc(v___x_779_);
v___x_793_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_793_, 0, v___x_779_);
lean_ctor_set(v___x_793_, 1, v___x_789_);
lean_ctor_set(v___x_793_, 2, v___x_791_);
lean_ctor_set(v___x_793_, 3, v___x_792_);
lean_inc_ref(v___x_785_);
lean_inc(v___x_779_);
v___x_794_ = l_Lean_Syntax_node2(v___x_779_, v___x_788_, v___x_793_, v___x_785_);
v___x_795_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__18));
v___x_796_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__19));
lean_inc(v___x_779_);
v___x_797_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_779_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
lean_inc_ref(v___x_785_);
lean_inc_ref(v___x_797_);
lean_inc(v___x_779_);
v___x_798_ = l_Lean_Syntax_node3(v___x_779_, v___x_795_, v___x_797_, v___x_785_, v___x_775_);
lean_inc_ref_n(v___x_785_, 2);
lean_inc(v___x_779_);
v___x_799_ = l_Lean_Syntax_node3(v___x_779_, v___x_783_, v___x_785_, v___x_785_, v___x_798_);
lean_inc(v___x_779_);
v___x_800_ = l_Lean_Syntax_node2(v___x_779_, v___x_787_, v___x_794_, v___x_799_);
v___x_801_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__20));
lean_inc(v___x_779_);
v___x_802_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_779_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__1);
v___x_804_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__2));
lean_inc(v_currMacroScope_772_);
lean_inc(v_quotContext_771_);
v___x_805_ = l_Lean_addMacroScope(v_quotContext_771_, v___x_804_, v_currMacroScope_772_);
v___x_806_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__5));
lean_inc(v___x_779_);
v___x_807_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_807_, 0, v___x_779_);
lean_ctor_set(v___x_807_, 1, v___x_803_);
lean_ctor_set(v___x_807_, 2, v___x_805_);
lean_ctor_set(v___x_807_, 3, v___x_806_);
lean_inc_ref(v___x_785_);
lean_inc(v___x_779_);
v___x_808_ = l_Lean_Syntax_node2(v___x_779_, v___x_788_, v___x_807_, v___x_785_);
lean_inc_ref(v___x_785_);
lean_inc_ref(v___x_797_);
lean_inc(v___x_779_);
v___x_809_ = l_Lean_Syntax_node3(v___x_779_, v___x_795_, v___x_797_, v___x_785_, v___x_777_);
lean_inc_ref_n(v___x_785_, 2);
lean_inc(v___x_779_);
v___x_810_ = l_Lean_Syntax_node3(v___x_779_, v___x_783_, v___x_785_, v___x_785_, v___x_809_);
lean_inc(v___x_779_);
v___x_811_ = l_Lean_Syntax_node2(v___x_779_, v___x_787_, v___x_808_, v___x_810_);
v___x_812_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__22);
v___x_813_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__23));
lean_inc(v_currMacroScope_772_);
lean_inc(v_quotContext_771_);
v___x_814_ = l_Lean_addMacroScope(v_quotContext_771_, v___x_813_, v_currMacroScope_772_);
v___x_815_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__26));
lean_inc(v___x_779_);
v___x_816_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_816_, 0, v___x_779_);
lean_ctor_set(v___x_816_, 1, v___x_812_);
lean_ctor_set(v___x_816_, 2, v___x_814_);
lean_ctor_set(v___x_816_, 3, v___x_815_);
lean_inc_ref(v___x_785_);
lean_inc(v___x_779_);
v___x_817_ = l_Lean_Syntax_node2(v___x_779_, v___x_788_, v___x_816_, v___x_785_);
v___x_818_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__7));
v___x_819_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__8));
lean_inc(v___x_779_);
v___x_820_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_779_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__4));
v___x_822_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__7));
v___x_823_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__9));
v___x_824_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b___x3a___x3a___x5d__1___closed__10));
lean_inc(v___x_779_);
v___x_825_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_779_);
lean_ctor_set(v___x_825_, 1, v___x_823_);
v___x_826_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__15));
lean_inc_ref(v___x_785_);
lean_inc(v___x_779_);
v___x_827_ = l_Lean_Syntax_node1(v___x_779_, v___x_826_, v___x_785_);
lean_inc(v___x_779_);
v___x_828_ = l_Lean_Syntax_node2(v___x_779_, v___x_824_, v___x_825_, v___x_827_);
lean_inc(v___x_779_);
v___x_829_ = l_Lean_Syntax_node1(v___x_779_, v___x_783_, v___x_828_);
lean_inc(v___x_779_);
v___x_830_ = l_Lean_Syntax_node1(v___x_779_, v___x_822_, v___x_829_);
lean_inc(v___x_779_);
v___x_831_ = l_Lean_Syntax_node1(v___x_779_, v___x_821_, v___x_830_);
lean_inc(v___x_779_);
v___x_832_ = l_Lean_Syntax_node2(v___x_779_, v___x_818_, v___x_820_, v___x_831_);
lean_inc_ref(v___x_785_);
lean_inc(v___x_779_);
v___x_833_ = l_Lean_Syntax_node3(v___x_779_, v___x_795_, v___x_797_, v___x_785_, v___x_832_);
lean_inc_ref_n(v___x_785_, 2);
lean_inc(v___x_779_);
v___x_834_ = l_Lean_Syntax_node3(v___x_779_, v___x_783_, v___x_785_, v___x_785_, v___x_833_);
lean_inc(v___x_779_);
v___x_835_ = l_Lean_Syntax_node2(v___x_779_, v___x_787_, v___x_817_, v___x_834_);
lean_inc_ref(v___x_802_);
lean_inc(v___x_779_);
v___x_836_ = l_Lean_Syntax_node5(v___x_779_, v___x_783_, v___x_800_, v___x_802_, v___x_811_, v___x_802_, v___x_835_);
lean_inc(v___x_779_);
v___x_837_ = l_Lean_Syntax_node1(v___x_779_, v___x_786_, v___x_836_);
v___x_838_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__35));
lean_inc_ref(v___x_785_);
lean_inc(v___x_779_);
v___x_839_ = l_Lean_Syntax_node1(v___x_779_, v___x_838_, v___x_785_);
v___x_840_ = ((lean_object*)(l_Std_Legacy_Range_term_x5b_x3a___x5d___closed__11));
lean_inc(v___x_779_);
v___x_841_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_779_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = lean_obj_once(&l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36, &l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36_once, _init_l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__36);
v___x_843_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__37));
v___x_844_ = l_Lean_addMacroScope(v_quotContext_771_, v___x_843_, v_currMacroScope_772_);
v___x_845_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__42));
lean_inc(v___x_779_);
v___x_846_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_846_, 0, v___x_779_);
lean_ctor_set(v___x_846_, 1, v___x_842_);
lean_ctor_set(v___x_846_, 2, v___x_844_);
lean_ctor_set(v___x_846_, 3, v___x_845_);
lean_inc(v___x_779_);
v___x_847_ = l_Lean_Syntax_node2(v___x_779_, v___x_783_, v___x_841_, v___x_846_);
v___x_848_ = ((lean_object*)(l_Std_Legacy_Range___aux__Init__Data__Range__Basic______macroRules__Std__Legacy__Range__term_x5b_x3a___x5d__1___closed__43));
lean_inc(v___x_779_);
v___x_849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_779_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = l_Lean_Syntax_node6(v___x_779_, v___x_780_, v___x_782_, v___x_785_, v___x_837_, v___x_839_, v___x_847_, v___x_849_);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v_a_766_);
return v___x_851_;
}
}
}
static lean_object* _init_l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__6));
v___x_869_ = l_String_toRawSubstring_x27(v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1(lean_object* v_x_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_898_ = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__1));
v___x_899_ = l_Lean_Syntax_isOfKind(v_x_895_, v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec_ref(v_a_896_);
v___x_900_ = lean_box(1);
v___x_901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v_a_897_);
return v___x_901_;
}
else
{
lean_object* v_quotContext_902_; lean_object* v_currMacroScope_903_; lean_object* v_ref_904_; uint8_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_quotContext_902_ = lean_ctor_get(v_a_896_, 1);
lean_inc(v_quotContext_902_);
v_currMacroScope_903_ = lean_ctor_get(v_a_896_, 2);
lean_inc(v_currMacroScope_903_);
v_ref_904_ = lean_ctor_get(v_a_896_, 5);
lean_inc(v_ref_904_);
lean_dec_ref(v_a_896_);
v___x_905_ = 0;
v___x_906_ = l_Lean_SourceInfo_fromRef(v_ref_904_, v___x_905_);
lean_dec(v_ref_904_);
v___x_907_ = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__3));
v___x_908_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1___closed__9));
v___x_909_ = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__4));
v___x_910_ = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__5));
lean_inc(v___x_906_);
v___x_911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_906_);
lean_ctor_set(v___x_911_, 1, v___x_909_);
v___x_912_ = lean_obj_once(&l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7, &l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7_once, _init_l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__7);
v___x_913_ = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__10));
v___x_914_ = l_Lean_addMacroScope(v_quotContext_902_, v___x_913_, v_currMacroScope_903_);
v___x_915_ = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__12));
lean_inc(v___x_906_);
v___x_916_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_916_, 0, v___x_906_);
lean_ctor_set(v___x_916_, 1, v___x_912_);
lean_ctor_set(v___x_916_, 2, v___x_914_);
lean_ctor_set(v___x_916_, 3, v___x_915_);
lean_inc(v___x_906_);
v___x_917_ = l_Lean_Syntax_node2(v___x_906_, v___x_910_, v___x_911_, v___x_916_);
v___x_918_ = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__13));
lean_inc(v___x_906_);
v___x_919_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_906_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__14));
v___x_921_ = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__15));
lean_inc(v___x_906_);
v___x_922_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_906_);
lean_ctor_set(v___x_922_, 1, v___x_920_);
lean_inc(v___x_906_);
v___x_923_ = l_Lean_Syntax_node1(v___x_906_, v___x_921_, v___x_922_);
v___x_924_ = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__17));
v___x_925_ = ((lean_object*)(l___aux__Init__Data__Range__Basic______macroRules__tacticGet__elem__tactic__extensible__1___closed__18));
lean_inc(v___x_906_);
v___x_926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_906_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
lean_inc(v___x_906_);
v___x_927_ = l_Lean_Syntax_node1(v___x_906_, v___x_924_, v___x_926_);
lean_inc_ref(v___x_919_);
lean_inc(v___x_906_);
v___x_928_ = l_Lean_Syntax_node5(v___x_906_, v___x_908_, v___x_917_, v___x_919_, v___x_923_, v___x_919_, v___x_927_);
v___x_929_ = l_Lean_Syntax_node1(v___x_906_, v___x_907_, v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v_a_897_);
return v___x_930_;
}
}
}
lean_object* runtime_initialize_Init_Control_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Legacy_instMembershipNatRange = _init_l_Std_Legacy_instMembershipNatRange();
lean_mark_persistent(l_Std_Legacy_instMembershipNatRange);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1 = _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1();
lean_mark_persistent(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Basic(uint8_t builtin);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
