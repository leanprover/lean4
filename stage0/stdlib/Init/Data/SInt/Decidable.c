// Lean compiler output
// Module: Init.Data.SInt.Decidable
// Imports: public import Init.Data.SInt.Basic public import Init.PropLemmas public import Init.Data.BitVec.Decidable
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
uint8_t lean_uint8_of_nat_mk(lean_object*);
uint8_t l_BitVec_instDecidableForallBitVec___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint16_t lean_uint16_of_nat_mk(lean_object*);
uint8_t l_BitVec_instDecidableExistsBitVec___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat_mk(lean_object*);
uint64_t lean_uint64_of_nat_mk(lean_object*);
static const lean_string_object l_commandDeclare__decidable__int__quantifiers_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "commandDeclare_decidable_int_quantifiers__"};
static const lean_object* l_commandDeclare__decidable__int__quantifiers_____00__closed__0 = (const lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__0_value;
static const lean_ctor_object l_commandDeclare__decidable__int__quantifiers_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 43, 117, 152, 7, 64, 61, 215)}};
static const lean_object* l_commandDeclare__decidable__int__quantifiers_____00__closed__1 = (const lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__1_value;
static const lean_string_object l_commandDeclare__decidable__int__quantifiers_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_commandDeclare__decidable__int__quantifiers_____00__closed__2 = (const lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__2_value;
static const lean_ctor_object l_commandDeclare__decidable__int__quantifiers_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_commandDeclare__decidable__int__quantifiers_____00__closed__3 = (const lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__3_value;
static const lean_string_object l_commandDeclare__decidable__int__quantifiers_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "declare_decidable_int_quantifiers"};
static const lean_object* l_commandDeclare__decidable__int__quantifiers_____00__closed__4 = (const lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__4_value;
static const lean_ctor_object l_commandDeclare__decidable__int__quantifiers_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__4_value)}};
static const lean_object* l_commandDeclare__decidable__int__quantifiers_____00__closed__5 = (const lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__5_value;
static const lean_string_object l_commandDeclare__decidable__int__quantifiers_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_commandDeclare__decidable__int__quantifiers_____00__closed__6 = (const lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__6_value;
static const lean_ctor_object l_commandDeclare__decidable__int__quantifiers_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_commandDeclare__decidable__int__quantifiers_____00__closed__7 = (const lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__7_value;
static const lean_ctor_object l_commandDeclare__decidable__int__quantifiers_____00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__7_value)}};
static const lean_object* l_commandDeclare__decidable__int__quantifiers_____00__closed__8 = (const lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__8_value;
static const lean_ctor_object l_commandDeclare__decidable__int__quantifiers_____00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__3_value),((lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__5_value),((lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__8_value)}};
static const lean_object* l_commandDeclare__decidable__int__quantifiers_____00__closed__9 = (const lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__9_value;
static const lean_string_object l_commandDeclare__decidable__int__quantifiers_____00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_commandDeclare__decidable__int__quantifiers_____00__closed__10 = (const lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__10_value;
static const lean_ctor_object l_commandDeclare__decidable__int__quantifiers_____00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_commandDeclare__decidable__int__quantifiers_____00__closed__11 = (const lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__11_value;
static const lean_ctor_object l_commandDeclare__decidable__int__quantifiers_____00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__11_value),((lean_object*)(((size_t)(1023) << 1) | 1))}};
static const lean_object* l_commandDeclare__decidable__int__quantifiers_____00__closed__12 = (const lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__12_value;
static const lean_ctor_object l_commandDeclare__decidable__int__quantifiers_____00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__3_value),((lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__9_value),((lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__12_value)}};
static const lean_object* l_commandDeclare__decidable__int__quantifiers_____00__closed__13 = (const lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__13_value;
static const lean_ctor_object l_commandDeclare__decidable__int__quantifiers_____00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__13_value)}};
static const lean_object* l_commandDeclare__decidable__int__quantifiers_____00__closed__14 = (const lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__14_value;
LEAN_EXPORT const lean_object* l_commandDeclare__decidable__int__quantifiers____ = (const lean_object*)&l_commandDeclare__decidable__int__quantifiers_____00__closed__14_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__0 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__0_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__1 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__1_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__4 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__4_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namespace"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__5 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__5_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__6_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__6_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__6_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(84, 17, 124, 142, 243, 161, 231, 243)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__6 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__6_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__7 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__7_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__8_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__8_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__8_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__8 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__8_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__9 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__9_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__10_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__10_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__10_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__10 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__10_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__11;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "theorem"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__12 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__12_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__13_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__13_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__13_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(238, 116, 137, 74, 194, 103, 58, 54)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__13 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__13_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__14 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__14_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__15_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__15_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__15_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__15 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__15_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "forall_iff_forall_ofBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__16 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__16_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__17;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(80, 238, 149, 31, 196, 23, 38, 18)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__18 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__18_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__19 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__19_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__20_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__20_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__20_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__20 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__20_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__21 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__21_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implicitBinder"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__22 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__22_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__23_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__23_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__23_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(39, 181, 62, 102, 86, 14, 161, 96)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__23 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__23_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__24 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__24_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "P"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__25 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__25_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__26;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(160, 230, 119, 31, 245, 11, 149, 236)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__27 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__27_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__28 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__28_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arrow"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__29 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__29_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__30_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__30_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__30_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(182, 146, 143, 73, 122, 115, 5, 207)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__30 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__30_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "→"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__31 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__31_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prop"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__32 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__32_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__33_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__33_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__33_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(200, 217, 246, 140, 179, 171, 30, 243)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__33 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__33_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prop"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__34 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__34_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__35 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__35_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__36 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__36_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__37_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__37_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__37_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__37 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__37_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_↔_"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__38 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__38_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__38_value),LEAN_SCALAR_PTR_LITERAL(220, 124, 41, 198, 228, 162, 237, 244)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__39 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__39_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__40 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__40_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__41_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__41_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__41_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__41 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__41_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__42 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__42_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__43_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__43_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__43_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__43 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__43_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__44 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__44_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__45 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__45_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__46 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__46_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__47 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__47_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__48;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "forall"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__49 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__49_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__50_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__50_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__50_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__49_value),LEAN_SCALAR_PTR_LITERAL(195, 142, 115, 15, 55, 103, 31, 115)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__50 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__50_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∀"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__51 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__51_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__52 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__52_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__53;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__52_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__54 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__54_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__55 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__55_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__56 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__56_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__57_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__57_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__57_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__57 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__57_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__58 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__58_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "↔"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__59 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__59_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__60 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__60_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__61_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__61_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__61_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__60_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__61 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__61_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__62 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__62_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__63;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__62_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__64 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__64_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ofBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__65 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__65_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__66;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__65_value),LEAN_SCALAR_PTR_LITERAL(109, 13, 70, 115, 31, 141, 156, 173)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__67 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__67_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__68 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__68_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__69_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__69_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__69_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__68_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__69 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__69_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__70 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__70_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__71 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__71_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__72_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__72_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__72_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__71_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__72 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__72_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__73 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__73_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__74 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__74_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__75_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__75_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__75_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__75_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__75_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__74_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__75 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__75_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__76 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__76_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__77_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__77_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__77_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__77_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__77_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__77_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__76_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__77 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__77_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__78 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__78_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__79_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__79;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__78_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__80 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__80_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__81 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__81_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "x.toBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__82 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__82_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__83;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__84 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__84_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__85_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__52_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__85_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__84_value),LEAN_SCALAR_PTR_LITERAL(154, 27, 47, 236, 186, 178, 171, 172)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__85 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__85_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__86 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__86_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__87 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__87_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__88 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__88_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__89_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__89_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__89_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__89_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__89_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__87_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__89_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__88_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__89 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__89_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__90 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__90_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__91_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__91_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__91_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__91_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__91_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__91_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__90_value),LEAN_SCALAR_PTR_LITERAL(37, 156, 84, 218, 244, 57, 142, 153)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__91 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__91_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__92 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__92_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__93_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__93_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__93_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__93_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__93_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__93_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__92_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__93 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__93_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instDecidableForall"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__94 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__94_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__95_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__95;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__94_value),LEAN_SCALAR_PTR_LITERAL(111, 114, 57, 32, 119, 142, 151, 176)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__96 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__96_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instBinder"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__97 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__97_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__98_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__98_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__98_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__98_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__98_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__97_value),LEAN_SCALAR_PTR_LITERAL(198, 219, 89, 171, 221, 95, 22, 227)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__98 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__98_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__99 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__99_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "DecidablePred"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__100 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__100_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__101_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__101;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__100_value),LEAN_SCALAR_PTR_LITERAL(16, 236, 239, 206, 255, 167, 201, 157)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__102 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__102_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__103 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__103_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__104 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__104_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__105_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__105;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__104_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__106 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__106_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "decidable_of_iff'"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__107 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__107_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__108_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__108;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__107_value),LEAN_SCALAR_PTR_LITERAL(107, 5, 65, 49, 195, 60, 169, 181)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__109 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__109_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__110 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__110_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__111_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__111_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__111_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__111_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__111_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__111_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__110_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__111 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__111_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__112 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__112_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "exists_iff_exists_ofBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__113 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__113_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__114_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__114;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__113_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 57, 207, 237, 42, 141, 238)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__115 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__115_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 8, .m_data = "term∃_,_"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__116 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__116_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__116_value),LEAN_SCALAR_PTR_LITERAL(224, 105, 219, 112, 166, 139, 167, 161)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__117 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__117_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∃"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__118 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__118_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "explicitBinders"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__119 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__119_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__120_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__120_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__119_value),LEAN_SCALAR_PTR_LITERAL(167, 149, 127, 13, 202, 239, 226, 94)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__120 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__120_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unbracketedExplicitBinders"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__121 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__121_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__122_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__122_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__121_value),LEAN_SCALAR_PTR_LITERAL(187, 220, 119, 82, 242, 112, 119, 200)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__122 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__122_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__123 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__123_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__124_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__124_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__123_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__124 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__124_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "bracketedExplicitBinders"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__125 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__125_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__126_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__126_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__125_value),LEAN_SCALAR_PTR_LITERAL(22, 65, 7, 186, 44, 89, 152, 79)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__126 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__126_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "hx"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__127 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__127_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__128_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__128;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__127_value),LEAN_SCALAR_PTR_LITERAL(214, 92, 204, 191, 107, 147, 103, 110)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__129 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__129_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instDecidableExists"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__130 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__130_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__131_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__131;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__130_value),LEAN_SCALAR_PTR_LITERAL(214, 97, 88, 214, 200, 207, 123, 169)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__132 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__132_value;
static const lean_string_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__133 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__133_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__134_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__134_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__134_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__134_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__134_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__134_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__133_value),LEAN_SCALAR_PTR_LITERAL(254, 132, 206, 38, 133, 164, 145, 139)}};
static const lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__134 = (const lean_object*)&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__134_value;
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int8_instDecidableForall___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int8_instDecidableForall___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int8_instDecidableForall___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Int8_instDecidableForall___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int8_instDecidableForall(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int8_instDecidableForall___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int8_instDecidableExists___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Int8_instDecidableExists___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int8_instDecidableExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int8_instDecidableExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int16_instDecidableForall___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int16_instDecidableForall___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int16_instDecidableForall___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Int16_instDecidableForall___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int16_instDecidableForall(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int16_instDecidableForall___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int16_instDecidableExists___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Int16_instDecidableExists___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int16_instDecidableExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int16_instDecidableExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int32_instDecidableForall___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int32_instDecidableForall___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int32_instDecidableForall___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Int32_instDecidableForall___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int32_instDecidableForall(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int32_instDecidableForall___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int32_instDecidableExists___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Int32_instDecidableExists___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int32_instDecidableExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int32_instDecidableExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int64_instDecidableForall___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int64_instDecidableForall___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int64_instDecidableForall___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Int64_instDecidableForall___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int64_instDecidableForall(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int64_instDecidableForall___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int64_instDecidableExists___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Int64_instDecidableExists___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int64_instDecidableExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int64_instDecidableExists___boxed(lean_object*, lean_object*);
static lean_object* _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__11(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Array_mkArray0___redArg();
return v___x_58_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__17(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__16));
v___x_73_ = l_String_toRawSubstring_x27(v___x_72_);
return v___x_73_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__26(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__25));
v___x_92_ = l_String_toRawSubstring_x27(v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__48(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__47));
v___x_138_ = l_String_toRawSubstring_x27(v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__53(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__52));
v___x_148_ = l_String_toRawSubstring_x27(v___x_147_);
return v___x_148_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__63(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__62));
v___x_168_ = l_String_toRawSubstring_x27(v___x_167_);
return v___x_168_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__66(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__65));
v___x_173_ = l_String_toRawSubstring_x27(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__79(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__78));
v___x_204_ = l_String_toRawSubstring_x27(v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__83(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__82));
v___x_210_ = l_String_toRawSubstring_x27(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__95(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__94));
v___x_237_ = l_String_toRawSubstring_x27(v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__101(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__100));
v___x_249_ = l_String_toRawSubstring_x27(v___x_248_);
return v___x_249_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__105(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__104));
v___x_255_ = l_String_toRawSubstring_x27(v___x_254_);
return v___x_255_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__108(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__107));
v___x_260_ = l_String_toRawSubstring_x27(v___x_259_);
return v___x_260_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__114(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__113));
v___x_272_ = l_String_toRawSubstring_x27(v___x_271_);
return v___x_272_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__128(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__127));
v___x_297_ = l_String_toRawSubstring_x27(v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__131(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__130));
v___x_302_ = l_String_toRawSubstring_x27(v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1(lean_object* v_x_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_314_ = ((lean_object*)(l_commandDeclare__decidable__int__quantifiers_____00__closed__1));
lean_inc(v_x_311_);
v___x_315_ = l_Lean_Syntax_isOfKind(v_x_311_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v_x_311_);
v___x_316_ = lean_box(1);
v___x_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v_a_313_);
return v___x_317_;
}
else
{
lean_object* v_ref_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_ref_318_ = lean_ctor_get(v_a_312_, 5);
v___x_319_ = lean_unsigned_to_nat(1u);
v___x_320_ = l_Lean_Syntax_getArg(v_x_311_, v___x_319_);
v___x_321_ = lean_unsigned_to_nat(2u);
v___x_322_ = l_Lean_Syntax_getArg(v_x_311_, v___x_321_);
lean_dec(v_x_311_);
v___x_323_ = 0;
v___x_324_ = l_Lean_SourceInfo_fromRef(v_ref_318_, v___x_323_);
v___x_325_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__1));
v___x_326_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__5));
v___x_327_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__6));
lean_inc_n(v___x_324_, 141);
v___x_328_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_324_);
lean_ctor_set(v___x_328_, 1, v___x_326_);
lean_inc_n(v___x_320_, 2);
v___x_329_ = l_Lean_Syntax_node2(v___x_324_, v___x_327_, v___x_328_, v___x_320_);
v___x_330_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__8));
v___x_331_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__10));
v___x_332_ = lean_obj_once(&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__11, &l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__11_once, _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__11);
v___x_333_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_333_, 0, v___x_324_);
lean_ctor_set(v___x_333_, 1, v___x_325_);
lean_ctor_set(v___x_333_, 2, v___x_332_);
lean_inc_ref_n(v___x_333_, 30);
v___x_334_ = l_Lean_Syntax_node7(v___x_324_, v___x_331_, v___x_333_, v___x_333_, v___x_333_, v___x_333_, v___x_333_, v___x_333_, v___x_333_);
v___x_335_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__12));
v___x_336_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__13));
v___x_337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_324_);
lean_ctor_set(v___x_337_, 1, v___x_335_);
v___x_338_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__15));
v___x_339_ = lean_obj_once(&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__17, &l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__17_once, _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__17);
v___x_340_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__18));
v___x_341_ = lean_box(0);
v___x_342_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_342_, 0, v___x_324_);
lean_ctor_set(v___x_342_, 1, v___x_339_);
lean_ctor_set(v___x_342_, 2, v___x_340_);
lean_ctor_set(v___x_342_, 3, v___x_341_);
lean_inc_ref(v___x_342_);
v___x_343_ = l_Lean_Syntax_node2(v___x_324_, v___x_338_, v___x_342_, v___x_333_);
v___x_344_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__20));
v___x_345_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__23));
v___x_346_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__24));
v___x_347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_324_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = lean_obj_once(&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__26, &l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__26_once, _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__26);
v___x_349_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__27));
v___x_350_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_350_, 0, v___x_324_);
lean_ctor_set(v___x_350_, 1, v___x_348_);
lean_ctor_set(v___x_350_, 2, v___x_349_);
lean_ctor_set(v___x_350_, 3, v___x_341_);
lean_inc_ref_n(v___x_350_, 2);
v___x_351_ = l_Lean_Syntax_node1(v___x_324_, v___x_325_, v___x_350_);
v___x_352_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__28));
v___x_353_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_324_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__30));
v___x_355_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__31));
v___x_356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_324_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__33));
v___x_358_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__34));
v___x_359_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_324_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = l_Lean_Syntax_node1(v___x_324_, v___x_357_, v___x_359_);
v___x_361_ = l_Lean_Syntax_node3(v___x_324_, v___x_354_, v___x_320_, v___x_356_, v___x_360_);
lean_inc_ref_n(v___x_353_, 6);
v___x_362_ = l_Lean_Syntax_node2(v___x_324_, v___x_325_, v___x_353_, v___x_361_);
v___x_363_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__35));
v___x_364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_324_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
lean_inc(v___x_362_);
lean_inc_n(v___x_351_, 2);
v___x_365_ = l_Lean_Syntax_node4(v___x_324_, v___x_345_, v___x_347_, v___x_351_, v___x_362_, v___x_364_);
v___x_366_ = l_Lean_Syntax_node1(v___x_324_, v___x_325_, v___x_365_);
v___x_367_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__37));
v___x_368_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__39));
v___x_369_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__41));
v___x_370_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__43));
v___x_371_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__44));
v___x_372_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_324_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
v___x_373_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__46));
v___x_374_ = lean_obj_once(&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__48, &l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__48_once, _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__48);
v___x_375_ = lean_box(0);
v___x_376_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_376_, 0, v___x_324_);
lean_ctor_set(v___x_376_, 1, v___x_374_);
lean_ctor_set(v___x_376_, 2, v___x_375_);
lean_ctor_set(v___x_376_, 3, v___x_341_);
v___x_377_ = l_Lean_Syntax_node1(v___x_324_, v___x_373_, v___x_376_);
lean_inc_ref_n(v___x_372_, 3);
v___x_378_ = l_Lean_Syntax_node2(v___x_324_, v___x_370_, v___x_372_, v___x_377_);
v___x_379_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__50));
v___x_380_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__51));
v___x_381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_324_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
v___x_382_ = lean_obj_once(&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__53, &l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__53_once, _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__53);
v___x_383_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__54));
v___x_384_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_384_, 0, v___x_324_);
lean_ctor_set(v___x_384_, 1, v___x_382_);
lean_ctor_set(v___x_384_, 2, v___x_383_);
lean_ctor_set(v___x_384_, 3, v___x_341_);
lean_inc_ref_n(v___x_384_, 3);
v___x_385_ = l_Lean_Syntax_node1(v___x_324_, v___x_325_, v___x_384_);
v___x_386_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__55));
v___x_387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_324_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__57));
lean_inc_n(v___x_385_, 3);
v___x_389_ = l_Lean_Syntax_node2(v___x_324_, v___x_388_, v___x_350_, v___x_385_);
lean_inc(v___x_389_);
lean_inc_ref_n(v___x_387_, 8);
lean_inc_ref(v___x_381_);
v___x_390_ = l_Lean_Syntax_node5(v___x_324_, v___x_379_, v___x_381_, v___x_385_, v___x_333_, v___x_387_, v___x_389_);
v___x_391_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__58));
v___x_392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_324_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
lean_inc_ref_n(v___x_392_, 5);
lean_inc_n(v___x_378_, 2);
v___x_393_ = l_Lean_Syntax_node3(v___x_324_, v___x_369_, v___x_378_, v___x_390_, v___x_392_);
v___x_394_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__59));
v___x_395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_324_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__61));
v___x_397_ = lean_obj_once(&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__63, &l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__63_once, _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__63);
v___x_398_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__64));
v___x_399_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_399_, 0, v___x_324_);
lean_ctor_set(v___x_399_, 1, v___x_397_);
lean_ctor_set(v___x_399_, 2, v___x_398_);
lean_ctor_set(v___x_399_, 3, v___x_341_);
v___x_400_ = l_Lean_Syntax_node1(v___x_324_, v___x_325_, v___x_322_);
v___x_401_ = l_Lean_Syntax_node2(v___x_324_, v___x_388_, v___x_399_, v___x_400_);
lean_inc(v___x_401_);
v___x_402_ = l_Lean_Syntax_node2(v___x_324_, v___x_325_, v___x_353_, v___x_401_);
v___x_403_ = l_Lean_Syntax_node5(v___x_324_, v___x_396_, v___x_372_, v___x_385_, v___x_402_, v___x_333_, v___x_392_);
v___x_404_ = l_Lean_Syntax_node1(v___x_324_, v___x_325_, v___x_403_);
v___x_405_ = lean_obj_once(&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__66, &l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__66_once, _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__66);
v___x_406_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__67));
v___x_407_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_407_, 0, v___x_324_);
lean_ctor_set(v___x_407_, 1, v___x_405_);
lean_ctor_set(v___x_407_, 2, v___x_406_);
lean_ctor_set(v___x_407_, 3, v___x_341_);
v___x_408_ = l_Lean_Syntax_node2(v___x_324_, v___x_388_, v___x_407_, v___x_385_);
lean_inc(v___x_408_);
v___x_409_ = l_Lean_Syntax_node3(v___x_324_, v___x_369_, v___x_378_, v___x_408_, v___x_392_);
v___x_410_ = l_Lean_Syntax_node1(v___x_324_, v___x_325_, v___x_409_);
lean_inc(v___x_410_);
v___x_411_ = l_Lean_Syntax_node2(v___x_324_, v___x_388_, v___x_350_, v___x_410_);
lean_inc(v___x_411_);
v___x_412_ = l_Lean_Syntax_node5(v___x_324_, v___x_379_, v___x_381_, v___x_404_, v___x_333_, v___x_387_, v___x_411_);
lean_inc_ref(v___x_395_);
lean_inc(v___x_393_);
v___x_413_ = l_Lean_Syntax_node3(v___x_324_, v___x_368_, v___x_393_, v___x_395_, v___x_412_);
v___x_414_ = l_Lean_Syntax_node2(v___x_324_, v___x_367_, v___x_353_, v___x_413_);
lean_inc(v___x_366_);
v___x_415_ = l_Lean_Syntax_node2(v___x_324_, v___x_344_, v___x_366_, v___x_414_);
v___x_416_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__69));
v___x_417_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__70));
v___x_418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_324_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__72));
v___x_420_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__73));
v___x_421_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_324_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v___x_422_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__74));
v___x_423_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__75));
v___x_424_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_324_);
lean_ctor_set(v___x_424_, 1, v___x_422_);
v___x_425_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__77));
v___x_426_ = lean_obj_once(&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__79, &l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__79_once, _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__79);
v___x_427_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__80));
v___x_428_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_428_, 0, v___x_324_);
lean_ctor_set(v___x_428_, 1, v___x_426_);
lean_ctor_set(v___x_428_, 2, v___x_427_);
lean_ctor_set(v___x_428_, 3, v___x_341_);
lean_inc_ref_n(v___x_428_, 2);
v___x_429_ = l_Lean_Syntax_node2(v___x_324_, v___x_325_, v___x_428_, v___x_384_);
v___x_430_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__81));
v___x_431_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_324_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v___x_432_ = l_Lean_Syntax_node2(v___x_324_, v___x_388_, v___x_428_, v___x_410_);
lean_inc_ref_n(v___x_431_, 3);
lean_inc(v___x_429_);
v___x_433_ = l_Lean_Syntax_node4(v___x_324_, v___x_425_, v___x_429_, v___x_333_, v___x_431_, v___x_432_);
lean_inc_ref_n(v___x_424_, 3);
v___x_434_ = l_Lean_Syntax_node2(v___x_324_, v___x_423_, v___x_424_, v___x_433_);
v___x_435_ = lean_obj_once(&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__83, &l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__83_once, _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__83);
v___x_436_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__85));
v___x_437_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_437_, 0, v___x_324_);
lean_ctor_set(v___x_437_, 1, v___x_435_);
lean_ctor_set(v___x_437_, 2, v___x_436_);
lean_ctor_set(v___x_437_, 3, v___x_341_);
lean_inc_ref(v___x_437_);
v___x_438_ = l_Lean_Syntax_node1(v___x_324_, v___x_325_, v___x_437_);
v___x_439_ = l_Lean_Syntax_node2(v___x_324_, v___x_388_, v___x_428_, v___x_438_);
v___x_440_ = l_Lean_Syntax_node4(v___x_324_, v___x_425_, v___x_429_, v___x_333_, v___x_431_, v___x_439_);
v___x_441_ = l_Lean_Syntax_node2(v___x_324_, v___x_423_, v___x_424_, v___x_440_);
v___x_442_ = l_Lean_Syntax_node3(v___x_324_, v___x_325_, v___x_434_, v___x_387_, v___x_441_);
v___x_443_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__86));
v___x_444_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_324_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
lean_inc_ref_n(v___x_444_, 4);
lean_inc_ref_n(v___x_421_, 4);
v___x_445_ = l_Lean_Syntax_node3(v___x_324_, v___x_419_, v___x_421_, v___x_442_, v___x_444_);
v___x_446_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__89));
v___x_447_ = l_Lean_Syntax_node2(v___x_324_, v___x_446_, v___x_333_, v___x_333_);
lean_inc_n(v___x_447_, 3);
lean_inc_ref_n(v___x_418_, 3);
v___x_448_ = l_Lean_Syntax_node4(v___x_324_, v___x_416_, v___x_418_, v___x_445_, v___x_447_, v___x_333_);
lean_inc_ref(v___x_337_);
v___x_449_ = l_Lean_Syntax_node4(v___x_324_, v___x_336_, v___x_337_, v___x_343_, v___x_415_, v___x_448_);
lean_inc_n(v___x_334_, 3);
v___x_450_ = l_Lean_Syntax_node2(v___x_324_, v___x_330_, v___x_334_, v___x_449_);
v___x_451_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__90));
v___x_452_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__91));
v___x_453_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__93));
v___x_454_ = l_Lean_Syntax_node1(v___x_324_, v___x_453_, v___x_333_);
v___x_455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_324_);
lean_ctor_set(v___x_455_, 1, v___x_451_);
v___x_456_ = lean_obj_once(&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__95, &l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__95_once, _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__95);
v___x_457_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__96));
v___x_458_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_458_, 0, v___x_324_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
lean_ctor_set(v___x_458_, 2, v___x_457_);
lean_ctor_set(v___x_458_, 3, v___x_341_);
v___x_459_ = l_Lean_Syntax_node2(v___x_324_, v___x_338_, v___x_458_, v___x_333_);
v___x_460_ = l_Lean_Syntax_node1(v___x_324_, v___x_325_, v___x_459_);
v___x_461_ = l_Lean_Syntax_node5(v___x_324_, v___x_396_, v___x_372_, v___x_351_, v___x_362_, v___x_333_, v___x_392_);
v___x_462_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__98));
v___x_463_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__99));
v___x_464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_324_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = lean_obj_once(&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__101, &l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__101_once, _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__101);
v___x_466_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__102));
v___x_467_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_467_, 0, v___x_324_);
lean_ctor_set(v___x_467_, 1, v___x_465_);
lean_ctor_set(v___x_467_, 2, v___x_466_);
lean_ctor_set(v___x_467_, 3, v___x_341_);
v___x_468_ = l_Lean_Syntax_node2(v___x_324_, v___x_388_, v___x_467_, v___x_351_);
v___x_469_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__103));
v___x_470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_324_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = l_Lean_Syntax_node4(v___x_324_, v___x_462_, v___x_464_, v___x_333_, v___x_468_, v___x_470_);
v___x_472_ = l_Lean_Syntax_node2(v___x_324_, v___x_325_, v___x_461_, v___x_471_);
v___x_473_ = lean_obj_once(&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__105, &l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__105_once, _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__105);
v___x_474_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__106));
v___x_475_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_475_, 0, v___x_324_);
lean_ctor_set(v___x_475_, 1, v___x_473_);
lean_ctor_set(v___x_475_, 2, v___x_474_);
lean_ctor_set(v___x_475_, 3, v___x_341_);
v___x_476_ = l_Lean_Syntax_node1(v___x_324_, v___x_325_, v___x_393_);
lean_inc_ref(v___x_475_);
v___x_477_ = l_Lean_Syntax_node2(v___x_324_, v___x_388_, v___x_475_, v___x_476_);
v___x_478_ = l_Lean_Syntax_node2(v___x_324_, v___x_367_, v___x_353_, v___x_477_);
lean_inc(v___x_472_);
v___x_479_ = l_Lean_Syntax_node2(v___x_324_, v___x_344_, v___x_472_, v___x_478_);
v___x_480_ = lean_obj_once(&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__108, &l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__108_once, _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__108);
v___x_481_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__109));
v___x_482_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_482_, 0, v___x_324_);
lean_ctor_set(v___x_482_, 1, v___x_480_);
lean_ctor_set(v___x_482_, 2, v___x_481_);
lean_ctor_set(v___x_482_, 3, v___x_341_);
v___x_483_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__111));
v___x_484_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__112));
v___x_485_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_324_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = l_Lean_Syntax_node1(v___x_324_, v___x_483_, v___x_485_);
lean_inc(v___x_486_);
v___x_487_ = l_Lean_Syntax_node2(v___x_324_, v___x_325_, v___x_486_, v___x_342_);
lean_inc_ref(v___x_482_);
v___x_488_ = l_Lean_Syntax_node2(v___x_324_, v___x_388_, v___x_482_, v___x_487_);
v___x_489_ = l_Lean_Syntax_node4(v___x_324_, v___x_416_, v___x_418_, v___x_488_, v___x_447_, v___x_333_);
lean_inc_ref(v___x_455_);
lean_inc(v___x_454_);
v___x_490_ = l_Lean_Syntax_node6(v___x_324_, v___x_452_, v___x_454_, v___x_455_, v___x_333_, v___x_460_, v___x_479_, v___x_489_);
v___x_491_ = l_Lean_Syntax_node2(v___x_324_, v___x_330_, v___x_334_, v___x_490_);
v___x_492_ = lean_obj_once(&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__114, &l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__114_once, _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__114);
v___x_493_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__115));
v___x_494_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_494_, 0, v___x_324_);
lean_ctor_set(v___x_494_, 1, v___x_492_);
lean_ctor_set(v___x_494_, 2, v___x_493_);
lean_ctor_set(v___x_494_, 3, v___x_341_);
lean_inc_ref(v___x_494_);
v___x_495_ = l_Lean_Syntax_node2(v___x_324_, v___x_338_, v___x_494_, v___x_333_);
v___x_496_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__117));
v___x_497_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__118));
v___x_498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_324_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__120));
v___x_500_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__122));
v___x_501_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__124));
v___x_502_ = l_Lean_Syntax_node1(v___x_324_, v___x_501_, v___x_384_);
v___x_503_ = l_Lean_Syntax_node1(v___x_324_, v___x_325_, v___x_502_);
lean_inc(v___x_503_);
v___x_504_ = l_Lean_Syntax_node2(v___x_324_, v___x_500_, v___x_503_, v___x_333_);
v___x_505_ = l_Lean_Syntax_node1(v___x_324_, v___x_499_, v___x_504_);
lean_inc_ref(v___x_498_);
v___x_506_ = l_Lean_Syntax_node4(v___x_324_, v___x_496_, v___x_498_, v___x_505_, v___x_387_, v___x_389_);
v___x_507_ = l_Lean_Syntax_node3(v___x_324_, v___x_369_, v___x_378_, v___x_506_, v___x_392_);
v___x_508_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__126));
v___x_509_ = l_Lean_Syntax_node5(v___x_324_, v___x_508_, v___x_372_, v___x_503_, v___x_353_, v___x_401_, v___x_392_);
v___x_510_ = l_Lean_Syntax_node1(v___x_324_, v___x_325_, v___x_509_);
v___x_511_ = l_Lean_Syntax_node1(v___x_324_, v___x_499_, v___x_510_);
v___x_512_ = l_Lean_Syntax_node4(v___x_324_, v___x_496_, v___x_498_, v___x_511_, v___x_387_, v___x_411_);
lean_inc(v___x_507_);
v___x_513_ = l_Lean_Syntax_node3(v___x_324_, v___x_368_, v___x_507_, v___x_395_, v___x_512_);
v___x_514_ = l_Lean_Syntax_node2(v___x_324_, v___x_367_, v___x_353_, v___x_513_);
v___x_515_ = l_Lean_Syntax_node2(v___x_324_, v___x_344_, v___x_366_, v___x_514_);
v___x_516_ = lean_obj_once(&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__128, &l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__128_once, _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__128);
v___x_517_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__129));
v___x_518_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_518_, 0, v___x_324_);
lean_ctor_set(v___x_518_, 1, v___x_516_);
lean_ctor_set(v___x_518_, 2, v___x_517_);
lean_ctor_set(v___x_518_, 3, v___x_341_);
lean_inc_ref_n(v___x_518_, 2);
v___x_519_ = l_Lean_Syntax_node3(v___x_324_, v___x_325_, v___x_384_, v___x_387_, v___x_518_);
v___x_520_ = l_Lean_Syntax_node3(v___x_324_, v___x_419_, v___x_421_, v___x_519_, v___x_444_);
v___x_521_ = l_Lean_Syntax_node1(v___x_324_, v___x_325_, v___x_520_);
v___x_522_ = l_Lean_Syntax_node3(v___x_324_, v___x_325_, v___x_437_, v___x_387_, v___x_518_);
v___x_523_ = l_Lean_Syntax_node3(v___x_324_, v___x_419_, v___x_421_, v___x_522_, v___x_444_);
lean_inc(v___x_521_);
v___x_524_ = l_Lean_Syntax_node4(v___x_324_, v___x_425_, v___x_521_, v___x_333_, v___x_431_, v___x_523_);
v___x_525_ = l_Lean_Syntax_node2(v___x_324_, v___x_423_, v___x_424_, v___x_524_);
v___x_526_ = l_Lean_Syntax_node3(v___x_324_, v___x_325_, v___x_408_, v___x_387_, v___x_518_);
v___x_527_ = l_Lean_Syntax_node3(v___x_324_, v___x_419_, v___x_421_, v___x_526_, v___x_444_);
v___x_528_ = l_Lean_Syntax_node4(v___x_324_, v___x_425_, v___x_521_, v___x_333_, v___x_431_, v___x_527_);
v___x_529_ = l_Lean_Syntax_node2(v___x_324_, v___x_423_, v___x_424_, v___x_528_);
v___x_530_ = l_Lean_Syntax_node3(v___x_324_, v___x_325_, v___x_525_, v___x_387_, v___x_529_);
v___x_531_ = l_Lean_Syntax_node3(v___x_324_, v___x_419_, v___x_421_, v___x_530_, v___x_444_);
v___x_532_ = l_Lean_Syntax_node4(v___x_324_, v___x_416_, v___x_418_, v___x_531_, v___x_447_, v___x_333_);
v___x_533_ = l_Lean_Syntax_node4(v___x_324_, v___x_336_, v___x_337_, v___x_495_, v___x_515_, v___x_532_);
v___x_534_ = l_Lean_Syntax_node2(v___x_324_, v___x_330_, v___x_334_, v___x_533_);
v___x_535_ = lean_obj_once(&l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__131, &l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__131_once, _init_l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__131);
v___x_536_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__132));
v___x_537_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_537_, 0, v___x_324_);
lean_ctor_set(v___x_537_, 1, v___x_535_);
lean_ctor_set(v___x_537_, 2, v___x_536_);
lean_ctor_set(v___x_537_, 3, v___x_341_);
v___x_538_ = l_Lean_Syntax_node2(v___x_324_, v___x_338_, v___x_537_, v___x_333_);
v___x_539_ = l_Lean_Syntax_node1(v___x_324_, v___x_325_, v___x_538_);
v___x_540_ = l_Lean_Syntax_node1(v___x_324_, v___x_325_, v___x_507_);
v___x_541_ = l_Lean_Syntax_node2(v___x_324_, v___x_388_, v___x_475_, v___x_540_);
v___x_542_ = l_Lean_Syntax_node2(v___x_324_, v___x_367_, v___x_353_, v___x_541_);
v___x_543_ = l_Lean_Syntax_node2(v___x_324_, v___x_344_, v___x_472_, v___x_542_);
v___x_544_ = l_Lean_Syntax_node2(v___x_324_, v___x_325_, v___x_486_, v___x_494_);
v___x_545_ = l_Lean_Syntax_node2(v___x_324_, v___x_388_, v___x_482_, v___x_544_);
v___x_546_ = l_Lean_Syntax_node4(v___x_324_, v___x_416_, v___x_418_, v___x_545_, v___x_447_, v___x_333_);
v___x_547_ = l_Lean_Syntax_node6(v___x_324_, v___x_452_, v___x_454_, v___x_455_, v___x_333_, v___x_539_, v___x_543_, v___x_546_);
v___x_548_ = l_Lean_Syntax_node2(v___x_324_, v___x_330_, v___x_334_, v___x_547_);
v___x_549_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__133));
v___x_550_ = ((lean_object*)(l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___closed__134));
v___x_551_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_324_);
lean_ctor_set(v___x_551_, 1, v___x_549_);
v___x_552_ = l_Lean_Syntax_node2(v___x_324_, v___x_325_, v___x_320_, v___x_333_);
v___x_553_ = l_Lean_Syntax_node2(v___x_324_, v___x_550_, v___x_551_, v___x_552_);
v___x_554_ = l_Lean_Syntax_node6(v___x_324_, v___x_325_, v___x_329_, v___x_450_, v___x_491_, v___x_534_, v___x_548_, v___x_553_);
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v_a_313_);
return v___x_555_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1___boxed(lean_object* v_x_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___aux__Init__Data__SInt__Decidable______macroRules__commandDeclare__decidable__int__quantifiers______1(v_x_556_, v_a_557_, v_a_558_);
lean_dec_ref(v_a_557_);
return v_res_559_;
}
}
LEAN_EXPORT uint8_t l_Int8_instDecidableForall___redArg___lam__0(lean_object* v_inst_560_, lean_object* v_a_561_){
_start:
{
uint8_t v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_562_ = lean_uint8_of_nat_mk(v_a_561_);
v___x_563_ = lean_box(v___x_562_);
v___x_564_ = lean_apply_1(v_inst_560_, v___x_563_);
v___x_565_ = lean_unbox(v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Int8_instDecidableForall___redArg___lam__0___boxed(lean_object* v_inst_566_, lean_object* v_a_567_){
_start:
{
uint8_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = l_Int8_instDecidableForall___redArg___lam__0(v_inst_566_, v_a_567_);
v_r_569_ = lean_box(v_res_568_);
return v_r_569_;
}
}
LEAN_EXPORT uint8_t l_Int8_instDecidableForall___redArg(lean_object* v_inst_570_){
_start:
{
lean_object* v___f_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___f_571_ = lean_alloc_closure((void*)(l_Int8_instDecidableForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_571_, 0, v_inst_570_);
v___x_572_ = lean_unsigned_to_nat(8u);
v___x_573_ = l_BitVec_instDecidableForallBitVec___redArg(v___x_572_, v___f_571_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Int8_instDecidableForall___redArg___boxed(lean_object* v_inst_574_){
_start:
{
uint8_t v_res_575_; lean_object* v_r_576_; 
v_res_575_ = l_Int8_instDecidableForall___redArg(v_inst_574_);
v_r_576_ = lean_box(v_res_575_);
return v_r_576_;
}
}
LEAN_EXPORT uint8_t l_Int8_instDecidableForall(lean_object* v_P_577_, lean_object* v_inst_578_){
_start:
{
uint8_t v___x_579_; 
v___x_579_ = l_Int8_instDecidableForall___redArg(v_inst_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Int8_instDecidableForall___boxed(lean_object* v_P_580_, lean_object* v_inst_581_){
_start:
{
uint8_t v_res_582_; lean_object* v_r_583_; 
v_res_582_ = l_Int8_instDecidableForall(v_P_580_, v_inst_581_);
v_r_583_ = lean_box(v_res_582_);
return v_r_583_;
}
}
LEAN_EXPORT uint8_t l_Int8_instDecidableExists___redArg(lean_object* v_inst_584_){
_start:
{
lean_object* v___f_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___f_585_ = lean_alloc_closure((void*)(l_Int8_instDecidableForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_585_, 0, v_inst_584_);
v___x_586_ = lean_unsigned_to_nat(8u);
v___x_587_ = l_BitVec_instDecidableExistsBitVec___redArg(v___x_586_, v___f_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Int8_instDecidableExists___redArg___boxed(lean_object* v_inst_588_){
_start:
{
uint8_t v_res_589_; lean_object* v_r_590_; 
v_res_589_ = l_Int8_instDecidableExists___redArg(v_inst_588_);
v_r_590_ = lean_box(v_res_589_);
return v_r_590_;
}
}
LEAN_EXPORT uint8_t l_Int8_instDecidableExists(lean_object* v_P_591_, lean_object* v_inst_592_){
_start:
{
uint8_t v___x_593_; 
v___x_593_ = l_Int8_instDecidableExists___redArg(v_inst_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Int8_instDecidableExists___boxed(lean_object* v_P_594_, lean_object* v_inst_595_){
_start:
{
uint8_t v_res_596_; lean_object* v_r_597_; 
v_res_596_ = l_Int8_instDecidableExists(v_P_594_, v_inst_595_);
v_r_597_ = lean_box(v_res_596_);
return v_r_597_;
}
}
LEAN_EXPORT uint8_t l_Int16_instDecidableForall___redArg___lam__0(lean_object* v_inst_598_, lean_object* v_a_599_){
_start:
{
uint16_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_600_ = lean_uint16_of_nat_mk(v_a_599_);
v___x_601_ = lean_box(v___x_600_);
v___x_602_ = lean_apply_1(v_inst_598_, v___x_601_);
v___x_603_ = lean_unbox(v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Int16_instDecidableForall___redArg___lam__0___boxed(lean_object* v_inst_604_, lean_object* v_a_605_){
_start:
{
uint8_t v_res_606_; lean_object* v_r_607_; 
v_res_606_ = l_Int16_instDecidableForall___redArg___lam__0(v_inst_604_, v_a_605_);
v_r_607_ = lean_box(v_res_606_);
return v_r_607_;
}
}
LEAN_EXPORT uint8_t l_Int16_instDecidableForall___redArg(lean_object* v_inst_608_){
_start:
{
lean_object* v___f_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v___f_609_ = lean_alloc_closure((void*)(l_Int16_instDecidableForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_609_, 0, v_inst_608_);
v___x_610_ = lean_unsigned_to_nat(16u);
v___x_611_ = l_BitVec_instDecidableForallBitVec___redArg(v___x_610_, v___f_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Int16_instDecidableForall___redArg___boxed(lean_object* v_inst_612_){
_start:
{
uint8_t v_res_613_; lean_object* v_r_614_; 
v_res_613_ = l_Int16_instDecidableForall___redArg(v_inst_612_);
v_r_614_ = lean_box(v_res_613_);
return v_r_614_;
}
}
LEAN_EXPORT uint8_t l_Int16_instDecidableForall(lean_object* v_P_615_, lean_object* v_inst_616_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = l_Int16_instDecidableForall___redArg(v_inst_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Int16_instDecidableForall___boxed(lean_object* v_P_618_, lean_object* v_inst_619_){
_start:
{
uint8_t v_res_620_; lean_object* v_r_621_; 
v_res_620_ = l_Int16_instDecidableForall(v_P_618_, v_inst_619_);
v_r_621_ = lean_box(v_res_620_);
return v_r_621_;
}
}
LEAN_EXPORT uint8_t l_Int16_instDecidableExists___redArg(lean_object* v_inst_622_){
_start:
{
lean_object* v___f_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___f_623_ = lean_alloc_closure((void*)(l_Int16_instDecidableForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_623_, 0, v_inst_622_);
v___x_624_ = lean_unsigned_to_nat(16u);
v___x_625_ = l_BitVec_instDecidableExistsBitVec___redArg(v___x_624_, v___f_623_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Int16_instDecidableExists___redArg___boxed(lean_object* v_inst_626_){
_start:
{
uint8_t v_res_627_; lean_object* v_r_628_; 
v_res_627_ = l_Int16_instDecidableExists___redArg(v_inst_626_);
v_r_628_ = lean_box(v_res_627_);
return v_r_628_;
}
}
LEAN_EXPORT uint8_t l_Int16_instDecidableExists(lean_object* v_P_629_, lean_object* v_inst_630_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = l_Int16_instDecidableExists___redArg(v_inst_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Int16_instDecidableExists___boxed(lean_object* v_P_632_, lean_object* v_inst_633_){
_start:
{
uint8_t v_res_634_; lean_object* v_r_635_; 
v_res_634_ = l_Int16_instDecidableExists(v_P_632_, v_inst_633_);
v_r_635_ = lean_box(v_res_634_);
return v_r_635_;
}
}
LEAN_EXPORT uint8_t l_Int32_instDecidableForall___redArg___lam__0(lean_object* v_inst_636_, lean_object* v_a_637_){
_start:
{
uint32_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_638_ = lean_uint32_of_nat_mk(v_a_637_);
v___x_639_ = lean_box_uint32(v___x_638_);
v___x_640_ = lean_apply_1(v_inst_636_, v___x_639_);
v___x_641_ = lean_unbox(v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Int32_instDecidableForall___redArg___lam__0___boxed(lean_object* v_inst_642_, lean_object* v_a_643_){
_start:
{
uint8_t v_res_644_; lean_object* v_r_645_; 
v_res_644_ = l_Int32_instDecidableForall___redArg___lam__0(v_inst_642_, v_a_643_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT uint8_t l_Int32_instDecidableForall___redArg(lean_object* v_inst_646_){
_start:
{
lean_object* v___f_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___f_647_ = lean_alloc_closure((void*)(l_Int32_instDecidableForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_647_, 0, v_inst_646_);
v___x_648_ = lean_unsigned_to_nat(32u);
v___x_649_ = l_BitVec_instDecidableForallBitVec___redArg(v___x_648_, v___f_647_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Int32_instDecidableForall___redArg___boxed(lean_object* v_inst_650_){
_start:
{
uint8_t v_res_651_; lean_object* v_r_652_; 
v_res_651_ = l_Int32_instDecidableForall___redArg(v_inst_650_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
LEAN_EXPORT uint8_t l_Int32_instDecidableForall(lean_object* v_P_653_, lean_object* v_inst_654_){
_start:
{
uint8_t v___x_655_; 
v___x_655_ = l_Int32_instDecidableForall___redArg(v_inst_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Int32_instDecidableForall___boxed(lean_object* v_P_656_, lean_object* v_inst_657_){
_start:
{
uint8_t v_res_658_; lean_object* v_r_659_; 
v_res_658_ = l_Int32_instDecidableForall(v_P_656_, v_inst_657_);
v_r_659_ = lean_box(v_res_658_);
return v_r_659_;
}
}
LEAN_EXPORT uint8_t l_Int32_instDecidableExists___redArg(lean_object* v_inst_660_){
_start:
{
lean_object* v___f_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___f_661_ = lean_alloc_closure((void*)(l_Int32_instDecidableForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_661_, 0, v_inst_660_);
v___x_662_ = lean_unsigned_to_nat(32u);
v___x_663_ = l_BitVec_instDecidableExistsBitVec___redArg(v___x_662_, v___f_661_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Int32_instDecidableExists___redArg___boxed(lean_object* v_inst_664_){
_start:
{
uint8_t v_res_665_; lean_object* v_r_666_; 
v_res_665_ = l_Int32_instDecidableExists___redArg(v_inst_664_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT uint8_t l_Int32_instDecidableExists(lean_object* v_P_667_, lean_object* v_inst_668_){
_start:
{
uint8_t v___x_669_; 
v___x_669_ = l_Int32_instDecidableExists___redArg(v_inst_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Int32_instDecidableExists___boxed(lean_object* v_P_670_, lean_object* v_inst_671_){
_start:
{
uint8_t v_res_672_; lean_object* v_r_673_; 
v_res_672_ = l_Int32_instDecidableExists(v_P_670_, v_inst_671_);
v_r_673_ = lean_box(v_res_672_);
return v_r_673_;
}
}
LEAN_EXPORT uint8_t l_Int64_instDecidableForall___redArg___lam__0(lean_object* v_inst_674_, lean_object* v_a_675_){
_start:
{
uint64_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_676_ = lean_uint64_of_nat_mk(v_a_675_);
v___x_677_ = lean_box_uint64(v___x_676_);
v___x_678_ = lean_apply_1(v_inst_674_, v___x_677_);
v___x_679_ = lean_unbox(v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Int64_instDecidableForall___redArg___lam__0___boxed(lean_object* v_inst_680_, lean_object* v_a_681_){
_start:
{
uint8_t v_res_682_; lean_object* v_r_683_; 
v_res_682_ = l_Int64_instDecidableForall___redArg___lam__0(v_inst_680_, v_a_681_);
v_r_683_ = lean_box(v_res_682_);
return v_r_683_;
}
}
LEAN_EXPORT uint8_t l_Int64_instDecidableForall___redArg(lean_object* v_inst_684_){
_start:
{
lean_object* v___f_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___f_685_ = lean_alloc_closure((void*)(l_Int64_instDecidableForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_685_, 0, v_inst_684_);
v___x_686_ = lean_unsigned_to_nat(64u);
v___x_687_ = l_BitVec_instDecidableForallBitVec___redArg(v___x_686_, v___f_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Int64_instDecidableForall___redArg___boxed(lean_object* v_inst_688_){
_start:
{
uint8_t v_res_689_; lean_object* v_r_690_; 
v_res_689_ = l_Int64_instDecidableForall___redArg(v_inst_688_);
v_r_690_ = lean_box(v_res_689_);
return v_r_690_;
}
}
LEAN_EXPORT uint8_t l_Int64_instDecidableForall(lean_object* v_P_691_, lean_object* v_inst_692_){
_start:
{
uint8_t v___x_693_; 
v___x_693_ = l_Int64_instDecidableForall___redArg(v_inst_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Int64_instDecidableForall___boxed(lean_object* v_P_694_, lean_object* v_inst_695_){
_start:
{
uint8_t v_res_696_; lean_object* v_r_697_; 
v_res_696_ = l_Int64_instDecidableForall(v_P_694_, v_inst_695_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
LEAN_EXPORT uint8_t l_Int64_instDecidableExists___redArg(lean_object* v_inst_698_){
_start:
{
lean_object* v___f_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v___f_699_ = lean_alloc_closure((void*)(l_Int64_instDecidableForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_699_, 0, v_inst_698_);
v___x_700_ = lean_unsigned_to_nat(64u);
v___x_701_ = l_BitVec_instDecidableExistsBitVec___redArg(v___x_700_, v___f_699_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Int64_instDecidableExists___redArg___boxed(lean_object* v_inst_702_){
_start:
{
uint8_t v_res_703_; lean_object* v_r_704_; 
v_res_703_ = l_Int64_instDecidableExists___redArg(v_inst_702_);
v_r_704_ = lean_box(v_res_703_);
return v_r_704_;
}
}
LEAN_EXPORT uint8_t l_Int64_instDecidableExists(lean_object* v_P_705_, lean_object* v_inst_706_){
_start:
{
uint8_t v___x_707_; 
v___x_707_ = l_Int64_instDecidableExists___redArg(v_inst_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Int64_instDecidableExists___boxed(lean_object* v_P_708_, lean_object* v_inst_709_){
_start:
{
uint8_t v_res_710_; lean_object* v_r_711_; 
v_res_710_ = l_Int64_instDecidableExists(v_P_708_, v_inst_709_);
v_r_711_ = lean_box(v_res_710_);
return v_r_711_;
}
}
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Decidable(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_SInt_Decidable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Decidable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_SInt_Decidable(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Decidable(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_SInt_Decidable(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Decidable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Decidable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_SInt_Decidable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_SInt_Decidable(builtin);
}
#ifdef __cplusplus
}
#endif
