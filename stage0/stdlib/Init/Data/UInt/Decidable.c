// Lean compiler output
// Module: Init.Data.UInt.Decidable
// Imports: public import Init.Data.UInt.Basic public import Init.PropLemmas public import Init.Data.BitVec.Decidable
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
uint32_t lean_uint32_of_nat_mk(lean_object*);
uint8_t l_BitVec_instDecidableForallBitVec___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint16_t lean_uint16_of_nat_mk(lean_object*);
uint64_t lean_uint64_of_nat_mk(lean_object*);
uint8_t l_BitVec_instDecidableExistsBitVec___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_uint8_of_nat_mk(lean_object*);
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
static const lean_string_object l_commandDeclare__decidable__uint__quantifiers_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "commandDeclare_decidable_uint_quantifiers__"};
static const lean_object* l_commandDeclare__decidable__uint__quantifiers_____00__closed__0 = (const lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__0_value;
static const lean_ctor_object l_commandDeclare__decidable__uint__quantifiers_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 229, 178, 126, 144, 245, 217, 138)}};
static const lean_object* l_commandDeclare__decidable__uint__quantifiers_____00__closed__1 = (const lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__1_value;
static const lean_string_object l_commandDeclare__decidable__uint__quantifiers_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_commandDeclare__decidable__uint__quantifiers_____00__closed__2 = (const lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__2_value;
static const lean_ctor_object l_commandDeclare__decidable__uint__quantifiers_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_commandDeclare__decidable__uint__quantifiers_____00__closed__3 = (const lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__3_value;
static const lean_string_object l_commandDeclare__decidable__uint__quantifiers_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "declare_decidable_uint_quantifiers"};
static const lean_object* l_commandDeclare__decidable__uint__quantifiers_____00__closed__4 = (const lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__4_value;
static const lean_ctor_object l_commandDeclare__decidable__uint__quantifiers_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__4_value)}};
static const lean_object* l_commandDeclare__decidable__uint__quantifiers_____00__closed__5 = (const lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__5_value;
static const lean_string_object l_commandDeclare__decidable__uint__quantifiers_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_commandDeclare__decidable__uint__quantifiers_____00__closed__6 = (const lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__6_value;
static const lean_ctor_object l_commandDeclare__decidable__uint__quantifiers_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_commandDeclare__decidable__uint__quantifiers_____00__closed__7 = (const lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__7_value;
static const lean_ctor_object l_commandDeclare__decidable__uint__quantifiers_____00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__7_value)}};
static const lean_object* l_commandDeclare__decidable__uint__quantifiers_____00__closed__8 = (const lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__8_value;
static const lean_ctor_object l_commandDeclare__decidable__uint__quantifiers_____00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__3_value),((lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__5_value),((lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__8_value)}};
static const lean_object* l_commandDeclare__decidable__uint__quantifiers_____00__closed__9 = (const lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__9_value;
static const lean_string_object l_commandDeclare__decidable__uint__quantifiers_____00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_commandDeclare__decidable__uint__quantifiers_____00__closed__10 = (const lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__10_value;
static const lean_ctor_object l_commandDeclare__decidable__uint__quantifiers_____00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_commandDeclare__decidable__uint__quantifiers_____00__closed__11 = (const lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__11_value;
static const lean_ctor_object l_commandDeclare__decidable__uint__quantifiers_____00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__11_value),((lean_object*)(((size_t)(1023) << 1) | 1))}};
static const lean_object* l_commandDeclare__decidable__uint__quantifiers_____00__closed__12 = (const lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__12_value;
static const lean_ctor_object l_commandDeclare__decidable__uint__quantifiers_____00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__3_value),((lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__9_value),((lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__12_value)}};
static const lean_object* l_commandDeclare__decidable__uint__quantifiers_____00__closed__13 = (const lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__13_value;
static const lean_ctor_object l_commandDeclare__decidable__uint__quantifiers_____00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__13_value)}};
static const lean_object* l_commandDeclare__decidable__uint__quantifiers_____00__closed__14 = (const lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__14_value;
LEAN_EXPORT const lean_object* l_commandDeclare__decidable__uint__quantifiers____ = (const lean_object*)&l_commandDeclare__decidable__uint__quantifiers_____00__closed__14_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__0 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__0_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__1 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__1_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__4 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__4_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namespace"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__5 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__5_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__6_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__6_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__6_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(84, 17, 124, 142, 243, 161, 231, 243)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__6 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__6_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__7 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__7_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__8_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__8_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__8_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__8 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__8_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__9 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__9_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__10_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__10_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__10_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__10 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__10_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__11;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "theorem"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__12 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__12_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__13_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__13_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__13_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(238, 116, 137, 74, 194, 103, 58, 54)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__13 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__13_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__14 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__14_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__15_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__15_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__15_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__15 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__15_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "forall_iff_forall_ofBitVec"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__16 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__16_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__17;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(80, 238, 149, 31, 196, 23, 38, 18)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__18 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__18_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__19 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__19_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__20_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__20_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__20_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__20 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__20_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implicitBinder"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__22 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__22_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__23_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__23_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__23_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(39, 181, 62, 102, 86, 14, 161, 96)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__23 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__23_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__24 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__24_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "P"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__25 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__25_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__26;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(160, 230, 119, 31, 245, 11, 149, 236)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__27 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__27_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__28 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__28_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arrow"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__29 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__29_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__30_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__30_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__30_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(182, 146, 143, 73, 122, 115, 5, 207)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__30 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__30_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "→"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__31 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__31_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prop"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__32 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__32_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__33_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__33_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__33_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(200, 217, 246, 140, 179, 171, 30, 243)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__33 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__33_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prop"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__34 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__34_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__35 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__35_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__36 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__36_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__37_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__37_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__37_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__37 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__37_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_↔_"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__38 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__38_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__38_value),LEAN_SCALAR_PTR_LITERAL(220, 124, 41, 198, 228, 162, 237, 244)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__39 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__39_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__40 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__40_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__41_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__41_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__41_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__41 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__41_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__42 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__42_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__43_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__43_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__43_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__43 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__43_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__44 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__44_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__45 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__45_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__46 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__46_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__47 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__47_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__48;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "forall"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__49 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__49_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__50_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__50_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__50_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__49_value),LEAN_SCALAR_PTR_LITERAL(195, 142, 115, 15, 55, 103, 31, 115)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__50 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__50_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∀"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__51 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__51_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__52 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__52_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__53;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__52_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__54 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__54_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__55 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__55_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__56 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__56_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__57_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__57_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__57_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__57 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__57_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__58 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__58_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "↔"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__59 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__59_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__60 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__60_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__61_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__61_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__61_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__60_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__61 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__61_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__62 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__62_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__63;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__62_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__64 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__64_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ofBitVec"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__65 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__65_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__66;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__65_value),LEAN_SCALAR_PTR_LITERAL(109, 13, 70, 115, 31, 141, 156, 173)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__67 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__67_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__68 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__68_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__69_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__69_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__69_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__68_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__69 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__69_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__70 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__70_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__71 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__71_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__72_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__72_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__72_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__71_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__72 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__72_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__73 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__73_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__74 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__74_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__75_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__75_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__75_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__75_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__75_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__74_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__75 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__75_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__76 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__76_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__77_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__77_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__77_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__77_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__77_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__77_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__76_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__77 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__77_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__78 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__78_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__79_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__79;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__78_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__80 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__80_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__81 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__81_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "x.toBitVec"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__82 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__82_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__83;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toBitVec"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__84 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__84_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__85_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__52_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__85_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__84_value),LEAN_SCALAR_PTR_LITERAL(154, 27, 47, 236, 186, 178, 171, 172)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__85 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__85_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__86 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__86_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__87 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__87_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__88 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__88_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__89_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__89_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__89_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__89_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__89_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__87_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__89_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__88_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__89 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__89_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__90 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__90_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__91_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__91_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__91_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__91_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__91_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__91_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__90_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__91 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__91_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "/--"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__92 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__92_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "commentBody"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__93 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__93_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__94_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__94_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__94_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__94_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__94_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__94_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__93_value),LEAN_SCALAR_PTR_LITERAL(181, 50, 60, 220, 73, 28, 0, 197)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__94 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__94_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 239, .m_capacity = 239, .m_length = 236, .m_data = "Decides `∀ x, P x` by enumerating all values. This is not a global instance, since the enumeration\nis infeasible for the wider types, but may be activated locally, for example with\n`attribute [local instance] UInt8.instDecidableForall`."};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__95 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__95_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-/"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__96 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__96_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__97 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__97_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__98_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__98_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__98_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__98_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__98_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__97_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__98 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__98_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__99 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__99_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__100 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__100_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__101_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__101_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__101_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__101_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__101_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__101_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__100_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__101 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__101_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__102 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__102_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__103_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__103_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__103_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__103_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__103_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__103_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__102_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__103 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__103_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__104 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__104_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__105 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__105_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__106_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__106_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__106_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__106_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__106_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__104_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__106_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__105_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__106 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__106_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "instance_reducible"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__107 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__107_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__108_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__108;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__107_value),LEAN_SCALAR_PTR_LITERAL(125, 180, 213, 185, 56, 77, 23, 14)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__109 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__109_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__110 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__110_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__111 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__111_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__112_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__112_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__112_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__112_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__112_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__112_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__111_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__112 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__112_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__113 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__113_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instDecidableForall"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__114 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__114_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__115_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__115;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__114_value),LEAN_SCALAR_PTR_LITERAL(111, 114, 57, 32, 119, 142, 151, 176)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__116 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__116_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__117 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__117_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__118_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__118_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__118_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__118_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__118_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__118_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__118 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__118_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instBinder"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__119 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__119_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__120_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__120_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__120_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__120_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__120_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__120_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__119_value),LEAN_SCALAR_PTR_LITERAL(198, 219, 89, 171, 221, 95, 22, 227)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__120 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__120_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__121 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__121_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "DecidablePred"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__122 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__122_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__123_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__123;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__122_value),LEAN_SCALAR_PTR_LITERAL(16, 236, 239, 206, 255, 167, 201, 157)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__124 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__124_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__125 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__125_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__126_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__126;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__125_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__127 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__127_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "decidable_of_iff'"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__128 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__128_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__129_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__129;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__128_value),LEAN_SCALAR_PTR_LITERAL(107, 5, 65, 49, 195, 60, 169, 181)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__130 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__130_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__131 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__131_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__132_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__132_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__132_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__132_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__132_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__132_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__131_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__132 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__132_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__133 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__133_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "exists_iff_exists_ofBitVec"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__134 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__134_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__135_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__135;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__134_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 57, 207, 237, 42, 141, 238)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__136 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__136_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 8, .m_data = "term∃_,_"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__137 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__137_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__137_value),LEAN_SCALAR_PTR_LITERAL(224, 105, 219, 112, 166, 139, 167, 161)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__138 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__138_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∃"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__139 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__139_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "explicitBinders"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__140 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__140_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__141_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__141_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__140_value),LEAN_SCALAR_PTR_LITERAL(167, 149, 127, 13, 202, 239, 226, 94)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__141 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__141_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unbracketedExplicitBinders"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__142 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__142_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__143_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__143_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__142_value),LEAN_SCALAR_PTR_LITERAL(187, 220, 119, 82, 242, 112, 119, 200)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__143 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__143_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__144 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__144_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__145_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__145_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__144_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__145 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__145_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "bracketedExplicitBinders"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__146 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__146_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__147_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__147_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__146_value),LEAN_SCALAR_PTR_LITERAL(22, 65, 7, 186, 44, 89, 152, 79)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__147 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__147_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "hx"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__148 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__148_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__149_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__149;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__148_value),LEAN_SCALAR_PTR_LITERAL(214, 92, 204, 191, 107, 147, 103, 110)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__150 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__150_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 239, .m_capacity = 239, .m_length = 236, .m_data = "Decides `∃ x, P x` by enumerating all values. This is not a global instance, since the enumeration\nis infeasible for the wider types, but may be activated locally, for example with\n`attribute [local instance] UInt8.instDecidableExists`."};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__151 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__151_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instDecidableExists"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__152 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__152_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__153_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__153;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__152_value),LEAN_SCALAR_PTR_LITERAL(214, 97, 88, 214, 200, 207, 123, 169)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__154 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__154_value;
static const lean_string_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__155 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__155_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__156_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__156_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__156_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__156_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__156_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__156_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__155_value),LEAN_SCALAR_PTR_LITERAL(254, 132, 206, 38, 133, 164, 145, 139)}};
static const lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__156 = (const lean_object*)&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__156_value;
LEAN_EXPORT lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt8_instDecidableForall___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_instDecidableForall___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt8_instDecidableForall___redArg(lean_object*);
LEAN_EXPORT lean_object* l_UInt8_instDecidableForall___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt8_instDecidableForall(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_instDecidableForall___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt8_instDecidableExists___redArg(lean_object*);
LEAN_EXPORT lean_object* l_UInt8_instDecidableExists___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt8_instDecidableExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_instDecidableExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt16_instDecidableForall___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt16_instDecidableForall___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt16_instDecidableForall___redArg(lean_object*);
LEAN_EXPORT lean_object* l_UInt16_instDecidableForall___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt16_instDecidableForall(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt16_instDecidableForall___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt16_instDecidableExists___redArg(lean_object*);
LEAN_EXPORT lean_object* l_UInt16_instDecidableExists___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt16_instDecidableExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt16_instDecidableExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt32_instDecidableForall___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt32_instDecidableForall___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt32_instDecidableForall___redArg(lean_object*);
LEAN_EXPORT lean_object* l_UInt32_instDecidableForall___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt32_instDecidableForall(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt32_instDecidableForall___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt32_instDecidableExists___redArg(lean_object*);
LEAN_EXPORT lean_object* l_UInt32_instDecidableExists___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt32_instDecidableExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt32_instDecidableExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt64_instDecidableForall___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_instDecidableForall___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt64_instDecidableForall___redArg(lean_object*);
LEAN_EXPORT lean_object* l_UInt64_instDecidableForall___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt64_instDecidableForall(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_instDecidableForall___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt64_instDecidableExists___redArg(lean_object*);
LEAN_EXPORT lean_object* l_UInt64_instDecidableExists___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt64_instDecidableExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_instDecidableExists___boxed(lean_object*, lean_object*);
static lean_object* _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__11(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Array_mkArray0___redArg();
return v___x_58_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__17(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__16));
v___x_73_ = l_String_toRawSubstring_x27(v___x_72_);
return v___x_73_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__26(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__25));
v___x_92_ = l_String_toRawSubstring_x27(v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__48(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__47));
v___x_138_ = l_String_toRawSubstring_x27(v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__53(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__52));
v___x_148_ = l_String_toRawSubstring_x27(v___x_147_);
return v___x_148_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__63(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__62));
v___x_168_ = l_String_toRawSubstring_x27(v___x_167_);
return v___x_168_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__66(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__65));
v___x_173_ = l_String_toRawSubstring_x27(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__79(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__78));
v___x_204_ = l_String_toRawSubstring_x27(v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__83(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__82));
v___x_210_ = l_String_toRawSubstring_x27(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__108(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__107));
v___x_266_ = l_String_toRawSubstring_x27(v___x_265_);
return v___x_266_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__115(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__114));
v___x_279_ = l_String_toRawSubstring_x27(v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__123(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__122));
v___x_297_ = l_String_toRawSubstring_x27(v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__126(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__125));
v___x_302_ = l_String_toRawSubstring_x27(v___x_301_);
return v___x_302_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__129(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__128));
v___x_307_ = l_String_toRawSubstring_x27(v___x_306_);
return v___x_307_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__135(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__134));
v___x_319_ = l_String_toRawSubstring_x27(v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__149(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__148));
v___x_344_ = l_String_toRawSubstring_x27(v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__153(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__152));
v___x_350_ = l_String_toRawSubstring_x27(v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1(lean_object* v_x_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = ((lean_object*)(l_commandDeclare__decidable__uint__quantifiers_____00__closed__1));
lean_inc(v_x_359_);
v___x_363_ = l_Lean_Syntax_isOfKind(v_x_359_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec(v_x_359_);
v___x_364_ = lean_box(1);
v___x_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v_a_361_);
return v___x_365_;
}
else
{
lean_object* v_ref_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_ref_366_ = lean_ctor_get(v_a_360_, 5);
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = l_Lean_Syntax_getArg(v_x_359_, v___x_367_);
v___x_369_ = lean_unsigned_to_nat(2u);
v___x_370_ = l_Lean_Syntax_getArg(v_x_359_, v___x_369_);
lean_dec(v_x_359_);
v___x_371_ = 0;
v___x_372_ = l_Lean_SourceInfo_fromRef(v_ref_366_, v___x_371_);
v___x_373_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__1));
v___x_374_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__5));
v___x_375_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__6));
lean_inc_n(v___x_372_, 160);
v___x_376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_372_);
lean_ctor_set(v___x_376_, 1, v___x_374_);
lean_inc_n(v___x_368_, 2);
v___x_377_ = l_Lean_Syntax_node2(v___x_372_, v___x_375_, v___x_376_, v___x_368_);
v___x_378_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__8));
v___x_379_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__10));
v___x_380_ = lean_obj_once(&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__11, &l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__11_once, _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__11);
v___x_381_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_381_, 0, v___x_372_);
lean_ctor_set(v___x_381_, 1, v___x_373_);
lean_ctor_set(v___x_381_, 2, v___x_380_);
lean_inc_ref_n(v___x_381_, 41);
v___x_382_ = l_Lean_Syntax_node7(v___x_372_, v___x_379_, v___x_381_, v___x_381_, v___x_381_, v___x_381_, v___x_381_, v___x_381_, v___x_381_);
v___x_383_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__12));
v___x_384_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__13));
v___x_385_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_372_);
lean_ctor_set(v___x_385_, 1, v___x_383_);
v___x_386_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__15));
v___x_387_ = lean_obj_once(&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__17, &l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__17_once, _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__17);
v___x_388_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__18));
v___x_389_ = lean_box(0);
v___x_390_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_390_, 0, v___x_372_);
lean_ctor_set(v___x_390_, 1, v___x_387_);
lean_ctor_set(v___x_390_, 2, v___x_388_);
lean_ctor_set(v___x_390_, 3, v___x_389_);
lean_inc_ref(v___x_390_);
v___x_391_ = l_Lean_Syntax_node2(v___x_372_, v___x_386_, v___x_390_, v___x_381_);
v___x_392_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__20));
v___x_393_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__23));
v___x_394_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__24));
v___x_395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_372_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = lean_obj_once(&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__26, &l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__26_once, _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__26);
v___x_397_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__27));
v___x_398_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_398_, 0, v___x_372_);
lean_ctor_set(v___x_398_, 1, v___x_396_);
lean_ctor_set(v___x_398_, 2, v___x_397_);
lean_ctor_set(v___x_398_, 3, v___x_389_);
lean_inc_ref_n(v___x_398_, 2);
v___x_399_ = l_Lean_Syntax_node1(v___x_372_, v___x_373_, v___x_398_);
v___x_400_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__28));
v___x_401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_372_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__30));
v___x_403_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__31));
v___x_404_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_372_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__33));
v___x_406_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__34));
v___x_407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_372_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = l_Lean_Syntax_node1(v___x_372_, v___x_405_, v___x_407_);
v___x_409_ = l_Lean_Syntax_node3(v___x_372_, v___x_402_, v___x_368_, v___x_404_, v___x_408_);
lean_inc_ref_n(v___x_401_, 6);
v___x_410_ = l_Lean_Syntax_node2(v___x_372_, v___x_373_, v___x_401_, v___x_409_);
v___x_411_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__35));
v___x_412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_372_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
lean_inc(v___x_410_);
lean_inc_n(v___x_399_, 2);
v___x_413_ = l_Lean_Syntax_node4(v___x_372_, v___x_393_, v___x_395_, v___x_399_, v___x_410_, v___x_412_);
v___x_414_ = l_Lean_Syntax_node1(v___x_372_, v___x_373_, v___x_413_);
v___x_415_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__37));
v___x_416_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__39));
v___x_417_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__41));
v___x_418_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__43));
v___x_419_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__44));
v___x_420_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_372_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__46));
v___x_422_ = lean_obj_once(&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__48, &l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__48_once, _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__48);
v___x_423_ = lean_box(0);
v___x_424_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_424_, 0, v___x_372_);
lean_ctor_set(v___x_424_, 1, v___x_422_);
lean_ctor_set(v___x_424_, 2, v___x_423_);
lean_ctor_set(v___x_424_, 3, v___x_389_);
v___x_425_ = l_Lean_Syntax_node1(v___x_372_, v___x_421_, v___x_424_);
lean_inc_ref_n(v___x_420_, 3);
v___x_426_ = l_Lean_Syntax_node2(v___x_372_, v___x_418_, v___x_420_, v___x_425_);
v___x_427_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__50));
v___x_428_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__51));
v___x_429_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_372_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v___x_430_ = lean_obj_once(&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__53, &l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__53_once, _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__53);
v___x_431_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__54));
v___x_432_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_432_, 0, v___x_372_);
lean_ctor_set(v___x_432_, 1, v___x_430_);
lean_ctor_set(v___x_432_, 2, v___x_431_);
lean_ctor_set(v___x_432_, 3, v___x_389_);
lean_inc_ref_n(v___x_432_, 3);
v___x_433_ = l_Lean_Syntax_node1(v___x_372_, v___x_373_, v___x_432_);
v___x_434_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__55));
v___x_435_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_372_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
v___x_436_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__57));
lean_inc_n(v___x_433_, 3);
v___x_437_ = l_Lean_Syntax_node2(v___x_372_, v___x_436_, v___x_398_, v___x_433_);
lean_inc(v___x_437_);
lean_inc_ref_n(v___x_435_, 8);
lean_inc_ref(v___x_429_);
v___x_438_ = l_Lean_Syntax_node5(v___x_372_, v___x_427_, v___x_429_, v___x_433_, v___x_381_, v___x_435_, v___x_437_);
v___x_439_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__58));
v___x_440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_372_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
lean_inc_ref_n(v___x_440_, 5);
lean_inc_n(v___x_426_, 2);
v___x_441_ = l_Lean_Syntax_node3(v___x_372_, v___x_417_, v___x_426_, v___x_438_, v___x_440_);
v___x_442_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__59));
v___x_443_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_372_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__61));
v___x_445_ = lean_obj_once(&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__63, &l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__63_once, _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__63);
v___x_446_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__64));
v___x_447_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_447_, 0, v___x_372_);
lean_ctor_set(v___x_447_, 1, v___x_445_);
lean_ctor_set(v___x_447_, 2, v___x_446_);
lean_ctor_set(v___x_447_, 3, v___x_389_);
v___x_448_ = l_Lean_Syntax_node1(v___x_372_, v___x_373_, v___x_370_);
v___x_449_ = l_Lean_Syntax_node2(v___x_372_, v___x_436_, v___x_447_, v___x_448_);
lean_inc(v___x_449_);
v___x_450_ = l_Lean_Syntax_node2(v___x_372_, v___x_373_, v___x_401_, v___x_449_);
v___x_451_ = l_Lean_Syntax_node5(v___x_372_, v___x_444_, v___x_420_, v___x_433_, v___x_450_, v___x_381_, v___x_440_);
v___x_452_ = l_Lean_Syntax_node1(v___x_372_, v___x_373_, v___x_451_);
v___x_453_ = lean_obj_once(&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__66, &l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__66_once, _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__66);
v___x_454_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__67));
v___x_455_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_455_, 0, v___x_372_);
lean_ctor_set(v___x_455_, 1, v___x_453_);
lean_ctor_set(v___x_455_, 2, v___x_454_);
lean_ctor_set(v___x_455_, 3, v___x_389_);
v___x_456_ = l_Lean_Syntax_node2(v___x_372_, v___x_436_, v___x_455_, v___x_433_);
lean_inc(v___x_456_);
v___x_457_ = l_Lean_Syntax_node3(v___x_372_, v___x_417_, v___x_426_, v___x_456_, v___x_440_);
v___x_458_ = l_Lean_Syntax_node1(v___x_372_, v___x_373_, v___x_457_);
lean_inc(v___x_458_);
v___x_459_ = l_Lean_Syntax_node2(v___x_372_, v___x_436_, v___x_398_, v___x_458_);
lean_inc(v___x_459_);
v___x_460_ = l_Lean_Syntax_node5(v___x_372_, v___x_427_, v___x_429_, v___x_452_, v___x_381_, v___x_435_, v___x_459_);
lean_inc_ref(v___x_443_);
lean_inc(v___x_441_);
v___x_461_ = l_Lean_Syntax_node3(v___x_372_, v___x_416_, v___x_441_, v___x_443_, v___x_460_);
v___x_462_ = l_Lean_Syntax_node2(v___x_372_, v___x_415_, v___x_401_, v___x_461_);
lean_inc(v___x_414_);
v___x_463_ = l_Lean_Syntax_node2(v___x_372_, v___x_392_, v___x_414_, v___x_462_);
v___x_464_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__69));
v___x_465_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__70));
v___x_466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_372_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v___x_467_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__72));
v___x_468_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__73));
v___x_469_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_372_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__74));
v___x_471_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__75));
v___x_472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_372_);
lean_ctor_set(v___x_472_, 1, v___x_470_);
v___x_473_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__77));
v___x_474_ = lean_obj_once(&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__79, &l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__79_once, _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__79);
v___x_475_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__80));
v___x_476_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_476_, 0, v___x_372_);
lean_ctor_set(v___x_476_, 1, v___x_474_);
lean_ctor_set(v___x_476_, 2, v___x_475_);
lean_ctor_set(v___x_476_, 3, v___x_389_);
lean_inc_ref_n(v___x_476_, 2);
v___x_477_ = l_Lean_Syntax_node2(v___x_372_, v___x_373_, v___x_476_, v___x_432_);
v___x_478_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__81));
v___x_479_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_372_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v___x_480_ = l_Lean_Syntax_node2(v___x_372_, v___x_436_, v___x_476_, v___x_458_);
lean_inc_ref_n(v___x_479_, 3);
lean_inc(v___x_477_);
v___x_481_ = l_Lean_Syntax_node4(v___x_372_, v___x_473_, v___x_477_, v___x_381_, v___x_479_, v___x_480_);
lean_inc_ref_n(v___x_472_, 3);
v___x_482_ = l_Lean_Syntax_node2(v___x_372_, v___x_471_, v___x_472_, v___x_481_);
v___x_483_ = lean_obj_once(&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__83, &l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__83_once, _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__83);
v___x_484_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__85));
v___x_485_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_485_, 0, v___x_372_);
lean_ctor_set(v___x_485_, 1, v___x_483_);
lean_ctor_set(v___x_485_, 2, v___x_484_);
lean_ctor_set(v___x_485_, 3, v___x_389_);
lean_inc_ref(v___x_485_);
v___x_486_ = l_Lean_Syntax_node1(v___x_372_, v___x_373_, v___x_485_);
v___x_487_ = l_Lean_Syntax_node2(v___x_372_, v___x_436_, v___x_476_, v___x_486_);
v___x_488_ = l_Lean_Syntax_node4(v___x_372_, v___x_473_, v___x_477_, v___x_381_, v___x_479_, v___x_487_);
v___x_489_ = l_Lean_Syntax_node2(v___x_372_, v___x_471_, v___x_472_, v___x_488_);
v___x_490_ = l_Lean_Syntax_node3(v___x_372_, v___x_373_, v___x_482_, v___x_435_, v___x_489_);
v___x_491_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__86));
v___x_492_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_372_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
lean_inc_ref_n(v___x_492_, 4);
lean_inc_ref_n(v___x_469_, 4);
v___x_493_ = l_Lean_Syntax_node3(v___x_372_, v___x_467_, v___x_469_, v___x_490_, v___x_492_);
v___x_494_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__89));
v___x_495_ = l_Lean_Syntax_node2(v___x_372_, v___x_494_, v___x_381_, v___x_381_);
lean_inc_n(v___x_495_, 3);
lean_inc_ref_n(v___x_466_, 3);
v___x_496_ = l_Lean_Syntax_node4(v___x_372_, v___x_464_, v___x_466_, v___x_493_, v___x_495_, v___x_381_);
lean_inc_ref(v___x_385_);
v___x_497_ = l_Lean_Syntax_node4(v___x_372_, v___x_384_, v___x_385_, v___x_391_, v___x_463_, v___x_496_);
lean_inc(v___x_382_);
v___x_498_ = l_Lean_Syntax_node2(v___x_372_, v___x_378_, v___x_382_, v___x_497_);
v___x_499_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__91));
v___x_500_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__92));
v___x_501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_372_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__94));
v___x_503_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__95));
v___x_504_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_372_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___x_505_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__96));
v___x_506_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_372_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
lean_inc_ref(v___x_506_);
v___x_507_ = l_Lean_Syntax_node2(v___x_372_, v___x_502_, v___x_504_, v___x_506_);
lean_inc_ref(v___x_501_);
v___x_508_ = l_Lean_Syntax_node2(v___x_372_, v___x_499_, v___x_501_, v___x_507_);
v___x_509_ = l_Lean_Syntax_node1(v___x_372_, v___x_373_, v___x_508_);
v___x_510_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__98));
v___x_511_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__99));
v___x_512_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_372_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__101));
v___x_514_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__103));
v___x_515_ = l_Lean_Syntax_node1(v___x_372_, v___x_514_, v___x_381_);
v___x_516_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__106));
v___x_517_ = lean_obj_once(&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__108, &l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__108_once, _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__108);
v___x_518_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__109));
v___x_519_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_519_, 0, v___x_372_);
lean_ctor_set(v___x_519_, 1, v___x_517_);
lean_ctor_set(v___x_519_, 2, v___x_518_);
lean_ctor_set(v___x_519_, 3, v___x_389_);
v___x_520_ = l_Lean_Syntax_node2(v___x_372_, v___x_516_, v___x_519_, v___x_381_);
v___x_521_ = l_Lean_Syntax_node2(v___x_372_, v___x_513_, v___x_515_, v___x_520_);
v___x_522_ = l_Lean_Syntax_node1(v___x_372_, v___x_373_, v___x_521_);
v___x_523_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__110));
v___x_524_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_372_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
lean_inc_ref(v___x_524_);
v___x_525_ = l_Lean_Syntax_node3(v___x_372_, v___x_510_, v___x_512_, v___x_522_, v___x_524_);
v___x_526_ = l_Lean_Syntax_node1(v___x_372_, v___x_373_, v___x_525_);
lean_inc(v___x_526_);
v___x_527_ = l_Lean_Syntax_node7(v___x_372_, v___x_379_, v___x_509_, v___x_526_, v___x_381_, v___x_381_, v___x_381_, v___x_381_, v___x_381_);
v___x_528_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__112));
v___x_529_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__113));
v___x_530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_372_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_obj_once(&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__115, &l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__115_once, _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__115);
v___x_532_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__116));
v___x_533_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_533_, 0, v___x_372_);
lean_ctor_set(v___x_533_, 1, v___x_531_);
lean_ctor_set(v___x_533_, 2, v___x_532_);
lean_ctor_set(v___x_533_, 3, v___x_389_);
v___x_534_ = l_Lean_Syntax_node2(v___x_372_, v___x_386_, v___x_533_, v___x_381_);
v___x_535_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__118));
v___x_536_ = l_Lean_Syntax_node5(v___x_372_, v___x_444_, v___x_420_, v___x_399_, v___x_410_, v___x_381_, v___x_440_);
v___x_537_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__120));
v___x_538_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__121));
v___x_539_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_372_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_obj_once(&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__123, &l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__123_once, _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__123);
v___x_541_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__124));
v___x_542_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_542_, 0, v___x_372_);
lean_ctor_set(v___x_542_, 1, v___x_540_);
lean_ctor_set(v___x_542_, 2, v___x_541_);
lean_ctor_set(v___x_542_, 3, v___x_389_);
v___x_543_ = l_Lean_Syntax_node2(v___x_372_, v___x_436_, v___x_542_, v___x_399_);
v___x_544_ = l_Lean_Syntax_node4(v___x_372_, v___x_537_, v___x_539_, v___x_381_, v___x_543_, v___x_524_);
v___x_545_ = l_Lean_Syntax_node2(v___x_372_, v___x_373_, v___x_536_, v___x_544_);
v___x_546_ = lean_obj_once(&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__126, &l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__126_once, _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__126);
v___x_547_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__127));
v___x_548_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_548_, 0, v___x_372_);
lean_ctor_set(v___x_548_, 1, v___x_546_);
lean_ctor_set(v___x_548_, 2, v___x_547_);
lean_ctor_set(v___x_548_, 3, v___x_389_);
v___x_549_ = l_Lean_Syntax_node1(v___x_372_, v___x_373_, v___x_441_);
lean_inc_ref(v___x_548_);
v___x_550_ = l_Lean_Syntax_node2(v___x_372_, v___x_436_, v___x_548_, v___x_549_);
v___x_551_ = l_Lean_Syntax_node2(v___x_372_, v___x_415_, v___x_401_, v___x_550_);
v___x_552_ = l_Lean_Syntax_node1(v___x_372_, v___x_373_, v___x_551_);
lean_inc(v___x_545_);
v___x_553_ = l_Lean_Syntax_node2(v___x_372_, v___x_535_, v___x_545_, v___x_552_);
v___x_554_ = lean_obj_once(&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__129, &l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__129_once, _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__129);
v___x_555_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__130));
v___x_556_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_556_, 0, v___x_372_);
lean_ctor_set(v___x_556_, 1, v___x_554_);
lean_ctor_set(v___x_556_, 2, v___x_555_);
lean_ctor_set(v___x_556_, 3, v___x_389_);
v___x_557_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__132));
v___x_558_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__133));
v___x_559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_372_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = l_Lean_Syntax_node1(v___x_372_, v___x_557_, v___x_559_);
lean_inc(v___x_560_);
v___x_561_ = l_Lean_Syntax_node2(v___x_372_, v___x_373_, v___x_560_, v___x_390_);
lean_inc_ref(v___x_556_);
v___x_562_ = l_Lean_Syntax_node2(v___x_372_, v___x_436_, v___x_556_, v___x_561_);
v___x_563_ = l_Lean_Syntax_node4(v___x_372_, v___x_464_, v___x_466_, v___x_562_, v___x_495_, v___x_381_);
lean_inc_ref(v___x_530_);
v___x_564_ = l_Lean_Syntax_node5(v___x_372_, v___x_528_, v___x_530_, v___x_534_, v___x_553_, v___x_563_, v___x_381_);
v___x_565_ = l_Lean_Syntax_node2(v___x_372_, v___x_378_, v___x_527_, v___x_564_);
v___x_566_ = lean_obj_once(&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__135, &l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__135_once, _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__135);
v___x_567_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__136));
v___x_568_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_568_, 0, v___x_372_);
lean_ctor_set(v___x_568_, 1, v___x_566_);
lean_ctor_set(v___x_568_, 2, v___x_567_);
lean_ctor_set(v___x_568_, 3, v___x_389_);
lean_inc_ref(v___x_568_);
v___x_569_ = l_Lean_Syntax_node2(v___x_372_, v___x_386_, v___x_568_, v___x_381_);
v___x_570_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__138));
v___x_571_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__139));
v___x_572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_372_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__141));
v___x_574_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__143));
v___x_575_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__145));
v___x_576_ = l_Lean_Syntax_node1(v___x_372_, v___x_575_, v___x_432_);
v___x_577_ = l_Lean_Syntax_node1(v___x_372_, v___x_373_, v___x_576_);
lean_inc(v___x_577_);
v___x_578_ = l_Lean_Syntax_node2(v___x_372_, v___x_574_, v___x_577_, v___x_381_);
v___x_579_ = l_Lean_Syntax_node1(v___x_372_, v___x_573_, v___x_578_);
lean_inc_ref(v___x_572_);
v___x_580_ = l_Lean_Syntax_node4(v___x_372_, v___x_570_, v___x_572_, v___x_579_, v___x_435_, v___x_437_);
v___x_581_ = l_Lean_Syntax_node3(v___x_372_, v___x_417_, v___x_426_, v___x_580_, v___x_440_);
v___x_582_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__147));
v___x_583_ = l_Lean_Syntax_node5(v___x_372_, v___x_582_, v___x_420_, v___x_577_, v___x_401_, v___x_449_, v___x_440_);
v___x_584_ = l_Lean_Syntax_node1(v___x_372_, v___x_373_, v___x_583_);
v___x_585_ = l_Lean_Syntax_node1(v___x_372_, v___x_573_, v___x_584_);
v___x_586_ = l_Lean_Syntax_node4(v___x_372_, v___x_570_, v___x_572_, v___x_585_, v___x_435_, v___x_459_);
lean_inc(v___x_581_);
v___x_587_ = l_Lean_Syntax_node3(v___x_372_, v___x_416_, v___x_581_, v___x_443_, v___x_586_);
v___x_588_ = l_Lean_Syntax_node2(v___x_372_, v___x_415_, v___x_401_, v___x_587_);
v___x_589_ = l_Lean_Syntax_node2(v___x_372_, v___x_392_, v___x_414_, v___x_588_);
v___x_590_ = lean_obj_once(&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__149, &l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__149_once, _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__149);
v___x_591_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__150));
v___x_592_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_592_, 0, v___x_372_);
lean_ctor_set(v___x_592_, 1, v___x_590_);
lean_ctor_set(v___x_592_, 2, v___x_591_);
lean_ctor_set(v___x_592_, 3, v___x_389_);
lean_inc_ref_n(v___x_592_, 2);
v___x_593_ = l_Lean_Syntax_node3(v___x_372_, v___x_373_, v___x_432_, v___x_435_, v___x_592_);
v___x_594_ = l_Lean_Syntax_node3(v___x_372_, v___x_467_, v___x_469_, v___x_593_, v___x_492_);
v___x_595_ = l_Lean_Syntax_node1(v___x_372_, v___x_373_, v___x_594_);
v___x_596_ = l_Lean_Syntax_node3(v___x_372_, v___x_373_, v___x_485_, v___x_435_, v___x_592_);
v___x_597_ = l_Lean_Syntax_node3(v___x_372_, v___x_467_, v___x_469_, v___x_596_, v___x_492_);
lean_inc(v___x_595_);
v___x_598_ = l_Lean_Syntax_node4(v___x_372_, v___x_473_, v___x_595_, v___x_381_, v___x_479_, v___x_597_);
v___x_599_ = l_Lean_Syntax_node2(v___x_372_, v___x_471_, v___x_472_, v___x_598_);
v___x_600_ = l_Lean_Syntax_node3(v___x_372_, v___x_373_, v___x_456_, v___x_435_, v___x_592_);
v___x_601_ = l_Lean_Syntax_node3(v___x_372_, v___x_467_, v___x_469_, v___x_600_, v___x_492_);
v___x_602_ = l_Lean_Syntax_node4(v___x_372_, v___x_473_, v___x_595_, v___x_381_, v___x_479_, v___x_601_);
v___x_603_ = l_Lean_Syntax_node2(v___x_372_, v___x_471_, v___x_472_, v___x_602_);
v___x_604_ = l_Lean_Syntax_node3(v___x_372_, v___x_373_, v___x_599_, v___x_435_, v___x_603_);
v___x_605_ = l_Lean_Syntax_node3(v___x_372_, v___x_467_, v___x_469_, v___x_604_, v___x_492_);
v___x_606_ = l_Lean_Syntax_node4(v___x_372_, v___x_464_, v___x_466_, v___x_605_, v___x_495_, v___x_381_);
v___x_607_ = l_Lean_Syntax_node4(v___x_372_, v___x_384_, v___x_385_, v___x_569_, v___x_589_, v___x_606_);
v___x_608_ = l_Lean_Syntax_node2(v___x_372_, v___x_378_, v___x_382_, v___x_607_);
v___x_609_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__151));
v___x_610_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_372_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = l_Lean_Syntax_node2(v___x_372_, v___x_502_, v___x_610_, v___x_506_);
v___x_612_ = l_Lean_Syntax_node2(v___x_372_, v___x_499_, v___x_501_, v___x_611_);
v___x_613_ = l_Lean_Syntax_node1(v___x_372_, v___x_373_, v___x_612_);
v___x_614_ = l_Lean_Syntax_node7(v___x_372_, v___x_379_, v___x_613_, v___x_526_, v___x_381_, v___x_381_, v___x_381_, v___x_381_, v___x_381_);
v___x_615_ = lean_obj_once(&l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__153, &l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__153_once, _init_l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__153);
v___x_616_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__154));
v___x_617_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_617_, 0, v___x_372_);
lean_ctor_set(v___x_617_, 1, v___x_615_);
lean_ctor_set(v___x_617_, 2, v___x_616_);
lean_ctor_set(v___x_617_, 3, v___x_389_);
v___x_618_ = l_Lean_Syntax_node2(v___x_372_, v___x_386_, v___x_617_, v___x_381_);
v___x_619_ = l_Lean_Syntax_node1(v___x_372_, v___x_373_, v___x_581_);
v___x_620_ = l_Lean_Syntax_node2(v___x_372_, v___x_436_, v___x_548_, v___x_619_);
v___x_621_ = l_Lean_Syntax_node2(v___x_372_, v___x_415_, v___x_401_, v___x_620_);
v___x_622_ = l_Lean_Syntax_node1(v___x_372_, v___x_373_, v___x_621_);
v___x_623_ = l_Lean_Syntax_node2(v___x_372_, v___x_535_, v___x_545_, v___x_622_);
v___x_624_ = l_Lean_Syntax_node2(v___x_372_, v___x_373_, v___x_560_, v___x_568_);
v___x_625_ = l_Lean_Syntax_node2(v___x_372_, v___x_436_, v___x_556_, v___x_624_);
v___x_626_ = l_Lean_Syntax_node4(v___x_372_, v___x_464_, v___x_466_, v___x_625_, v___x_495_, v___x_381_);
v___x_627_ = l_Lean_Syntax_node5(v___x_372_, v___x_528_, v___x_530_, v___x_618_, v___x_623_, v___x_626_, v___x_381_);
v___x_628_ = l_Lean_Syntax_node2(v___x_372_, v___x_378_, v___x_614_, v___x_627_);
v___x_629_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__155));
v___x_630_ = ((lean_object*)(l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___closed__156));
v___x_631_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_372_);
lean_ctor_set(v___x_631_, 1, v___x_629_);
v___x_632_ = l_Lean_Syntax_node2(v___x_372_, v___x_373_, v___x_368_, v___x_381_);
v___x_633_ = l_Lean_Syntax_node2(v___x_372_, v___x_630_, v___x_631_, v___x_632_);
v___x_634_ = l_Lean_Syntax_node6(v___x_372_, v___x_373_, v___x_377_, v___x_498_, v___x_565_, v___x_608_, v___x_628_, v___x_633_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v_a_361_);
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1___boxed(lean_object* v_x_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___aux__Init__Data__UInt__Decidable______macroRules__commandDeclare__decidable__uint__quantifiers______1(v_x_636_, v_a_637_, v_a_638_);
lean_dec_ref(v_a_637_);
return v_res_639_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instDecidableForall___redArg___lam__0(lean_object* v_inst_640_, lean_object* v_a_641_){
_start:
{
uint8_t v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_642_ = lean_uint8_of_nat_mk(v_a_641_);
v___x_643_ = lean_box(v___x_642_);
v___x_644_ = lean_apply_1(v_inst_640_, v___x_643_);
v___x_645_ = lean_unbox(v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instDecidableForall___redArg___lam__0___boxed(lean_object* v_inst_646_, lean_object* v_a_647_){
_start:
{
uint8_t v_res_648_; lean_object* v_r_649_; 
v_res_648_ = l_UInt8_instDecidableForall___redArg___lam__0(v_inst_646_, v_a_647_);
v_r_649_ = lean_box(v_res_648_);
return v_r_649_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instDecidableForall___redArg(lean_object* v_inst_650_){
_start:
{
lean_object* v___f_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___f_651_ = lean_alloc_closure((void*)(l_UInt8_instDecidableForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_651_, 0, v_inst_650_);
v___x_652_ = lean_unsigned_to_nat(8u);
v___x_653_ = l_BitVec_instDecidableForallBitVec___redArg(v___x_652_, v___f_651_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instDecidableForall___redArg___boxed(lean_object* v_inst_654_){
_start:
{
uint8_t v_res_655_; lean_object* v_r_656_; 
v_res_655_ = l_UInt8_instDecidableForall___redArg(v_inst_654_);
v_r_656_ = lean_box(v_res_655_);
return v_r_656_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instDecidableForall(lean_object* v_P_657_, lean_object* v_inst_658_){
_start:
{
uint8_t v___x_659_; 
v___x_659_ = l_UInt8_instDecidableForall___redArg(v_inst_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instDecidableForall___boxed(lean_object* v_P_660_, lean_object* v_inst_661_){
_start:
{
uint8_t v_res_662_; lean_object* v_r_663_; 
v_res_662_ = l_UInt8_instDecidableForall(v_P_660_, v_inst_661_);
v_r_663_ = lean_box(v_res_662_);
return v_r_663_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instDecidableExists___redArg(lean_object* v_inst_664_){
_start:
{
lean_object* v___f_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___f_665_ = lean_alloc_closure((void*)(l_UInt8_instDecidableForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_665_, 0, v_inst_664_);
v___x_666_ = lean_unsigned_to_nat(8u);
v___x_667_ = l_BitVec_instDecidableExistsBitVec___redArg(v___x_666_, v___f_665_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instDecidableExists___redArg___boxed(lean_object* v_inst_668_){
_start:
{
uint8_t v_res_669_; lean_object* v_r_670_; 
v_res_669_ = l_UInt8_instDecidableExists___redArg(v_inst_668_);
v_r_670_ = lean_box(v_res_669_);
return v_r_670_;
}
}
LEAN_EXPORT uint8_t l_UInt8_instDecidableExists(lean_object* v_P_671_, lean_object* v_inst_672_){
_start:
{
uint8_t v___x_673_; 
v___x_673_ = l_UInt8_instDecidableExists___redArg(v_inst_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instDecidableExists___boxed(lean_object* v_P_674_, lean_object* v_inst_675_){
_start:
{
uint8_t v_res_676_; lean_object* v_r_677_; 
v_res_676_ = l_UInt8_instDecidableExists(v_P_674_, v_inst_675_);
v_r_677_ = lean_box(v_res_676_);
return v_r_677_;
}
}
LEAN_EXPORT uint8_t l_UInt16_instDecidableForall___redArg___lam__0(lean_object* v_inst_678_, lean_object* v_a_679_){
_start:
{
uint16_t v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_680_ = lean_uint16_of_nat_mk(v_a_679_);
v___x_681_ = lean_box(v___x_680_);
v___x_682_ = lean_apply_1(v_inst_678_, v___x_681_);
v___x_683_ = lean_unbox(v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_UInt16_instDecidableForall___redArg___lam__0___boxed(lean_object* v_inst_684_, lean_object* v_a_685_){
_start:
{
uint8_t v_res_686_; lean_object* v_r_687_; 
v_res_686_ = l_UInt16_instDecidableForall___redArg___lam__0(v_inst_684_, v_a_685_);
v_r_687_ = lean_box(v_res_686_);
return v_r_687_;
}
}
LEAN_EXPORT uint8_t l_UInt16_instDecidableForall___redArg(lean_object* v_inst_688_){
_start:
{
lean_object* v___f_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___f_689_ = lean_alloc_closure((void*)(l_UInt16_instDecidableForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_689_, 0, v_inst_688_);
v___x_690_ = lean_unsigned_to_nat(16u);
v___x_691_ = l_BitVec_instDecidableForallBitVec___redArg(v___x_690_, v___f_689_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_UInt16_instDecidableForall___redArg___boxed(lean_object* v_inst_692_){
_start:
{
uint8_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = l_UInt16_instDecidableForall___redArg(v_inst_692_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT uint8_t l_UInt16_instDecidableForall(lean_object* v_P_695_, lean_object* v_inst_696_){
_start:
{
uint8_t v___x_697_; 
v___x_697_ = l_UInt16_instDecidableForall___redArg(v_inst_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_UInt16_instDecidableForall___boxed(lean_object* v_P_698_, lean_object* v_inst_699_){
_start:
{
uint8_t v_res_700_; lean_object* v_r_701_; 
v_res_700_ = l_UInt16_instDecidableForall(v_P_698_, v_inst_699_);
v_r_701_ = lean_box(v_res_700_);
return v_r_701_;
}
}
LEAN_EXPORT uint8_t l_UInt16_instDecidableExists___redArg(lean_object* v_inst_702_){
_start:
{
lean_object* v___f_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v___f_703_ = lean_alloc_closure((void*)(l_UInt16_instDecidableForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_703_, 0, v_inst_702_);
v___x_704_ = lean_unsigned_to_nat(16u);
v___x_705_ = l_BitVec_instDecidableExistsBitVec___redArg(v___x_704_, v___f_703_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_UInt16_instDecidableExists___redArg___boxed(lean_object* v_inst_706_){
_start:
{
uint8_t v_res_707_; lean_object* v_r_708_; 
v_res_707_ = l_UInt16_instDecidableExists___redArg(v_inst_706_);
v_r_708_ = lean_box(v_res_707_);
return v_r_708_;
}
}
LEAN_EXPORT uint8_t l_UInt16_instDecidableExists(lean_object* v_P_709_, lean_object* v_inst_710_){
_start:
{
uint8_t v___x_711_; 
v___x_711_ = l_UInt16_instDecidableExists___redArg(v_inst_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_UInt16_instDecidableExists___boxed(lean_object* v_P_712_, lean_object* v_inst_713_){
_start:
{
uint8_t v_res_714_; lean_object* v_r_715_; 
v_res_714_ = l_UInt16_instDecidableExists(v_P_712_, v_inst_713_);
v_r_715_ = lean_box(v_res_714_);
return v_r_715_;
}
}
LEAN_EXPORT uint8_t l_UInt32_instDecidableForall___redArg___lam__0(lean_object* v_inst_716_, lean_object* v_a_717_){
_start:
{
uint32_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_718_ = lean_uint32_of_nat_mk(v_a_717_);
v___x_719_ = lean_box_uint32(v___x_718_);
v___x_720_ = lean_apply_1(v_inst_716_, v___x_719_);
v___x_721_ = lean_unbox(v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_UInt32_instDecidableForall___redArg___lam__0___boxed(lean_object* v_inst_722_, lean_object* v_a_723_){
_start:
{
uint8_t v_res_724_; lean_object* v_r_725_; 
v_res_724_ = l_UInt32_instDecidableForall___redArg___lam__0(v_inst_722_, v_a_723_);
v_r_725_ = lean_box(v_res_724_);
return v_r_725_;
}
}
LEAN_EXPORT uint8_t l_UInt32_instDecidableForall___redArg(lean_object* v_inst_726_){
_start:
{
lean_object* v___f_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___f_727_ = lean_alloc_closure((void*)(l_UInt32_instDecidableForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_727_, 0, v_inst_726_);
v___x_728_ = lean_unsigned_to_nat(32u);
v___x_729_ = l_BitVec_instDecidableForallBitVec___redArg(v___x_728_, v___f_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_UInt32_instDecidableForall___redArg___boxed(lean_object* v_inst_730_){
_start:
{
uint8_t v_res_731_; lean_object* v_r_732_; 
v_res_731_ = l_UInt32_instDecidableForall___redArg(v_inst_730_);
v_r_732_ = lean_box(v_res_731_);
return v_r_732_;
}
}
LEAN_EXPORT uint8_t l_UInt32_instDecidableForall(lean_object* v_P_733_, lean_object* v_inst_734_){
_start:
{
uint8_t v___x_735_; 
v___x_735_ = l_UInt32_instDecidableForall___redArg(v_inst_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_UInt32_instDecidableForall___boxed(lean_object* v_P_736_, lean_object* v_inst_737_){
_start:
{
uint8_t v_res_738_; lean_object* v_r_739_; 
v_res_738_ = l_UInt32_instDecidableForall(v_P_736_, v_inst_737_);
v_r_739_ = lean_box(v_res_738_);
return v_r_739_;
}
}
LEAN_EXPORT uint8_t l_UInt32_instDecidableExists___redArg(lean_object* v_inst_740_){
_start:
{
lean_object* v___f_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v___f_741_ = lean_alloc_closure((void*)(l_UInt32_instDecidableForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_741_, 0, v_inst_740_);
v___x_742_ = lean_unsigned_to_nat(32u);
v___x_743_ = l_BitVec_instDecidableExistsBitVec___redArg(v___x_742_, v___f_741_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_UInt32_instDecidableExists___redArg___boxed(lean_object* v_inst_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l_UInt32_instDecidableExists___redArg(v_inst_744_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT uint8_t l_UInt32_instDecidableExists(lean_object* v_P_747_, lean_object* v_inst_748_){
_start:
{
uint8_t v___x_749_; 
v___x_749_ = l_UInt32_instDecidableExists___redArg(v_inst_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_UInt32_instDecidableExists___boxed(lean_object* v_P_750_, lean_object* v_inst_751_){
_start:
{
uint8_t v_res_752_; lean_object* v_r_753_; 
v_res_752_ = l_UInt32_instDecidableExists(v_P_750_, v_inst_751_);
v_r_753_ = lean_box(v_res_752_);
return v_r_753_;
}
}
LEAN_EXPORT uint8_t l_UInt64_instDecidableForall___redArg___lam__0(lean_object* v_inst_754_, lean_object* v_a_755_){
_start:
{
uint64_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_756_ = lean_uint64_of_nat_mk(v_a_755_);
v___x_757_ = lean_box_uint64(v___x_756_);
v___x_758_ = lean_apply_1(v_inst_754_, v___x_757_);
v___x_759_ = lean_unbox(v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_UInt64_instDecidableForall___redArg___lam__0___boxed(lean_object* v_inst_760_, lean_object* v_a_761_){
_start:
{
uint8_t v_res_762_; lean_object* v_r_763_; 
v_res_762_ = l_UInt64_instDecidableForall___redArg___lam__0(v_inst_760_, v_a_761_);
v_r_763_ = lean_box(v_res_762_);
return v_r_763_;
}
}
LEAN_EXPORT uint8_t l_UInt64_instDecidableForall___redArg(lean_object* v_inst_764_){
_start:
{
lean_object* v___f_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___f_765_ = lean_alloc_closure((void*)(l_UInt64_instDecidableForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_765_, 0, v_inst_764_);
v___x_766_ = lean_unsigned_to_nat(64u);
v___x_767_ = l_BitVec_instDecidableForallBitVec___redArg(v___x_766_, v___f_765_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_UInt64_instDecidableForall___redArg___boxed(lean_object* v_inst_768_){
_start:
{
uint8_t v_res_769_; lean_object* v_r_770_; 
v_res_769_ = l_UInt64_instDecidableForall___redArg(v_inst_768_);
v_r_770_ = lean_box(v_res_769_);
return v_r_770_;
}
}
LEAN_EXPORT uint8_t l_UInt64_instDecidableForall(lean_object* v_P_771_, lean_object* v_inst_772_){
_start:
{
uint8_t v___x_773_; 
v___x_773_ = l_UInt64_instDecidableForall___redArg(v_inst_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_UInt64_instDecidableForall___boxed(lean_object* v_P_774_, lean_object* v_inst_775_){
_start:
{
uint8_t v_res_776_; lean_object* v_r_777_; 
v_res_776_ = l_UInt64_instDecidableForall(v_P_774_, v_inst_775_);
v_r_777_ = lean_box(v_res_776_);
return v_r_777_;
}
}
LEAN_EXPORT uint8_t l_UInt64_instDecidableExists___redArg(lean_object* v_inst_778_){
_start:
{
lean_object* v___f_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v___f_779_ = lean_alloc_closure((void*)(l_UInt64_instDecidableForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_779_, 0, v_inst_778_);
v___x_780_ = lean_unsigned_to_nat(64u);
v___x_781_ = l_BitVec_instDecidableExistsBitVec___redArg(v___x_780_, v___f_779_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_UInt64_instDecidableExists___redArg___boxed(lean_object* v_inst_782_){
_start:
{
uint8_t v_res_783_; lean_object* v_r_784_; 
v_res_783_ = l_UInt64_instDecidableExists___redArg(v_inst_782_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT uint8_t l_UInt64_instDecidableExists(lean_object* v_P_785_, lean_object* v_inst_786_){
_start:
{
uint8_t v___x_787_; 
v___x_787_ = l_UInt64_instDecidableExists___redArg(v_inst_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_UInt64_instDecidableExists___boxed(lean_object* v_P_788_, lean_object* v_inst_789_){
_start:
{
uint8_t v_res_790_; lean_object* v_r_791_; 
v_res_790_ = l_UInt64_instDecidableExists(v_P_788_, v_inst_789_);
v_r_791_ = lean_box(v_res_790_);
return v_r_791_;
}
}
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Decidable(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_UInt_Decidable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Init_Data_UInt_Decidable(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Decidable(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_UInt_Decidable(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Decidable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Decidable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_UInt_Decidable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_UInt_Decidable(builtin);
}
#ifdef __cplusplus
}
#endif
