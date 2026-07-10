// Lean compiler output
// Module: Init.Data.Bool
// Imports: public import Init.NotationExtra
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_xor(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Bool_xor___boxed(lean_object*, lean_object*);
static const lean_string_object l_Bool_term___x5e_x5e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Bool_term___x5e_x5e___00__closed__0 = (const lean_object*)&l_Bool_term___x5e_x5e___00__closed__0_value;
static const lean_string_object l_Bool_term___x5e_x5e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_^^_"};
static const lean_object* l_Bool_term___x5e_x5e___00__closed__1 = (const lean_object*)&l_Bool_term___x5e_x5e___00__closed__1_value;
static const lean_ctor_object l_Bool_term___x5e_x5e___00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Bool_term___x5e_x5e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Bool_term___x5e_x5e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Bool_term___x5e_x5e___00__closed__2_value_aux_0),((lean_object*)&l_Bool_term___x5e_x5e___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(108, 188, 171, 230, 73, 21, 37, 140)}};
static const lean_object* l_Bool_term___x5e_x5e___00__closed__2 = (const lean_object*)&l_Bool_term___x5e_x5e___00__closed__2_value;
static const lean_string_object l_Bool_term___x5e_x5e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Bool_term___x5e_x5e___00__closed__3 = (const lean_object*)&l_Bool_term___x5e_x5e___00__closed__3_value;
static const lean_ctor_object l_Bool_term___x5e_x5e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Bool_term___x5e_x5e___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Bool_term___x5e_x5e___00__closed__4 = (const lean_object*)&l_Bool_term___x5e_x5e___00__closed__4_value;
static const lean_string_object l_Bool_term___x5e_x5e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " ^^ "};
static const lean_object* l_Bool_term___x5e_x5e___00__closed__5 = (const lean_object*)&l_Bool_term___x5e_x5e___00__closed__5_value;
static const lean_ctor_object l_Bool_term___x5e_x5e___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Bool_term___x5e_x5e___00__closed__5_value)}};
static const lean_object* l_Bool_term___x5e_x5e___00__closed__6 = (const lean_object*)&l_Bool_term___x5e_x5e___00__closed__6_value;
static const lean_string_object l_Bool_term___x5e_x5e___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Bool_term___x5e_x5e___00__closed__7 = (const lean_object*)&l_Bool_term___x5e_x5e___00__closed__7_value;
static const lean_ctor_object l_Bool_term___x5e_x5e___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Bool_term___x5e_x5e___00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Bool_term___x5e_x5e___00__closed__8 = (const lean_object*)&l_Bool_term___x5e_x5e___00__closed__8_value;
static const lean_ctor_object l_Bool_term___x5e_x5e___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Bool_term___x5e_x5e___00__closed__8_value),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l_Bool_term___x5e_x5e___00__closed__9 = (const lean_object*)&l_Bool_term___x5e_x5e___00__closed__9_value;
static const lean_ctor_object l_Bool_term___x5e_x5e___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Bool_term___x5e_x5e___00__closed__4_value),((lean_object*)&l_Bool_term___x5e_x5e___00__closed__6_value),((lean_object*)&l_Bool_term___x5e_x5e___00__closed__9_value)}};
static const lean_object* l_Bool_term___x5e_x5e___00__closed__10 = (const lean_object*)&l_Bool_term___x5e_x5e___00__closed__10_value;
static const lean_ctor_object l_Bool_term___x5e_x5e___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Bool_term___x5e_x5e___00__closed__2_value),((lean_object*)(((size_t)(33) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1)),((lean_object*)&l_Bool_term___x5e_x5e___00__closed__10_value)}};
static const lean_object* l_Bool_term___x5e_x5e___00__closed__11 = (const lean_object*)&l_Bool_term___x5e_x5e___00__closed__11_value;
LEAN_EXPORT const lean_object* l_Bool_term___x5e_x5e__ = (const lean_object*)&l_Bool_term___x5e_x5e___00__closed__11_value;
static const lean_string_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__0 = (const lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__0_value;
static const lean_string_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__1 = (const lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__1_value;
static const lean_string_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__2 = (const lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__2_value;
static const lean_string_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__3 = (const lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__3_value;
static const lean_ctor_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value_aux_0),((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value_aux_1),((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value_aux_2),((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4 = (const lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value;
static const lean_string_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "xor"};
static const lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__5 = (const lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__5_value;
static lean_once_cell_t l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6;
static const lean_ctor_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(202, 242, 219, 132, 101, 186, 164, 72)}};
static const lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__7 = (const lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__7_value;
static const lean_ctor_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Bool_term___x5e_x5e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__8_value_aux_0),((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(159, 35, 146, 118, 24, 65, 174, 144)}};
static const lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__8 = (const lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__8_value;
static const lean_ctor_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__9 = (const lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__9_value;
static const lean_ctor_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__10 = (const lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__10_value;
static const lean_string_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__11 = (const lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__11_value;
static const lean_ctor_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__12 = (const lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__12_value;
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__0 = (const lean_object*)&l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__0_value;
static const lean_ctor_object l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__1 = (const lean_object*)&l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__1_value;
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Bool_instDecidableForallOfDecidablePred___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Bool_instDecidableForallOfDecidablePred___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Bool_instDecidableForallOfDecidablePred(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool_instDecidableForallOfDecidablePred___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Bool_instDecidableExistsOfDecidablePred___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Bool_instDecidableExistsOfDecidablePred___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Bool_instDecidableExistsOfDecidablePred(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool_instDecidableExistsOfDecidablePred___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool_instLE;
LEAN_EXPORT lean_object* l_Bool_instLT;
LEAN_EXPORT uint8_t l_Bool_instDecidableLe(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Bool_instDecidableLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Bool_instDecidableLt(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Bool_instDecidableLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Bool_instMax___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Bool_instMax___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Bool_instMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Bool_instMax___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Bool_instMax___closed__0 = (const lean_object*)&l_Bool_instMax___closed__0_value;
LEAN_EXPORT const lean_object* l_Bool_instMax = (const lean_object*)&l_Bool_instMax___closed__0_value;
LEAN_EXPORT uint8_t l_Bool_instMin___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Bool_instMin___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Bool_instMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Bool_instMin___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Bool_instMin___closed__0 = (const lean_object*)&l_Bool_instMin___closed__0_value;
LEAN_EXPORT const lean_object* l_Bool_instMin = (const lean_object*)&l_Bool_instMin___closed__0_value;
lean_object* lean_bool_to_nat(uint8_t);
LEAN_EXPORT lean_object* l_Bool_toNat___boxed(lean_object*);
static lean_once_cell_t l_Bool_toInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Bool_toInt___closed__0;
static lean_once_cell_t l_Bool_toInt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Bool_toInt___closed__1;
LEAN_EXPORT lean_object* l_Bool_toInt(uint8_t);
LEAN_EXPORT lean_object* l_Bool_toInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_boolPredToPred(lean_object*);
LEAN_EXPORT lean_object* l_boolRelToRel(lean_object*);
LEAN_EXPORT lean_object* l_Bool_xor___boxed(lean_object* v_a_00___x40___internal___hyg_3_, lean_object* v_a_00___x40___internal___hyg_4_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_5_; uint8_t v_a_00___x40___internal___hyg_2__boxed_6_; uint8_t v_res_7_; lean_object* v_r_8_; 
v_a_00___x40___internal___hyg_1__boxed_5_ = lean_unbox(v_a_00___x40___internal___hyg_3_);
v_a_00___x40___internal___hyg_2__boxed_6_ = lean_unbox(v_a_00___x40___internal___hyg_4_);
v_res_7_ = lean_bool_xor(v_a_00___x40___internal___hyg_1__boxed_5_, v_a_00___x40___internal___hyg_2__boxed_6_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
static lean_object* _init_l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__5));
v___x_46_ = l_String_toRawSubstring_x27(v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1(lean_object* v_x_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = ((lean_object*)(l_Bool_term___x5e_x5e___00__closed__2));
lean_inc(v_x_61_);
v___x_65_ = l_Lean_Syntax_isOfKind(v_x_61_, v___x_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; 
lean_dec(v_x_61_);
v___x_66_ = lean_box(1);
v___x_67_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v_a_63_);
return v___x_67_;
}
else
{
lean_object* v_quotContext_68_; lean_object* v_currMacroScope_69_; lean_object* v_ref_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_quotContext_68_ = lean_ctor_get(v_a_62_, 1);
v_currMacroScope_69_ = lean_ctor_get(v_a_62_, 2);
v_ref_70_ = lean_ctor_get(v_a_62_, 5);
v___x_71_ = lean_unsigned_to_nat(0u);
v___x_72_ = l_Lean_Syntax_getArg(v_x_61_, v___x_71_);
v___x_73_ = lean_unsigned_to_nat(2u);
v___x_74_ = l_Lean_Syntax_getArg(v_x_61_, v___x_73_);
lean_dec(v_x_61_);
v___x_75_ = 0;
v___x_76_ = l_Lean_SourceInfo_fromRef(v_ref_70_, v___x_75_);
v___x_77_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4));
v___x_78_ = lean_obj_once(&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6, &l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6_once, _init_l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6);
v___x_79_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__7));
lean_inc(v_currMacroScope_69_);
lean_inc(v_quotContext_68_);
v___x_80_ = l_Lean_addMacroScope(v_quotContext_68_, v___x_79_, v_currMacroScope_69_);
v___x_81_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__10));
lean_inc_n(v___x_76_, 2);
v___x_82_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_82_, 0, v___x_76_);
lean_ctor_set(v___x_82_, 1, v___x_78_);
lean_ctor_set(v___x_82_, 2, v___x_80_);
lean_ctor_set(v___x_82_, 3, v___x_81_);
v___x_83_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__12));
v___x_84_ = l_Lean_Syntax_node2(v___x_76_, v___x_83_, v___x_72_, v___x_74_);
v___x_85_ = l_Lean_Syntax_node2(v___x_76_, v___x_77_, v___x_82_, v___x_84_);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v_a_63_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___boxed(lean_object* v_x_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1(v_x_87_, v_a_88_, v_a_89_);
lean_dec_ref(v_a_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1(lean_object* v_x_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4));
lean_inc(v_x_94_);
v___x_98_ = l_Lean_Syntax_isOfKind(v_x_94_, v___x_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_100_; 
lean_dec(v_x_94_);
v___x_99_ = lean_box(0);
v___x_100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v_a_96_);
return v___x_100_;
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = l_Lean_Syntax_getArg(v_x_94_, v___x_101_);
v___x_103_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__1));
lean_inc(v___x_102_);
v___x_104_ = l_Lean_Syntax_isOfKind(v___x_102_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec(v___x_102_);
lean_dec(v_x_94_);
v___x_105_ = lean_box(0);
v___x_106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v_a_96_);
return v___x_106_;
}
else
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_107_ = lean_unsigned_to_nat(1u);
v___x_108_ = l_Lean_Syntax_getArg(v_x_94_, v___x_107_);
lean_dec(v_x_94_);
v___x_109_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_108_);
v___x_110_ = l_Lean_Syntax_matchesNull(v___x_108_, v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; 
lean_dec(v___x_108_);
lean_dec(v___x_102_);
v___x_111_ = lean_box(0);
v___x_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v_a_96_);
return v___x_112_;
}
else
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v_ref_115_; uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_113_ = l_Lean_Syntax_getArg(v___x_108_, v___x_101_);
v___x_114_ = l_Lean_Syntax_getArg(v___x_108_, v___x_107_);
lean_dec(v___x_108_);
v_ref_115_ = l_Lean_replaceRef(v___x_102_, v_a_95_);
lean_dec(v___x_102_);
v___x_116_ = 0;
v___x_117_ = l_Lean_SourceInfo_fromRef(v_ref_115_, v___x_116_);
lean_dec(v_ref_115_);
v___x_118_ = ((lean_object*)(l_Bool_term___x5e_x5e___00__closed__2));
v___x_119_ = ((lean_object*)(l_Bool_term___x5e_x5e___00__closed__5));
lean_inc(v___x_117_);
v___x_120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_117_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = l_Lean_Syntax_node3(v___x_117_, v___x_118_, v___x_113_, v___x_120_, v___x_114_);
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
lean_ctor_set(v___x_122_, 1, v_a_96_);
return v___x_122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___boxed(lean_object* v_x_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1(v_x_123_, v_a_124_, v_a_125_);
lean_dec(v_a_124_);
return v_res_126_;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableForallOfDecidablePred___redArg(lean_object* v_inst_127_){
_start:
{
uint8_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_128_ = 1;
v___x_129_ = lean_box(v___x_128_);
lean_inc_ref(v_inst_127_);
v___x_130_ = lean_apply_1(v_inst_127_, v___x_129_);
v___x_131_ = lean_unbox(v___x_130_);
if (v___x_131_ == 0)
{
uint8_t v___x_132_; 
lean_dec_ref(v_inst_127_);
v___x_132_ = lean_unbox(v___x_130_);
return v___x_132_;
}
else
{
uint8_t v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_133_ = 0;
v___x_134_ = lean_box(v___x_133_);
v___x_135_ = lean_apply_1(v_inst_127_, v___x_134_);
v___x_136_ = lean_unbox(v___x_135_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableForallOfDecidablePred___redArg___boxed(lean_object* v_inst_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Bool_instDecidableForallOfDecidablePred___redArg(v_inst_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableForallOfDecidablePred(lean_object* v_p_140_, lean_object* v_inst_141_){
_start:
{
uint8_t v___x_142_; 
v___x_142_ = l_Bool_instDecidableForallOfDecidablePred___redArg(v_inst_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableForallOfDecidablePred___boxed(lean_object* v_p_143_, lean_object* v_inst_144_){
_start:
{
uint8_t v_res_145_; lean_object* v_r_146_; 
v_res_145_ = l_Bool_instDecidableForallOfDecidablePred(v_p_143_, v_inst_144_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableExistsOfDecidablePred___redArg(lean_object* v_inst_147_){
_start:
{
uint8_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_148_ = 1;
v___x_149_ = lean_box(v___x_148_);
lean_inc_ref(v_inst_147_);
v___x_150_ = lean_apply_1(v_inst_147_, v___x_149_);
v___x_151_ = lean_unbox(v___x_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = lean_apply_1(v_inst_147_, v___x_150_);
v___x_153_ = lean_unbox(v___x_152_);
return v___x_153_;
}
else
{
uint8_t v___x_154_; 
lean_dec_ref(v_inst_147_);
v___x_154_ = lean_unbox(v___x_150_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableExistsOfDecidablePred___redArg___boxed(lean_object* v_inst_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_Bool_instDecidableExistsOfDecidablePred___redArg(v_inst_155_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableExistsOfDecidablePred(lean_object* v_p_158_, lean_object* v_inst_159_){
_start:
{
uint8_t v___x_160_; 
v___x_160_ = l_Bool_instDecidableExistsOfDecidablePred___redArg(v_inst_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableExistsOfDecidablePred___boxed(lean_object* v_p_161_, lean_object* v_inst_162_){
_start:
{
uint8_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l_Bool_instDecidableExistsOfDecidablePred(v_p_161_, v_inst_162_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
static lean_object* _init_l_Bool_instLE(void){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_box(0);
return v___x_165_;
}
}
static lean_object* _init_l_Bool_instLT(void){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_box(0);
return v___x_166_;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableLe(uint8_t v_x_167_, uint8_t v_y_168_){
_start:
{
if (v_x_167_ == 0)
{
uint8_t v___x_169_; 
v___x_169_ = 1;
return v___x_169_;
}
else
{
return v_y_168_;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableLe___boxed(lean_object* v_x_170_, lean_object* v_y_171_){
_start:
{
uint8_t v_x_boxed_172_; uint8_t v_y_boxed_173_; uint8_t v_res_174_; lean_object* v_r_175_; 
v_x_boxed_172_ = lean_unbox(v_x_170_);
v_y_boxed_173_ = lean_unbox(v_y_171_);
v_res_174_ = l_Bool_instDecidableLe(v_x_boxed_172_, v_y_boxed_173_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableLt(uint8_t v_x_176_, uint8_t v_y_177_){
_start:
{
uint8_t v___x_178_; 
v___x_178_ = lean_bool_not(v_x_176_);
if (v___x_178_ == 0)
{
return v___x_178_;
}
else
{
return v_y_177_;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableLt___boxed(lean_object* v_x_179_, lean_object* v_y_180_){
_start:
{
uint8_t v_x_boxed_181_; uint8_t v_y_boxed_182_; uint8_t v_res_183_; lean_object* v_r_184_; 
v_x_boxed_181_ = lean_unbox(v_x_179_);
v_y_boxed_182_ = lean_unbox(v_y_180_);
v_res_183_ = l_Bool_instDecidableLt(v_x_boxed_181_, v_y_boxed_182_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT uint8_t l_Bool_instMax___lam__0(uint8_t v_x_185_, uint8_t v_y_186_){
_start:
{
if (v_x_185_ == 0)
{
return v_y_186_;
}
else
{
return v_x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instMax___lam__0___boxed(lean_object* v_x_187_, lean_object* v_y_188_){
_start:
{
uint8_t v_x_boxed_189_; uint8_t v_y_boxed_190_; uint8_t v_res_191_; lean_object* v_r_192_; 
v_x_boxed_189_ = lean_unbox(v_x_187_);
v_y_boxed_190_ = lean_unbox(v_y_188_);
v_res_191_ = l_Bool_instMax___lam__0(v_x_boxed_189_, v_y_boxed_190_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT uint8_t l_Bool_instMin___lam__0(uint8_t v_x_195_, uint8_t v_y_196_){
_start:
{
if (v_x_195_ == 0)
{
return v_x_195_;
}
else
{
return v_y_196_;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instMin___lam__0___boxed(lean_object* v_x_197_, lean_object* v_y_198_){
_start:
{
uint8_t v_x_boxed_199_; uint8_t v_y_boxed_200_; uint8_t v_res_201_; lean_object* v_r_202_; 
v_x_boxed_199_ = lean_unbox(v_x_197_);
v_y_boxed_200_ = lean_unbox(v_y_198_);
v_res_201_ = l_Bool_instMin___lam__0(v_x_boxed_199_, v_y_boxed_200_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT lean_object* l_Bool_toNat___boxed(lean_object* v_b_206_){
_start:
{
uint8_t v_b_boxed_207_; lean_object* v_res_208_; 
v_b_boxed_207_ = lean_unbox(v_b_206_);
v_res_208_ = lean_bool_to_nat(v_b_boxed_207_);
return v_res_208_;
}
}
static lean_object* _init_l_Bool_toInt___closed__0(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_nat_to_int(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Bool_toInt___closed__1(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_to_int(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt(uint8_t v_b_213_){
_start:
{
if (v_b_213_ == 0)
{
lean_object* v___x_214_; 
v___x_214_ = lean_obj_once(&l_Bool_toInt___closed__0, &l_Bool_toInt___closed__0_once, _init_l_Bool_toInt___closed__0);
return v___x_214_;
}
else
{
lean_object* v___x_215_; 
v___x_215_ = lean_obj_once(&l_Bool_toInt___closed__1, &l_Bool_toInt___closed__1_once, _init_l_Bool_toInt___closed__1);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l_Bool_toInt___boxed(lean_object* v_b_216_){
_start:
{
uint8_t v_b_boxed_217_; lean_object* v_res_218_; 
v_b_boxed_217_ = lean_unbox(v_b_216_);
v_res_218_ = l_Bool_toInt(v_b_boxed_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_boolPredToPred(lean_object* v_00_u03b1_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = lean_box(0);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_boolRelToRel(lean_object* v_00_u03b1_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_box(0);
return v___x_222_;
}
}
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Bool_instLE = _init_l_Bool_instLE();
lean_mark_persistent(l_Bool_instLE);
l_Bool_instLT = _init_l_Bool_instLT();
lean_mark_persistent(l_Bool_instLT);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Bool(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Bool(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Bool(builtin);
}
#ifdef __cplusplus
}
#endif
