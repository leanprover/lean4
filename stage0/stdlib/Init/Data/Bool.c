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
LEAN_EXPORT uint8_t l_Bool_xor(uint8_t, uint8_t);
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
LEAN_EXPORT lean_object* l_Bool_toNat(uint8_t);
LEAN_EXPORT lean_object* l_Bool_toNat___boxed(lean_object*);
static lean_once_cell_t l_Bool_toInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Bool_toInt___closed__0;
static lean_once_cell_t l_Bool_toInt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Bool_toInt___closed__1;
LEAN_EXPORT lean_object* l_Bool_toInt(uint8_t);
LEAN_EXPORT lean_object* l_Bool_toInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_boolPredToPred___redArg();
LEAN_EXPORT lean_object* l_boolPredToPred___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_boolPredToPred(lean_object*);
LEAN_EXPORT lean_object* l_boolRelToRel___redArg();
LEAN_EXPORT lean_object* l_boolRelToRel___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_boolRelToRel(lean_object*);
LEAN_EXPORT uint8_t l_Bool_and_x27(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Bool_and_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Bool_or_x27(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Bool_or_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Bool_not_x27(uint8_t);
LEAN_EXPORT lean_object* l_Bool_not_x27___boxed(lean_object*);
uint8_t l_Bool_xor(uint8_t v_a_1_, uint8_t v_b_2_){
_start:
{
if (v_b_2_ == 0)
{
return v_a_1_;
}
else
{
if (v_a_1_ == 0)
{
return v_b_2_;
}
else
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
}
}
}
LEAN_EXPORT void l_Bool_xor_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_1_ = stack[0].m_num;
uint8_t v_b_2_ = stack[1].m_num;
uint8_t v_res_4_;
v_res_4_ = l_Bool_xor(v_a_1_, v_b_2_);
stack->m_num = v_res_4_;
}
LEAN_EXPORT lean_object* l_Bool_xor___boxed(lean_object* v_a_5_, lean_object* v_b_6_){
_start:
{
uint8_t v_a_boxed_7_; uint8_t v_b_boxed_8_; uint8_t v_res_9_; lean_object* v_r_10_; 
v_a_boxed_7_ = lean_unbox(v_a_5_);
v_b_boxed_8_ = lean_unbox(v_b_6_);
v_res_9_ = l_Bool_xor(v_a_boxed_7_, v_b_boxed_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
static lean_object* _init_l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__5));
v___x_48_ = l_String_toRawSubstring_x27(v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1(lean_object* v_x_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_66_ = ((lean_object*)(l_Bool_term___x5e_x5e___00__closed__2));
lean_inc(v_x_63_);
v___x_67_ = l_Lean_Syntax_isOfKind(v_x_63_, v___x_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; lean_object* v___x_69_; 
lean_dec(v_x_63_);
v___x_68_ = lean_box(1);
v___x_69_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v_a_65_);
return v___x_69_;
}
else
{
lean_object* v_quotContext_70_; lean_object* v_currMacroScope_71_; lean_object* v_ref_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_quotContext_70_ = lean_ctor_get(v_a_64_, 1);
v_currMacroScope_71_ = lean_ctor_get(v_a_64_, 2);
v_ref_72_ = lean_ctor_get(v_a_64_, 5);
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = l_Lean_Syntax_getArg(v_x_63_, v___x_73_);
v___x_75_ = lean_unsigned_to_nat(2u);
v___x_76_ = l_Lean_Syntax_getArg(v_x_63_, v___x_75_);
lean_dec(v_x_63_);
v___x_77_ = 0;
v___x_78_ = l_Lean_SourceInfo_fromRef(v_ref_72_, v___x_77_);
v___x_79_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4));
v___x_80_ = lean_obj_once(&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6, &l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6_once, _init_l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6);
v___x_81_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__7));
lean_inc(v_currMacroScope_71_);
lean_inc(v_quotContext_70_);
v___x_82_ = l_Lean_addMacroScope(v_quotContext_70_, v___x_81_, v_currMacroScope_71_);
v___x_83_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__10));
lean_inc_n(v___x_78_, 2);
v___x_84_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_84_, 0, v___x_78_);
lean_ctor_set(v___x_84_, 1, v___x_80_);
lean_ctor_set(v___x_84_, 2, v___x_82_);
lean_ctor_set(v___x_84_, 3, v___x_83_);
v___x_85_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__12));
v___x_86_ = l_Lean_Syntax_node2(v___x_78_, v___x_85_, v___x_74_, v___x_76_);
v___x_87_ = l_Lean_Syntax_node2(v___x_78_, v___x_79_, v___x_84_, v___x_86_);
v___x_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v_a_65_);
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___boxed(lean_object* v_x_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1(v_x_89_, v_a_90_, v_a_91_);
lean_dec_ref(v_a_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1(lean_object* v_x_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4));
lean_inc(v_x_96_);
v___x_100_ = l_Lean_Syntax_isOfKind(v_x_96_, v___x_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; lean_object* v___x_102_; 
lean_dec(v_x_96_);
v___x_101_ = lean_box(0);
v___x_102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v_a_98_);
return v___x_102_;
}
else
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = l_Lean_Syntax_getArg(v_x_96_, v___x_103_);
v___x_105_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__1));
lean_inc(v___x_104_);
v___x_106_ = l_Lean_Syntax_isOfKind(v___x_104_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; 
lean_dec(v___x_104_);
lean_dec(v_x_96_);
v___x_107_ = lean_box(0);
v___x_108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v_a_98_);
return v___x_108_;
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_109_ = lean_unsigned_to_nat(1u);
v___x_110_ = l_Lean_Syntax_getArg(v_x_96_, v___x_109_);
lean_dec(v_x_96_);
v___x_111_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_110_);
v___x_112_ = l_Lean_Syntax_matchesNull(v___x_110_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec(v___x_110_);
lean_dec(v___x_104_);
v___x_113_ = lean_box(0);
v___x_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v_a_98_);
return v___x_114_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v_ref_117_; uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_115_ = l_Lean_Syntax_getArg(v___x_110_, v___x_103_);
v___x_116_ = l_Lean_Syntax_getArg(v___x_110_, v___x_109_);
lean_dec(v___x_110_);
v_ref_117_ = l_Lean_replaceRef(v___x_104_, v_a_97_);
lean_dec(v___x_104_);
v___x_118_ = 0;
v___x_119_ = l_Lean_SourceInfo_fromRef(v_ref_117_, v___x_118_);
lean_dec(v_ref_117_);
v___x_120_ = ((lean_object*)(l_Bool_term___x5e_x5e___00__closed__2));
v___x_121_ = ((lean_object*)(l_Bool_term___x5e_x5e___00__closed__5));
lean_inc(v___x_119_);
v___x_122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_119_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = l_Lean_Syntax_node3(v___x_119_, v___x_120_, v___x_115_, v___x_122_, v___x_116_);
v___x_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v_a_98_);
return v___x_124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___boxed(lean_object* v_x_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1(v_x_125_, v_a_126_, v_a_127_);
lean_dec(v_a_126_);
return v_res_128_;
}
}
uint8_t l_Bool_instDecidableForallOfDecidablePred___redArg(lean_object* v_inst_129_){
_start:
{
uint8_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_130_ = 1;
v___x_131_ = lean_box(v___x_130_);
lean_inc_ref(v_inst_129_);
v___x_132_ = lean_apply_1(v_inst_129_, v___x_131_);
v___x_133_ = lean_unbox(v___x_132_);
if (v___x_133_ == 0)
{
uint8_t v___x_134_; 
lean_dec_ref(v_inst_129_);
v___x_134_ = lean_unbox(v___x_132_);
return v___x_134_;
}
else
{
uint8_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_135_ = 0;
v___x_136_ = lean_box(v___x_135_);
v___x_137_ = lean_apply_1(v_inst_129_, v___x_136_);
v___x_138_ = lean_unbox(v___x_137_);
return v___x_138_;
}
}
}
LEAN_EXPORT void l_Bool_instDecidableForallOfDecidablePred___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_129_ = stack[0].m_obj;
uint8_t v_res_139_;
v_res_139_ = l_Bool_instDecidableForallOfDecidablePred___redArg(v_inst_129_);
stack->m_num = v_res_139_;
}
LEAN_EXPORT lean_object* l_Bool_instDecidableForallOfDecidablePred___redArg___boxed(lean_object* v_inst_140_){
_start:
{
uint8_t v_res_141_; lean_object* v_r_142_; 
v_res_141_ = l_Bool_instDecidableForallOfDecidablePred___redArg(v_inst_140_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
uint8_t l_Bool_instDecidableForallOfDecidablePred(lean_object* v_p_143_, lean_object* v_inst_144_){
_start:
{
uint8_t v___x_145_; 
v___x_145_ = l_Bool_instDecidableForallOfDecidablePred___redArg(v_inst_144_);
return v___x_145_;
}
}
LEAN_EXPORT void l_Bool_instDecidableForallOfDecidablePred_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_144_ = stack[1].m_obj;
uint8_t v_res_146_;
v_res_146_ = l_Bool_instDecidableForallOfDecidablePred(lean_box(0), v_inst_144_);
stack->m_num = v_res_146_;
}
LEAN_EXPORT lean_object* l_Bool_instDecidableForallOfDecidablePred___boxed(lean_object* v_p_147_, lean_object* v_inst_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Bool_instDecidableForallOfDecidablePred(v_p_147_, v_inst_148_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
uint8_t l_Bool_instDecidableExistsOfDecidablePred___redArg(lean_object* v_inst_151_){
_start:
{
uint8_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_152_ = 1;
v___x_153_ = lean_box(v___x_152_);
lean_inc_ref(v_inst_151_);
v___x_154_ = lean_apply_1(v_inst_151_, v___x_153_);
v___x_155_ = lean_unbox(v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = lean_apply_1(v_inst_151_, v___x_154_);
v___x_157_ = lean_unbox(v___x_156_);
return v___x_157_;
}
else
{
uint8_t v___x_158_; 
lean_dec_ref(v_inst_151_);
v___x_158_ = lean_unbox(v___x_154_);
return v___x_158_;
}
}
}
LEAN_EXPORT void l_Bool_instDecidableExistsOfDecidablePred___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_151_ = stack[0].m_obj;
uint8_t v_res_159_;
v_res_159_ = l_Bool_instDecidableExistsOfDecidablePred___redArg(v_inst_151_);
stack->m_num = v_res_159_;
}
LEAN_EXPORT lean_object* l_Bool_instDecidableExistsOfDecidablePred___redArg___boxed(lean_object* v_inst_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Bool_instDecidableExistsOfDecidablePred___redArg(v_inst_160_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
uint8_t l_Bool_instDecidableExistsOfDecidablePred(lean_object* v_p_163_, lean_object* v_inst_164_){
_start:
{
uint8_t v___x_165_; 
v___x_165_ = l_Bool_instDecidableExistsOfDecidablePred___redArg(v_inst_164_);
return v___x_165_;
}
}
LEAN_EXPORT void l_Bool_instDecidableExistsOfDecidablePred_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_164_ = stack[1].m_obj;
uint8_t v_res_166_;
v_res_166_ = l_Bool_instDecidableExistsOfDecidablePred(lean_box(0), v_inst_164_);
stack->m_num = v_res_166_;
}
LEAN_EXPORT lean_object* l_Bool_instDecidableExistsOfDecidablePred___boxed(lean_object* v_p_167_, lean_object* v_inst_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Bool_instDecidableExistsOfDecidablePred(v_p_167_, v_inst_168_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
static lean_object* _init_l_Bool_instLE(void){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_box(0);
return v___x_171_;
}
}
static lean_object* _init_l_Bool_instLT(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_box(0);
return v___x_172_;
}
}
uint8_t l_Bool_instDecidableLe(uint8_t v_x_173_, uint8_t v_y_174_){
_start:
{
if (v_x_173_ == 0)
{
uint8_t v___x_175_; 
v___x_175_ = 1;
return v___x_175_;
}
else
{
return v_y_174_;
}
}
}
LEAN_EXPORT void l_Bool_instDecidableLe_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_173_ = stack[0].m_num;
uint8_t v_y_174_ = stack[1].m_num;
uint8_t v_res_176_;
v_res_176_ = l_Bool_instDecidableLe(v_x_173_, v_y_174_);
stack->m_num = v_res_176_;
}
LEAN_EXPORT lean_object* l_Bool_instDecidableLe___boxed(lean_object* v_x_177_, lean_object* v_y_178_){
_start:
{
uint8_t v_x_boxed_179_; uint8_t v_y_boxed_180_; uint8_t v_res_181_; lean_object* v_r_182_; 
v_x_boxed_179_ = lean_unbox(v_x_177_);
v_y_boxed_180_ = lean_unbox(v_y_178_);
v_res_181_ = l_Bool_instDecidableLe(v_x_boxed_179_, v_y_boxed_180_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
uint8_t l_Bool_instDecidableLt(uint8_t v_x_183_, uint8_t v_y_184_){
_start:
{
if (v_x_183_ == 0)
{
return v_y_184_;
}
else
{
uint8_t v___x_185_; 
v___x_185_ = 0;
return v___x_185_;
}
}
}
LEAN_EXPORT void l_Bool_instDecidableLt_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_183_ = stack[0].m_num;
uint8_t v_y_184_ = stack[1].m_num;
uint8_t v_res_186_;
v_res_186_ = l_Bool_instDecidableLt(v_x_183_, v_y_184_);
stack->m_num = v_res_186_;
}
LEAN_EXPORT lean_object* l_Bool_instDecidableLt___boxed(lean_object* v_x_187_, lean_object* v_y_188_){
_start:
{
uint8_t v_x_boxed_189_; uint8_t v_y_boxed_190_; uint8_t v_res_191_; lean_object* v_r_192_; 
v_x_boxed_189_ = lean_unbox(v_x_187_);
v_y_boxed_190_ = lean_unbox(v_y_188_);
v_res_191_ = l_Bool_instDecidableLt(v_x_boxed_189_, v_y_boxed_190_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
uint8_t l_Bool_instMax___lam__0(uint8_t v_x_193_, uint8_t v_y_194_){
_start:
{
if (v_x_193_ == 0)
{
return v_y_194_;
}
else
{
return v_x_193_;
}
}
}
LEAN_EXPORT void l_Bool_instMax___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_193_ = stack[0].m_num;
uint8_t v_y_194_ = stack[1].m_num;
uint8_t v_res_195_;
v_res_195_ = l_Bool_instMax___lam__0(v_x_193_, v_y_194_);
stack->m_num = v_res_195_;
}
LEAN_EXPORT lean_object* l_Bool_instMax___lam__0___boxed(lean_object* v_x_196_, lean_object* v_y_197_){
_start:
{
uint8_t v_x_boxed_198_; uint8_t v_y_boxed_199_; uint8_t v_res_200_; lean_object* v_r_201_; 
v_x_boxed_198_ = lean_unbox(v_x_196_);
v_y_boxed_199_ = lean_unbox(v_y_197_);
v_res_200_ = l_Bool_instMax___lam__0(v_x_boxed_198_, v_y_boxed_199_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
uint8_t l_Bool_instMin___lam__0(uint8_t v_x_204_, uint8_t v_y_205_){
_start:
{
if (v_x_204_ == 0)
{
return v_x_204_;
}
else
{
return v_y_205_;
}
}
}
LEAN_EXPORT void l_Bool_instMin___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_204_ = stack[0].m_num;
uint8_t v_y_205_ = stack[1].m_num;
uint8_t v_res_206_;
v_res_206_ = l_Bool_instMin___lam__0(v_x_204_, v_y_205_);
stack->m_num = v_res_206_;
}
LEAN_EXPORT lean_object* l_Bool_instMin___lam__0___boxed(lean_object* v_x_207_, lean_object* v_y_208_){
_start:
{
uint8_t v_x_boxed_209_; uint8_t v_y_boxed_210_; uint8_t v_res_211_; lean_object* v_r_212_; 
v_x_boxed_209_ = lean_unbox(v_x_207_);
v_y_boxed_210_ = lean_unbox(v_y_208_);
v_res_211_ = l_Bool_instMin___lam__0(v_x_boxed_209_, v_y_boxed_210_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
lean_object* l_Bool_toNat(uint8_t v_b_215_){
_start:
{
if (v_b_215_ == 0)
{
lean_object* v___x_216_; 
v___x_216_ = lean_unsigned_to_nat(0u);
return v___x_216_;
}
else
{
lean_object* v___x_217_; 
v___x_217_ = lean_unsigned_to_nat(1u);
return v___x_217_;
}
}
}
LEAN_EXPORT void l_Bool_toNat_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_215_ = stack[0].m_num;
lean_object* v_res_218_;
v_res_218_ = l_Bool_toNat(v_b_215_);
stack->m_obj
 = v_res_218_;
}
LEAN_EXPORT lean_object* l_Bool_toNat___boxed(lean_object* v_b_219_){
_start:
{
uint8_t v_b_boxed_220_; lean_object* v_res_221_; 
v_b_boxed_220_ = lean_unbox(v_b_219_);
v_res_221_ = l_Bool_toNat(v_b_boxed_220_);
return v_res_221_;
}
}
static lean_object* _init_l_Bool_toInt___closed__0(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_nat_to_int(v___x_222_);
return v___x_223_;
}
}
static lean_object* _init_l_Bool_toInt___closed__1(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_nat_to_int(v___x_224_);
return v___x_225_;
}
}
lean_object* l_Bool_toInt(uint8_t v_b_226_){
_start:
{
if (v_b_226_ == 0)
{
lean_object* v___x_227_; 
v___x_227_ = lean_obj_once(&l_Bool_toInt___closed__0, &l_Bool_toInt___closed__0_once, _init_l_Bool_toInt___closed__0);
return v___x_227_;
}
else
{
lean_object* v___x_228_; 
v___x_228_ = lean_obj_once(&l_Bool_toInt___closed__1, &l_Bool_toInt___closed__1_once, _init_l_Bool_toInt___closed__1);
return v___x_228_;
}
}
}
LEAN_EXPORT void l_Bool_toInt_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_226_ = stack[0].m_num;
lean_object* v_res_229_;
v_res_229_ = l_Bool_toInt(v_b_226_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l_Bool_toInt___boxed(lean_object* v_b_230_){
_start:
{
uint8_t v_b_boxed_231_; lean_object* v_res_232_; 
v_b_boxed_231_ = lean_unbox(v_b_230_);
v_res_232_ = l_Bool_toInt(v_b_boxed_231_);
return v_res_232_;
}
}
lean_object* l_boolPredToPred___redArg(){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_box(0);
return v___x_234_;
}
}
LEAN_EXPORT void l_boolPredToPred___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_235_;
v_res_235_ = l_boolPredToPred___redArg();
stack->m_obj
 = v_res_235_;
}
LEAN_EXPORT lean_object* l_boolPredToPred___redArg___boxed(lean_object* v___dummy_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_boolPredToPred___redArg();
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_boolPredToPred(lean_object* v_00_u03b1_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = lean_box(0);
return v___x_239_;
}
}
lean_object* l_boolRelToRel___redArg(){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_box(0);
return v___x_241_;
}
}
LEAN_EXPORT void l_boolRelToRel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_242_;
v_res_242_ = l_boolRelToRel___redArg();
stack->m_obj
 = v_res_242_;
}
LEAN_EXPORT lean_object* l_boolRelToRel___redArg___boxed(lean_object* v___dummy_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_boolRelToRel___redArg();
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_boolRelToRel(lean_object* v_00_u03b1_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_box(0);
return v___x_246_;
}
}
uint8_t l_Bool_and_x27(uint8_t v_a_247_, uint8_t v_b_248_){
_start:
{
if (v_a_247_ == 0)
{
return v_a_247_;
}
else
{
return v_b_248_;
}
}
}
LEAN_EXPORT void l_Bool_and_x27_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_247_ = stack[0].m_num;
uint8_t v_b_248_ = stack[1].m_num;
uint8_t v_res_249_;
v_res_249_ = l_Bool_and_x27(v_a_247_, v_b_248_);
stack->m_num = v_res_249_;
}
LEAN_EXPORT lean_object* l_Bool_and_x27___boxed(lean_object* v_a_250_, lean_object* v_b_251_){
_start:
{
uint8_t v_a_boxed_252_; uint8_t v_b_boxed_253_; uint8_t v_res_254_; lean_object* v_r_255_; 
v_a_boxed_252_ = lean_unbox(v_a_250_);
v_b_boxed_253_ = lean_unbox(v_b_251_);
v_res_254_ = l_Bool_and_x27(v_a_boxed_252_, v_b_boxed_253_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
uint8_t l_Bool_or_x27(uint8_t v_a_256_, uint8_t v_b_257_){
_start:
{
if (v_a_256_ == 0)
{
return v_b_257_;
}
else
{
return v_a_256_;
}
}
}
LEAN_EXPORT void l_Bool_or_x27_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_256_ = stack[0].m_num;
uint8_t v_b_257_ = stack[1].m_num;
uint8_t v_res_258_;
v_res_258_ = l_Bool_or_x27(v_a_256_, v_b_257_);
stack->m_num = v_res_258_;
}
LEAN_EXPORT lean_object* l_Bool_or_x27___boxed(lean_object* v_a_259_, lean_object* v_b_260_){
_start:
{
uint8_t v_a_boxed_261_; uint8_t v_b_boxed_262_; uint8_t v_res_263_; lean_object* v_r_264_; 
v_a_boxed_261_ = lean_unbox(v_a_259_);
v_b_boxed_262_ = lean_unbox(v_b_260_);
v_res_263_ = l_Bool_or_x27(v_a_boxed_261_, v_b_boxed_262_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
}
}
uint8_t l_Bool_not_x27(uint8_t v_a_265_){
_start:
{
if (v_a_265_ == 0)
{
uint8_t v___x_266_; 
v___x_266_ = 1;
return v___x_266_;
}
else
{
uint8_t v___x_267_; 
v___x_267_ = 0;
return v___x_267_;
}
}
}
LEAN_EXPORT void l_Bool_not_x27_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_265_ = stack[0].m_num;
uint8_t v_res_268_;
v_res_268_ = l_Bool_not_x27(v_a_265_);
stack->m_num = v_res_268_;
}
LEAN_EXPORT lean_object* l_Bool_not_x27___boxed(lean_object* v_a_269_){
_start:
{
uint8_t v_a_boxed_270_; uint8_t v_res_271_; lean_object* v_r_272_; 
v_a_boxed_270_ = lean_unbox(v_a_269_);
v_res_271_ = l_Bool_not_x27(v_a_boxed_270_);
v_r_272_ = lean_box(v_res_271_);
return v_r_272_;
}
}
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
