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
LEAN_EXPORT lean_object* l_boolPredToPred(lean_object*);
LEAN_EXPORT lean_object* l_boolRelToRel(lean_object*);
LEAN_EXPORT uint8_t l_Bool_xor(uint8_t v_a_1_, uint8_t v_b_2_){
_start:
{
if (v_a_1_ == 0)
{
return v_b_2_;
}
else
{
if (v_b_2_ == 0)
{
return v_a_1_;
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
LEAN_EXPORT lean_object* l_Bool_xor___boxed(lean_object* v_a_4_, lean_object* v_b_5_){
_start:
{
uint8_t v_a_boxed_6_; uint8_t v_b_boxed_7_; uint8_t v_res_8_; lean_object* v_r_9_; 
v_a_boxed_6_ = lean_unbox(v_a_4_);
v_b_boxed_7_ = lean_unbox(v_b_5_);
v_res_8_ = l_Bool_xor(v_a_boxed_6_, v_b_boxed_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
static lean_object* _init_l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__5));
v___x_47_ = l_String_toRawSubstring_x27(v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1(lean_object* v_x_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = ((lean_object*)(l_Bool_term___x5e_x5e___00__closed__2));
lean_inc(v_x_62_);
v___x_66_ = l_Lean_Syntax_isOfKind(v_x_62_, v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v_x_62_);
v___x_67_ = lean_box(1);
v___x_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v_a_64_);
return v___x_68_;
}
else
{
lean_object* v_quotContext_69_; lean_object* v_currMacroScope_70_; lean_object* v_ref_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_quotContext_69_ = lean_ctor_get(v_a_63_, 1);
v_currMacroScope_70_ = lean_ctor_get(v_a_63_, 2);
v_ref_71_ = lean_ctor_get(v_a_63_, 5);
v___x_72_ = lean_unsigned_to_nat(0u);
v___x_73_ = l_Lean_Syntax_getArg(v_x_62_, v___x_72_);
v___x_74_ = lean_unsigned_to_nat(2u);
v___x_75_ = l_Lean_Syntax_getArg(v_x_62_, v___x_74_);
lean_dec(v_x_62_);
v___x_76_ = 0;
v___x_77_ = l_Lean_SourceInfo_fromRef(v_ref_71_, v___x_76_);
v___x_78_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4));
v___x_79_ = lean_obj_once(&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6, &l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6_once, _init_l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6);
v___x_80_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__7));
lean_inc(v_currMacroScope_70_);
lean_inc(v_quotContext_69_);
v___x_81_ = l_Lean_addMacroScope(v_quotContext_69_, v___x_80_, v_currMacroScope_70_);
v___x_82_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__10));
lean_inc_n(v___x_77_, 2);
v___x_83_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_83_, 0, v___x_77_);
lean_ctor_set(v___x_83_, 1, v___x_79_);
lean_ctor_set(v___x_83_, 2, v___x_81_);
lean_ctor_set(v___x_83_, 3, v___x_82_);
v___x_84_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__12));
v___x_85_ = l_Lean_Syntax_node2(v___x_77_, v___x_84_, v___x_73_, v___x_75_);
v___x_86_ = l_Lean_Syntax_node2(v___x_77_, v___x_78_, v___x_83_, v___x_85_);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v_a_64_);
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___boxed(lean_object* v_x_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1(v_x_88_, v_a_89_, v_a_90_);
lean_dec_ref(v_a_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1(lean_object* v_x_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4));
lean_inc(v_x_95_);
v___x_99_ = l_Lean_Syntax_isOfKind(v_x_95_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v_x_95_);
v___x_100_ = lean_box(0);
v___x_101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v_a_97_);
return v___x_101_;
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = l_Lean_Syntax_getArg(v_x_95_, v___x_102_);
v___x_104_ = ((lean_object*)(l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__1));
lean_inc(v___x_103_);
v___x_105_ = l_Lean_Syntax_isOfKind(v___x_103_, v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; 
lean_dec(v___x_103_);
lean_dec(v_x_95_);
v___x_106_ = lean_box(0);
v___x_107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v_a_97_);
return v___x_107_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = l_Lean_Syntax_getArg(v_x_95_, v___x_108_);
lean_dec(v_x_95_);
v___x_110_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_109_);
v___x_111_ = l_Lean_Syntax_matchesNull(v___x_109_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec(v___x_109_);
lean_dec(v___x_103_);
v___x_112_ = lean_box(0);
v___x_113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v_a_97_);
return v___x_113_;
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v_ref_116_; uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_114_ = l_Lean_Syntax_getArg(v___x_109_, v___x_102_);
v___x_115_ = l_Lean_Syntax_getArg(v___x_109_, v___x_108_);
lean_dec(v___x_109_);
v_ref_116_ = l_Lean_replaceRef(v___x_103_, v_a_96_);
lean_dec(v___x_103_);
v___x_117_ = 0;
v___x_118_ = l_Lean_SourceInfo_fromRef(v_ref_116_, v___x_117_);
lean_dec(v_ref_116_);
v___x_119_ = ((lean_object*)(l_Bool_term___x5e_x5e___00__closed__2));
v___x_120_ = ((lean_object*)(l_Bool_term___x5e_x5e___00__closed__5));
lean_inc(v___x_118_);
v___x_121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_118_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = l_Lean_Syntax_node3(v___x_118_, v___x_119_, v___x_114_, v___x_121_, v___x_115_);
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v_a_97_);
return v___x_123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___boxed(lean_object* v_x_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1(v_x_124_, v_a_125_, v_a_126_);
lean_dec(v_a_125_);
return v_res_127_;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableForallOfDecidablePred___redArg(lean_object* v_inst_128_){
_start:
{
uint8_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_129_ = 1;
v___x_130_ = lean_box(v___x_129_);
lean_inc_ref(v_inst_128_);
v___x_131_ = lean_apply_1(v_inst_128_, v___x_130_);
v___x_132_ = lean_unbox(v___x_131_);
if (v___x_132_ == 0)
{
uint8_t v___x_133_; 
lean_dec_ref(v_inst_128_);
v___x_133_ = lean_unbox(v___x_131_);
return v___x_133_;
}
else
{
uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_134_ = 0;
v___x_135_ = lean_box(v___x_134_);
v___x_136_ = lean_apply_1(v_inst_128_, v___x_135_);
v___x_137_ = lean_unbox(v___x_136_);
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableForallOfDecidablePred___redArg___boxed(lean_object* v_inst_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Bool_instDecidableForallOfDecidablePred___redArg(v_inst_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableForallOfDecidablePred(lean_object* v_p_141_, lean_object* v_inst_142_){
_start:
{
uint8_t v___x_143_; 
v___x_143_ = l_Bool_instDecidableForallOfDecidablePred___redArg(v_inst_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableForallOfDecidablePred___boxed(lean_object* v_p_144_, lean_object* v_inst_145_){
_start:
{
uint8_t v_res_146_; lean_object* v_r_147_; 
v_res_146_ = l_Bool_instDecidableForallOfDecidablePred(v_p_144_, v_inst_145_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableExistsOfDecidablePred___redArg(lean_object* v_inst_148_){
_start:
{
uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_149_ = 1;
v___x_150_ = lean_box(v___x_149_);
lean_inc_ref(v_inst_148_);
v___x_151_ = lean_apply_1(v_inst_148_, v___x_150_);
v___x_152_ = lean_unbox(v___x_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = lean_apply_1(v_inst_148_, v___x_151_);
v___x_154_ = lean_unbox(v___x_153_);
return v___x_154_;
}
else
{
uint8_t v___x_155_; 
lean_dec_ref(v_inst_148_);
v___x_155_ = lean_unbox(v___x_151_);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableExistsOfDecidablePred___redArg___boxed(lean_object* v_inst_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Bool_instDecidableExistsOfDecidablePred___redArg(v_inst_156_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableExistsOfDecidablePred(lean_object* v_p_159_, lean_object* v_inst_160_){
_start:
{
uint8_t v___x_161_; 
v___x_161_ = l_Bool_instDecidableExistsOfDecidablePred___redArg(v_inst_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableExistsOfDecidablePred___boxed(lean_object* v_p_162_, lean_object* v_inst_163_){
_start:
{
uint8_t v_res_164_; lean_object* v_r_165_; 
v_res_164_ = l_Bool_instDecidableExistsOfDecidablePred(v_p_162_, v_inst_163_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
static lean_object* _init_l_Bool_instLE(void){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_box(0);
return v___x_166_;
}
}
static lean_object* _init_l_Bool_instLT(void){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_box(0);
return v___x_167_;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableLe(uint8_t v_x_168_, uint8_t v_y_169_){
_start:
{
if (v_x_168_ == 0)
{
uint8_t v___x_170_; 
v___x_170_ = 1;
return v___x_170_;
}
else
{
return v_y_169_;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableLe___boxed(lean_object* v_x_171_, lean_object* v_y_172_){
_start:
{
uint8_t v_x_boxed_173_; uint8_t v_y_boxed_174_; uint8_t v_res_175_; lean_object* v_r_176_; 
v_x_boxed_173_ = lean_unbox(v_x_171_);
v_y_boxed_174_ = lean_unbox(v_y_172_);
v_res_175_ = l_Bool_instDecidableLe(v_x_boxed_173_, v_y_boxed_174_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableLt(uint8_t v_x_177_, uint8_t v_y_178_){
_start:
{
if (v_x_177_ == 0)
{
return v_y_178_;
}
else
{
uint8_t v___x_179_; 
v___x_179_ = 0;
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableLt___boxed(lean_object* v_x_180_, lean_object* v_y_181_){
_start:
{
uint8_t v_x_boxed_182_; uint8_t v_y_boxed_183_; uint8_t v_res_184_; lean_object* v_r_185_; 
v_x_boxed_182_ = lean_unbox(v_x_180_);
v_y_boxed_183_ = lean_unbox(v_y_181_);
v_res_184_ = l_Bool_instDecidableLt(v_x_boxed_182_, v_y_boxed_183_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT uint8_t l_Bool_instMax___lam__0(uint8_t v_x_186_, uint8_t v_y_187_){
_start:
{
if (v_x_186_ == 0)
{
return v_y_187_;
}
else
{
return v_x_186_;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instMax___lam__0___boxed(lean_object* v_x_188_, lean_object* v_y_189_){
_start:
{
uint8_t v_x_boxed_190_; uint8_t v_y_boxed_191_; uint8_t v_res_192_; lean_object* v_r_193_; 
v_x_boxed_190_ = lean_unbox(v_x_188_);
v_y_boxed_191_ = lean_unbox(v_y_189_);
v_res_192_ = l_Bool_instMax___lam__0(v_x_boxed_190_, v_y_boxed_191_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT uint8_t l_Bool_instMin___lam__0(uint8_t v_x_196_, uint8_t v_y_197_){
_start:
{
if (v_x_196_ == 0)
{
return v_x_196_;
}
else
{
return v_y_197_;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instMin___lam__0___boxed(lean_object* v_x_198_, lean_object* v_y_199_){
_start:
{
uint8_t v_x_boxed_200_; uint8_t v_y_boxed_201_; uint8_t v_res_202_; lean_object* v_r_203_; 
v_x_boxed_200_ = lean_unbox(v_x_198_);
v_y_boxed_201_ = lean_unbox(v_y_199_);
v_res_202_ = l_Bool_instMin___lam__0(v_x_boxed_200_, v_y_boxed_201_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT lean_object* l_Bool_toNat(uint8_t v_b_206_){
_start:
{
if (v_b_206_ == 0)
{
lean_object* v___x_207_; 
v___x_207_ = lean_unsigned_to_nat(0u);
return v___x_207_;
}
else
{
lean_object* v___x_208_; 
v___x_208_ = lean_unsigned_to_nat(1u);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_Bool_toNat___boxed(lean_object* v_b_209_){
_start:
{
uint8_t v_b_boxed_210_; lean_object* v_res_211_; 
v_b_boxed_210_ = lean_unbox(v_b_209_);
v_res_211_ = l_Bool_toNat(v_b_boxed_210_);
return v_res_211_;
}
}
static lean_object* _init_l_Bool_toInt___closed__0(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = lean_nat_to_int(v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_Bool_toInt___closed__1(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_nat_to_int(v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt(uint8_t v_b_216_){
_start:
{
if (v_b_216_ == 0)
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&l_Bool_toInt___closed__0, &l_Bool_toInt___closed__0_once, _init_l_Bool_toInt___closed__0);
return v___x_217_;
}
else
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&l_Bool_toInt___closed__1, &l_Bool_toInt___closed__1_once, _init_l_Bool_toInt___closed__1);
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l_Bool_toInt___boxed(lean_object* v_b_219_){
_start:
{
uint8_t v_b_boxed_220_; lean_object* v_res_221_; 
v_b_boxed_220_ = lean_unbox(v_b_219_);
v_res_221_ = l_Bool_toInt(v_b_boxed_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_boolPredToPred(lean_object* v_00_u03b1_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_box(0);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_boolRelToRel(lean_object* v_00_u03b1_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = lean_box(0);
return v___x_225_;
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
