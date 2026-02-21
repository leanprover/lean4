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
LEAN_EXPORT uint8_t l_Bool_xor(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Bool_xor___boxed(lean_object*, lean_object*);
static const lean_string_object l_Bool_term___x5e_x5e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Bool_term___x5e_x5e___00__closed__0 = (const lean_object*)&l_Bool_term___x5e_x5e___00__closed__0_value;
static const lean_string_object l_Bool_term___x5e_x5e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_^^_"};
static const lean_object* l_Bool_term___x5e_x5e___00__closed__1 = (const lean_object*)&l_Bool_term___x5e_x5e___00__closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Bool_term___x5e_x5e___00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Bool_term___x5e_x5e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Bool_term___x5e_x5e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Bool_term___x5e_x5e___00__closed__2_value_aux_0),((lean_object*)&l_Bool_term___x5e_x5e___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(108, 188, 171, 230, 73, 21, 37, 140)}};
static const lean_object* l_Bool_term___x5e_x5e___00__closed__2 = (const lean_object*)&l_Bool_term___x5e_x5e___00__closed__2_value;
static const lean_string_object l_Bool_term___x5e_x5e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Bool_term___x5e_x5e___00__closed__3 = (const lean_object*)&l_Bool_term___x5e_x5e___00__closed__3_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value_aux_0),((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value_aux_1),((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value_aux_2),((lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4 = (const lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4_value;
static const lean_string_object l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "xor"};
static const lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__5 = (const lean_object*)&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__5_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__0 = (const lean_object*)&l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__0_value;
static const lean_ctor_object l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__1 = (const lean_object*)&l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__1_value;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Bool_toInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Bool_toInt___closed__0;
static lean_once_cell_t l_Bool_toInt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Bool_toInt___closed__1;
LEAN_EXPORT lean_object* l_Bool_toInt(uint8_t);
LEAN_EXPORT lean_object* l_Bool_toInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_boolPredToPred(lean_object*);
LEAN_EXPORT lean_object* l_boolRelToRel(lean_object*);
LEAN_EXPORT uint8_t l_Bool_xor(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
return x_2;
}
else
{
if (x_2 == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_Bool_xor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Bool_xor(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__5));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Bool_term___x5e_x5e___00__closed__2));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = 0;
x_16 = l_Lean_SourceInfo_fromRef(x_10, x_15);
lean_dec(x_10);
x_17 = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4));
x_18 = lean_obj_once(&l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6, &l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6_once, _init_l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__6);
x_19 = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__7));
x_20 = l_Lean_addMacroScope(x_8, x_19, x_9);
x_21 = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__10));
lean_inc(x_16);
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
x_23 = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__12));
lean_inc(x_16);
x_24 = l_Lean_Syntax_node2(x_16, x_23, x_12, x_14);
x_25 = l_Lean_Syntax_node2(x_16, x_17, x_22, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1___closed__4));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = ((lean_object*)(l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___closed__1));
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(2u);
lean_inc(x_15);
x_17 = l_Lean_Syntax_matchesNull(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = l_Lean_Syntax_getArg(x_15, x_8);
x_21 = l_Lean_Syntax_getArg(x_15, x_14);
lean_dec(x_15);
x_22 = l_Lean_replaceRef(x_9, x_2);
lean_dec(x_9);
x_23 = 0;
x_24 = l_Lean_SourceInfo_fromRef(x_22, x_23);
lean_dec(x_22);
x_25 = ((lean_object*)(l_Bool_term___x5e_x5e___00__closed__2));
x_26 = ((lean_object*)(l_Bool_term___x5e_x5e___00__closed__5));
lean_inc(x_24);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Syntax_node3(x_24, x_25, x_20, x_27, x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableForallOfDecidablePred___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = 1;
x_3 = lean_box(x_2);
lean_inc_ref(x_1);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec_ref(x_1);
x_6 = lean_unbox(x_4);
return x_6;
}
else
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableForallOfDecidablePred___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Bool_instDecidableForallOfDecidablePred___redArg(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableForallOfDecidablePred(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Bool_instDecidableForallOfDecidablePred___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableForallOfDecidablePred___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Bool_instDecidableForallOfDecidablePred(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableExistsOfDecidablePred___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = 1;
x_3 = lean_box(x_2);
lean_inc_ref(x_1);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec_ref(x_1);
x_8 = lean_unbox(x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableExistsOfDecidablePred___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Bool_instDecidableExistsOfDecidablePred___redArg(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableExistsOfDecidablePred(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Bool_instDecidableExistsOfDecidablePred___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableExistsOfDecidablePred___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Bool_instDecidableExistsOfDecidablePred(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Bool_instLE(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Bool_instLT(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableLe(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Bool_instDecidableLe(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableLt(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Bool_instDecidableLt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Bool_instMax___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
return x_2;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instMax___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Bool_instMax___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Bool_instMin___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instMin___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Bool_instMin___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Bool_toNat(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Bool_toNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Bool_toNat(x_2);
return x_3;
}
}
static lean_object* _init_l_Bool_toInt___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Bool_toInt___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Bool_toInt___closed__0, &l_Bool_toInt___closed__0_once, _init_l_Bool_toInt___closed__0);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_obj_once(&l_Bool_toInt___closed__1, &l_Bool_toInt___closed__1_once, _init_l_Bool_toInt___closed__1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Bool_toInt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Bool_toInt(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_boolPredToPred(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_boolRelToRel(lean_object* x_1) {
_start:
{
return lean_box(0);
}
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
l_Bool_instLE = _init_l_Bool_instLE();
lean_mark_persistent(l_Bool_instLE);
l_Bool_instLT = _init_l_Bool_instLT();
lean_mark_persistent(l_Bool_instLT);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
