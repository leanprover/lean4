// Lean compiler output
// Module: Lean.Meta.NatTable
// Imports: public import Lean.Meta.Basic import Lean.Meta.InferType import Init.Omega
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
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0_value;
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5;
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value;
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__8 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__8_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__9 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__9_value;
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__10 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(138, 49, 229, 237, 137, 52, 176, 206)}};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value;
lean_object* l_Lean_mkAtom(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__12;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__13;
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__14 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__16;
static lean_once_cell_t l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__17;
static lean_once_cell_t l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__18;
static lean_once_cell_t l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__19;
static lean_once_cell_t l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__20;
static lean_once_cell_t l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__21;
static lean_once_cell_t l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__22;
static lean_once_cell_t l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__23;
static lean_once_cell_t l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__24;
static lean_once_cell_t l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__25;
static lean_once_cell_t l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26;
LEAN_EXPORT lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__3;
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ble"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__3_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(18, 188, 15, 95, 29, 42, 30, 33)}};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__4_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00mkNatLookupTable_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00mkNatLookupTable_spec__0___closed__0 = (const lean_object*)&l_panic___at___00mkNatLookupTable_spec__0___closed__0_value;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00mkNatLookupTable_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00mkNatLookupTable_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_mkNatLookupTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Meta.NatTable"};
static const lean_object* l_mkNatLookupTable___closed__0 = (const lean_object*)&l_mkNatLookupTable___closed__0_value;
static const lean_string_object l_mkNatLookupTable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "mkNatLookupTable"};
static const lean_object* l_mkNatLookupTable___closed__1 = (const lean_object*)&l_mkNatLookupTable___closed__1_value;
static const lean_string_object l_mkNatLookupTable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "mkNatLookupTable: expected non-empty array"};
static const lean_object* l_mkNatLookupTable___closed__2 = (const lean_object*)&l_mkNatLookupTable___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_mkNatLookupTable___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkNatLookupTable___closed__3;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkNatLookupTable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkNatLookupTable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__10));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__12, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__12_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__12);
x_2 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5);
x_2 = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__16, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__16_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__16);
x_2 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__17, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__17_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__17);
x_2 = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__18, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__18_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__18);
x_2 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__13, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__13_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__13);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__19, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__19_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__19);
x_2 = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__20, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__20_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__20);
x_2 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__21, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__21_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__21);
x_2 = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__22, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__22_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__22);
x_2 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__23, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__23_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__23);
x_2 = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__25(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__24, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__24_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__24);
x_2 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__25, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__25_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__25);
x_2 = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__3(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_5, x_8);
x_10 = lean_nat_dec_eq(x_9, x_6);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_nat_add(x_5, x_6);
x_12 = lean_nat_shiftr(x_11, x_8);
lean_dec(x_11);
lean_inc(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_13 = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(x_1, x_2, x_3, x_4, x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_15 = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(x_1, x_2, x_3, x_4, x_12, x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__1));
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_mkConst(x_18, x_20);
x_22 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5);
x_23 = lean_nat_sub(x_12, x_8);
lean_dec(x_12);
x_24 = l_Lean_mkRawNatLit(x_23);
x_25 = l_Lean_mkAppB(x_22, x_1, x_24);
x_26 = l_Lean_mkApp4(x_21, x_2, x_25, x_14, x_17);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
lean_dec(x_15);
x_28 = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__1));
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_mkConst(x_28, x_30);
x_32 = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5);
x_33 = lean_nat_sub(x_12, x_8);
lean_dec(x_12);
x_34 = l_Lean_mkRawNatLit(x_33);
x_35 = l_Lean_mkAppB(x_32, x_1, x_34);
x_36 = l_Lean_mkApp4(x_31, x_2, x_35, x_14, x_27);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_38 = lean_array_fget_borrowed(x_3, x_5);
lean_inc(x_38);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_panic___at___00mkNatLookupTable_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = ((lean_object*)(l_panic___at___00mkNatLookupTable_spec__0___closed__0));
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___00mkNatLookupTable_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00mkNatLookupTable_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_mkNatLookupTable___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_mkNatLookupTable___closed__2));
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(25u);
x_4 = ((lean_object*)(l_mkNatLookupTable___closed__1));
x_5 = ((lean_object*)(l_mkNatLookupTable___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_mkNatLookupTable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_inc_ref(x_2);
x_12 = l_Lean_Meta_getLevel(x_2, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(x_1, x_2, x_3, x_13, x_10, x_9);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = lean_obj_once(&l_mkNatLookupTable___closed__3, &l_mkNatLookupTable___closed__3_once, _init_l_mkNatLookupTable___closed__3);
x_19 = l_panic___at___00mkNatLookupTable_spec__0(x_18, x_4, x_5, x_6, x_7);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_mkNatLookupTable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_mkNatLookupTable(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
return x_9;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_NatTable(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1 = _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1();
lean_mark_persistent(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1);
l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__3 = _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__3();
lean_mark_persistent(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
