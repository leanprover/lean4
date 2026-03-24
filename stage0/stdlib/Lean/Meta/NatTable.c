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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0_value;
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4_value;
static const lean_array_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5_value;
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7_value;
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__8 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__9 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__9_value;
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__10 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(138, 49, 229, 237, 137, 52, 176, 206)}};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__12;
static lean_once_cell_t l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__13;
static const lean_string_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__14 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__9_value),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5_value)}};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__16 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__16_value;
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
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(18, 188, 15, 95, 29, 42, 30, 33)}};
static const lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00mkNatLookupTable_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00mkNatLookupTable_spec__0___closed__0 = (const lean_object*)&l_panic___at___00mkNatLookupTable_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00mkNatLookupTable_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00mkNatLookupTable_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_mkNatLookupTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Meta.NatTable"};
static const lean_object* l_mkNatLookupTable___closed__0 = (const lean_object*)&l_mkNatLookupTable___closed__0_value;
static const lean_string_object l_mkNatLookupTable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "mkNatLookupTable"};
static const lean_object* l_mkNatLookupTable___closed__1 = (const lean_object*)&l_mkNatLookupTable___closed__1_value;
static const lean_string_object l_mkNatLookupTable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "mkNatLookupTable: expected non-empty array"};
static const lean_object* l_mkNatLookupTable___closed__2 = (const lean_object*)&l_mkNatLookupTable___closed__2_value;
static lean_once_cell_t l_mkNatLookupTable___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkNatLookupTable___closed__3;
LEAN_EXPORT lean_object* l_mkNatLookupTable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkNatLookupTable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__12, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__12_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__17(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__16));
v___x_43_ = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5));
v___x_44_ = lean_array_push(v___x_43_, v___x_42_);
return v___x_44_;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__18(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_45_ = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__17, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__17_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__17);
v___x_46_ = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__15));
v___x_47_ = lean_box(2);
v___x_48_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_46_);
lean_ctor_set(v___x_48_, 2, v___x_45_);
return v___x_48_;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__19(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__18, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__18_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__18);
v___x_50_ = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__13, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__13_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__13);
v___x_51_ = lean_array_push(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__20(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__19, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__19_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__19);
v___x_53_ = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__11));
v___x_54_ = lean_box(2);
v___x_55_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
lean_ctor_set(v___x_55_, 2, v___x_52_);
return v___x_55_;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__21(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__20, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__20_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__20);
v___x_57_ = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5));
v___x_58_ = lean_array_push(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__22(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__21, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__21_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__21);
v___x_60_ = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__9));
v___x_61_ = lean_box(2);
v___x_62_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
lean_ctor_set(v___x_62_, 2, v___x_59_);
return v___x_62_;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__23(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__22, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__22_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__22);
v___x_64_ = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5));
v___x_65_ = lean_array_push(v___x_64_, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__24(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__23, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__23_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__23);
v___x_67_ = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__7));
v___x_68_ = lean_box(2);
v___x_69_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_66_);
return v___x_69_;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__25(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__24, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__24_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__24);
v___x_71_ = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__5));
v___x_72_ = lean_array_push(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__25, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__25_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__25);
v___x_74_ = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__4));
v___x_75_ = lean_box(2);
v___x_76_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
lean_ctor_set(v___x_76_, 2, v___x_73_);
return v___x_76_;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26);
return v___x_77_;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__3(void){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1___closed__26);
return v___x_78_;
}
}
static lean_object* _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_box(0);
v___x_88_ = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__4));
v___x_89_ = l_Lean_mkConst(v___x_88_, v___x_87_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(lean_object* v_i_90_, lean_object* v_type_91_, lean_object* v_es_92_, lean_object* v_u_93_, lean_object* v_start_94_, lean_object* v_stop_95_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = lean_nat_add(v_start_94_, v___x_97_);
v___x_99_ = lean_nat_dec_eq(v___x_98_, v_stop_95_);
lean_dec(v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v_mid_101_; lean_object* v___x_102_; lean_object* v_a_103_; lean_object* v___x_104_; lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_121_; 
v___x_100_ = lean_nat_add(v_start_94_, v_stop_95_);
v_mid_101_ = lean_nat_shiftr(v___x_100_, v___x_97_);
lean_dec(v___x_100_);
lean_inc(v_u_93_);
lean_inc_ref(v_type_91_);
lean_inc_ref(v_i_90_);
v___x_102_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(v_i_90_, v_type_91_, v_es_92_, v_u_93_, v_start_94_, v_mid_101_);
v_a_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_103_);
lean_dec_ref(v___x_102_);
lean_inc(v_u_93_);
lean_inc_ref(v_type_91_);
lean_inc_ref(v_i_90_);
v___x_104_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(v_i_90_, v_type_91_, v_es_92_, v_u_93_, v_mid_101_, v_stop_95_);
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_121_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_121_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_121_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_109_ = ((lean_object*)(l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__1));
v___x_110_ = lean_box(0);
v___x_111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_111_, 0, v_u_93_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = l_Lean_mkConst(v___x_109_, v___x_111_);
v___x_113_ = lean_obj_once(&l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5, &l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5_once, _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___closed__5);
v___x_114_ = lean_nat_sub(v_mid_101_, v___x_97_);
lean_dec(v_mid_101_);
v___x_115_ = l_Lean_mkRawNatLit(v___x_114_);
v___x_116_ = l_Lean_mkAppB(v___x_113_, v_i_90_, v___x_115_);
v___x_117_ = l_Lean_mkApp4(v___x_112_, v_type_91_, v___x_116_, v_a_103_, v_a_105_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_117_);
v___x_119_ = v___x_107_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
else
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v_u_93_);
lean_dec_ref(v_type_91_);
lean_dec_ref(v_i_90_);
v___x_122_ = lean_array_fget_borrowed(v_es_92_, v_start_94_);
lean_inc(v___x_122_);
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg___boxed(lean_object* v_i_124_, lean_object* v_type_125_, lean_object* v_es_126_, lean_object* v_u_127_, lean_object* v_start_128_, lean_object* v_stop_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(v_i_124_, v_type_125_, v_es_126_, v_u_127_, v_start_128_, v_stop_129_);
lean_dec(v_stop_129_);
lean_dec(v_start_128_);
lean_dec_ref(v_es_126_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go(lean_object* v_i_132_, lean_object* v_type_133_, lean_object* v_es_134_, lean_object* v_u_135_, lean_object* v_start_136_, lean_object* v_stop_137_, lean_object* v_hstart_138_, lean_object* v_hstop_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(v_i_132_, v_type_133_, v_es_134_, v_u_135_, v_start_136_, v_stop_137_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___boxed(lean_object* v_i_146_, lean_object* v_type_147_, lean_object* v_es_148_, lean_object* v_u_149_, lean_object* v_start_150_, lean_object* v_stop_151_, lean_object* v_hstart_152_, lean_object* v_hstop_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go(v_i_146_, v_type_147_, v_es_148_, v_u_149_, v_start_150_, v_stop_151_, v_hstart_152_, v_hstop_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_stop_151_);
lean_dec(v_start_150_);
lean_dec_ref(v_es_148_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00mkNatLookupTable_spec__0(lean_object* v_msg_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___f_167_; lean_object* v___x_133__overap_168_; lean_object* v___x_169_; 
v___f_167_ = ((lean_object*)(l_panic___at___00mkNatLookupTable_spec__0___closed__0));
v___x_133__overap_168_ = lean_panic_fn(v___f_167_, v_msg_161_);
lean_inc(v___y_165_);
lean_inc_ref(v___y_164_);
lean_inc(v___y_163_);
lean_inc_ref(v___y_162_);
v___x_169_ = lean_apply_5(v___x_133__overap_168_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, lean_box(0));
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00mkNatLookupTable_spec__0___boxed(lean_object* v_msg_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_panic___at___00mkNatLookupTable_spec__0(v_msg_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
return v_res_176_;
}
}
static lean_object* _init_l_mkNatLookupTable___closed__3(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_180_ = ((lean_object*)(l_mkNatLookupTable___closed__2));
v___x_181_ = lean_unsigned_to_nat(4u);
v___x_182_ = lean_unsigned_to_nat(25u);
v___x_183_ = ((lean_object*)(l_mkNatLookupTable___closed__1));
v___x_184_ = ((lean_object*)(l_mkNatLookupTable___closed__0));
v___x_185_ = l_mkPanicMessageWithDecl(v___x_184_, v___x_183_, v___x_182_, v___x_181_, v___x_180_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_mkNatLookupTable(lean_object* v_i_186_, lean_object* v_type_187_, lean_object* v_es_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_194_ = lean_array_get_size(v_es_188_);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_nat_dec_eq(v___x_194_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; 
lean_inc_ref(v_type_187_);
v___x_197_ = l_Lean_Meta_getLevel(v_type_187_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; lean_object* v___x_199_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_a_198_);
lean_dec_ref(v___x_197_);
v___x_199_ = l___private_Lean_Meta_NatTable_0__mkNatLookupTable_go___redArg(v_i_186_, v_type_187_, v_es_188_, v_a_198_, v___x_195_, v___x_194_);
return v___x_199_;
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec_ref(v_type_187_);
lean_dec_ref(v_i_186_);
v_a_200_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_197_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_197_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
else
{
lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec_ref(v_type_187_);
lean_dec_ref(v_i_186_);
v___x_208_ = lean_obj_once(&l_mkNatLookupTable___closed__3, &l_mkNatLookupTable___closed__3_once, _init_l_mkNatLookupTable___closed__3);
v___x_209_ = l_panic___at___00mkNatLookupTable_spec__0(v___x_208_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l_mkNatLookupTable___boxed(lean_object* v_i_210_, lean_object* v_type_211_, lean_object* v_es_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_mkNatLookupTable(v_i_210_, v_type_211_, v_es_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec_ref(v_es_212_);
return v_res_218_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_NatTable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_NatTable(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1 = _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1();
lean_mark_persistent(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__1);
l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__3 = _init_l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__3();
lean_mark_persistent(l___private_Lean_Meta_NatTable_0__mkNatLookupTable___auto__3);
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Meta_NatTable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_NatTable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_NatTable(builtin);
}
#ifdef __cplusplus
}
#endif
