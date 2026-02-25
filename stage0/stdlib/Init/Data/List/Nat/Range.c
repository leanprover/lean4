// Lean compiler output
// Module: Init.Data.List.Nat.Range
// Imports: public import Init.Data.Nat.Lemmas public import Init.Ext import Init.ByCases import Init.Data.List.Erase import Init.Data.List.Find import Init.Data.List.Nat.TakeDrop import Init.Data.List.Pairwise import Init.Data.List.Range import Init.Data.List.Zip import Init.Data.Nat.Dvd import Init.Data.Option.Lemmas import Init.Omega import Init.TacticsExtra
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
static const lean_string_object l_List_pairwise__lt__range_x27___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__0 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__0_value;
static const lean_string_object l_List_pairwise__lt__range_x27___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__1 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__1_value;
static const lean_string_object l_List_pairwise__lt__range_x27___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__2 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__2_value;
static const lean_string_object l_List_pairwise__lt__range_x27___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__3 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__4_value_aux_0),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__4_value_aux_1),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__4_value_aux_2),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__4 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__4_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__5;
static const lean_string_object l_List_pairwise__lt__range_x27___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__6 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__6_value;
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__7_value_aux_0),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__7_value_aux_1),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__7_value_aux_2),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__7 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__7_value;
static const lean_string_object l_List_pairwise__lt__range_x27___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__8 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__8_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__9 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__9_value;
static const lean_string_object l_List_pairwise__lt__range_x27___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__10 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__10_value;
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__11_value_aux_0),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__11_value_aux_1),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__11_value_aux_2),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__11 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__11_value;
lean_object* l_Lean_mkAtom(lean_object*);
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__12;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__13;
static const lean_string_object l_List_pairwise__lt__range_x27___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__14 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__14_value;
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__15_value_aux_0),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__15_value_aux_1),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__15_value_aux_2),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__15 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__15_value;
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__16;
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__17;
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__18;
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__19;
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__20;
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__21;
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__22;
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__23;
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__24;
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__25;
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__26;
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__27;
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__28;
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__29;
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__30;
LEAN_EXPORT lean_object* l_List_pairwise__lt__range_x27___auto__1;
LEAN_EXPORT lean_object* l_List_nodup__range_x27___auto__1;
LEAN_EXPORT lean_object* l_List_count__range_x27___auto__1;
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__10));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__12, &l_List_pairwise__lt__range_x27___auto__1___closed__12_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__12);
x_2 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__5, &l_List_pairwise__lt__range_x27___auto__1___closed__5_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__5, &l_List_pairwise__lt__range_x27___auto__1___closed__5_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__5);
x_2 = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__16, &l_List_pairwise__lt__range_x27___auto__1___closed__16_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__16);
x_2 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__5, &l_List_pairwise__lt__range_x27___auto__1___closed__5_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__17, &l_List_pairwise__lt__range_x27___auto__1___closed__17_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__17);
x_2 = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__15));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__18, &l_List_pairwise__lt__range_x27___auto__1___closed__18_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__18);
x_2 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__13, &l_List_pairwise__lt__range_x27___auto__1___closed__13_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__13);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__16, &l_List_pairwise__lt__range_x27___auto__1___closed__16_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__16);
x_2 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__19, &l_List_pairwise__lt__range_x27___auto__1___closed__19_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__19);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__16, &l_List_pairwise__lt__range_x27___auto__1___closed__16_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__16);
x_2 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__20, &l_List_pairwise__lt__range_x27___auto__1___closed__20_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__20);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__16, &l_List_pairwise__lt__range_x27___auto__1___closed__16_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__16);
x_2 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__21, &l_List_pairwise__lt__range_x27___auto__1___closed__21_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__21);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__16, &l_List_pairwise__lt__range_x27___auto__1___closed__16_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__16);
x_2 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__22, &l_List_pairwise__lt__range_x27___auto__1___closed__22_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__22);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__23, &l_List_pairwise__lt__range_x27___auto__1___closed__23_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__23);
x_2 = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__11));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__25(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__24, &l_List_pairwise__lt__range_x27___auto__1___closed__24_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__24);
x_2 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__5, &l_List_pairwise__lt__range_x27___auto__1___closed__5_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__25, &l_List_pairwise__lt__range_x27___auto__1___closed__25_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__25);
x_2 = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__27(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__26, &l_List_pairwise__lt__range_x27___auto__1___closed__26_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__26);
x_2 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__5, &l_List_pairwise__lt__range_x27___auto__1___closed__5_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__28(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__27, &l_List_pairwise__lt__range_x27___auto__1___closed__27_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__27);
x_2 = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__7));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__29(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__28, &l_List_pairwise__lt__range_x27___auto__1___closed__28_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__28);
x_2 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__5, &l_List_pairwise__lt__range_x27___auto__1___closed__5_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__5);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__30(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__29, &l_List_pairwise__lt__range_x27___auto__1___closed__29_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__29);
x_2 = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__4));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__30, &l_List_pairwise__lt__range_x27___auto__1___closed__30_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__30);
return x_1;
}
}
static lean_object* _init_l_List_nodup__range_x27___auto__1(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__30, &l_List_pairwise__lt__range_x27___auto__1___closed__30_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__30);
return x_1;
}
}
static lean_object* _init_l_List_count__range_x27___auto__1(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__30, &l_List_pairwise__lt__range_x27___auto__1___closed__30_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__30);
return x_1;
}
}
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_List_Erase(uint8_t builtin);
lean_object* initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* initialize_Init_Data_List_Zip(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Nat_Range(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_pairwise__lt__range_x27___auto__1 = _init_l_List_pairwise__lt__range_x27___auto__1();
lean_mark_persistent(l_List_pairwise__lt__range_x27___auto__1);
l_List_nodup__range_x27___auto__1 = _init_l_List_nodup__range_x27___auto__1();
lean_mark_persistent(l_List_nodup__range_x27___auto__1);
l_List_count__range_x27___auto__1 = _init_l_List_count__range_x27___auto__1();
lean_mark_persistent(l_List_count__range_x27___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
