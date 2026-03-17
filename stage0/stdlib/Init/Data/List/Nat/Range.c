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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_pairwise__lt__range_x27___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__0 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__0_value;
static const lean_string_object l_List_pairwise__lt__range_x27___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__1 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__1_value;
static const lean_string_object l_List_pairwise__lt__range_x27___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__2 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__2_value;
static const lean_string_object l_List_pairwise__lt__range_x27___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__3 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__3_value;
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__4_value_aux_0),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__4_value_aux_1),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__4_value_aux_2),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__4 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__4_value;
static const lean_array_object l_List_pairwise__lt__range_x27___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__5 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__5_value;
static const lean_string_object l_List_pairwise__lt__range_x27___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__6 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__6_value;
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__7_value_aux_0),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__7_value_aux_1),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__7_value_aux_2),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__7 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__7_value;
static const lean_string_object l_List_pairwise__lt__range_x27___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__8 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__8_value;
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__9 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__9_value;
static const lean_string_object l_List_pairwise__lt__range_x27___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__10 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__10_value;
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__11_value_aux_0),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__11_value_aux_1),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__11_value_aux_2),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__11 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__11_value;
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__12;
static lean_once_cell_t l_List_pairwise__lt__range_x27___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__13;
static const lean_string_object l_List_pairwise__lt__range_x27___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__14 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__14_value;
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__15_value_aux_0),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__15_value_aux_1),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__15_value_aux_2),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__15 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__15_value;
static const lean_ctor_object l_List_pairwise__lt__range_x27___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__9_value),((lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__5_value)}};
static const lean_object* l_List_pairwise__lt__range_x27___auto__1___closed__16 = (const lean_object*)&l_List_pairwise__lt__range_x27___auto__1___closed__16_value;
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
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__12, &l_List_pairwise__lt__range_x27___auto__1___closed__12_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__17(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__16));
v___x_43_ = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__5));
v___x_44_ = lean_array_push(v___x_43_, v___x_42_);
return v___x_44_;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__18(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_45_ = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__17, &l_List_pairwise__lt__range_x27___auto__1___closed__17_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__17);
v___x_46_ = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__15));
v___x_47_ = lean_box(2);
v___x_48_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_46_);
lean_ctor_set(v___x_48_, 2, v___x_45_);
return v___x_48_;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__19(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__18, &l_List_pairwise__lt__range_x27___auto__1___closed__18_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__18);
v___x_50_ = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__13, &l_List_pairwise__lt__range_x27___auto__1___closed__13_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__13);
v___x_51_ = lean_array_push(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__20(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__16));
v___x_53_ = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__19, &l_List_pairwise__lt__range_x27___auto__1___closed__19_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__19);
v___x_54_ = lean_array_push(v___x_53_, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__21(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__16));
v___x_56_ = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__20, &l_List_pairwise__lt__range_x27___auto__1___closed__20_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__20);
v___x_57_ = lean_array_push(v___x_56_, v___x_55_);
return v___x_57_;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__22(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__16));
v___x_59_ = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__21, &l_List_pairwise__lt__range_x27___auto__1___closed__21_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__21);
v___x_60_ = lean_array_push(v___x_59_, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__23(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__16));
v___x_62_ = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__22, &l_List_pairwise__lt__range_x27___auto__1___closed__22_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__22);
v___x_63_ = lean_array_push(v___x_62_, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__24(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_64_ = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__23, &l_List_pairwise__lt__range_x27___auto__1___closed__23_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__23);
v___x_65_ = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__11));
v___x_66_ = lean_box(2);
v___x_67_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
lean_ctor_set(v___x_67_, 2, v___x_64_);
return v___x_67_;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__25(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__24, &l_List_pairwise__lt__range_x27___auto__1___closed__24_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__24);
v___x_69_ = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__5));
v___x_70_ = lean_array_push(v___x_69_, v___x_68_);
return v___x_70_;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__26(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_71_ = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__25, &l_List_pairwise__lt__range_x27___auto__1___closed__25_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__25);
v___x_72_ = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__9));
v___x_73_ = lean_box(2);
v___x_74_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___x_72_);
lean_ctor_set(v___x_74_, 2, v___x_71_);
return v___x_74_;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__27(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__26, &l_List_pairwise__lt__range_x27___auto__1___closed__26_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__26);
v___x_76_ = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__5));
v___x_77_ = lean_array_push(v___x_76_, v___x_75_);
return v___x_77_;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__28(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__27, &l_List_pairwise__lt__range_x27___auto__1___closed__27_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__27);
v___x_79_ = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__7));
v___x_80_ = lean_box(2);
v___x_81_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_79_);
lean_ctor_set(v___x_81_, 2, v___x_78_);
return v___x_81_;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__29(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__28, &l_List_pairwise__lt__range_x27___auto__1___closed__28_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__28);
v___x_83_ = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__5));
v___x_84_ = lean_array_push(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1___closed__30(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_85_ = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__29, &l_List_pairwise__lt__range_x27___auto__1___closed__29_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__29);
v___x_86_ = ((lean_object*)(l_List_pairwise__lt__range_x27___auto__1___closed__4));
v___x_87_ = lean_box(2);
v___x_88_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_86_);
lean_ctor_set(v___x_88_, 2, v___x_85_);
return v___x_88_;
}
}
static lean_object* _init_l_List_pairwise__lt__range_x27___auto__1(void){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__30, &l_List_pairwise__lt__range_x27___auto__1___closed__30_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__30);
return v___x_89_;
}
}
static lean_object* _init_l_List_nodup__range_x27___auto__1(void){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__30, &l_List_pairwise__lt__range_x27___auto__1___closed__30_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__30);
return v___x_90_;
}
}
static lean_object* _init_l_List_count__range_x27___auto__1(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_obj_once(&l_List_pairwise__lt__range_x27___auto__1___closed__30, &l_List_pairwise__lt__range_x27___auto__1___closed__30_once, _init_l_List_pairwise__lt__range_x27___auto__1___closed__30);
return v___x_91_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Erase(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Zip(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Nat_Range(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Nat_Range(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_List_pairwise__lt__range_x27___auto__1 = _init_l_List_pairwise__lt__range_x27___auto__1();
lean_mark_persistent(l_List_pairwise__lt__range_x27___auto__1);
l_List_nodup__range_x27___auto__1 = _init_l_List_nodup__range_x27___auto__1();
lean_mark_persistent(l_List_nodup__range_x27___auto__1);
l_List_count__range_x27___auto__1 = _init_l_List_count__range_x27___auto__1();
lean_mark_persistent(l_List_count__range_x27___auto__1);
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Init_Data_List_Nat_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Nat_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Nat_Range(builtin);
}
#ifdef __cplusplus
}
#endif
