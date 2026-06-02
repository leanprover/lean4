// Lean compiler output
// Module: Init.Control.Lawful.Basic
// Imports: public import Init.Control.Id public import Init.Grind.Tactics import Init.Ext
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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_LawfulMonad_mk_x27___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_LawfulMonad_mk_x27___auto__1___closed__0 = (const lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__0_value;
static const lean_string_object l_LawfulMonad_mk_x27___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_LawfulMonad_mk_x27___auto__1___closed__1 = (const lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__1_value;
static const lean_string_object l_LawfulMonad_mk_x27___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_LawfulMonad_mk_x27___auto__1___closed__2 = (const lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__2_value;
static const lean_string_object l_LawfulMonad_mk_x27___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_LawfulMonad_mk_x27___auto__1___closed__3 = (const lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__3_value;
static const lean_ctor_object l_LawfulMonad_mk_x27___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_LawfulMonad_mk_x27___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__4_value_aux_0),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_LawfulMonad_mk_x27___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__4_value_aux_1),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_LawfulMonad_mk_x27___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__4_value_aux_2),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_LawfulMonad_mk_x27___auto__1___closed__4 = (const lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__4_value;
static const lean_array_object l_LawfulMonad_mk_x27___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_LawfulMonad_mk_x27___auto__1___closed__5 = (const lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__5_value;
static const lean_string_object l_LawfulMonad_mk_x27___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_LawfulMonad_mk_x27___auto__1___closed__6 = (const lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__6_value;
static const lean_ctor_object l_LawfulMonad_mk_x27___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_LawfulMonad_mk_x27___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__7_value_aux_0),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_LawfulMonad_mk_x27___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__7_value_aux_1),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_LawfulMonad_mk_x27___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__7_value_aux_2),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_LawfulMonad_mk_x27___auto__1___closed__7 = (const lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__7_value;
static const lean_string_object l_LawfulMonad_mk_x27___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_LawfulMonad_mk_x27___auto__1___closed__8 = (const lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__8_value;
static const lean_ctor_object l_LawfulMonad_mk_x27___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_LawfulMonad_mk_x27___auto__1___closed__9 = (const lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__9_value;
static const lean_string_object l_LawfulMonad_mk_x27___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "intros"};
static const lean_object* l_LawfulMonad_mk_x27___auto__1___closed__10 = (const lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__10_value;
static const lean_ctor_object l_LawfulMonad_mk_x27___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_LawfulMonad_mk_x27___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__11_value_aux_0),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_LawfulMonad_mk_x27___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__11_value_aux_1),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_LawfulMonad_mk_x27___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__11_value_aux_2),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(26, 175, 18, 116, 252, 50, 128, 45)}};
static const lean_object* l_LawfulMonad_mk_x27___auto__1___closed__11 = (const lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__11_value;
static lean_once_cell_t l_LawfulMonad_mk_x27___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulMonad_mk_x27___auto__1___closed__12;
static lean_once_cell_t l_LawfulMonad_mk_x27___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulMonad_mk_x27___auto__1___closed__13;
static const lean_ctor_object l_LawfulMonad_mk_x27___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__9_value),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__5_value)}};
static const lean_object* l_LawfulMonad_mk_x27___auto__1___closed__14 = (const lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__14_value;
static lean_once_cell_t l_LawfulMonad_mk_x27___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulMonad_mk_x27___auto__1___closed__15;
static lean_once_cell_t l_LawfulMonad_mk_x27___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulMonad_mk_x27___auto__1___closed__16;
static lean_once_cell_t l_LawfulMonad_mk_x27___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulMonad_mk_x27___auto__1___closed__17;
static const lean_string_object l_LawfulMonad_mk_x27___auto__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_LawfulMonad_mk_x27___auto__1___closed__18 = (const lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__18_value;
static lean_once_cell_t l_LawfulMonad_mk_x27___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulMonad_mk_x27___auto__1___closed__19;
static lean_once_cell_t l_LawfulMonad_mk_x27___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulMonad_mk_x27___auto__1___closed__20;
static const lean_string_object l_LawfulMonad_mk_x27___auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l_LawfulMonad_mk_x27___auto__1___closed__21 = (const lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__21_value;
static const lean_ctor_object l_LawfulMonad_mk_x27___auto__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_LawfulMonad_mk_x27___auto__1___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__22_value_aux_0),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_LawfulMonad_mk_x27___auto__1___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__22_value_aux_1),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_LawfulMonad_mk_x27___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__22_value_aux_2),((lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l_LawfulMonad_mk_x27___auto__1___closed__22 = (const lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__22_value;
static const lean_string_object l_LawfulMonad_mk_x27___auto__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_LawfulMonad_mk_x27___auto__1___closed__23 = (const lean_object*)&l_LawfulMonad_mk_x27___auto__1___closed__23_value;
static lean_once_cell_t l_LawfulMonad_mk_x27___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulMonad_mk_x27___auto__1___closed__24;
static lean_once_cell_t l_LawfulMonad_mk_x27___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulMonad_mk_x27___auto__1___closed__25;
static lean_once_cell_t l_LawfulMonad_mk_x27___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulMonad_mk_x27___auto__1___closed__26;
static lean_once_cell_t l_LawfulMonad_mk_x27___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulMonad_mk_x27___auto__1___closed__27;
static lean_once_cell_t l_LawfulMonad_mk_x27___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulMonad_mk_x27___auto__1___closed__28;
static lean_once_cell_t l_LawfulMonad_mk_x27___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulMonad_mk_x27___auto__1___closed__29;
static lean_once_cell_t l_LawfulMonad_mk_x27___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulMonad_mk_x27___auto__1___closed__30;
static lean_once_cell_t l_LawfulMonad_mk_x27___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulMonad_mk_x27___auto__1___closed__31;
static lean_once_cell_t l_LawfulMonad_mk_x27___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LawfulMonad_mk_x27___auto__1___closed__32;
LEAN_EXPORT lean_object* l_LawfulMonad_mk_x27___auto__1;
LEAN_EXPORT lean_object* l_LawfulMonad_mk_x27___auto__3;
LEAN_EXPORT lean_object* l_LawfulMonad_mk_x27___auto__5;
LEAN_EXPORT lean_object* l_LawfulMonad_mk_x27___auto__7;
LEAN_EXPORT lean_object* l_LawfulMonad_mk_x27___auto__9;
static lean_object* _init_l_LawfulMonad_mk_x27___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_LawfulMonad_mk_x27___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__12, &l_LawfulMonad_mk_x27___auto__1___closed__12_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l_LawfulMonad_mk_x27___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__1___closed__15(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = ((lean_object*)(l_LawfulMonad_mk_x27___auto__1___closed__14));
v___x_37_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__13, &l_LawfulMonad_mk_x27___auto__1___closed__13_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__13);
v___x_38_ = lean_array_push(v___x_37_, v___x_36_);
return v___x_38_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__1___closed__16(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_39_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__15, &l_LawfulMonad_mk_x27___auto__1___closed__15_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__15);
v___x_40_ = ((lean_object*)(l_LawfulMonad_mk_x27___auto__1___closed__11));
v___x_41_ = lean_box(2);
v___x_42_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v___x_40_);
lean_ctor_set(v___x_42_, 2, v___x_39_);
return v___x_42_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__1___closed__17(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__16, &l_LawfulMonad_mk_x27___auto__1___closed__16_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__16);
v___x_44_ = ((lean_object*)(l_LawfulMonad_mk_x27___auto__1___closed__5));
v___x_45_ = lean_array_push(v___x_44_, v___x_43_);
return v___x_45_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__1___closed__19(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = ((lean_object*)(l_LawfulMonad_mk_x27___auto__1___closed__18));
v___x_48_ = l_Lean_mkAtom(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__1___closed__20(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__19, &l_LawfulMonad_mk_x27___auto__1___closed__19_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__19);
v___x_50_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__17, &l_LawfulMonad_mk_x27___auto__1___closed__17_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__17);
v___x_51_ = lean_array_push(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__1___closed__24(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(l_LawfulMonad_mk_x27___auto__1___closed__23));
v___x_60_ = l_Lean_mkAtom(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__1___closed__25(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__24, &l_LawfulMonad_mk_x27___auto__1___closed__24_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__24);
v___x_62_ = ((lean_object*)(l_LawfulMonad_mk_x27___auto__1___closed__5));
v___x_63_ = lean_array_push(v___x_62_, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__1___closed__26(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_64_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__25, &l_LawfulMonad_mk_x27___auto__1___closed__25_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__25);
v___x_65_ = ((lean_object*)(l_LawfulMonad_mk_x27___auto__1___closed__22));
v___x_66_ = lean_box(2);
v___x_67_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
lean_ctor_set(v___x_67_, 2, v___x_64_);
return v___x_67_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__1___closed__27(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__26, &l_LawfulMonad_mk_x27___auto__1___closed__26_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__26);
v___x_69_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__20, &l_LawfulMonad_mk_x27___auto__1___closed__20_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__20);
v___x_70_ = lean_array_push(v___x_69_, v___x_68_);
return v___x_70_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__1___closed__28(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_71_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__27, &l_LawfulMonad_mk_x27___auto__1___closed__27_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__27);
v___x_72_ = ((lean_object*)(l_LawfulMonad_mk_x27___auto__1___closed__9));
v___x_73_ = lean_box(2);
v___x_74_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___x_72_);
lean_ctor_set(v___x_74_, 2, v___x_71_);
return v___x_74_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__1___closed__29(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__28, &l_LawfulMonad_mk_x27___auto__1___closed__28_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__28);
v___x_76_ = ((lean_object*)(l_LawfulMonad_mk_x27___auto__1___closed__5));
v___x_77_ = lean_array_push(v___x_76_, v___x_75_);
return v___x_77_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__1___closed__30(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__29, &l_LawfulMonad_mk_x27___auto__1___closed__29_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__29);
v___x_79_ = ((lean_object*)(l_LawfulMonad_mk_x27___auto__1___closed__7));
v___x_80_ = lean_box(2);
v___x_81_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_79_);
lean_ctor_set(v___x_81_, 2, v___x_78_);
return v___x_81_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__1___closed__31(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__30, &l_LawfulMonad_mk_x27___auto__1___closed__30_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__30);
v___x_83_ = ((lean_object*)(l_LawfulMonad_mk_x27___auto__1___closed__5));
v___x_84_ = lean_array_push(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__1___closed__32(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_85_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__31, &l_LawfulMonad_mk_x27___auto__1___closed__31_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__31);
v___x_86_ = ((lean_object*)(l_LawfulMonad_mk_x27___auto__1___closed__4));
v___x_87_ = lean_box(2);
v___x_88_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_86_);
lean_ctor_set(v___x_88_, 2, v___x_85_);
return v___x_88_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__1(void){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__32, &l_LawfulMonad_mk_x27___auto__1___closed__32_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__32);
return v___x_89_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__3(void){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__32, &l_LawfulMonad_mk_x27___auto__1___closed__32_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__32);
return v___x_90_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__5(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__32, &l_LawfulMonad_mk_x27___auto__1___closed__32_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__32);
return v___x_91_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__7(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__32, &l_LawfulMonad_mk_x27___auto__1___closed__32_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__32);
return v___x_92_;
}
}
static lean_object* _init_l_LawfulMonad_mk_x27___auto__9(void){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_obj_once(&l_LawfulMonad_mk_x27___auto__1___closed__32, &l_LawfulMonad_mk_x27___auto__1___closed__32_once, _init_l_LawfulMonad_mk_x27___auto__1___closed__32);
return v___x_93_;
}
}
lean_object* runtime_initialize_Init_Control_Id(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_Lawful_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Id(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Control_Lawful_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_LawfulMonad_mk_x27___auto__1 = _init_l_LawfulMonad_mk_x27___auto__1();
lean_mark_persistent(l_LawfulMonad_mk_x27___auto__1);
l_LawfulMonad_mk_x27___auto__3 = _init_l_LawfulMonad_mk_x27___auto__3();
lean_mark_persistent(l_LawfulMonad_mk_x27___auto__3);
l_LawfulMonad_mk_x27___auto__5 = _init_l_LawfulMonad_mk_x27___auto__5();
lean_mark_persistent(l_LawfulMonad_mk_x27___auto__5);
l_LawfulMonad_mk_x27___auto__7 = _init_l_LawfulMonad_mk_x27___auto__7();
lean_mark_persistent(l_LawfulMonad_mk_x27___auto__7);
l_LawfulMonad_mk_x27___auto__9 = _init_l_LawfulMonad_mk_x27___auto__9();
lean_mark_persistent(l_LawfulMonad_mk_x27___auto__9);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Id(uint8_t builtin);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_Lawful_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Id(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Lawful_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Control_Lawful_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Control_Lawful_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
