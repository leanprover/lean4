// Lean compiler output
// Module: Init.Data.Array.Range
// Imports: import all Init.Data.Array.Basic import all Init.Data.Array.OfFn public import Init.BinderPredicates public import Init.Data.Nat.Lemmas public import Init.Ext import Init.ByCases import Init.Data.Array.Count import Init.Data.Array.MapIdx import Init.Data.Array.Zip import Init.Data.List.Find import Init.Data.List.Nat.Range import Init.Data.List.Range
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Range_0__Array_ofFn_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Range_0__Array_ofFn_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Range_0__Array_ofFn_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Range_0__Array_ofFn_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_count__range_x27___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Array_count__range_x27___auto__1___closed__0 = (const lean_object*)&l_Array_count__range_x27___auto__1___closed__0_value;
static const lean_string_object l_Array_count__range_x27___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Array_count__range_x27___auto__1___closed__1 = (const lean_object*)&l_Array_count__range_x27___auto__1___closed__1_value;
static const lean_string_object l_Array_count__range_x27___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Array_count__range_x27___auto__1___closed__2 = (const lean_object*)&l_Array_count__range_x27___auto__1___closed__2_value;
static const lean_string_object l_Array_count__range_x27___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Array_count__range_x27___auto__1___closed__3 = (const lean_object*)&l_Array_count__range_x27___auto__1___closed__3_value;
static const lean_ctor_object l_Array_count__range_x27___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_count__range_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_count__range_x27___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_count__range_x27___auto__1___closed__4_value_aux_0),((lean_object*)&l_Array_count__range_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_count__range_x27___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_count__range_x27___auto__1___closed__4_value_aux_1),((lean_object*)&l_Array_count__range_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_count__range_x27___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_count__range_x27___auto__1___closed__4_value_aux_2),((lean_object*)&l_Array_count__range_x27___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Array_count__range_x27___auto__1___closed__4 = (const lean_object*)&l_Array_count__range_x27___auto__1___closed__4_value;
static const lean_array_object l_Array_count__range_x27___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_count__range_x27___auto__1___closed__5 = (const lean_object*)&l_Array_count__range_x27___auto__1___closed__5_value;
static const lean_string_object l_Array_count__range_x27___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Array_count__range_x27___auto__1___closed__6 = (const lean_object*)&l_Array_count__range_x27___auto__1___closed__6_value;
static const lean_ctor_object l_Array_count__range_x27___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_count__range_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_count__range_x27___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_count__range_x27___auto__1___closed__7_value_aux_0),((lean_object*)&l_Array_count__range_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_count__range_x27___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_count__range_x27___auto__1___closed__7_value_aux_1),((lean_object*)&l_Array_count__range_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_count__range_x27___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_count__range_x27___auto__1___closed__7_value_aux_2),((lean_object*)&l_Array_count__range_x27___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Array_count__range_x27___auto__1___closed__7 = (const lean_object*)&l_Array_count__range_x27___auto__1___closed__7_value;
static const lean_string_object l_Array_count__range_x27___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Array_count__range_x27___auto__1___closed__8 = (const lean_object*)&l_Array_count__range_x27___auto__1___closed__8_value;
static const lean_ctor_object l_Array_count__range_x27___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_count__range_x27___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Array_count__range_x27___auto__1___closed__9 = (const lean_object*)&l_Array_count__range_x27___auto__1___closed__9_value;
static const lean_string_object l_Array_count__range_x27___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Array_count__range_x27___auto__1___closed__10 = (const lean_object*)&l_Array_count__range_x27___auto__1___closed__10_value;
static const lean_ctor_object l_Array_count__range_x27___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_count__range_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_count__range_x27___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_count__range_x27___auto__1___closed__11_value_aux_0),((lean_object*)&l_Array_count__range_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_count__range_x27___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_count__range_x27___auto__1___closed__11_value_aux_1),((lean_object*)&l_Array_count__range_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_count__range_x27___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_count__range_x27___auto__1___closed__11_value_aux_2),((lean_object*)&l_Array_count__range_x27___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Array_count__range_x27___auto__1___closed__11 = (const lean_object*)&l_Array_count__range_x27___auto__1___closed__11_value;
static lean_once_cell_t l_Array_count__range_x27___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_count__range_x27___auto__1___closed__12;
static lean_once_cell_t l_Array_count__range_x27___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_count__range_x27___auto__1___closed__13;
static const lean_string_object l_Array_count__range_x27___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Array_count__range_x27___auto__1___closed__14 = (const lean_object*)&l_Array_count__range_x27___auto__1___closed__14_value;
static const lean_ctor_object l_Array_count__range_x27___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_count__range_x27___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_count__range_x27___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_count__range_x27___auto__1___closed__15_value_aux_0),((lean_object*)&l_Array_count__range_x27___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_count__range_x27___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_count__range_x27___auto__1___closed__15_value_aux_1),((lean_object*)&l_Array_count__range_x27___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_count__range_x27___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_count__range_x27___auto__1___closed__15_value_aux_2),((lean_object*)&l_Array_count__range_x27___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Array_count__range_x27___auto__1___closed__15 = (const lean_object*)&l_Array_count__range_x27___auto__1___closed__15_value;
static const lean_ctor_object l_Array_count__range_x27___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Array_count__range_x27___auto__1___closed__9_value),((lean_object*)&l_Array_count__range_x27___auto__1___closed__5_value)}};
static const lean_object* l_Array_count__range_x27___auto__1___closed__16 = (const lean_object*)&l_Array_count__range_x27___auto__1___closed__16_value;
static lean_once_cell_t l_Array_count__range_x27___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_count__range_x27___auto__1___closed__17;
static lean_once_cell_t l_Array_count__range_x27___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_count__range_x27___auto__1___closed__18;
static lean_once_cell_t l_Array_count__range_x27___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_count__range_x27___auto__1___closed__19;
static lean_once_cell_t l_Array_count__range_x27___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_count__range_x27___auto__1___closed__20;
static lean_once_cell_t l_Array_count__range_x27___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_count__range_x27___auto__1___closed__21;
static lean_once_cell_t l_Array_count__range_x27___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_count__range_x27___auto__1___closed__22;
static lean_once_cell_t l_Array_count__range_x27___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_count__range_x27___auto__1___closed__23;
static lean_once_cell_t l_Array_count__range_x27___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_count__range_x27___auto__1___closed__24;
static lean_once_cell_t l_Array_count__range_x27___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_count__range_x27___auto__1___closed__25;
static lean_once_cell_t l_Array_count__range_x27___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_count__range_x27___auto__1___closed__26;
static lean_once_cell_t l_Array_count__range_x27___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_count__range_x27___auto__1___closed__27;
static lean_once_cell_t l_Array_count__range_x27___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_count__range_x27___auto__1___closed__28;
static lean_once_cell_t l_Array_count__range_x27___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_count__range_x27___auto__1___closed__29;
static lean_once_cell_t l_Array_count__range_x27___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_count__range_x27___auto__1___closed__30;
LEAN_EXPORT lean_object* l_Array_count__range_x27___auto__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Range_0__Array_ofFn_go_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_1_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_object* v___x_6_; 
lean_dec(v_h__1_2_);
v___x_6_ = lean_apply_1(v_h__2_3_, lean_box(0));
return v___x_6_;
}
else
{
lean_object* v_one_7_; lean_object* v_n_8_; lean_object* v___x_9_; 
lean_dec(v_h__2_3_);
v_one_7_ = lean_unsigned_to_nat(1u);
v_n_8_ = lean_nat_sub(v_x_1_, v_one_7_);
v___x_9_ = lean_apply_2(v_h__1_2_, v_n_8_, lean_box(0));
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Range_0__Array_ofFn_go_match__1_splitter___redArg___boxed(lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Init_Data_Array_Range_0__Array_ofFn_go_match__1_splitter___redArg(v_x_10_, v_h__1_11_, v_h__2_12_);
lean_dec(v_x_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Range_0__Array_ofFn_go_match__1_splitter(lean_object* v_n_14_, lean_object* v_motive_15_, lean_object* v_x_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l___private_Init_Data_Array_Range_0__Array_ofFn_go_match__1_splitter___redArg(v_x_16_, v_h__1_18_, v_h__2_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Range_0__Array_ofFn_go_match__1_splitter___boxed(lean_object* v_n_21_, lean_object* v_motive_22_, lean_object* v_x_23_, lean_object* v_x_24_, lean_object* v_h__1_25_, lean_object* v_h__2_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l___private_Init_Data_Array_Range_0__Array_ofFn_go_match__1_splitter(v_n_21_, v_motive_22_, v_x_23_, v_x_24_, v_h__1_25_, v_h__2_26_);
lean_dec(v_x_23_);
lean_dec(v_n_21_);
return v_res_27_;
}
}
static lean_object* _init_l_Array_count__range_x27___auto__1___closed__12(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = ((lean_object*)(l_Array_count__range_x27___auto__1___closed__10));
v___x_55_ = l_Lean_mkAtom(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Array_count__range_x27___auto__1___closed__13(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_obj_once(&l_Array_count__range_x27___auto__1___closed__12, &l_Array_count__range_x27___auto__1___closed__12_once, _init_l_Array_count__range_x27___auto__1___closed__12);
v___x_57_ = ((lean_object*)(l_Array_count__range_x27___auto__1___closed__5));
v___x_58_ = lean_array_push(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_l_Array_count__range_x27___auto__1___closed__17(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = ((lean_object*)(l_Array_count__range_x27___auto__1___closed__16));
v___x_70_ = ((lean_object*)(l_Array_count__range_x27___auto__1___closed__5));
v___x_71_ = lean_array_push(v___x_70_, v___x_69_);
return v___x_71_;
}
}
static lean_object* _init_l_Array_count__range_x27___auto__1___closed__18(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_72_ = lean_obj_once(&l_Array_count__range_x27___auto__1___closed__17, &l_Array_count__range_x27___auto__1___closed__17_once, _init_l_Array_count__range_x27___auto__1___closed__17);
v___x_73_ = ((lean_object*)(l_Array_count__range_x27___auto__1___closed__15));
v___x_74_ = lean_box(2);
v___x_75_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v___x_73_);
lean_ctor_set(v___x_75_, 2, v___x_72_);
return v___x_75_;
}
}
static lean_object* _init_l_Array_count__range_x27___auto__1___closed__19(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_obj_once(&l_Array_count__range_x27___auto__1___closed__18, &l_Array_count__range_x27___auto__1___closed__18_once, _init_l_Array_count__range_x27___auto__1___closed__18);
v___x_77_ = lean_obj_once(&l_Array_count__range_x27___auto__1___closed__13, &l_Array_count__range_x27___auto__1___closed__13_once, _init_l_Array_count__range_x27___auto__1___closed__13);
v___x_78_ = lean_array_push(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_l_Array_count__range_x27___auto__1___closed__20(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = ((lean_object*)(l_Array_count__range_x27___auto__1___closed__16));
v___x_80_ = lean_obj_once(&l_Array_count__range_x27___auto__1___closed__19, &l_Array_count__range_x27___auto__1___closed__19_once, _init_l_Array_count__range_x27___auto__1___closed__19);
v___x_81_ = lean_array_push(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l_Array_count__range_x27___auto__1___closed__21(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = ((lean_object*)(l_Array_count__range_x27___auto__1___closed__16));
v___x_83_ = lean_obj_once(&l_Array_count__range_x27___auto__1___closed__20, &l_Array_count__range_x27___auto__1___closed__20_once, _init_l_Array_count__range_x27___auto__1___closed__20);
v___x_84_ = lean_array_push(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l_Array_count__range_x27___auto__1___closed__22(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = ((lean_object*)(l_Array_count__range_x27___auto__1___closed__16));
v___x_86_ = lean_obj_once(&l_Array_count__range_x27___auto__1___closed__21, &l_Array_count__range_x27___auto__1___closed__21_once, _init_l_Array_count__range_x27___auto__1___closed__21);
v___x_87_ = lean_array_push(v___x_86_, v___x_85_);
return v___x_87_;
}
}
static lean_object* _init_l_Array_count__range_x27___auto__1___closed__23(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = ((lean_object*)(l_Array_count__range_x27___auto__1___closed__16));
v___x_89_ = lean_obj_once(&l_Array_count__range_x27___auto__1___closed__22, &l_Array_count__range_x27___auto__1___closed__22_once, _init_l_Array_count__range_x27___auto__1___closed__22);
v___x_90_ = lean_array_push(v___x_89_, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_l_Array_count__range_x27___auto__1___closed__24(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = lean_obj_once(&l_Array_count__range_x27___auto__1___closed__23, &l_Array_count__range_x27___auto__1___closed__23_once, _init_l_Array_count__range_x27___auto__1___closed__23);
v___x_92_ = ((lean_object*)(l_Array_count__range_x27___auto__1___closed__11));
v___x_93_ = lean_box(2);
v___x_94_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___x_92_);
lean_ctor_set(v___x_94_, 2, v___x_91_);
return v___x_94_;
}
}
static lean_object* _init_l_Array_count__range_x27___auto__1___closed__25(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_obj_once(&l_Array_count__range_x27___auto__1___closed__24, &l_Array_count__range_x27___auto__1___closed__24_once, _init_l_Array_count__range_x27___auto__1___closed__24);
v___x_96_ = ((lean_object*)(l_Array_count__range_x27___auto__1___closed__5));
v___x_97_ = lean_array_push(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Array_count__range_x27___auto__1___closed__26(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_98_ = lean_obj_once(&l_Array_count__range_x27___auto__1___closed__25, &l_Array_count__range_x27___auto__1___closed__25_once, _init_l_Array_count__range_x27___auto__1___closed__25);
v___x_99_ = ((lean_object*)(l_Array_count__range_x27___auto__1___closed__9));
v___x_100_ = lean_box(2);
v___x_101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
lean_ctor_set(v___x_101_, 2, v___x_98_);
return v___x_101_;
}
}
static lean_object* _init_l_Array_count__range_x27___auto__1___closed__27(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_obj_once(&l_Array_count__range_x27___auto__1___closed__26, &l_Array_count__range_x27___auto__1___closed__26_once, _init_l_Array_count__range_x27___auto__1___closed__26);
v___x_103_ = ((lean_object*)(l_Array_count__range_x27___auto__1___closed__5));
v___x_104_ = lean_array_push(v___x_103_, v___x_102_);
return v___x_104_;
}
}
static lean_object* _init_l_Array_count__range_x27___auto__1___closed__28(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_105_ = lean_obj_once(&l_Array_count__range_x27___auto__1___closed__27, &l_Array_count__range_x27___auto__1___closed__27_once, _init_l_Array_count__range_x27___auto__1___closed__27);
v___x_106_ = ((lean_object*)(l_Array_count__range_x27___auto__1___closed__7));
v___x_107_ = lean_box(2);
v___x_108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_106_);
lean_ctor_set(v___x_108_, 2, v___x_105_);
return v___x_108_;
}
}
static lean_object* _init_l_Array_count__range_x27___auto__1___closed__29(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_obj_once(&l_Array_count__range_x27___auto__1___closed__28, &l_Array_count__range_x27___auto__1___closed__28_once, _init_l_Array_count__range_x27___auto__1___closed__28);
v___x_110_ = ((lean_object*)(l_Array_count__range_x27___auto__1___closed__5));
v___x_111_ = lean_array_push(v___x_110_, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l_Array_count__range_x27___auto__1___closed__30(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_112_ = lean_obj_once(&l_Array_count__range_x27___auto__1___closed__29, &l_Array_count__range_x27___auto__1___closed__29_once, _init_l_Array_count__range_x27___auto__1___closed__29);
v___x_113_ = ((lean_object*)(l_Array_count__range_x27___auto__1___closed__4));
v___x_114_ = lean_box(2);
v___x_115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_113_);
lean_ctor_set(v___x_115_, 2, v___x_112_);
return v___x_115_;
}
}
static lean_object* _init_l_Array_count__range_x27___auto__1(void){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&l_Array_count__range_x27___auto__1___closed__30, &l_Array_count__range_x27___auto__1___closed__30_once, _init_l_Array_count__range_x27___auto__1___closed__30);
return v___x_116_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_OfFn(uint8_t builtin);
lean_object* runtime_initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Count(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_MapIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Zip(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Range(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Range(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Range(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Array_count__range_x27___auto__1 = _init_l_Array_count__range_x27___auto__1();
lean_mark_persistent(l_Array_count__range_x27___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_OfFn(uint8_t builtin);
lean_object* initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Count(uint8_t builtin);
lean_object* initialize_Init_Data_Array_MapIdx(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Zip(uint8_t builtin);
lean_object* initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_Range(uint8_t builtin);
lean_object* initialize_Init_Data_List_Range(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Range(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Range(builtin);
}
#ifdef __cplusplus
}
#endif
