// Lean compiler output
// Module: Std.Data.DTreeMap.Lemmas
// Imports: import Std.Data.DTreeMap.Internal.Lemmas public import Std.Data.DTreeMap.AdditionalOperations public import Init.Data.Array.Perm import Init.Data.List.Pairwise import Init.Data.Prod
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
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Equiv_instTrans(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Equiv_instTrans___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Lemmas_0__Break_runK_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Lemmas_0__Break_runK_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_isSetoid___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__0_value;
static const lean_string_object l_Std_DTreeMap_isSetoid___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__1 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__1_value;
static const lean_string_object l_Std_DTreeMap_isSetoid___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__2 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__2_value;
static const lean_string_object l_Std_DTreeMap_isSetoid___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__3 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__3_value;
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__4 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__4_value;
static const lean_array_object l_Std_DTreeMap_isSetoid___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__5 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__5_value;
static const lean_string_object l_Std_DTreeMap_isSetoid___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__6 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__6_value;
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__7 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__7_value;
static const lean_string_object l_Std_DTreeMap_isSetoid___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__8 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__8_value;
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__9 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__9_value;
static const lean_string_object l_Std_DTreeMap_isSetoid___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__10 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__10_value;
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__11 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__11_value;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__12;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__13;
static const lean_string_object l_Std_DTreeMap_isSetoid___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__14 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__14_value;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__15;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__16;
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__17 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__17_value;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__18;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__19;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__20;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__21;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__22;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__23;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__24;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__25;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Std_DTreeMap_isSetoid___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_isSetoid(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_isSetoid___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__3(lean_object* v_00_u03b1_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Equiv_instTrans(lean_object* v_00_u03b1_3_, lean_object* v_00_u03b2_4_, lean_object* v_cmp_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Equiv_instTrans___boxed(lean_object* v_00_u03b1_7_, lean_object* v_00_u03b2_8_, lean_object* v_cmp_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_DTreeMap_Equiv_instTrans(v_00_u03b1_7_, v_00_u03b2_8_, v_cmp_9_);
lean_dec_ref(v_cmp_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Lemmas_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
if (lean_obj_tag(v_x_11_) == 0)
{
lean_object* v___x_14_; lean_object* v___x_15_; 
lean_dec(v_h__1_12_);
v___x_14_ = lean_box(0);
v___x_15_ = lean_apply_1(v_h__2_13_, v___x_14_);
return v___x_15_;
}
else
{
lean_object* v_val_16_; lean_object* v___x_17_; 
lean_dec(v_h__2_13_);
v_val_16_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_val_16_);
lean_dec_ref(v_x_11_);
v___x_17_ = lean_apply_1(v_h__1_12_, v_val_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Lemmas_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_18_, lean_object* v_motive_19_, lean_object* v_x_20_, lean_object* v_h__1_21_, lean_object* v_h__2_22_){
_start:
{
if (lean_obj_tag(v_x_20_) == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; 
lean_dec(v_h__1_21_);
v___x_23_ = lean_box(0);
v___x_24_ = lean_apply_1(v_h__2_22_, v___x_23_);
return v___x_24_;
}
else
{
lean_object* v_val_25_; lean_object* v___x_26_; 
lean_dec(v_h__2_22_);
v_val_25_ = lean_ctor_get(v_x_20_, 0);
lean_inc(v_val_25_);
lean_dec_ref(v_x_20_);
v___x_26_ = lean_apply_1(v_h__1_21_, v_val_25_);
return v___x_26_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__12(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__10));
v___x_54_ = l_Lean_mkAtom(v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__13(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__12, &l_Std_DTreeMap_isSetoid___auto__1___closed__12_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__12);
v___x_56_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__5));
v___x_57_ = lean_array_push(v___x_56_, v___x_55_);
return v___x_57_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__15(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__14));
v___x_60_ = lean_string_utf8_byte_size(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__16(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__15, &l_Std_DTreeMap_isSetoid___auto__1___closed__15_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__15);
v___x_62_ = lean_unsigned_to_nat(0u);
v___x_63_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__14));
v___x_64_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
lean_ctor_set(v___x_64_, 2, v___x_61_);
return v___x_64_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__18(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_67_ = lean_box(0);
v___x_68_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__17));
v___x_69_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__16, &l_Std_DTreeMap_isSetoid___auto__1___closed__16_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__16);
v___x_70_ = lean_box(2);
v___x_71_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
lean_ctor_set(v___x_71_, 3, v___x_67_);
return v___x_71_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__19(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__18, &l_Std_DTreeMap_isSetoid___auto__1___closed__18_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__18);
v___x_73_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__13, &l_Std_DTreeMap_isSetoid___auto__1___closed__13_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__13);
v___x_74_ = lean_array_push(v___x_73_, v___x_72_);
return v___x_74_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__20(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_75_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__19, &l_Std_DTreeMap_isSetoid___auto__1___closed__19_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__19);
v___x_76_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__11));
v___x_77_ = lean_box(2);
v___x_78_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___x_76_);
lean_ctor_set(v___x_78_, 2, v___x_75_);
return v___x_78_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__21(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__20, &l_Std_DTreeMap_isSetoid___auto__1___closed__20_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__20);
v___x_80_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__5));
v___x_81_ = lean_array_push(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__22(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_82_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__21, &l_Std_DTreeMap_isSetoid___auto__1___closed__21_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__21);
v___x_83_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__9));
v___x_84_ = lean_box(2);
v___x_85_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___x_83_);
lean_ctor_set(v___x_85_, 2, v___x_82_);
return v___x_85_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__23(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__22, &l_Std_DTreeMap_isSetoid___auto__1___closed__22_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__22);
v___x_87_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__5));
v___x_88_ = lean_array_push(v___x_87_, v___x_86_);
return v___x_88_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__24(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_89_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__23, &l_Std_DTreeMap_isSetoid___auto__1___closed__23_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__23);
v___x_90_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__7));
v___x_91_ = lean_box(2);
v___x_92_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
lean_ctor_set(v___x_92_, 1, v___x_90_);
lean_ctor_set(v___x_92_, 2, v___x_89_);
return v___x_92_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__25(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__24, &l_Std_DTreeMap_isSetoid___auto__1___closed__24_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__24);
v___x_94_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__5));
v___x_95_ = lean_array_push(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__26(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_96_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__25, &l_Std_DTreeMap_isSetoid___auto__1___closed__25_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__25);
v___x_97_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__4));
v___x_98_ = lean_box(2);
v___x_99_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v___x_97_);
lean_ctor_set(v___x_99_, 2, v___x_96_);
return v___x_99_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1(void){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__26, &l_Std_DTreeMap_isSetoid___auto__1___closed__26_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__26);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_isSetoid(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_cmp_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_box(0);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_isSetoid___boxed(lean_object* v_00_u03b1_105_, lean_object* v_00_u03b2_106_, lean_object* v_cmp_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_DTreeMap_isSetoid(v_00_u03b1_105_, v_00_u03b2_106_, v_cmp_107_);
lean_dec_ref(v_cmp_107_);
return v_res_108_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_AdditionalOperations(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Perm(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_DTreeMap_isSetoid___auto__1 = _init_l_Std_DTreeMap_isSetoid___auto__1();
lean_mark_persistent(l_Std_DTreeMap_isSetoid___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_AdditionalOperations(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Perm(uint8_t builtin);
lean_object* initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* initialize_Init_Data_Prod(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
