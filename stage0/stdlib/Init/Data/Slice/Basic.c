// Lean compiler output
// Module: Init.Data.Slice.Basic
// Imports: public import Init.Core
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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_string_object l_Std_Slice_Self_eq___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Slice_Self_eq___autoParam___closed__0 = (const lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__0_value;
static const lean_string_object l_Std_Slice_Self_eq___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Slice_Self_eq___autoParam___closed__1 = (const lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__1_value;
static const lean_string_object l_Std_Slice_Self_eq___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_Slice_Self_eq___autoParam___closed__2 = (const lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__2_value;
static const lean_string_object l_Std_Slice_Self_eq___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_Slice_Self_eq___autoParam___closed__3 = (const lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__3_value;
static const lean_ctor_object l_Std_Slice_Self_eq___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Slice_Self_eq___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__4_value_aux_0),((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Slice_Self_eq___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__4_value_aux_1),((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Slice_Self_eq___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__4_value_aux_2),((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_Slice_Self_eq___autoParam___closed__4 = (const lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__4_value;
static const lean_array_object l_Std_Slice_Self_eq___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Slice_Self_eq___autoParam___closed__5 = (const lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__5_value;
static const lean_string_object l_Std_Slice_Self_eq___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_Slice_Self_eq___autoParam___closed__6 = (const lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__6_value;
static const lean_ctor_object l_Std_Slice_Self_eq___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Slice_Self_eq___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__7_value_aux_0),((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Slice_Self_eq___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__7_value_aux_1),((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Slice_Self_eq___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__7_value_aux_2),((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_Slice_Self_eq___autoParam___closed__7 = (const lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__7_value;
static const lean_string_object l_Std_Slice_Self_eq___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Slice_Self_eq___autoParam___closed__8 = (const lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__8_value;
static const lean_ctor_object l_Std_Slice_Self_eq___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Slice_Self_eq___autoParam___closed__9 = (const lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__9_value;
static const lean_string_object l_Std_Slice_Self_eq___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l_Std_Slice_Self_eq___autoParam___closed__10 = (const lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__10_value;
static const lean_ctor_object l_Std_Slice_Self_eq___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Slice_Self_eq___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__11_value_aux_0),((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Slice_Self_eq___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__11_value_aux_1),((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Slice_Self_eq___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__11_value_aux_2),((lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l_Std_Slice_Self_eq___autoParam___closed__11 = (const lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__11_value;
static const lean_string_object l_Std_Slice_Self_eq___autoParam___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Std_Slice_Self_eq___autoParam___closed__12 = (const lean_object*)&l_Std_Slice_Self_eq___autoParam___closed__12_value;
static lean_once_cell_t l_Std_Slice_Self_eq___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Slice_Self_eq___autoParam___closed__13;
static lean_once_cell_t l_Std_Slice_Self_eq___autoParam___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Slice_Self_eq___autoParam___closed__14;
static lean_once_cell_t l_Std_Slice_Self_eq___autoParam___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Slice_Self_eq___autoParam___closed__15;
static lean_once_cell_t l_Std_Slice_Self_eq___autoParam___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Slice_Self_eq___autoParam___closed__16;
static lean_once_cell_t l_Std_Slice_Self_eq___autoParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Slice_Self_eq___autoParam___closed__17;
static lean_once_cell_t l_Std_Slice_Self_eq___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Slice_Self_eq___autoParam___closed__18;
static lean_once_cell_t l_Std_Slice_Self_eq___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Slice_Self_eq___autoParam___closed__19;
static lean_once_cell_t l_Std_Slice_Self_eq___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Slice_Self_eq___autoParam___closed__20;
static lean_once_cell_t l_Std_Slice_Self_eq___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Slice_Self_eq___autoParam___closed__21;
LEAN_EXPORT lean_object* l_Std_Slice_Self_eq___autoParam;
static lean_object* _init_l_Std_Slice_Self_eq___autoParam___closed__13(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = ((lean_object*)(l_Std_Slice_Self_eq___autoParam___closed__12));
v___x_29_ = l_Lean_mkAtom(v___x_28_);
return v___x_29_;
}
}
static lean_object* _init_l_Std_Slice_Self_eq___autoParam___closed__14(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_obj_once(&l_Std_Slice_Self_eq___autoParam___closed__13, &l_Std_Slice_Self_eq___autoParam___closed__13_once, _init_l_Std_Slice_Self_eq___autoParam___closed__13);
v___x_31_ = ((lean_object*)(l_Std_Slice_Self_eq___autoParam___closed__5));
v___x_32_ = lean_array_push(v___x_31_, v___x_30_);
return v___x_32_;
}
}
static lean_object* _init_l_Std_Slice_Self_eq___autoParam___closed__15(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_33_ = lean_obj_once(&l_Std_Slice_Self_eq___autoParam___closed__14, &l_Std_Slice_Self_eq___autoParam___closed__14_once, _init_l_Std_Slice_Self_eq___autoParam___closed__14);
v___x_34_ = ((lean_object*)(l_Std_Slice_Self_eq___autoParam___closed__11));
v___x_35_ = lean_box(2);
v___x_36_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v___x_34_);
lean_ctor_set(v___x_36_, 2, v___x_33_);
return v___x_36_;
}
}
static lean_object* _init_l_Std_Slice_Self_eq___autoParam___closed__16(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_obj_once(&l_Std_Slice_Self_eq___autoParam___closed__15, &l_Std_Slice_Self_eq___autoParam___closed__15_once, _init_l_Std_Slice_Self_eq___autoParam___closed__15);
v___x_38_ = ((lean_object*)(l_Std_Slice_Self_eq___autoParam___closed__5));
v___x_39_ = lean_array_push(v___x_38_, v___x_37_);
return v___x_39_;
}
}
static lean_object* _init_l_Std_Slice_Self_eq___autoParam___closed__17(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_40_ = lean_obj_once(&l_Std_Slice_Self_eq___autoParam___closed__16, &l_Std_Slice_Self_eq___autoParam___closed__16_once, _init_l_Std_Slice_Self_eq___autoParam___closed__16);
v___x_41_ = ((lean_object*)(l_Std_Slice_Self_eq___autoParam___closed__9));
v___x_42_ = lean_box(2);
v___x_43_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___x_41_);
lean_ctor_set(v___x_43_, 2, v___x_40_);
return v___x_43_;
}
}
static lean_object* _init_l_Std_Slice_Self_eq___autoParam___closed__18(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_obj_once(&l_Std_Slice_Self_eq___autoParam___closed__17, &l_Std_Slice_Self_eq___autoParam___closed__17_once, _init_l_Std_Slice_Self_eq___autoParam___closed__17);
v___x_45_ = ((lean_object*)(l_Std_Slice_Self_eq___autoParam___closed__5));
v___x_46_ = lean_array_push(v___x_45_, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_l_Std_Slice_Self_eq___autoParam___closed__19(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_Std_Slice_Self_eq___autoParam___closed__18, &l_Std_Slice_Self_eq___autoParam___closed__18_once, _init_l_Std_Slice_Self_eq___autoParam___closed__18);
v___x_48_ = ((lean_object*)(l_Std_Slice_Self_eq___autoParam___closed__7));
v___x_49_ = lean_box(2);
v___x_50_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
lean_ctor_set(v___x_50_, 2, v___x_47_);
return v___x_50_;
}
}
static lean_object* _init_l_Std_Slice_Self_eq___autoParam___closed__20(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Std_Slice_Self_eq___autoParam___closed__19, &l_Std_Slice_Self_eq___autoParam___closed__19_once, _init_l_Std_Slice_Self_eq___autoParam___closed__19);
v___x_52_ = ((lean_object*)(l_Std_Slice_Self_eq___autoParam___closed__5));
v___x_53_ = lean_array_push(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_Slice_Self_eq___autoParam___closed__21(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_obj_once(&l_Std_Slice_Self_eq___autoParam___closed__20, &l_Std_Slice_Self_eq___autoParam___closed__20_once, _init_l_Std_Slice_Self_eq___autoParam___closed__20);
v___x_55_ = ((lean_object*)(l_Std_Slice_Self_eq___autoParam___closed__4));
v___x_56_ = lean_box(2);
v___x_57_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_54_);
return v___x_57_;
}
}
static lean_object* _init_l_Std_Slice_Self_eq___autoParam(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_obj_once(&l_Std_Slice_Self_eq___autoParam___closed__21, &l_Std_Slice_Self_eq___autoParam___closed__21_once, _init_l_Std_Slice_Self_eq___autoParam___closed__21);
return v___x_58_;
}
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Slice_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Slice_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_Slice_Self_eq___autoParam = _init_l_Std_Slice_Self_eq___autoParam();
lean_mark_persistent(l_Std_Slice_Self_eq___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Core(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Slice_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Slice_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
