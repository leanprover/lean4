// Lean compiler output
// Module: Init.Data.Array.Set
// Imports: public import Init.Tactics
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static const lean_string_object l_Array_set___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Array_set___auto__1___closed__0 = (const lean_object*)&l_Array_set___auto__1___closed__0_value;
static const lean_string_object l_Array_set___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Array_set___auto__1___closed__1 = (const lean_object*)&l_Array_set___auto__1___closed__1_value;
static const lean_string_object l_Array_set___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Array_set___auto__1___closed__2 = (const lean_object*)&l_Array_set___auto__1___closed__2_value;
static const lean_string_object l_Array_set___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Array_set___auto__1___closed__3 = (const lean_object*)&l_Array_set___auto__1___closed__3_value;
static const lean_ctor_object l_Array_set___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_set___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_set___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_set___auto__1___closed__4_value_aux_0),((lean_object*)&l_Array_set___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_set___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_set___auto__1___closed__4_value_aux_1),((lean_object*)&l_Array_set___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_set___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_set___auto__1___closed__4_value_aux_2),((lean_object*)&l_Array_set___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Array_set___auto__1___closed__4 = (const lean_object*)&l_Array_set___auto__1___closed__4_value;
static const lean_array_object l_Array_set___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_set___auto__1___closed__5 = (const lean_object*)&l_Array_set___auto__1___closed__5_value;
static const lean_string_object l_Array_set___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Array_set___auto__1___closed__6 = (const lean_object*)&l_Array_set___auto__1___closed__6_value;
static const lean_ctor_object l_Array_set___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_set___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_set___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_set___auto__1___closed__7_value_aux_0),((lean_object*)&l_Array_set___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_set___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_set___auto__1___closed__7_value_aux_1),((lean_object*)&l_Array_set___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_set___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_set___auto__1___closed__7_value_aux_2),((lean_object*)&l_Array_set___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Array_set___auto__1___closed__7 = (const lean_object*)&l_Array_set___auto__1___closed__7_value;
static const lean_string_object l_Array_set___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Array_set___auto__1___closed__8 = (const lean_object*)&l_Array_set___auto__1___closed__8_value;
static const lean_ctor_object l_Array_set___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_set___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Array_set___auto__1___closed__9 = (const lean_object*)&l_Array_set___auto__1___closed__9_value;
static const lean_string_object l_Array_set___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticGet_elem_tactic"};
static const lean_object* l_Array_set___auto__1___closed__10 = (const lean_object*)&l_Array_set___auto__1___closed__10_value;
static const lean_ctor_object l_Array_set___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_set___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(141, 31, 109, 153, 11, 229, 201, 51)}};
static const lean_object* l_Array_set___auto__1___closed__11 = (const lean_object*)&l_Array_set___auto__1___closed__11_value;
static const lean_string_object l_Array_set___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "get_elem_tactic"};
static const lean_object* l_Array_set___auto__1___closed__12 = (const lean_object*)&l_Array_set___auto__1___closed__12_value;
static lean_once_cell_t l_Array_set___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_set___auto__1___closed__13;
static lean_once_cell_t l_Array_set___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_set___auto__1___closed__14;
static lean_once_cell_t l_Array_set___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_set___auto__1___closed__15;
static lean_once_cell_t l_Array_set___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_set___auto__1___closed__16;
static lean_once_cell_t l_Array_set___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_set___auto__1___closed__17;
static lean_once_cell_t l_Array_set___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_set___auto__1___closed__18;
static lean_once_cell_t l_Array_set___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_set___auto__1___closed__19;
static lean_once_cell_t l_Array_set___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_set___auto__1___closed__20;
static lean_once_cell_t l_Array_set___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_set___auto__1___closed__21;
LEAN_EXPORT lean_object* l_Array_set___auto__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_setIfInBounds___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_setIfInBounds___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_setIfInBounds(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_setIfInBounds___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_set_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Array_set___auto__1___closed__13(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = ((lean_object*)(l_Array_set___auto__1___closed__12));
v___x_26_ = l_Lean_mkAtom(v___x_25_);
return v___x_26_;
}
}
static lean_object* _init_l_Array_set___auto__1___closed__14(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_obj_once(&l_Array_set___auto__1___closed__13, &l_Array_set___auto__1___closed__13_once, _init_l_Array_set___auto__1___closed__13);
v___x_28_ = ((lean_object*)(l_Array_set___auto__1___closed__5));
v___x_29_ = lean_array_push(v___x_28_, v___x_27_);
return v___x_29_;
}
}
static lean_object* _init_l_Array_set___auto__1___closed__15(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_30_ = lean_obj_once(&l_Array_set___auto__1___closed__14, &l_Array_set___auto__1___closed__14_once, _init_l_Array_set___auto__1___closed__14);
v___x_31_ = ((lean_object*)(l_Array_set___auto__1___closed__11));
v___x_32_ = lean_box(2);
v___x_33_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v___x_31_);
lean_ctor_set(v___x_33_, 2, v___x_30_);
return v___x_33_;
}
}
static lean_object* _init_l_Array_set___auto__1___closed__16(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_obj_once(&l_Array_set___auto__1___closed__15, &l_Array_set___auto__1___closed__15_once, _init_l_Array_set___auto__1___closed__15);
v___x_35_ = ((lean_object*)(l_Array_set___auto__1___closed__5));
v___x_36_ = lean_array_push(v___x_35_, v___x_34_);
return v___x_36_;
}
}
static lean_object* _init_l_Array_set___auto__1___closed__17(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_37_ = lean_obj_once(&l_Array_set___auto__1___closed__16, &l_Array_set___auto__1___closed__16_once, _init_l_Array_set___auto__1___closed__16);
v___x_38_ = ((lean_object*)(l_Array_set___auto__1___closed__9));
v___x_39_ = lean_box(2);
v___x_40_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v___x_38_);
lean_ctor_set(v___x_40_, 2, v___x_37_);
return v___x_40_;
}
}
static lean_object* _init_l_Array_set___auto__1___closed__18(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = lean_obj_once(&l_Array_set___auto__1___closed__17, &l_Array_set___auto__1___closed__17_once, _init_l_Array_set___auto__1___closed__17);
v___x_42_ = ((lean_object*)(l_Array_set___auto__1___closed__5));
v___x_43_ = lean_array_push(v___x_42_, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_l_Array_set___auto__1___closed__19(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_44_ = lean_obj_once(&l_Array_set___auto__1___closed__18, &l_Array_set___auto__1___closed__18_once, _init_l_Array_set___auto__1___closed__18);
v___x_45_ = ((lean_object*)(l_Array_set___auto__1___closed__7));
v___x_46_ = lean_box(2);
v___x_47_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_45_);
lean_ctor_set(v___x_47_, 2, v___x_44_);
return v___x_47_;
}
}
static lean_object* _init_l_Array_set___auto__1___closed__20(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_obj_once(&l_Array_set___auto__1___closed__19, &l_Array_set___auto__1___closed__19_once, _init_l_Array_set___auto__1___closed__19);
v___x_49_ = ((lean_object*)(l_Array_set___auto__1___closed__5));
v___x_50_ = lean_array_push(v___x_49_, v___x_48_);
return v___x_50_;
}
}
static lean_object* _init_l_Array_set___auto__1___closed__21(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_51_ = lean_obj_once(&l_Array_set___auto__1___closed__20, &l_Array_set___auto__1___closed__20_once, _init_l_Array_set___auto__1___closed__20);
v___x_52_ = ((lean_object*)(l_Array_set___auto__1___closed__4));
v___x_53_ = lean_box(2);
v___x_54_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v___x_52_);
lean_ctor_set(v___x_54_, 2, v___x_51_);
return v___x_54_;
}
}
static lean_object* _init_l_Array_set___auto__1(void){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_obj_once(&l_Array_set___auto__1___closed__21, &l_Array_set___auto__1___closed__21_once, _init_l_Array_set___auto__1___closed__21);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Array_set___boxed(lean_object* v_00_u03b1_61_, lean_object* v_xs_62_, lean_object* v_i_63_, lean_object* v_v_64_, lean_object* v_h_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = lean_array_fset(v_xs_62_, v_i_63_, v_v_64_);
lean_dec(v_i_63_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Array_setIfInBounds___redArg(lean_object* v_xs_67_, lean_object* v_i_68_, lean_object* v_v_69_){
_start:
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = lean_array_get_size(v_xs_67_);
v___x_71_ = lean_nat_dec_lt(v_i_68_, v___x_70_);
if (v___x_71_ == 0)
{
lean_dec(v_v_69_);
return v_xs_67_;
}
else
{
lean_object* v___x_72_; 
v___x_72_ = lean_array_fset(v_xs_67_, v_i_68_, v_v_69_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l_Array_setIfInBounds___redArg___boxed(lean_object* v_xs_73_, lean_object* v_i_74_, lean_object* v_v_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Array_setIfInBounds___redArg(v_xs_73_, v_i_74_, v_v_75_);
lean_dec(v_i_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Array_setIfInBounds(lean_object* v_00_u03b1_77_, lean_object* v_xs_78_, lean_object* v_i_79_, lean_object* v_v_80_){
_start:
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = lean_array_get_size(v_xs_78_);
v___x_82_ = lean_nat_dec_lt(v_i_79_, v___x_81_);
if (v___x_82_ == 0)
{
lean_dec(v_v_80_);
return v_xs_78_;
}
else
{
lean_object* v___x_83_; 
v___x_83_ = lean_array_fset(v_xs_78_, v_i_79_, v_v_80_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Array_setIfInBounds___boxed(lean_object* v_00_u03b1_84_, lean_object* v_xs_85_, lean_object* v_i_86_, lean_object* v_v_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Array_setIfInBounds(v_00_u03b1_84_, v_xs_85_, v_i_86_, v_v_87_);
lean_dec(v_i_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Array_set_x21___boxed(lean_object* v_00_u03b1_93_, lean_object* v_xs_94_, lean_object* v_i_95_, lean_object* v_v_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = lean_array_set(v_xs_94_, v_i_95_, v_v_96_);
lean_dec(v_i_95_);
return v_res_97_;
}
}
lean_object* runtime_initialize_Init_Tactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Set(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Set(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Array_set___auto__1 = _init_l_Array_set___auto__1();
lean_mark_persistent(l_Array_set___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Tactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Set(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Set(builtin);
}
#ifdef __cplusplus
}
#endif
