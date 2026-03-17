// Lean compiler output
// Module: Init.Data.String.Legacy
// Imports: public import Init.Data.String.Basic
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
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitToList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitToList___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitOnAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_splitOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_splitOn___closed__0 = (const lean_object*)&l_String_splitOn___closed__0_value;
LEAN_EXPORT lean_object* l_String_splitOn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitOn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux(lean_object* v_s_1_, lean_object* v_p_2_, lean_object* v_b_3_, lean_object* v_i_4_, lean_object* v_r_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = lean_string_utf8_at_end(v_s_1_, v_i_4_);
if (v___x_6_ == 0)
{
uint32_t v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_7_ = lean_string_utf8_get(v_s_1_, v_i_4_);
v___x_8_ = lean_box_uint32(v___x_7_);
lean_inc_ref(v_p_2_);
v___x_9_ = lean_apply_1(v_p_2_, v___x_8_);
v___x_10_ = lean_unbox(v___x_9_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; 
v___x_11_ = lean_string_utf8_next(v_s_1_, v_i_4_);
lean_dec(v_i_4_);
v_i_4_ = v___x_11_;
goto _start;
}
else
{
lean_object* v_i_x27_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_i_x27_13_ = lean_string_utf8_next(v_s_1_, v_i_4_);
v___x_14_ = lean_string_utf8_extract(v_s_1_, v_b_3_, v_i_4_);
lean_dec(v_i_4_);
lean_dec(v_b_3_);
v___x_15_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v_r_5_);
lean_inc(v_i_x27_13_);
v_b_3_ = v_i_x27_13_;
v_i_4_ = v_i_x27_13_;
v_r_5_ = v___x_15_;
goto _start;
}
}
else
{
lean_object* v___x_17_; lean_object* v_r_18_; lean_object* v___x_19_; 
lean_dec_ref(v_p_2_);
v___x_17_ = lean_string_utf8_extract(v_s_1_, v_b_3_, v_i_4_);
lean_dec(v_i_4_);
lean_dec(v_b_3_);
v_r_18_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_r_18_, 0, v___x_17_);
lean_ctor_set(v_r_18_, 1, v_r_5_);
v___x_19_ = l_List_reverse___redArg(v_r_18_);
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l_String_splitAux___boxed(lean_object* v_s_20_, lean_object* v_p_21_, lean_object* v_b_22_, lean_object* v_i_23_, lean_object* v_r_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_String_splitAux(v_s_20_, v_p_21_, v_b_22_, v_i_23_, v_r_24_);
lean_dec_ref(v_s_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_String_splitToList(lean_object* v_s_26_, lean_object* v_p_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = lean_box(0);
v___x_30_ = l_String_splitAux(v_s_26_, v_p_27_, v___x_28_, v___x_28_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_String_splitToList___boxed(lean_object* v_s_31_, lean_object* v_p_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_String_splitToList(v_s_31_, v_p_32_);
lean_dec_ref(v_s_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_String_splitOnAux(lean_object* v_s_34_, lean_object* v_sep_35_, lean_object* v_b_36_, lean_object* v_i_37_, lean_object* v_j_38_, lean_object* v_r_39_){
_start:
{
uint8_t v___x_40_; 
v___x_40_ = lean_string_utf8_at_end(v_s_34_, v_i_37_);
if (v___x_40_ == 0)
{
uint32_t v___x_41_; uint32_t v___x_42_; uint8_t v___x_43_; 
v___x_41_ = lean_string_utf8_get(v_s_34_, v_i_37_);
v___x_42_ = lean_string_utf8_get(v_sep_35_, v_j_38_);
v___x_43_ = lean_uint32_dec_eq(v___x_41_, v___x_42_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_nat_sub(v_i_37_, v_j_38_);
lean_dec(v_j_38_);
lean_dec(v_i_37_);
v___x_45_ = lean_string_utf8_next(v_s_34_, v___x_44_);
lean_dec(v___x_44_);
v___x_46_ = lean_unsigned_to_nat(0u);
v_i_37_ = v___x_45_;
v_j_38_ = v___x_46_;
goto _start;
}
else
{
lean_object* v_i_48_; lean_object* v_j_49_; uint8_t v___x_50_; 
v_i_48_ = lean_string_utf8_next(v_s_34_, v_i_37_);
lean_dec(v_i_37_);
v_j_49_ = lean_string_utf8_next(v_sep_35_, v_j_38_);
lean_dec(v_j_38_);
v___x_50_ = lean_string_utf8_at_end(v_sep_35_, v_j_49_);
if (v___x_50_ == 0)
{
v_i_37_ = v_i_48_;
v_j_38_ = v_j_49_;
goto _start;
}
else
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = lean_unsigned_to_nat(0u);
v___x_53_ = lean_nat_sub(v_i_48_, v_j_49_);
lean_dec(v_j_49_);
v___x_54_ = lean_string_utf8_extract(v_s_34_, v_b_36_, v___x_53_);
lean_dec(v___x_53_);
lean_dec(v_b_36_);
v___x_55_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v_r_39_);
lean_inc(v_i_48_);
v_b_36_ = v_i_48_;
v_i_37_ = v_i_48_;
v_j_38_ = v___x_52_;
v_r_39_ = v___x_55_;
goto _start;
}
}
}
else
{
lean_object* v___x_57_; lean_object* v_r_58_; lean_object* v___x_59_; 
lean_dec(v_j_38_);
v___x_57_ = lean_string_utf8_extract(v_s_34_, v_b_36_, v_i_37_);
lean_dec(v_i_37_);
lean_dec(v_b_36_);
v_r_58_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_r_58_, 0, v___x_57_);
lean_ctor_set(v_r_58_, 1, v_r_39_);
v___x_59_ = l_List_reverse___redArg(v_r_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_String_splitOnAux___boxed(lean_object* v_s_60_, lean_object* v_sep_61_, lean_object* v_b_62_, lean_object* v_i_63_, lean_object* v_j_64_, lean_object* v_r_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_String_splitOnAux(v_s_60_, v_sep_61_, v_b_62_, v_i_63_, v_j_64_, v_r_65_);
lean_dec_ref(v_sep_61_);
lean_dec_ref(v_s_60_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_String_splitOn(lean_object* v_s_68_, lean_object* v_sep_69_){
_start:
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = ((lean_object*)(l_String_splitOn___closed__0));
v___x_71_ = lean_string_dec_eq(v_sep_69_, v___x_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_unsigned_to_nat(0u);
v___x_73_ = lean_box(0);
v___x_74_ = l_String_splitOnAux(v_s_68_, v_sep_69_, v___x_72_, v___x_72_, v___x_72_, v___x_73_);
lean_dec_ref(v_s_68_);
return v___x_74_;
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_box(0);
v___x_76_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_76_, 0, v_s_68_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_String_splitOn___boxed(lean_object* v_s_77_, lean_object* v_sep_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_String_splitOn(v_s_77_, v_sep_78_);
lean_dec_ref(v_sep_78_);
return v_res_79_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Legacy(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Legacy(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Legacy(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Legacy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Legacy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Legacy(builtin);
}
#ifdef __cplusplus
}
#endif
