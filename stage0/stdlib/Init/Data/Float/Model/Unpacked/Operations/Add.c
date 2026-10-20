// Lean compiler output
// Module: Init.Data.Float.Model.Unpacked.Operations.Add
// Imports: public import Init.Data.Float.Model.Unpacked.Round
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_decreaseExponent(lean_object*, lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_Sign_apply(uint8_t, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_normalize(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_UnpackedFloat_add_spec__0(lean_object*);
static const lean_ctor_object l_Float_Model_UnpackedFloat_add___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 2}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_add___closed__0 = (const lean_object*)&l_Float_Model_UnpackedFloat_add___closed__0_value;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_add___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_UnpackedFloat_add_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_add(lean_object* v_spec_5_, lean_object* v_x_6_, lean_object* v_x_7_){
_start:
{
switch(lean_obj_tag(v_x_6_))
{
case 0:
{
switch(lean_obj_tag(v_x_7_))
{
case 1:
{
lean_dec_ref_known(v_x_6_, 0);
return v_x_7_;
}
case 0:
{
uint8_t v_sign_8_; uint8_t v_sign_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; 
v_sign_8_ = lean_ctor_get_uint8(v_x_6_, 0);
v_sign_9_ = lean_ctor_get_uint8(v_x_7_, 0);
lean_dec_ref_known(v_x_7_, 0);
v___x_10_ = lean_box(v_sign_8_);
v___x_11_ = lean_obj_tag_nat(v___x_10_);
lean_dec(v___x_10_);
v___x_12_ = lean_box(v_sign_9_);
v___x_13_ = lean_obj_tag_nat(v___x_12_);
lean_dec(v___x_12_);
v___x_14_ = lean_nat_dec_eq(v___x_11_, v___x_13_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; 
lean_dec_ref_known(v_x_6_, 0);
v___x_15_ = lean_box(1);
return v___x_15_;
}
else
{
return v_x_6_;
}
}
default: 
{
lean_dec(v_x_7_);
return v_x_6_;
}
}
}
case 1:
{
lean_dec(v_x_7_);
return v_x_6_;
}
case 2:
{
if (lean_obj_tag(v_x_7_) == 2)
{
uint8_t v_sign_16_; uint8_t v_sign_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v_sign_16_ = lean_ctor_get_uint8(v_x_6_, 0);
v_sign_17_ = lean_ctor_get_uint8(v_x_7_, 0);
lean_dec_ref_known(v_x_7_, 0);
v___x_18_ = lean_box(v_sign_16_);
v___x_19_ = lean_obj_tag_nat(v___x_18_);
lean_dec(v___x_18_);
v___x_20_ = lean_box(v_sign_17_);
v___x_21_ = lean_obj_tag_nat(v___x_20_);
lean_dec(v___x_20_);
v___x_22_ = lean_nat_dec_eq(v___x_19_, v___x_21_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; 
lean_dec_ref_known(v_x_6_, 0);
v___x_23_ = ((lean_object*)(l_Float_Model_UnpackedFloat_add___closed__0));
return v___x_23_;
}
else
{
return v_x_6_;
}
}
else
{
lean_dec_ref_known(v_x_6_, 0);
return v_x_7_;
}
}
default: 
{
switch(lean_obj_tag(v_x_7_))
{
case 2:
{
uint8_t v_sign_24_; lean_object* v_mantissa_25_; lean_object* v_exponent_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_33_; 
lean_dec_ref_known(v_x_7_, 0);
v_sign_24_ = lean_ctor_get_uint8(v_x_6_, sizeof(void*)*2);
v_mantissa_25_ = lean_ctor_get(v_x_6_, 0);
v_exponent_26_ = lean_ctor_get(v_x_6_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_x_6_);
if (v_isSharedCheck_33_ == 0)
{
v___x_28_ = v_x_6_;
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_exponent_26_);
lean_inc(v_mantissa_25_);
lean_dec(v_x_6_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_31_; 
if (v_isShared_29_ == 0)
{
v___x_31_ = v___x_28_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_mantissa_25_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v_exponent_26_);
lean_ctor_set_uint8(v_reuseFailAlloc_32_, sizeof(void*)*2, v_sign_24_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
case 3:
{
uint8_t v_sign_34_; lean_object* v_mantissa_35_; lean_object* v_exponent_36_; uint8_t v_sign_37_; lean_object* v_mantissa_38_; lean_object* v_exponent_39_; lean_object* v___y_41_; uint8_t v___x_53_; 
v_sign_34_ = lean_ctor_get_uint8(v_x_6_, sizeof(void*)*2);
v_mantissa_35_ = lean_ctor_get(v_x_6_, 0);
lean_inc(v_mantissa_35_);
v_exponent_36_ = lean_ctor_get(v_x_6_, 1);
lean_inc(v_exponent_36_);
lean_dec_ref_known(v_x_6_, 2);
v_sign_37_ = lean_ctor_get_uint8(v_x_7_, sizeof(void*)*2);
v_mantissa_38_ = lean_ctor_get(v_x_7_, 0);
lean_inc(v_mantissa_38_);
v_exponent_39_ = lean_ctor_get(v_x_7_, 1);
lean_inc(v_exponent_39_);
lean_dec_ref_known(v_x_7_, 2);
v___x_53_ = lean_int_dec_le(v_exponent_36_, v_exponent_39_);
if (v___x_53_ == 0)
{
lean_inc(v_exponent_39_);
v___y_41_ = v_exponent_39_;
goto v___jp_40_;
}
else
{
lean_inc(v_exponent_36_);
v___y_41_ = v_exponent_36_;
goto v___jp_40_;
}
v___jp_40_:
{
lean_object* v___x_42_; lean_object* v_fst_43_; lean_object* v___x_44_; lean_object* v_fst_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v_mantissa_50_; uint8_t v___x_51_; lean_object* v___x_52_; 
v___x_42_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_mantissa_35_, v_exponent_36_, v___y_41_);
lean_dec(v_exponent_36_);
lean_dec(v_mantissa_35_);
v_fst_43_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_fst_43_);
lean_dec_ref(v___x_42_);
v___x_44_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_mantissa_38_, v_exponent_39_, v___y_41_);
lean_dec(v_exponent_39_);
lean_dec(v_mantissa_38_);
v_fst_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc(v_fst_45_);
lean_dec_ref(v___x_44_);
v___x_46_ = lean_nat_to_int(v_fst_43_);
v___x_47_ = l_Float_Model_UnpackedFloat_Sign_apply(v_sign_34_, v___x_46_);
lean_dec(v___x_46_);
v___x_48_ = lean_nat_to_int(v_fst_45_);
v___x_49_ = l_Float_Model_UnpackedFloat_Sign_apply(v_sign_37_, v___x_48_);
lean_dec(v___x_48_);
v_mantissa_50_ = lean_int_add(v___x_47_, v___x_49_);
lean_dec(v___x_49_);
lean_dec(v___x_47_);
v___x_51_ = 1;
v___x_52_ = l_Float_Model_UnpackedFloat_normalize(v_spec_5_, v_mantissa_50_, v___y_41_, v___x_51_);
lean_dec(v___y_41_);
lean_dec(v_mantissa_50_);
return v___x_52_;
}
}
default: 
{
lean_dec_ref_known(v_x_6_, 2);
return v_x_7_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_add___boxed(lean_object* v_spec_54_, lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Float_Model_UnpackedFloat_add(v_spec_54_, v_x_55_, v_x_56_);
lean_dec_ref(v_spec_54_);
return v_res_57_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Add(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Unpacked_Operations_Add(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Unpacked_Operations_Add(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Model_Unpacked_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Unpacked_Operations_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Unpacked_Operations_Add(builtin);
}
#ifdef __cplusplus
}
#endif
