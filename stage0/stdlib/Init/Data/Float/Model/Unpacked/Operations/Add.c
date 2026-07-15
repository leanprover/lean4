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
uint8_t l_Float_Model_UnpackedFloat_instBEqSign_beq(uint8_t, uint8_t);
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
uint8_t v_sign_8_; uint8_t v_sign_9_; uint8_t v___x_10_; 
v_sign_8_ = lean_ctor_get_uint8(v_x_6_, 0);
v_sign_9_ = lean_ctor_get_uint8(v_x_7_, 0);
lean_dec_ref_known(v_x_7_, 0);
v___x_10_ = l_Float_Model_UnpackedFloat_instBEqSign_beq(v_sign_8_, v_sign_9_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; 
lean_dec_ref_known(v_x_6_, 0);
v___x_11_ = lean_box(1);
return v___x_11_;
}
else
{
return v_x_6_;
}
}
case 2:
{
lean_dec_ref_known(v_x_7_, 0);
return v_x_6_;
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
switch(lean_obj_tag(v_x_7_))
{
case 1:
{
lean_dec_ref_known(v_x_6_, 0);
return v_x_7_;
}
case 0:
{
lean_dec_ref_known(v_x_6_, 0);
return v_x_7_;
}
case 2:
{
uint8_t v_sign_12_; uint8_t v_sign_13_; uint8_t v___x_14_; 
v_sign_12_ = lean_ctor_get_uint8(v_x_6_, 0);
v_sign_13_ = lean_ctor_get_uint8(v_x_7_, 0);
lean_dec_ref_known(v_x_7_, 0);
v___x_14_ = l_Float_Model_UnpackedFloat_instBEqSign_beq(v_sign_12_, v_sign_13_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; 
lean_dec_ref_known(v_x_6_, 0);
v___x_15_ = ((lean_object*)(l_Float_Model_UnpackedFloat_add___closed__0));
return v___x_15_;
}
else
{
return v_x_6_;
}
}
default: 
{
lean_dec_ref_known(v_x_6_, 0);
return v_x_7_;
}
}
}
default: 
{
switch(lean_obj_tag(v_x_7_))
{
case 2:
{
uint8_t v_sign_16_; lean_object* v_mantissa_17_; lean_object* v_exponent_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_25_; 
lean_dec_ref_known(v_x_7_, 0);
v_sign_16_ = lean_ctor_get_uint8(v_x_6_, sizeof(void*)*2);
v_mantissa_17_ = lean_ctor_get(v_x_6_, 0);
v_exponent_18_ = lean_ctor_get(v_x_6_, 1);
v_isSharedCheck_25_ = !lean_is_exclusive(v_x_6_);
if (v_isSharedCheck_25_ == 0)
{
v___x_20_ = v_x_6_;
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_exponent_18_);
lean_inc(v_mantissa_17_);
lean_dec(v_x_6_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_23_; 
if (v_isShared_21_ == 0)
{
v___x_23_ = v___x_20_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_mantissa_17_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v_exponent_18_);
lean_ctor_set_uint8(v_reuseFailAlloc_24_, sizeof(void*)*2, v_sign_16_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
case 3:
{
uint8_t v_sign_26_; lean_object* v_mantissa_27_; lean_object* v_exponent_28_; uint8_t v_sign_29_; lean_object* v_mantissa_30_; lean_object* v_exponent_31_; lean_object* v___y_33_; uint8_t v___x_45_; 
v_sign_26_ = lean_ctor_get_uint8(v_x_6_, sizeof(void*)*2);
v_mantissa_27_ = lean_ctor_get(v_x_6_, 0);
lean_inc(v_mantissa_27_);
v_exponent_28_ = lean_ctor_get(v_x_6_, 1);
lean_inc(v_exponent_28_);
lean_dec_ref_known(v_x_6_, 2);
v_sign_29_ = lean_ctor_get_uint8(v_x_7_, sizeof(void*)*2);
v_mantissa_30_ = lean_ctor_get(v_x_7_, 0);
lean_inc(v_mantissa_30_);
v_exponent_31_ = lean_ctor_get(v_x_7_, 1);
lean_inc(v_exponent_31_);
lean_dec_ref_known(v_x_7_, 2);
v___x_45_ = lean_int_dec_le(v_exponent_28_, v_exponent_31_);
if (v___x_45_ == 0)
{
lean_inc(v_exponent_31_);
v___y_33_ = v_exponent_31_;
goto v___jp_32_;
}
else
{
lean_inc(v_exponent_28_);
v___y_33_ = v_exponent_28_;
goto v___jp_32_;
}
v___jp_32_:
{
lean_object* v___x_34_; lean_object* v_fst_35_; lean_object* v___x_36_; lean_object* v_fst_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v_mantissa_42_; uint8_t v___x_43_; lean_object* v___x_44_; 
v___x_34_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_mantissa_27_, v_exponent_28_, v___y_33_);
lean_dec(v_exponent_28_);
lean_dec(v_mantissa_27_);
v_fst_35_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_fst_35_);
lean_dec_ref(v___x_34_);
v___x_36_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_mantissa_30_, v_exponent_31_, v___y_33_);
lean_dec(v_exponent_31_);
lean_dec(v_mantissa_30_);
v_fst_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc(v_fst_37_);
lean_dec_ref(v___x_36_);
v___x_38_ = lean_nat_to_int(v_fst_35_);
v___x_39_ = l_Float_Model_UnpackedFloat_Sign_apply(v_sign_26_, v___x_38_);
lean_dec(v___x_38_);
v___x_40_ = lean_nat_to_int(v_fst_37_);
v___x_41_ = l_Float_Model_UnpackedFloat_Sign_apply(v_sign_29_, v___x_40_);
lean_dec(v___x_40_);
v_mantissa_42_ = lean_int_add(v___x_39_, v___x_41_);
lean_dec(v___x_41_);
lean_dec(v___x_39_);
v___x_43_ = 1;
v___x_44_ = l_Float_Model_UnpackedFloat_normalize(v_spec_5_, v_mantissa_42_, v___y_33_, v___x_43_);
lean_dec(v___y_33_);
lean_dec(v_mantissa_42_);
return v___x_44_;
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
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_add___boxed(lean_object* v_spec_46_, lean_object* v_x_47_, lean_object* v_x_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Float_Model_UnpackedFloat_add(v_spec_46_, v_x_47_, v_x_48_);
lean_dec_ref(v_spec_46_);
return v_res_49_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Add(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
