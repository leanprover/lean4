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
lean_object* l_Float_Model_UnpackedFloat_Sign_ctorIdx(uint8_t);
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
uint8_t v_sign_8_; uint8_t v_sign_9_; lean_object* v___x_10_; lean_object* v___x_11_; uint8_t v___x_12_; 
v_sign_8_ = lean_ctor_get_uint8(v_x_6_, 0);
v_sign_9_ = lean_ctor_get_uint8(v_x_7_, 0);
lean_dec_ref_known(v_x_7_, 0);
v___x_10_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_sign_8_);
v___x_11_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_sign_9_);
v___x_12_ = lean_nat_dec_eq(v___x_10_, v___x_11_);
lean_dec(v___x_11_);
lean_dec(v___x_10_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; 
lean_dec_ref_known(v_x_6_, 0);
v___x_13_ = lean_box(1);
return v___x_13_;
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
uint8_t v_sign_14_; uint8_t v_sign_15_; lean_object* v___x_16_; lean_object* v___x_17_; uint8_t v___x_18_; 
v_sign_14_ = lean_ctor_get_uint8(v_x_6_, 0);
v_sign_15_ = lean_ctor_get_uint8(v_x_7_, 0);
lean_dec_ref_known(v_x_7_, 0);
v___x_16_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_sign_14_);
v___x_17_ = l_Float_Model_UnpackedFloat_Sign_ctorIdx(v_sign_15_);
v___x_18_ = lean_nat_dec_eq(v___x_16_, v___x_17_);
lean_dec(v___x_17_);
lean_dec(v___x_16_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; 
lean_dec_ref_known(v_x_6_, 0);
v___x_19_ = ((lean_object*)(l_Float_Model_UnpackedFloat_add___closed__0));
return v___x_19_;
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
uint8_t v_sign_20_; lean_object* v_mantissa_21_; lean_object* v_exponent_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
lean_dec_ref_known(v_x_7_, 0);
v_sign_20_ = lean_ctor_get_uint8(v_x_6_, sizeof(void*)*2);
v_mantissa_21_ = lean_ctor_get(v_x_6_, 0);
v_exponent_22_ = lean_ctor_get(v_x_6_, 1);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_6_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v_x_6_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_exponent_22_);
lean_inc(v_mantissa_21_);
lean_dec(v_x_6_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_mantissa_21_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_exponent_22_);
lean_ctor_set_uint8(v_reuseFailAlloc_28_, sizeof(void*)*2, v_sign_20_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
case 3:
{
uint8_t v_sign_30_; lean_object* v_mantissa_31_; lean_object* v_exponent_32_; uint8_t v_sign_33_; lean_object* v_mantissa_34_; lean_object* v_exponent_35_; lean_object* v___y_37_; uint8_t v___x_49_; 
v_sign_30_ = lean_ctor_get_uint8(v_x_6_, sizeof(void*)*2);
v_mantissa_31_ = lean_ctor_get(v_x_6_, 0);
lean_inc(v_mantissa_31_);
v_exponent_32_ = lean_ctor_get(v_x_6_, 1);
lean_inc(v_exponent_32_);
lean_dec_ref_known(v_x_6_, 2);
v_sign_33_ = lean_ctor_get_uint8(v_x_7_, sizeof(void*)*2);
v_mantissa_34_ = lean_ctor_get(v_x_7_, 0);
lean_inc(v_mantissa_34_);
v_exponent_35_ = lean_ctor_get(v_x_7_, 1);
lean_inc(v_exponent_35_);
lean_dec_ref_known(v_x_7_, 2);
v___x_49_ = lean_int_dec_le(v_exponent_32_, v_exponent_35_);
if (v___x_49_ == 0)
{
lean_inc(v_exponent_35_);
v___y_37_ = v_exponent_35_;
goto v___jp_36_;
}
else
{
lean_inc(v_exponent_32_);
v___y_37_ = v_exponent_32_;
goto v___jp_36_;
}
v___jp_36_:
{
lean_object* v___x_38_; lean_object* v_fst_39_; lean_object* v___x_40_; lean_object* v_fst_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v_mantissa_46_; uint8_t v___x_47_; lean_object* v___x_48_; 
v___x_38_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_mantissa_31_, v_exponent_32_, v___y_37_);
lean_dec(v_exponent_32_);
lean_dec(v_mantissa_31_);
v_fst_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_fst_39_);
lean_dec_ref(v___x_38_);
v___x_40_ = l_Float_Model_UnpackedFloat_decreaseExponent(v_mantissa_34_, v_exponent_35_, v___y_37_);
lean_dec(v_exponent_35_);
lean_dec(v_mantissa_34_);
v_fst_41_ = lean_ctor_get(v___x_40_, 0);
lean_inc(v_fst_41_);
lean_dec_ref(v___x_40_);
v___x_42_ = lean_nat_to_int(v_fst_39_);
v___x_43_ = l_Float_Model_UnpackedFloat_Sign_apply(v_sign_30_, v___x_42_);
lean_dec(v___x_42_);
v___x_44_ = lean_nat_to_int(v_fst_41_);
v___x_45_ = l_Float_Model_UnpackedFloat_Sign_apply(v_sign_33_, v___x_44_);
lean_dec(v___x_44_);
v_mantissa_46_ = lean_int_add(v___x_43_, v___x_45_);
lean_dec(v___x_45_);
lean_dec(v___x_43_);
v___x_47_ = 1;
v___x_48_ = l_Float_Model_UnpackedFloat_normalize(v_spec_5_, v_mantissa_46_, v___y_37_, v___x_47_);
lean_dec(v___y_37_);
lean_dec(v_mantissa_46_);
return v___x_48_;
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
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_add___boxed(lean_object* v_spec_50_, lean_object* v_x_51_, lean_object* v_x_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Float_Model_UnpackedFloat_add(v_spec_50_, v_x_51_, v_x_52_);
lean_dec_ref(v_spec_50_);
return v_res_53_;
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
