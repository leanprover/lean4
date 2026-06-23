// Lean compiler output
// Module: Init.Data.Float.Model.Unpacked.Operations.Mul
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_roundWithAccuracy(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Float_Model_UnpackedFloat_mul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_mul___closed__0 = (const lean_object*)&l_Float_Model_UnpackedFloat_mul___closed__0_value;
static const lean_ctor_object l_Float_Model_UnpackedFloat_mul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 2}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_mul___closed__1 = (const lean_object*)&l_Float_Model_UnpackedFloat_mul___closed__1_value;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_mul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_mul___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_mul(lean_object* v_spec_5_, lean_object* v_x_6_, lean_object* v_x_7_){
_start:
{
switch(lean_obj_tag(v_x_6_))
{
case 0:
{
switch(lean_obj_tag(v_x_7_))
{
case 0:
{
uint8_t v_sign_8_; 
v_sign_8_ = lean_ctor_get_uint8(v_x_6_, 0);
if (v_sign_8_ == 0)
{
uint8_t v_sign_9_; 
v_sign_9_ = lean_ctor_get_uint8(v_x_7_, 0);
lean_dec_ref_known(v_x_7_, 0);
if (v_sign_9_ == 0)
{
lean_object* v___x_10_; 
lean_dec_ref_known(v_x_6_, 0);
v___x_10_ = ((lean_object*)(l_Float_Model_UnpackedFloat_mul___closed__0));
return v___x_10_;
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
case 1:
{
lean_dec_ref_known(v_x_6_, 0);
return v_x_7_;
}
case 2:
{
lean_object* v___x_11_; 
lean_dec_ref_known(v_x_7_, 0);
lean_dec_ref_known(v_x_6_, 0);
v___x_11_ = lean_box(1);
return v___x_11_;
}
default: 
{
uint8_t v_sign_12_; 
v_sign_12_ = lean_ctor_get_uint8(v_x_6_, 0);
if (v_sign_12_ == 0)
{
uint8_t v_sign_13_; 
v_sign_13_ = lean_ctor_get_uint8(v_x_7_, sizeof(void*)*2);
lean_dec_ref_known(v_x_7_, 2);
if (v_sign_13_ == 0)
{
lean_object* v___x_14_; 
lean_dec_ref_known(v_x_6_, 0);
v___x_14_ = ((lean_object*)(l_Float_Model_UnpackedFloat_mul___closed__0));
return v___x_14_;
}
else
{
return v_x_6_;
}
}
else
{
lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_22_; 
v_isSharedCheck_22_ = !lean_is_exclusive(v_x_6_);
if (v_isSharedCheck_22_ == 0)
{
v___x_16_ = v_x_6_;
v_isShared_17_ = v_isSharedCheck_22_;
goto v_resetjp_15_;
}
else
{
lean_dec(v_x_6_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_22_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
uint8_t v_sign_18_; lean_object* v___x_20_; 
v_sign_18_ = lean_ctor_get_uint8(v_x_7_, sizeof(void*)*2);
lean_dec_ref_known(v_x_7_, 2);
if (v_isShared_17_ == 0)
{
v___x_20_ = v___x_16_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 0, 1);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_ctor_set_uint8(v___x_20_, 0, v_sign_18_);
return v___x_20_;
}
}
}
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
case 0:
{
lean_object* v___x_23_; 
lean_dec_ref_known(v_x_7_, 0);
lean_dec_ref_known(v_x_6_, 0);
v___x_23_ = lean_box(1);
return v___x_23_;
}
case 1:
{
lean_dec_ref_known(v_x_6_, 0);
return v_x_7_;
}
case 2:
{
uint8_t v_sign_24_; 
v_sign_24_ = lean_ctor_get_uint8(v_x_6_, 0);
if (v_sign_24_ == 0)
{
uint8_t v_sign_25_; 
v_sign_25_ = lean_ctor_get_uint8(v_x_7_, 0);
lean_dec_ref_known(v_x_7_, 0);
if (v_sign_25_ == 0)
{
lean_object* v___x_26_; 
lean_dec_ref_known(v_x_6_, 0);
v___x_26_ = ((lean_object*)(l_Float_Model_UnpackedFloat_mul___closed__1));
return v___x_26_;
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
uint8_t v_sign_27_; 
v_sign_27_ = lean_ctor_get_uint8(v_x_6_, 0);
if (v_sign_27_ == 0)
{
uint8_t v_sign_28_; 
v_sign_28_ = lean_ctor_get_uint8(v_x_7_, sizeof(void*)*2);
lean_dec_ref_known(v_x_7_, 2);
if (v_sign_28_ == 0)
{
lean_object* v___x_29_; 
lean_dec_ref_known(v_x_6_, 0);
v___x_29_ = ((lean_object*)(l_Float_Model_UnpackedFloat_mul___closed__1));
return v___x_29_;
}
else
{
return v_x_6_;
}
}
else
{
lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_37_; 
v_isSharedCheck_37_ = !lean_is_exclusive(v_x_6_);
if (v_isSharedCheck_37_ == 0)
{
v___x_31_ = v_x_6_;
v_isShared_32_ = v_isSharedCheck_37_;
goto v_resetjp_30_;
}
else
{
lean_dec(v_x_6_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_37_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
uint8_t v_sign_33_; lean_object* v___x_35_; 
v_sign_33_ = lean_ctor_get_uint8(v_x_7_, sizeof(void*)*2);
lean_dec_ref_known(v_x_7_, 2);
if (v_isShared_32_ == 0)
{
v___x_35_ = v___x_31_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(2, 0, 1);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_ctor_set_uint8(v___x_35_, 0, v_sign_33_);
return v___x_35_;
}
}
}
}
}
}
default: 
{
switch(lean_obj_tag(v_x_7_))
{
case 0:
{
uint8_t v_sign_38_; 
v_sign_38_ = lean_ctor_get_uint8(v_x_6_, sizeof(void*)*2);
lean_dec_ref_known(v_x_6_, 2);
if (v_sign_38_ == 0)
{
uint8_t v_sign_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_47_; 
v_sign_39_ = lean_ctor_get_uint8(v_x_7_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v_x_7_);
if (v_isSharedCheck_47_ == 0)
{
v___x_41_ = v_x_7_;
v_isShared_42_ = v_isSharedCheck_47_;
goto v_resetjp_40_;
}
else
{
lean_dec(v_x_7_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_47_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
if (v_sign_39_ == 0)
{
lean_object* v___x_43_; 
lean_del_object(v___x_41_);
v___x_43_ = ((lean_object*)(l_Float_Model_UnpackedFloat_mul___closed__0));
return v___x_43_;
}
else
{
lean_object* v___x_45_; 
if (v_isShared_42_ == 0)
{
v___x_45_ = v___x_41_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 0, 1);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
lean_ctor_set_uint8(v___x_45_, 0, v_sign_38_);
return v___x_45_;
}
}
}
}
else
{
return v_x_7_;
}
}
case 1:
{
lean_dec_ref_known(v_x_6_, 2);
return v_x_7_;
}
case 2:
{
uint8_t v_sign_48_; 
v_sign_48_ = lean_ctor_get_uint8(v_x_6_, sizeof(void*)*2);
lean_dec_ref_known(v_x_6_, 2);
if (v_sign_48_ == 0)
{
uint8_t v_sign_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_57_; 
v_sign_49_ = lean_ctor_get_uint8(v_x_7_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v_x_7_);
if (v_isSharedCheck_57_ == 0)
{
v___x_51_ = v_x_7_;
v_isShared_52_ = v_isSharedCheck_57_;
goto v_resetjp_50_;
}
else
{
lean_dec(v_x_7_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_57_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
if (v_sign_49_ == 0)
{
lean_object* v___x_53_; 
lean_del_object(v___x_51_);
v___x_53_ = ((lean_object*)(l_Float_Model_UnpackedFloat_mul___closed__1));
return v___x_53_;
}
else
{
lean_object* v___x_55_; 
if (v_isShared_52_ == 0)
{
v___x_55_ = v___x_51_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(2, 0, 1);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
lean_ctor_set_uint8(v___x_55_, 0, v_sign_48_);
return v___x_55_;
}
}
}
}
else
{
return v_x_7_;
}
}
default: 
{
uint8_t v_sign_58_; lean_object* v_mantissa_59_; lean_object* v_exponent_60_; uint8_t v_sign_61_; lean_object* v_mantissa_62_; lean_object* v_exponent_63_; uint8_t v___y_65_; 
v_sign_58_ = lean_ctor_get_uint8(v_x_6_, sizeof(void*)*2);
v_mantissa_59_ = lean_ctor_get(v_x_6_, 0);
lean_inc(v_mantissa_59_);
v_exponent_60_ = lean_ctor_get(v_x_6_, 1);
lean_inc(v_exponent_60_);
lean_dec_ref_known(v_x_6_, 2);
v_sign_61_ = lean_ctor_get_uint8(v_x_7_, sizeof(void*)*2);
v_mantissa_62_ = lean_ctor_get(v_x_7_, 0);
lean_inc(v_mantissa_62_);
v_exponent_63_ = lean_ctor_get(v_x_7_, 1);
lean_inc(v_exponent_63_);
lean_dec_ref_known(v_x_7_, 2);
if (v_sign_58_ == 0)
{
if (v_sign_61_ == 0)
{
uint8_t v___x_70_; 
v___x_70_ = 1;
v___y_65_ = v___x_70_;
goto v___jp_64_;
}
else
{
v___y_65_ = v_sign_58_;
goto v___jp_64_;
}
}
else
{
v___y_65_ = v_sign_61_;
goto v___jp_64_;
}
v___jp_64_:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = lean_nat_mul(v_mantissa_59_, v_mantissa_62_);
lean_dec(v_mantissa_62_);
lean_dec(v_mantissa_59_);
v___x_67_ = lean_int_add(v_exponent_60_, v_exponent_63_);
lean_dec(v_exponent_63_);
lean_dec(v_exponent_60_);
v___x_68_ = lean_box(0);
v___x_69_ = l_Float_Model_UnpackedFloat_roundWithAccuracy(v_spec_5_, v___y_65_, v___x_66_, v___x_67_, v___x_68_);
lean_dec(v___x_67_);
return v___x_69_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_mul___boxed(lean_object* v_spec_71_, lean_object* v_x_72_, lean_object* v_x_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Float_Model_UnpackedFloat_mul(v_spec_71_, v_x_72_, v_x_73_);
lean_dec_ref(v_spec_71_);
return v_res_74_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Mul(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Unpacked_Operations_Mul(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Unpacked_Operations_Mul(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Model_Unpacked_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Mul(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Unpacked_Operations_Mul(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Unpacked_Operations_Mul(builtin);
}
#ifdef __cplusplus
}
#endif
