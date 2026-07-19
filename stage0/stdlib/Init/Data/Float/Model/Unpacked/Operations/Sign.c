// Lean compiler output
// Module: Init.Data.Float.Model.Unpacked.Operations.Sign
// Imports: public import Init.Data.Float.Model.Unpacked.Basic
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
static const lean_ctor_object l_Float_Model_UnpackedFloat_neg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_neg___closed__0 = (const lean_object*)&l_Float_Model_UnpackedFloat_neg___closed__0_value;
static const lean_ctor_object l_Float_Model_UnpackedFloat_neg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_neg___closed__1 = (const lean_object*)&l_Float_Model_UnpackedFloat_neg___closed__1_value;
static const lean_ctor_object l_Float_Model_UnpackedFloat_neg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 2}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_neg___closed__2 = (const lean_object*)&l_Float_Model_UnpackedFloat_neg___closed__2_value;
static const lean_ctor_object l_Float_Model_UnpackedFloat_neg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 2}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_neg___closed__3 = (const lean_object*)&l_Float_Model_UnpackedFloat_neg___closed__3_value;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_neg(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_neg(lean_object* v_x_9_){
_start:
{
switch(lean_obj_tag(v_x_9_))
{
case 0:
{
uint8_t v_sign_10_; 
v_sign_10_ = lean_ctor_get_uint8(v_x_9_, 0);
lean_dec_ref_known(v_x_9_, 0);
if (v_sign_10_ == 0)
{
lean_object* v___x_11_; 
v___x_11_ = ((lean_object*)(l_Float_Model_UnpackedFloat_neg___closed__0));
return v___x_11_;
}
else
{
lean_object* v___x_12_; 
v___x_12_ = ((lean_object*)(l_Float_Model_UnpackedFloat_neg___closed__1));
return v___x_12_;
}
}
case 1:
{
return v_x_9_;
}
case 2:
{
uint8_t v_sign_13_; 
v_sign_13_ = lean_ctor_get_uint8(v_x_9_, 0);
lean_dec_ref_known(v_x_9_, 0);
if (v_sign_13_ == 0)
{
lean_object* v___x_14_; 
v___x_14_ = ((lean_object*)(l_Float_Model_UnpackedFloat_neg___closed__2));
return v___x_14_;
}
else
{
lean_object* v___x_15_; 
v___x_15_ = ((lean_object*)(l_Float_Model_UnpackedFloat_neg___closed__3));
return v___x_15_;
}
}
default: 
{
uint8_t v_sign_16_; 
v_sign_16_ = lean_ctor_get_uint8(v_x_9_, sizeof(void*)*2);
if (v_sign_16_ == 0)
{
lean_object* v_mantissa_17_; lean_object* v_exponent_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_26_; 
v_mantissa_17_ = lean_ctor_get(v_x_9_, 0);
v_exponent_18_ = lean_ctor_get(v_x_9_, 1);
v_isSharedCheck_26_ = !lean_is_exclusive(v_x_9_);
if (v_isSharedCheck_26_ == 0)
{
v___x_20_ = v_x_9_;
v_isShared_21_ = v_isSharedCheck_26_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_exponent_18_);
lean_inc(v_mantissa_17_);
lean_dec(v_x_9_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_26_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
uint8_t v___x_22_; lean_object* v___x_24_; 
v___x_22_ = 1;
if (v_isShared_21_ == 0)
{
v___x_24_ = v___x_20_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_mantissa_17_);
lean_ctor_set(v_reuseFailAlloc_25_, 1, v_exponent_18_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_ctor_set_uint8(v___x_24_, sizeof(void*)*2, v___x_22_);
return v___x_24_;
}
}
}
else
{
lean_object* v_mantissa_27_; lean_object* v_exponent_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_36_; 
v_mantissa_27_ = lean_ctor_get(v_x_9_, 0);
v_exponent_28_ = lean_ctor_get(v_x_9_, 1);
v_isSharedCheck_36_ = !lean_is_exclusive(v_x_9_);
if (v_isSharedCheck_36_ == 0)
{
v___x_30_ = v_x_9_;
v_isShared_31_ = v_isSharedCheck_36_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_exponent_28_);
lean_inc(v_mantissa_27_);
lean_dec(v_x_9_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_36_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
uint8_t v___x_32_; lean_object* v___x_34_; 
v___x_32_ = 0;
if (v_isShared_31_ == 0)
{
v___x_34_ = v___x_30_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_mantissa_27_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v_exponent_28_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
lean_ctor_set_uint8(v___x_34_, sizeof(void*)*2, v___x_32_);
return v___x_34_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_abs(lean_object* v_x_37_){
_start:
{
switch(lean_obj_tag(v_x_37_))
{
case 0:
{
lean_object* v___x_38_; 
lean_dec_ref_known(v_x_37_, 0);
v___x_38_ = ((lean_object*)(l_Float_Model_UnpackedFloat_neg___closed__0));
return v___x_38_;
}
case 1:
{
return v_x_37_;
}
case 2:
{
lean_object* v___x_39_; 
lean_dec_ref_known(v_x_37_, 0);
v___x_39_ = ((lean_object*)(l_Float_Model_UnpackedFloat_neg___closed__2));
return v___x_39_;
}
default: 
{
lean_object* v_mantissa_40_; lean_object* v_exponent_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_49_; 
v_mantissa_40_ = lean_ctor_get(v_x_37_, 0);
v_exponent_41_ = lean_ctor_get(v_x_37_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v_x_37_);
if (v_isSharedCheck_49_ == 0)
{
v___x_43_ = v_x_37_;
v_isShared_44_ = v_isSharedCheck_49_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_exponent_41_);
lean_inc(v_mantissa_40_);
lean_dec(v_x_37_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_49_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
uint8_t v___x_45_; lean_object* v___x_47_; 
v___x_45_ = 1;
if (v_isShared_44_ == 0)
{
v___x_47_ = v___x_43_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_mantissa_40_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v_exponent_41_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
lean_ctor_set_uint8(v___x_47_, sizeof(void*)*2, v___x_45_);
return v___x_47_;
}
}
}
}
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Sign(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Unpacked_Operations_Sign(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Model_Unpacked_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Unpacked_Operations_Sign(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Model_Unpacked_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Sign(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Unpacked_Operations_Sign(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Unpacked_Operations_Sign(builtin);
}
#ifdef __cplusplus
}
#endif
