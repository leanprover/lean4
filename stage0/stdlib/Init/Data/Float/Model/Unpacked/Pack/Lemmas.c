// Lean compiler output
// Module: Init.Data.Float.Model.Unpacked.Pack.Lemmas
// Imports: public import Init.Data.Float.Model.Unpacked.Pack.Basic public import Init.Data.Float.Model.Format.Valid
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
LEAN_EXPORT lean_object* l___private_Init_Data_Float_Model_Unpacked_Pack_Lemmas_0__Float_Model_UnpackedFloat_pack_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Float_Model_Unpacked_Pack_Lemmas_0__Float_Model_UnpackedFloat_pack_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Float_Model_Unpacked_Pack_Lemmas_0__Float_Model_UnpackedFloat_pack_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_, lean_object* v_h__4_5_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
uint8_t v_sign_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
lean_dec(v_h__4_5_);
lean_dec(v_h__3_4_);
lean_dec(v_h__1_2_);
v_sign_6_ = lean_ctor_get_uint8(v_x_1_, 0);
lean_dec_ref_known(v_x_1_, 0);
v___x_7_ = lean_box(v_sign_6_);
v___x_8_ = lean_apply_1(v_h__2_3_, v___x_7_);
return v___x_8_;
}
case 1:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
lean_dec(v_h__4_5_);
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v___x_9_ = lean_box(0);
v___x_10_ = lean_apply_1(v_h__1_2_, v___x_9_);
return v___x_10_;
}
case 2:
{
uint8_t v_sign_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
lean_dec(v_h__4_5_);
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v_sign_11_ = lean_ctor_get_uint8(v_x_1_, 0);
lean_dec_ref_known(v_x_1_, 0);
v___x_12_ = lean_box(v_sign_11_);
v___x_13_ = lean_apply_1(v_h__3_4_, v___x_12_);
return v___x_13_;
}
default: 
{
uint8_t v_sign_14_; lean_object* v_mantissa_15_; lean_object* v_exponent_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v_sign_14_ = lean_ctor_get_uint8(v_x_1_, sizeof(void*)*2);
v_mantissa_15_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_mantissa_15_);
v_exponent_16_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_exponent_16_);
lean_dec_ref_known(v_x_1_, 2);
v___x_17_ = lean_box(v_sign_14_);
v___x_18_ = lean_apply_4(v_h__4_5_, v___x_17_, v_mantissa_15_, v_exponent_16_, lean_box(0));
return v___x_18_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Float_Model_Unpacked_Pack_Lemmas_0__Float_Model_UnpackedFloat_pack_match__1_splitter(lean_object* v_motive_19_, lean_object* v_x_20_, lean_object* v_h__1_21_, lean_object* v_h__2_22_, lean_object* v_h__3_23_, lean_object* v_h__4_24_){
_start:
{
switch(lean_obj_tag(v_x_20_))
{
case 0:
{
uint8_t v_sign_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec(v_h__4_24_);
lean_dec(v_h__3_23_);
lean_dec(v_h__1_21_);
v_sign_25_ = lean_ctor_get_uint8(v_x_20_, 0);
lean_dec_ref_known(v_x_20_, 0);
v___x_26_ = lean_box(v_sign_25_);
v___x_27_ = lean_apply_1(v_h__2_22_, v___x_26_);
return v___x_27_;
}
case 1:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
lean_dec(v_h__4_24_);
lean_dec(v_h__3_23_);
lean_dec(v_h__2_22_);
v___x_28_ = lean_box(0);
v___x_29_ = lean_apply_1(v_h__1_21_, v___x_28_);
return v___x_29_;
}
case 2:
{
uint8_t v_sign_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec(v_h__4_24_);
lean_dec(v_h__2_22_);
lean_dec(v_h__1_21_);
v_sign_30_ = lean_ctor_get_uint8(v_x_20_, 0);
lean_dec_ref_known(v_x_20_, 0);
v___x_31_ = lean_box(v_sign_30_);
v___x_32_ = lean_apply_1(v_h__3_23_, v___x_31_);
return v___x_32_;
}
default: 
{
uint8_t v_sign_33_; lean_object* v_mantissa_34_; lean_object* v_exponent_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec(v_h__3_23_);
lean_dec(v_h__2_22_);
lean_dec(v_h__1_21_);
v_sign_33_ = lean_ctor_get_uint8(v_x_20_, sizeof(void*)*2);
v_mantissa_34_ = lean_ctor_get(v_x_20_, 0);
lean_inc(v_mantissa_34_);
v_exponent_35_ = lean_ctor_get(v_x_20_, 1);
lean_inc(v_exponent_35_);
lean_dec_ref_known(v_x_20_, 2);
v___x_36_ = lean_box(v_sign_33_);
v___x_37_ = lean_apply_4(v_h__4_24_, v___x_36_, v_mantissa_34_, v_exponent_35_, lean_box(0));
return v___x_37_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Pack_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Format_Valid(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Pack_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Pack_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Format_Valid(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Unpacked_Pack_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Model_Unpacked_Pack_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Float_Model_Format_Valid(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Unpacked_Pack_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Model_Unpacked_Pack_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Float_Model_Format_Valid(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Pack_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Unpacked_Pack_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Unpacked_Pack_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
