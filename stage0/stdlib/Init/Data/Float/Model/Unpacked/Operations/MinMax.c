// Lean compiler output
// Module: Init.Data.Float.Model.Unpacked.Operations.MinMax
// Imports: public import Init.Data.Float.Model.Unpacked.Operations.Compare
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
uint8_t l_Float_Model_UnpackedFloat_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_minimum(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_minimum___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_minimumNumber(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_minimumNumber___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_maximum(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_maximum___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_maximumNumber(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_maximumNumber___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_minimum(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_a_4_; lean_object* v_b_5_; 
switch(lean_obj_tag(v_x_1_))
{
case 1:
{
return v_x_1_;
}
case 2:
{
switch(lean_obj_tag(v_x_2_))
{
case 1:
{
return v_x_2_;
}
case 2:
{
uint8_t v_sign_7_; 
v_sign_7_ = lean_ctor_get_uint8(v_x_1_, 0);
if (v_sign_7_ == 0)
{
lean_inc_ref(v_x_1_);
return v_x_1_;
}
else
{
lean_inc_ref(v_x_2_);
return v_x_2_;
}
}
default: 
{
v_a_4_ = v_x_1_;
v_b_5_ = v_x_2_;
goto v___jp_3_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_2_) == 1)
{
return v_x_2_;
}
else
{
v_a_4_ = v_x_1_;
v_b_5_ = v_x_2_;
goto v___jp_3_;
}
}
}
v___jp_3_:
{
uint8_t v___x_6_; 
v___x_6_ = l_Float_Model_UnpackedFloat_le(v_a_4_, v_b_5_);
if (v___x_6_ == 0)
{
lean_inc(v_b_5_);
return v_b_5_;
}
else
{
lean_inc(v_a_4_);
return v_a_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_minimum___boxed(lean_object* v_x_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Float_Model_UnpackedFloat_minimum(v_x_8_, v_x_9_);
lean_dec(v_x_9_);
lean_dec(v_x_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_minimumNumber(lean_object* v_x_11_, lean_object* v_x_12_){
_start:
{
lean_object* v_a_14_; lean_object* v_b_15_; 
switch(lean_obj_tag(v_x_11_))
{
case 1:
{
lean_inc(v_x_12_);
return v_x_12_;
}
case 2:
{
switch(lean_obj_tag(v_x_12_))
{
case 1:
{
lean_inc_ref(v_x_11_);
return v_x_11_;
}
case 2:
{
uint8_t v_sign_17_; 
v_sign_17_ = lean_ctor_get_uint8(v_x_11_, 0);
if (v_sign_17_ == 0)
{
lean_inc_ref(v_x_11_);
return v_x_11_;
}
else
{
lean_inc_ref(v_x_12_);
return v_x_12_;
}
}
default: 
{
v_a_14_ = v_x_11_;
v_b_15_ = v_x_12_;
goto v___jp_13_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_12_) == 1)
{
lean_inc(v_x_11_);
return v_x_11_;
}
else
{
v_a_14_ = v_x_11_;
v_b_15_ = v_x_12_;
goto v___jp_13_;
}
}
}
v___jp_13_:
{
uint8_t v___x_16_; 
v___x_16_ = l_Float_Model_UnpackedFloat_le(v_a_14_, v_b_15_);
if (v___x_16_ == 0)
{
lean_inc(v_b_15_);
return v_b_15_;
}
else
{
lean_inc(v_a_14_);
return v_a_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_minimumNumber___boxed(lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Float_Model_UnpackedFloat_minimumNumber(v_x_18_, v_x_19_);
lean_dec(v_x_19_);
lean_dec(v_x_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_maximum(lean_object* v_x_21_, lean_object* v_x_22_){
_start:
{
lean_object* v_a_24_; lean_object* v_b_25_; 
switch(lean_obj_tag(v_x_21_))
{
case 1:
{
return v_x_21_;
}
case 2:
{
switch(lean_obj_tag(v_x_22_))
{
case 1:
{
return v_x_22_;
}
case 2:
{
uint8_t v_sign_27_; 
v_sign_27_ = lean_ctor_get_uint8(v_x_21_, 0);
if (v_sign_27_ == 0)
{
lean_inc_ref(v_x_22_);
return v_x_22_;
}
else
{
lean_inc_ref(v_x_21_);
return v_x_21_;
}
}
default: 
{
v_a_24_ = v_x_21_;
v_b_25_ = v_x_22_;
goto v___jp_23_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_22_) == 1)
{
return v_x_22_;
}
else
{
v_a_24_ = v_x_21_;
v_b_25_ = v_x_22_;
goto v___jp_23_;
}
}
}
v___jp_23_:
{
uint8_t v___x_26_; 
v___x_26_ = l_Float_Model_UnpackedFloat_le(v_a_24_, v_b_25_);
if (v___x_26_ == 0)
{
lean_inc(v_a_24_);
return v_a_24_;
}
else
{
lean_inc(v_b_25_);
return v_b_25_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_maximum___boxed(lean_object* v_x_28_, lean_object* v_x_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Float_Model_UnpackedFloat_maximum(v_x_28_, v_x_29_);
lean_dec(v_x_29_);
lean_dec(v_x_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_maximumNumber(lean_object* v_x_31_, lean_object* v_x_32_){
_start:
{
lean_object* v_a_34_; lean_object* v_b_35_; 
switch(lean_obj_tag(v_x_31_))
{
case 1:
{
lean_inc(v_x_32_);
return v_x_32_;
}
case 2:
{
switch(lean_obj_tag(v_x_32_))
{
case 1:
{
lean_inc_ref(v_x_31_);
return v_x_31_;
}
case 2:
{
uint8_t v_sign_37_; 
v_sign_37_ = lean_ctor_get_uint8(v_x_31_, 0);
if (v_sign_37_ == 0)
{
lean_inc_ref(v_x_32_);
return v_x_32_;
}
else
{
lean_inc_ref(v_x_31_);
return v_x_31_;
}
}
default: 
{
v_a_34_ = v_x_31_;
v_b_35_ = v_x_32_;
goto v___jp_33_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_32_) == 1)
{
lean_inc(v_x_31_);
return v_x_31_;
}
else
{
v_a_34_ = v_x_31_;
v_b_35_ = v_x_32_;
goto v___jp_33_;
}
}
}
v___jp_33_:
{
uint8_t v___x_36_; 
v___x_36_ = l_Float_Model_UnpackedFloat_le(v_a_34_, v_b_35_);
if (v___x_36_ == 0)
{
lean_inc(v_a_34_);
return v_a_34_;
}
else
{
lean_inc(v_b_35_);
return v_b_35_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_maximumNumber___boxed(lean_object* v_x_38_, lean_object* v_x_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Float_Model_UnpackedFloat_maximumNumber(v_x_38_, v_x_39_);
lean_dec(v_x_39_);
lean_dec(v_x_38_);
return v_res_40_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Compare(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_MinMax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Unpacked_Operations_MinMax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Model_Unpacked_Operations_Compare(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Unpacked_Operations_MinMax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Model_Unpacked_Operations_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Unpacked_Operations_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Unpacked_Operations_MinMax(builtin);
}
#ifdef __cplusplus
}
#endif
