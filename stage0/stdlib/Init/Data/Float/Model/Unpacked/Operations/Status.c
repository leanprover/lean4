// Lean compiler output
// Module: Init.Data.Float.Model.Unpacked.Operations.Status
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
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_isFinite(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_isFinite___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_isInf(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_isInf___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_isNaN(lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_isNaN___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_isFinite(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
uint8_t v___x_2_; 
v___x_2_ = 0;
return v___x_2_;
}
case 1:
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
default: 
{
uint8_t v___x_4_; 
v___x_4_ = 1;
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_isFinite___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = l_Float_Model_UnpackedFloat_isFinite(v_x_5_);
lean_dec(v_x_5_);
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_isInf(lean_object* v_x_8_){
_start:
{
if (lean_obj_tag(v_x_8_) == 0)
{
uint8_t v___x_9_; 
v___x_9_ = 1;
return v___x_9_;
}
else
{
uint8_t v___x_10_; 
v___x_10_ = 0;
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_isInf___boxed(lean_object* v_x_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Float_Model_UnpackedFloat_isInf(v_x_11_);
lean_dec(v_x_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT uint8_t l_Float_Model_UnpackedFloat_isNaN(lean_object* v_x_14_){
_start:
{
if (lean_obj_tag(v_x_14_) == 1)
{
uint8_t v___x_15_; 
v___x_15_ = 1;
return v___x_15_;
}
else
{
uint8_t v___x_16_; 
v___x_16_ = 0;
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_isNaN___boxed(lean_object* v_x_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l_Float_Model_UnpackedFloat_isNaN(v_x_17_);
lean_dec(v_x_17_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Status(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Unpacked_Operations_Status(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Model_Unpacked_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Unpacked_Operations_Status(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Model_Unpacked_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Status(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Unpacked_Operations_Status(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Unpacked_Operations_Status(builtin);
}
#ifdef __cplusplus
}
#endif
