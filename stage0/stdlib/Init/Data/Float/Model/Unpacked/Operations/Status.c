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
uint8_t l_Float_Model_UnpackedFloat_isFinite(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 2:
{
uint8_t v___x_2_; 
v___x_2_ = 1;
return v___x_2_;
}
case 3:
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
default: 
{
uint8_t v___x_4_; 
v___x_4_ = 0;
return v___x_4_;
}
}
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_isFinite_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
uint8_t v_res_5_;
v_res_5_ = l_Float_Model_UnpackedFloat_isFinite(v_x_1_);
stack->m_num = v_res_5_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_isFinite___boxed(lean_object* v_x_6_){
_start:
{
uint8_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = l_Float_Model_UnpackedFloat_isFinite(v_x_6_);
lean_dec(v_x_6_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
uint8_t l_Float_Model_UnpackedFloat_isInf(lean_object* v_x_9_){
_start:
{
if (lean_obj_tag(v_x_9_) == 0)
{
uint8_t v___x_10_; 
v___x_10_ = 1;
return v___x_10_;
}
else
{
uint8_t v___x_11_; 
v___x_11_ = 0;
return v___x_11_;
}
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_isInf_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_9_ = stack[0].m_obj;
uint8_t v_res_12_;
v_res_12_ = l_Float_Model_UnpackedFloat_isInf(v_x_9_);
stack->m_num = v_res_12_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_isInf___boxed(lean_object* v_x_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Float_Model_UnpackedFloat_isInf(v_x_13_);
lean_dec(v_x_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
uint8_t l_Float_Model_UnpackedFloat_isNaN(lean_object* v_x_16_){
_start:
{
if (lean_obj_tag(v_x_16_) == 1)
{
uint8_t v___x_17_; 
v___x_17_ = 1;
return v___x_17_;
}
else
{
uint8_t v___x_18_; 
v___x_18_ = 0;
return v___x_18_;
}
}
}
LEAN_EXPORT void l_Float_Model_UnpackedFloat_isNaN_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_16_ = stack[0].m_obj;
uint8_t v_res_19_;
v_res_19_ = l_Float_Model_UnpackedFloat_isNaN(v_x_16_);
stack->m_num = v_res_19_;
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_isNaN___boxed(lean_object* v_x_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_Float_Model_UnpackedFloat_isNaN(v_x_20_);
lean_dec(v_x_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Status(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
