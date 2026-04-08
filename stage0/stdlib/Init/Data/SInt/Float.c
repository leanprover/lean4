// Lean compiler output
// Module: Init.Data.SInt.Float
// Imports: public import Init.Data.Float public import Init.Data.SInt.Basic
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
uint8_t lean_float_to_int8(double);
LEAN_EXPORT lean_object* l_Float_toInt8___boxed(lean_object*);
uint16_t lean_float_to_int16(double);
LEAN_EXPORT lean_object* l_Float_toInt16___boxed(lean_object*);
uint32_t lean_float_to_int32(double);
LEAN_EXPORT lean_object* l_Float_toInt32___boxed(lean_object*);
uint64_t lean_float_to_int64(double);
LEAN_EXPORT lean_object* l_Float_toInt64___boxed(lean_object*);
size_t lean_float_to_isize(double);
LEAN_EXPORT lean_object* l_Float_toISize___boxed(lean_object*);
double lean_int8_to_float(uint8_t);
LEAN_EXPORT lean_object* l_Int8_toFloat___boxed(lean_object*);
double lean_int16_to_float(uint16_t);
LEAN_EXPORT lean_object* l_Int16_toFloat___boxed(lean_object*);
double lean_int32_to_float(uint32_t);
LEAN_EXPORT lean_object* l_Int32_toFloat___boxed(lean_object*);
double lean_int64_to_float(uint64_t);
LEAN_EXPORT lean_object* l_Int64_toFloat___boxed(lean_object*);
double lean_isize_to_float(size_t);
LEAN_EXPORT lean_object* l_ISize_toFloat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Float_toInt8___boxed(lean_object* v_a_00___x40___internal___hyg_2_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_3_; uint8_t v_res_4_; lean_object* v_r_5_; 
v_a_00___x40___internal___hyg_1__boxed_3_ = lean_unbox_float(v_a_00___x40___internal___hyg_2_);
lean_dec_ref(v_a_00___x40___internal___hyg_2_);
v_res_4_ = lean_float_to_int8(v_a_00___x40___internal___hyg_1__boxed_3_);
v_r_5_ = lean_box(v_res_4_);
return v_r_5_;
}
}
LEAN_EXPORT lean_object* l_Float_toInt16___boxed(lean_object* v_a_00___x40___internal___hyg_7_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_8_; uint16_t v_res_9_; lean_object* v_r_10_; 
v_a_00___x40___internal___hyg_1__boxed_8_ = lean_unbox_float(v_a_00___x40___internal___hyg_7_);
lean_dec_ref(v_a_00___x40___internal___hyg_7_);
v_res_9_ = lean_float_to_int16(v_a_00___x40___internal___hyg_1__boxed_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT lean_object* l_Float_toInt32___boxed(lean_object* v_a_00___x40___internal___hyg_12_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_13_; uint32_t v_res_14_; lean_object* v_r_15_; 
v_a_00___x40___internal___hyg_1__boxed_13_ = lean_unbox_float(v_a_00___x40___internal___hyg_12_);
lean_dec_ref(v_a_00___x40___internal___hyg_12_);
v_res_14_ = lean_float_to_int32(v_a_00___x40___internal___hyg_1__boxed_13_);
v_r_15_ = lean_box_uint32(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT lean_object* l_Float_toInt64___boxed(lean_object* v_a_00___x40___internal___hyg_17_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_18_; uint64_t v_res_19_; lean_object* v_r_20_; 
v_a_00___x40___internal___hyg_1__boxed_18_ = lean_unbox_float(v_a_00___x40___internal___hyg_17_);
lean_dec_ref(v_a_00___x40___internal___hyg_17_);
v_res_19_ = lean_float_to_int64(v_a_00___x40___internal___hyg_1__boxed_18_);
v_r_20_ = lean_box_uint64(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT lean_object* l_Float_toISize___boxed(lean_object* v_a_00___x40___internal___hyg_22_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_23_; size_t v_res_24_; lean_object* v_r_25_; 
v_a_00___x40___internal___hyg_1__boxed_23_ = lean_unbox_float(v_a_00___x40___internal___hyg_22_);
lean_dec_ref(v_a_00___x40___internal___hyg_22_);
v_res_24_ = lean_float_to_isize(v_a_00___x40___internal___hyg_1__boxed_23_);
v_r_25_ = lean_box_usize(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT lean_object* l_Int8_toFloat___boxed(lean_object* v_n_27_){
_start:
{
uint8_t v_n_boxed_28_; double v_res_29_; lean_object* v_r_30_; 
v_n_boxed_28_ = lean_unbox(v_n_27_);
v_res_29_ = lean_int8_to_float(v_n_boxed_28_);
v_r_30_ = lean_box_float(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT lean_object* l_Int16_toFloat___boxed(lean_object* v_n_32_){
_start:
{
uint16_t v_n_boxed_33_; double v_res_34_; lean_object* v_r_35_; 
v_n_boxed_33_ = lean_unbox(v_n_32_);
v_res_34_ = lean_int16_to_float(v_n_boxed_33_);
v_r_35_ = lean_box_float(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT lean_object* l_Int32_toFloat___boxed(lean_object* v_n_37_){
_start:
{
uint32_t v_n_boxed_38_; double v_res_39_; lean_object* v_r_40_; 
v_n_boxed_38_ = lean_unbox_uint32(v_n_37_);
lean_dec(v_n_37_);
v_res_39_ = lean_int32_to_float(v_n_boxed_38_);
v_r_40_ = lean_box_float(v_res_39_);
return v_r_40_;
}
}
LEAN_EXPORT lean_object* l_Int64_toFloat___boxed(lean_object* v_n_42_){
_start:
{
uint64_t v_n_boxed_43_; double v_res_44_; lean_object* v_r_45_; 
v_n_boxed_43_ = lean_unbox_uint64(v_n_42_);
lean_dec_ref(v_n_42_);
v_res_44_ = lean_int64_to_float(v_n_boxed_43_);
v_r_45_ = lean_box_float(v_res_44_);
return v_r_45_;
}
}
LEAN_EXPORT lean_object* l_ISize_toFloat___boxed(lean_object* v_n_47_){
_start:
{
size_t v_n_boxed_48_; double v_res_49_; lean_object* v_r_50_; 
v_n_boxed_48_ = lean_unbox_usize(v_n_47_);
lean_dec(v_n_47_);
v_res_49_ = lean_isize_to_float(v_n_boxed_48_);
v_r_50_ = lean_box_float(v_res_49_);
return v_r_50_;
}
}
lean_object* runtime_initialize_Init_Data_Float(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_SInt_Float(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_SInt_Float(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_SInt_Float(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_SInt_Float(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_SInt_Float(builtin);
}
#ifdef __cplusplus
}
#endif
