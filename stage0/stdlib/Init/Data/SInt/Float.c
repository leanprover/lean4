// Lean compiler output
// Module: Init.Data.SInt.Float
// Imports: public import Init.Data.Float.Float public import Init.Data.SInt.Basic
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
LEAN_EXPORT void l_Float_toInt8_0interp(lean_interpreter_value* stack)
{
double v_a_00___x40___internal___hyg_1_ = stack[0].m_float;
uint8_t v_res_2_;
v_res_2_ = lean_float_to_int8(v_a_00___x40___internal___hyg_1_);
stack->m_num = v_res_2_;
}
LEAN_EXPORT lean_object* l_Float_toInt8___boxed(lean_object* v_a_00___x40___internal___hyg_3_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_4_; uint8_t v_res_5_; lean_object* v_r_6_; 
v_a_00___x40___internal___hyg_1__boxed_4_ = lean_unbox_float(v_a_00___x40___internal___hyg_3_);
lean_dec_ref(v_a_00___x40___internal___hyg_3_);
v_res_5_ = lean_float_to_int8(v_a_00___x40___internal___hyg_1__boxed_4_);
v_r_6_ = lean_box(v_res_5_);
return v_r_6_;
}
}
LEAN_EXPORT void l_Float_toInt16_0interp(lean_interpreter_value* stack)
{
double v_a_00___x40___internal___hyg_7_ = stack[0].m_float;
uint16_t v_res_8_;
v_res_8_ = lean_float_to_int16(v_a_00___x40___internal___hyg_7_);
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l_Float_toInt16___boxed(lean_object* v_a_00___x40___internal___hyg_9_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_10_; uint16_t v_res_11_; lean_object* v_r_12_; 
v_a_00___x40___internal___hyg_1__boxed_10_ = lean_unbox_float(v_a_00___x40___internal___hyg_9_);
lean_dec_ref(v_a_00___x40___internal___hyg_9_);
v_res_11_ = lean_float_to_int16(v_a_00___x40___internal___hyg_1__boxed_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT void l_Float_toInt32_0interp(lean_interpreter_value* stack)
{
double v_a_00___x40___internal___hyg_13_ = stack[0].m_float;
uint32_t v_res_14_;
v_res_14_ = lean_float_to_int32(v_a_00___x40___internal___hyg_13_);
stack->m_num = v_res_14_;
}
LEAN_EXPORT lean_object* l_Float_toInt32___boxed(lean_object* v_a_00___x40___internal___hyg_15_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_16_; uint32_t v_res_17_; lean_object* v_r_18_; 
v_a_00___x40___internal___hyg_1__boxed_16_ = lean_unbox_float(v_a_00___x40___internal___hyg_15_);
lean_dec_ref(v_a_00___x40___internal___hyg_15_);
v_res_17_ = lean_float_to_int32(v_a_00___x40___internal___hyg_1__boxed_16_);
v_r_18_ = lean_box_uint32(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT void l_Float_toInt64_0interp(lean_interpreter_value* stack)
{
double v_a_00___x40___internal___hyg_19_ = stack[0].m_float;
uint64_t v_res_20_;
v_res_20_ = lean_float_to_int64(v_a_00___x40___internal___hyg_19_);
stack->m_num = v_res_20_;
}
LEAN_EXPORT lean_object* l_Float_toInt64___boxed(lean_object* v_a_00___x40___internal___hyg_21_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_22_; uint64_t v_res_23_; lean_object* v_r_24_; 
v_a_00___x40___internal___hyg_1__boxed_22_ = lean_unbox_float(v_a_00___x40___internal___hyg_21_);
lean_dec_ref(v_a_00___x40___internal___hyg_21_);
v_res_23_ = lean_float_to_int64(v_a_00___x40___internal___hyg_1__boxed_22_);
v_r_24_ = lean_box_uint64(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT void l_Float_toISize_0interp(lean_interpreter_value* stack)
{
double v_a_00___x40___internal___hyg_25_ = stack[0].m_float;
size_t v_res_26_;
v_res_26_ = lean_float_to_isize(v_a_00___x40___internal___hyg_25_);
stack->m_num = v_res_26_;
}
LEAN_EXPORT lean_object* l_Float_toISize___boxed(lean_object* v_a_00___x40___internal___hyg_27_){
_start:
{
double v_a_00___x40___internal___hyg_1__boxed_28_; size_t v_res_29_; lean_object* v_r_30_; 
v_a_00___x40___internal___hyg_1__boxed_28_ = lean_unbox_float(v_a_00___x40___internal___hyg_27_);
lean_dec_ref(v_a_00___x40___internal___hyg_27_);
v_res_29_ = lean_float_to_isize(v_a_00___x40___internal___hyg_1__boxed_28_);
v_r_30_ = lean_box_usize(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT void l_Int8_toFloat_0interp(lean_interpreter_value* stack)
{
uint8_t v_n_31_ = stack[0].m_num;
double v_res_32_;
v_res_32_ = lean_int8_to_float(v_n_31_);
stack->m_float
 = v_res_32_;
}
LEAN_EXPORT lean_object* l_Int8_toFloat___boxed(lean_object* v_n_33_){
_start:
{
uint8_t v_n_boxed_34_; double v_res_35_; lean_object* v_r_36_; 
v_n_boxed_34_ = lean_unbox(v_n_33_);
v_res_35_ = lean_int8_to_float(v_n_boxed_34_);
v_r_36_ = lean_box_float(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT void l_Int16_toFloat_0interp(lean_interpreter_value* stack)
{
uint16_t v_n_37_ = stack[0].m_num;
double v_res_38_;
v_res_38_ = lean_int16_to_float(v_n_37_);
stack->m_float
 = v_res_38_;
}
LEAN_EXPORT lean_object* l_Int16_toFloat___boxed(lean_object* v_n_39_){
_start:
{
uint16_t v_n_boxed_40_; double v_res_41_; lean_object* v_r_42_; 
v_n_boxed_40_ = lean_unbox(v_n_39_);
v_res_41_ = lean_int16_to_float(v_n_boxed_40_);
v_r_42_ = lean_box_float(v_res_41_);
return v_r_42_;
}
}
LEAN_EXPORT void l_Int32_toFloat_0interp(lean_interpreter_value* stack)
{
uint32_t v_n_43_ = stack[0].m_num;
double v_res_44_;
v_res_44_ = lean_int32_to_float(v_n_43_);
stack->m_float
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Int32_toFloat___boxed(lean_object* v_n_45_){
_start:
{
uint32_t v_n_boxed_46_; double v_res_47_; lean_object* v_r_48_; 
v_n_boxed_46_ = lean_unbox_uint32(v_n_45_);
lean_dec(v_n_45_);
v_res_47_ = lean_int32_to_float(v_n_boxed_46_);
v_r_48_ = lean_box_float(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT void l_Int64_toFloat_0interp(lean_interpreter_value* stack)
{
uint64_t v_n_49_ = stack[0].m_num;
double v_res_50_;
v_res_50_ = lean_int64_to_float(v_n_49_);
stack->m_float
 = v_res_50_;
}
LEAN_EXPORT lean_object* l_Int64_toFloat___boxed(lean_object* v_n_51_){
_start:
{
uint64_t v_n_boxed_52_; double v_res_53_; lean_object* v_r_54_; 
v_n_boxed_52_ = lean_unbox_uint64(v_n_51_);
lean_dec_ref(v_n_51_);
v_res_53_ = lean_int64_to_float(v_n_boxed_52_);
v_r_54_ = lean_box_float(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT void l_ISize_toFloat_0interp(lean_interpreter_value* stack)
{
size_t v_n_55_ = stack[0].m_num;
double v_res_56_;
v_res_56_ = lean_isize_to_float(v_n_55_);
stack->m_float
 = v_res_56_;
}
LEAN_EXPORT lean_object* l_ISize_toFloat___boxed(lean_object* v_n_57_){
_start:
{
size_t v_n_boxed_58_; double v_res_59_; lean_object* v_r_60_; 
v_n_boxed_58_ = lean_unbox_usize(v_n_57_);
lean_dec(v_n_57_);
v_res_59_ = lean_isize_to_float(v_n_boxed_58_);
v_r_60_ = lean_box_float(v_res_59_);
return v_r_60_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Float(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_SInt_Float(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Float_Float(builtin);
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
lean_object* initialize_Init_Data_Float_Float(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_SInt_Float(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Float(builtin);
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
