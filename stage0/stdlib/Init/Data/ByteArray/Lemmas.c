// Lean compiler output
// Module: Init.Data.ByteArray.Lemmas
// Imports: public import Init.Data.ByteArray.Basic import Init.ByCases import Init.Data.Array.Bootstrap import Init.Data.Array.Extract import Init.Data.Array.Lemmas import Init.Omega
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
lean_object* lean_byte_array_data(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__List_toByteArray_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__List_toByteArray_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_size_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_size_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__List_toByteArray_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_5_; 
lean_dec(v_h__2_4_);
v___x_5_ = lean_apply_1(v_h__1_3_, v_x_2_);
return v___x_5_;
}
else
{
lean_object* v_head_6_; lean_object* v_tail_7_; lean_object* v___x_8_; 
lean_dec(v_h__1_3_);
v_head_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_head_6_);
v_tail_7_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_tail_7_);
lean_dec_ref_known(v_x_1_, 2);
v___x_8_ = lean_apply_3(v_h__2_4_, v_head_6_, v_tail_7_, v_x_2_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__List_toByteArray_match__1_splitter(lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v___x_14_; 
lean_dec(v_h__2_13_);
v___x_14_ = lean_apply_1(v_h__1_12_, v_x_11_);
return v___x_14_;
}
else
{
lean_object* v_head_15_; lean_object* v_tail_16_; lean_object* v___x_17_; 
lean_dec(v_h__1_12_);
v_head_15_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_head_15_);
v_tail_16_ = lean_ctor_get(v_x_10_, 1);
lean_inc(v_tail_16_);
lean_dec_ref_known(v_x_10_, 2);
v___x_17_ = lean_apply_3(v_h__2_13_, v_head_15_, v_tail_16_, v_x_11_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg(lean_object* v_x_18_, lean_object* v_x_19_, uint8_t v_x_20_, lean_object* v_h__1_21_){
_start:
{
lean_object* v_data_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_data_22_ = lean_byte_array_data(v_x_18_);
v___x_23_ = lean_box(v_x_20_);
v___x_24_ = lean_apply_4(v_h__1_21_, v_data_22_, v_x_19_, v___x_23_, lean_box(0));
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg___boxed(lean_object* v_x_25_, lean_object* v_x_26_, lean_object* v_x_27_, lean_object* v_h__1_28_){
_start:
{
uint8_t v_x_22__boxed_29_; lean_object* v_res_30_; 
v_x_22__boxed_29_ = lean_unbox(v_x_27_);
v_res_30_ = l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___redArg(v_x_25_, v_x_26_, v_x_22__boxed_29_, v_h__1_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter(lean_object* v_motive_31_, lean_object* v_x_32_, lean_object* v_x_33_, uint8_t v_x_34_, lean_object* v_x_35_, lean_object* v_h__1_36_){
_start:
{
lean_object* v_data_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_data_37_ = lean_byte_array_data(v_x_32_);
v___x_38_ = lean_box(v_x_34_);
v___x_39_ = lean_apply_4(v_h__1_36_, v_data_37_, v_x_33_, v___x_38_, lean_box(0));
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter___boxed(lean_object* v_motive_40_, lean_object* v_x_41_, lean_object* v_x_42_, lean_object* v_x_43_, lean_object* v_x_44_, lean_object* v_h__1_45_){
_start:
{
uint8_t v_x_37__boxed_46_; lean_object* v_res_47_; 
v_x_37__boxed_46_ = lean_unbox(v_x_43_);
v_res_47_ = l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_set_match__1_splitter(v_motive_40_, v_x_41_, v_x_42_, v_x_37__boxed_46_, v_x_44_, v_h__1_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_size_match__1_splitter___redArg(lean_object* v_x_48_, lean_object* v_h__1_49_){
_start:
{
lean_object* v_data_50_; lean_object* v___x_51_; 
v_data_50_ = lean_byte_array_data(v_x_48_);
v___x_51_ = lean_apply_1(v_h__1_49_, v_data_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Lemmas_0__ByteArray_size_match__1_splitter(lean_object* v_motive_52_, lean_object* v_x_53_, lean_object* v_h__1_54_){
_start:
{
lean_object* v_data_55_; lean_object* v___x_56_; 
v_data_55_ = lean_byte_array_data(v_x_53_);
v___x_56_ = lean_apply_1(v_h__1_54_, v_data_55_);
return v___x_56_;
}
}
lean_object* runtime_initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Extract(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Extract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Extract(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Extract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_ByteArray_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
