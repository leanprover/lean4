// Lean compiler output
// Module: Init.Data.Order.MinMaxOn
// Imports: public import Init.Data.Order.Opposite import Init.Data.Order.Lemmas
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
LEAN_EXPORT lean_object* l_minOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_minOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_maxOn___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_maxOn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_maxOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_maxOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_minOn___redArg(lean_object* v_inst_1_, lean_object* v_f_2_, lean_object* v_x_3_, lean_object* v_y_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; uint8_t v___x_8_; 
lean_inc(v_f_2_);
lean_inc(v_x_3_);
v___x_5_ = lean_apply_1(v_f_2_, v_x_3_);
lean_inc(v_y_4_);
v___x_6_ = lean_apply_1(v_f_2_, v_y_4_);
v___x_7_ = lean_apply_2(v_inst_1_, v___x_5_, v___x_6_);
v___x_8_ = lean_unbox(v___x_7_);
if (v___x_8_ == 0)
{
lean_dec(v_x_3_);
return v_y_4_;
}
else
{
lean_dec(v_y_4_);
return v_x_3_;
}
}
}
LEAN_EXPORT lean_object* l_minOn(lean_object* v_00_u03b2_9_, lean_object* v_00_u03b1_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_f_13_, lean_object* v_x_14_, lean_object* v_y_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_minOn___redArg(v_inst_12_, v_f_13_, v_x_14_, v_y_15_);
return v___x_16_;
}
}
LEAN_EXPORT uint8_t l_maxOn___redArg___lam__0(lean_object* v_inst_17_, lean_object* v_a_18_, lean_object* v_b_19_){
_start:
{
lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_20_ = lean_apply_2(v_inst_17_, v_b_19_, v_a_18_);
v___x_21_ = lean_unbox(v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_maxOn___redArg___lam__0___boxed(lean_object* v_inst_22_, lean_object* v_a_23_, lean_object* v_b_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_maxOn___redArg___lam__0(v_inst_22_, v_a_23_, v_b_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT lean_object* l_maxOn___redArg(lean_object* v_inst_27_, lean_object* v_f_28_, lean_object* v_x_29_, lean_object* v_y_30_){
_start:
{
lean_object* v___f_31_; lean_object* v___x_32_; 
v___f_31_ = lean_alloc_closure((void*)(l_maxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_31_, 0, v_inst_27_);
v___x_32_ = l_minOn___redArg(v___f_31_, v_f_28_, v_x_29_, v_y_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_maxOn(lean_object* v_00_u03b2_33_, lean_object* v_00_u03b1_34_, lean_object* v_i_35_, lean_object* v_inst_36_, lean_object* v_f_37_, lean_object* v_x_38_, lean_object* v_y_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_maxOn___redArg(v_inst_36_, v_f_37_, v_x_38_, v_y_39_);
return v___x_40_;
}
}
lean_object* runtime_initialize_Init_Data_Order_Opposite(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Order_MinMaxOn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Order_Opposite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Order_MinMaxOn(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_Opposite(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Order_MinMaxOn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_Opposite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_MinMaxOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Order_MinMaxOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Order_MinMaxOn(builtin);
}
#ifdef __cplusplus
}
#endif
