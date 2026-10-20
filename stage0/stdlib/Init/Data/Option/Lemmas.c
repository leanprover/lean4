// Lean compiler output
// Module: Init.Data.Option.Lemmas
// Imports: import all Init.Data.Option.BasicAux public import Init.Data.Option.Instances import all Init.Data.Option.Instances public import Init.Ext public import Init.Data.Option.BasicAux public import Init.PropLemmas import Init.Classical import Init.Data.BEq import Init.Data.Bool
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
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_lt_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_lt_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_lt_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_, lean_object* v_h__3_5_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_dec(v_h__2_4_);
if (lean_obj_tag(v_x_2_) == 1)
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__3_5_);
v_val_6_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_val_6_);
lean_dec_ref_known(v_x_2_, 1);
v___x_7_ = lean_apply_1(v_h__1_3_, v_val_6_);
return v___x_7_;
}
else
{
lean_object* v___x_8_; 
lean_dec(v_h__1_3_);
v___x_8_ = lean_apply_4(v_h__3_5_, v_x_1_, v_x_2_, lean_box(0), lean_box(0));
return v___x_8_;
}
}
else
{
lean_dec(v_h__1_3_);
if (lean_obj_tag(v_x_2_) == 1)
{
lean_object* v_val_9_; lean_object* v_val_10_; lean_object* v___x_11_; 
lean_dec(v_h__3_5_);
v_val_9_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_9_);
lean_dec_ref_known(v_x_1_, 1);
v_val_10_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_val_10_);
lean_dec_ref_known(v_x_2_, 1);
v___x_11_ = lean_apply_2(v_h__2_4_, v_val_9_, v_val_10_);
return v___x_11_;
}
else
{
lean_object* v___x_12_; 
lean_dec(v_h__2_4_);
v___x_12_ = lean_apply_4(v_h__3_5_, v_x_1_, v_x_2_, lean_box(0), lean_box(0));
return v___x_12_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Lemmas_0__Option_lt_match__1_splitter(lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_motive_15_, lean_object* v_x_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_, lean_object* v_h__3_20_){
_start:
{
if (lean_obj_tag(v_x_16_) == 0)
{
lean_dec(v_h__2_19_);
if (lean_obj_tag(v_x_17_) == 1)
{
lean_object* v_val_21_; lean_object* v___x_22_; 
lean_dec(v_h__3_20_);
v_val_21_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_val_21_);
lean_dec_ref_known(v_x_17_, 1);
v___x_22_ = lean_apply_1(v_h__1_18_, v_val_21_);
return v___x_22_;
}
else
{
lean_object* v___x_23_; 
lean_dec(v_h__1_18_);
v___x_23_ = lean_apply_4(v_h__3_20_, v_x_16_, v_x_17_, lean_box(0), lean_box(0));
return v___x_23_;
}
}
else
{
lean_dec(v_h__1_18_);
if (lean_obj_tag(v_x_17_) == 1)
{
lean_object* v_val_24_; lean_object* v_val_25_; lean_object* v___x_26_; 
lean_dec(v_h__3_20_);
v_val_24_ = lean_ctor_get(v_x_16_, 0);
lean_inc(v_val_24_);
lean_dec_ref_known(v_x_16_, 1);
v_val_25_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_val_25_);
lean_dec_ref_known(v_x_17_, 1);
v___x_26_ = lean_apply_2(v_h__2_19_, v_val_24_, v_val_25_);
return v___x_26_;
}
else
{
lean_object* v___x_27_; 
lean_dec(v_h__2_19_);
v___x_27_ = lean_apply_4(v_h__3_20_, v_x_16_, v_x_17_, lean_box(0), lean_box(0));
return v___x_27_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Option_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Instances(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Instances(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
lean_object* initialize_Init_Data_BEq(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Option_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
