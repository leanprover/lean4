// Lean compiler output
// Module: Init.Data.List.Zip
// Imports: public import Init.Data.Function public import Init.Ext public import Init.NotationExtra import Init.Data.List.Lemmas import Init.Data.List.TakeDrop import Init.Data.Option.Lemmas
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Zip_0__List_getElem_x3f__zipWith_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Zip_0__List_getElem_x3f__zipWith_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Zip_0__instDecidableEqProd_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Zip_0__instDecidableEqProd_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Zip_0__List_getElem_x3f__zipWithAll_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Zip_0__List_getElem_x3f__zipWithAll_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Zip_0__List_getElem_x3f__zipWith_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_){
_start:
{
if (lean_obj_tag(v_x_1_) == 1)
{
if (lean_obj_tag(v_x_2_) == 1)
{
lean_object* v_val_5_; lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_4_);
v_val_5_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_5_);
lean_dec_ref(v_x_1_);
v_val_6_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_val_6_);
lean_dec_ref(v_x_2_);
v___x_7_ = lean_apply_2(v_h__1_3_, v_val_5_, v_val_6_);
return v___x_7_;
}
else
{
lean_object* v___x_8_; 
lean_dec(v_h__1_3_);
v___x_8_ = lean_apply_3(v_h__2_4_, v_x_1_, v_x_2_, lean_box(0));
return v___x_8_;
}
}
else
{
lean_object* v___x_9_; 
lean_dec(v_h__1_3_);
v___x_9_ = lean_apply_3(v_h__2_4_, v_x_1_, v_x_2_, lean_box(0));
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Zip_0__List_getElem_x3f__zipWith_match__1_splitter(lean_object* v_00_u03b1_10_, lean_object* v_00_u03b2_11_, lean_object* v_motive_12_, lean_object* v_x_13_, lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
if (lean_obj_tag(v_x_13_) == 1)
{
if (lean_obj_tag(v_x_14_) == 1)
{
lean_object* v_val_17_; lean_object* v_val_18_; lean_object* v___x_19_; 
lean_dec(v_h__2_16_);
v_val_17_ = lean_ctor_get(v_x_13_, 0);
lean_inc(v_val_17_);
lean_dec_ref(v_x_13_);
v_val_18_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_val_18_);
lean_dec_ref(v_x_14_);
v___x_19_ = lean_apply_2(v_h__1_15_, v_val_17_, v_val_18_);
return v___x_19_;
}
else
{
lean_object* v___x_20_; 
lean_dec(v_h__1_15_);
v___x_20_ = lean_apply_3(v_h__2_16_, v_x_13_, v_x_14_, lean_box(0));
return v___x_20_;
}
}
else
{
lean_object* v___x_21_; 
lean_dec(v_h__1_15_);
v___x_21_ = lean_apply_3(v_h__2_16_, v_x_13_, v_x_14_, lean_box(0));
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Zip_0__instDecidableEqProd_match__3_splitter___redArg(lean_object* v_x_22_, lean_object* v_h__1_23_){
_start:
{
lean_object* v_fst_24_; lean_object* v_snd_25_; lean_object* v___x_26_; 
v_fst_24_ = lean_ctor_get(v_x_22_, 0);
lean_inc(v_fst_24_);
v_snd_25_ = lean_ctor_get(v_x_22_, 1);
lean_inc(v_snd_25_);
lean_dec_ref(v_x_22_);
v___x_26_ = lean_apply_2(v_h__1_23_, v_fst_24_, v_snd_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Zip_0__instDecidableEqProd_match__3_splitter(lean_object* v_00_u03b1_27_, lean_object* v_00_u03b2_28_, lean_object* v_motive_29_, lean_object* v_x_30_, lean_object* v_h__1_31_){
_start:
{
lean_object* v_fst_32_; lean_object* v_snd_33_; lean_object* v___x_34_; 
v_fst_32_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_fst_32_);
v_snd_33_ = lean_ctor_get(v_x_30_, 1);
lean_inc(v_snd_33_);
lean_dec_ref(v_x_30_);
v___x_34_ = lean_apply_2(v_h__1_31_, v_fst_32_, v_snd_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Zip_0__List_getElem_x3f__zipWithAll_match__1_splitter___redArg(lean_object* v_x_35_, lean_object* v_x_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_){
_start:
{
if (lean_obj_tag(v_x_35_) == 0)
{
if (lean_obj_tag(v_x_36_) == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec(v_h__2_38_);
v___x_39_ = lean_box(0);
v___x_40_ = lean_apply_1(v_h__1_37_, v___x_39_);
return v___x_40_;
}
else
{
lean_object* v___x_41_; 
lean_dec(v_h__1_37_);
v___x_41_ = lean_apply_3(v_h__2_38_, v_x_35_, v_x_36_, lean_box(0));
return v___x_41_;
}
}
else
{
lean_object* v___x_42_; 
lean_dec(v_h__1_37_);
v___x_42_ = lean_apply_3(v_h__2_38_, v_x_35_, v_x_36_, lean_box(0));
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Zip_0__List_getElem_x3f__zipWithAll_match__1_splitter(lean_object* v_00_u03b1_43_, lean_object* v_00_u03b2_44_, lean_object* v_motive_45_, lean_object* v_x_46_, lean_object* v_x_47_, lean_object* v_h__1_48_, lean_object* v_h__2_49_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
if (lean_obj_tag(v_x_47_) == 0)
{
lean_object* v___x_50_; lean_object* v___x_51_; 
lean_dec(v_h__2_49_);
v___x_50_ = lean_box(0);
v___x_51_ = lean_apply_1(v_h__1_48_, v___x_50_);
return v___x_51_;
}
else
{
lean_object* v___x_52_; 
lean_dec(v_h__1_48_);
v___x_52_ = lean_apply_3(v_h__2_49_, v_x_46_, v_x_47_, lean_box(0));
return v___x_52_;
}
}
else
{
lean_object* v___x_53_; 
lean_dec(v_h__1_48_);
v___x_53_ = lean_apply_3(v_h__2_49_, v_x_46_, v_x_47_, lean_box(0));
return v___x_53_;
}
}
}
lean_object* runtime_initialize_Init_Data_Function(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Zip(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Zip(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Function(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Zip(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Zip(builtin);
}
#ifdef __cplusplus
}
#endif
