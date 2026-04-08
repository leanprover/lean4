// Lean compiler output
// Module: Init.Data.Range.Polymorphic.UpwardEnumerable
// Imports: public import Init.Data.Order.Classes public import Init.Classical import Init.Data.Option.Lemmas
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
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_succ___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_succ(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_succMany___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_succMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_least___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_least___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_least(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_least___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_succ___redArg(lean_object* v_inst_1_, lean_object* v_a_2_){
_start:
{
lean_object* v_succ_x3f_3_; lean_object* v___x_4_; lean_object* v_val_5_; 
v_succ_x3f_3_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_succ_x3f_3_);
lean_dec_ref(v_inst_1_);
v___x_4_ = lean_apply_1(v_succ_x3f_3_, v_a_2_);
v_val_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_val_5_);
lean_dec(v___x_4_);
return v_val_5_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_succ(lean_object* v_00_u03b1_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_a_9_){
_start:
{
lean_object* v_succ_x3f_10_; lean_object* v___x_11_; lean_object* v_val_12_; 
v_succ_x3f_10_ = lean_ctor_get(v_inst_7_, 0);
lean_inc_ref(v_succ_x3f_10_);
lean_dec_ref(v_inst_7_);
v___x_11_ = lean_apply_1(v_succ_x3f_10_, v_a_9_);
v_val_12_ = lean_ctor_get(v___x_11_, 0);
lean_inc(v_val_12_);
lean_dec(v___x_11_);
return v_val_12_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_succMany___redArg(lean_object* v_inst_13_, lean_object* v_n_14_, lean_object* v_a_15_){
_start:
{
lean_object* v_succMany_x3f_16_; lean_object* v___x_17_; lean_object* v_val_18_; 
v_succMany_x3f_16_ = lean_ctor_get(v_inst_13_, 1);
lean_inc_ref(v_succMany_x3f_16_);
lean_dec_ref(v_inst_13_);
v___x_17_ = lean_apply_2(v_succMany_x3f_16_, v_n_14_, v_a_15_);
v_val_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_val_18_);
lean_dec(v___x_17_);
return v_val_18_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_succMany(lean_object* v_00_u03b1_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_n_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_succMany_x3f_25_; lean_object* v___x_26_; lean_object* v_val_27_; 
v_succMany_x3f_25_ = lean_ctor_get(v_inst_20_, 1);
lean_inc_ref(v_succMany_x3f_25_);
lean_dec_ref(v_inst_20_);
v___x_26_ = lean_apply_2(v_succMany_x3f_25_, v_n_23_, v_a_24_);
v_val_27_ = lean_ctor_get(v___x_26_, 0);
lean_inc(v_val_27_);
lean_dec(v___x_26_);
return v_val_27_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE(lean_object* v_00_u03b1_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_box(0);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE___boxed(lean_object* v_00_u03b1_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_inst_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Std_PRange_UpwardEnumerable_instLETransOfLawfulUpwardEnumerableLE(v_00_u03b1_34_, v_inst_35_, v_inst_36_, v_inst_37_, v_inst_38_);
lean_dec_ref(v_inst_36_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT(lean_object* v_00_u03b1_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_inst_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT___boxed(lean_object* v_00_u03b1_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Std_PRange_UpwardEnumerable_instLTTransOfLawfulUpwardEnumerableLT(v_00_u03b1_46_, v_inst_47_, v_inst_48_, v_inst_49_, v_inst_50_);
lean_dec_ref(v_inst_48_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_least___redArg(lean_object* v_inst_52_){
_start:
{
lean_object* v_val_53_; 
v_val_53_ = lean_ctor_get(v_inst_52_, 0);
lean_inc(v_val_53_);
return v_val_53_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_least___redArg___boxed(lean_object* v_inst_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Std_PRange_UpwardEnumerable_least___redArg(v_inst_54_);
lean_dec(v_inst_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_least(lean_object* v_00_u03b1_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_hn_60_){
_start:
{
lean_object* v_val_61_; 
v_val_61_ = lean_ctor_get(v_inst_58_, 0);
lean_inc(v_val_61_);
return v_val_61_;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_UpwardEnumerable_least___boxed(lean_object* v_00_u03b1_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_hn_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Std_PRange_UpwardEnumerable_least(v_00_u03b1_62_, v_inst_63_, v_inst_64_, v_inst_65_, v_hn_66_);
lean_dec(v_inst_64_);
lean_dec_ref(v_inst_63_);
return v_res_67_;
}
}
lean_object* runtime_initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
}
#ifdef __cplusplus
}
#endif
