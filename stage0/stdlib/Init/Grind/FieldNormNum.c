// Lean compiler output
// Module: Init.Grind.FieldNormNum
// Imports: public import Init.Grind.Ring.Field public import Init.Data.Rat.Basic import Init.Data.Rat.Lemmas import Init.ByCases import Init.Omega
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
LEAN_EXPORT lean_object* l_Lean_Grind_Field_NormNum_ofRat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Field_NormNum_ofRat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Field_NormNum_ofRat___redArg(lean_object* v_inst_1_, lean_object* v_r_2_){
_start:
{
lean_object* v_toCommRing_3_; lean_object* v_toSemiring_4_; lean_object* v_toDiv_5_; lean_object* v_intCast_6_; lean_object* v_num_7_; lean_object* v_den_8_; lean_object* v_natCast_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_toCommRing_3_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toCommRing_3_);
v_toSemiring_4_ = lean_ctor_get(v_toCommRing_3_, 0);
lean_inc_ref(v_toSemiring_4_);
v_toDiv_5_ = lean_ctor_get(v_inst_1_, 2);
lean_inc(v_toDiv_5_);
lean_dec_ref(v_inst_1_);
v_intCast_6_ = lean_ctor_get(v_toCommRing_3_, 3);
lean_inc(v_intCast_6_);
lean_dec_ref(v_toCommRing_3_);
v_num_7_ = lean_ctor_get(v_r_2_, 0);
lean_inc(v_num_7_);
v_den_8_ = lean_ctor_get(v_r_2_, 1);
lean_inc(v_den_8_);
lean_dec_ref(v_r_2_);
v_natCast_9_ = lean_ctor_get(v_toSemiring_4_, 2);
lean_inc(v_natCast_9_);
lean_dec_ref(v_toSemiring_4_);
v___x_10_ = lean_apply_1(v_intCast_6_, v_num_7_);
v___x_11_ = lean_apply_1(v_natCast_9_, v_den_8_);
v___x_12_ = lean_apply_2(v_toDiv_5_, v___x_10_, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Field_NormNum_ofRat(lean_object* v_00_u03b1_13_, lean_object* v_inst_14_, lean_object* v_r_15_){
_start:
{
lean_object* v_toCommRing_16_; lean_object* v_toSemiring_17_; lean_object* v_toDiv_18_; lean_object* v_intCast_19_; lean_object* v_num_20_; lean_object* v_den_21_; lean_object* v_natCast_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v_toCommRing_16_ = lean_ctor_get(v_inst_14_, 0);
lean_inc_ref(v_toCommRing_16_);
v_toSemiring_17_ = lean_ctor_get(v_toCommRing_16_, 0);
lean_inc_ref(v_toSemiring_17_);
v_toDiv_18_ = lean_ctor_get(v_inst_14_, 2);
lean_inc(v_toDiv_18_);
lean_dec_ref(v_inst_14_);
v_intCast_19_ = lean_ctor_get(v_toCommRing_16_, 3);
lean_inc(v_intCast_19_);
lean_dec_ref(v_toCommRing_16_);
v_num_20_ = lean_ctor_get(v_r_15_, 0);
lean_inc(v_num_20_);
v_den_21_ = lean_ctor_get(v_r_15_, 1);
lean_inc(v_den_21_);
lean_dec_ref(v_r_15_);
v_natCast_22_ = lean_ctor_get(v_toSemiring_17_, 2);
lean_inc(v_natCast_22_);
lean_dec_ref(v_toSemiring_17_);
v___x_23_ = lean_apply_1(v_intCast_19_, v_num_20_);
v___x_24_ = lean_apply_1(v_natCast_22_, v_den_21_);
v___x_25_ = lean_apply_2(v_toDiv_18_, v___x_23_, v___x_24_);
return v___x_25_;
}
}
lean_object* runtime_initialize_Init_Grind_Ring_Field(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Rat_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Rat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_FieldNormNum(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Ring_Field(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Rat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Rat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_FieldNormNum(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ring_Field(uint8_t builtin);
lean_object* initialize_Init_Data_Rat_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Rat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_FieldNormNum(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_Field(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Rat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Rat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_FieldNormNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_FieldNormNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_FieldNormNum(builtin);
}
#ifdef __cplusplus
}
#endif
