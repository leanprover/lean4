// Lean compiler output
// Module: Init.Data.Float.Model.Unpacked.Operations.Sqrt
// Imports: public import Init.Data.Float.Model.Unpacked.Round public import Init.Data.Nat.Sqrt.Basic
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_Nat_sqrt(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Float_Model_totalExponent(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Float_Model_Format_targetExponent(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_roundWithAccuracy(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Float_Model_UnpackedFloat_sqrtCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_sqrtCore___closed__0;
static lean_once_cell_t l_Float_Model_UnpackedFloat_sqrtCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_sqrtCore___closed__1;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_sqrtCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_sqrtCore___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_sqrt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_sqrt___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Float_Model_UnpackedFloat_sqrtCore___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_sqrtCore___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_sqrtCore(lean_object* v_spec_5_, lean_object* v_m_6_, lean_object* v_e_7_){
_start:
{
lean_object* v___y_9_; lean_object* v___y_10_; lean_object* v___y_11_; lean_object* v___y_15_; lean_object* v___y_16_; uint8_t v___y_17_; lean_object* v___x_19_; lean_object* v___y_21_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_19_ = lean_obj_once(&l_Float_Model_UnpackedFloat_sqrtCore___closed__0, &l_Float_Model_UnpackedFloat_sqrtCore___closed__0_once, _init_l_Float_Model_UnpackedFloat_sqrtCore___closed__0);
v___x_35_ = lean_int_ediv(v_e_7_, v___x_19_);
v___x_36_ = l_Float_Model_totalExponent(v_m_6_, v_e_7_);
v___x_37_ = lean_obj_once(&l_Float_Model_UnpackedFloat_sqrtCore___closed__1, &l_Float_Model_UnpackedFloat_sqrtCore___closed__1_once, _init_l_Float_Model_UnpackedFloat_sqrtCore___closed__1);
v___x_38_ = lean_int_add(v___x_36_, v___x_37_);
lean_dec(v___x_36_);
v___x_39_ = lean_int_ediv(v___x_38_, v___x_19_);
lean_dec(v___x_38_);
v___x_40_ = l_Float_Model_Format_targetExponent(v_spec_5_, v___x_39_);
lean_dec(v___x_39_);
v___x_41_ = lean_int_dec_le(v___x_35_, v___x_40_);
if (v___x_41_ == 0)
{
lean_dec(v___x_35_);
v___y_21_ = v___x_40_;
goto v___jp_20_;
}
else
{
lean_dec(v___x_40_);
v___y_21_ = v___x_35_;
goto v___jp_20_;
}
v___jp_8_:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_12_, 0, v___y_10_);
lean_ctor_set(v___x_12_, 1, v___y_11_);
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v___y_9_);
lean_ctor_set(v___x_13_, 1, v___x_12_);
return v___x_13_;
}
v___jp_14_:
{
lean_object* v___x_18_; 
v___x_18_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_18_, 0, v___y_17_);
v___y_9_ = v___y_15_;
v___y_10_ = v___y_16_;
v___y_11_ = v___x_18_;
goto v___jp_8_;
}
v___jp_20_:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v_shiftAmount_24_; lean_object* v_m_25_; lean_object* v_root_26_; lean_object* v___x_27_; lean_object* v_rem_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_22_ = lean_int_mul(v___x_19_, v___y_21_);
v___x_23_ = lean_int_sub(v_e_7_, v___x_22_);
lean_dec(v___x_22_);
v_shiftAmount_24_ = l_Int_toNat(v___x_23_);
lean_dec(v___x_23_);
v_m_25_ = lean_nat_shiftl(v_m_6_, v_shiftAmount_24_);
lean_dec(v_shiftAmount_24_);
v_root_26_ = l_Nat_sqrt(v_m_25_);
v___x_27_ = lean_nat_mul(v_root_26_, v_root_26_);
v_rem_28_ = lean_nat_sub(v_m_25_, v___x_27_);
lean_dec(v___x_27_);
lean_dec(v_m_25_);
v___x_29_ = lean_unsigned_to_nat(0u);
v___x_30_ = lean_nat_dec_eq(v_rem_28_, v___x_29_);
if (v___x_30_ == 0)
{
uint8_t v___x_31_; 
v___x_31_ = lean_nat_dec_le(v_rem_28_, v_root_26_);
lean_dec(v_rem_28_);
if (v___x_31_ == 0)
{
uint8_t v___x_32_; 
v___x_32_ = 2;
v___y_15_ = v_root_26_;
v___y_16_ = v___y_21_;
v___y_17_ = v___x_32_;
goto v___jp_14_;
}
else
{
uint8_t v___x_33_; 
v___x_33_ = 0;
v___y_15_ = v_root_26_;
v___y_16_ = v___y_21_;
v___y_17_ = v___x_33_;
goto v___jp_14_;
}
}
else
{
lean_object* v___x_34_; 
lean_dec(v_rem_28_);
v___x_34_ = lean_box(0);
v___y_9_ = v_root_26_;
v___y_10_ = v___y_21_;
v___y_11_ = v___x_34_;
goto v___jp_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_sqrtCore___boxed(lean_object* v_spec_42_, lean_object* v_m_43_, lean_object* v_e_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Float_Model_UnpackedFloat_sqrtCore(v_spec_42_, v_m_43_, v_e_44_);
lean_dec(v_e_44_);
lean_dec(v_m_43_);
lean_dec_ref(v_spec_42_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_sqrt(lean_object* v_spec_46_, lean_object* v_x_47_){
_start:
{
switch(lean_obj_tag(v_x_47_))
{
case 0:
{
uint8_t v_sign_48_; 
v_sign_48_ = lean_ctor_get_uint8(v_x_47_, 0);
if (v_sign_48_ == 0)
{
lean_object* v___x_49_; 
v___x_49_ = lean_box(1);
return v___x_49_;
}
else
{
lean_inc_ref(v_x_47_);
return v_x_47_;
}
}
case 3:
{
uint8_t v_sign_50_; 
v_sign_50_ = lean_ctor_get_uint8(v_x_47_, sizeof(void*)*2);
if (v_sign_50_ == 0)
{
lean_object* v___x_51_; 
v___x_51_ = lean_box(1);
return v___x_51_;
}
else
{
lean_object* v_mantissa_52_; lean_object* v_exponent_53_; lean_object* v___x_54_; lean_object* v_snd_55_; lean_object* v_fst_56_; lean_object* v_fst_57_; lean_object* v_snd_58_; lean_object* v___x_59_; 
v_mantissa_52_ = lean_ctor_get(v_x_47_, 0);
v_exponent_53_ = lean_ctor_get(v_x_47_, 1);
v___x_54_ = l_Float_Model_UnpackedFloat_sqrtCore(v_spec_46_, v_mantissa_52_, v_exponent_53_);
v_snd_55_ = lean_ctor_get(v___x_54_, 1);
lean_inc(v_snd_55_);
v_fst_56_ = lean_ctor_get(v___x_54_, 0);
lean_inc(v_fst_56_);
lean_dec_ref(v___x_54_);
v_fst_57_ = lean_ctor_get(v_snd_55_, 0);
lean_inc(v_fst_57_);
v_snd_58_ = lean_ctor_get(v_snd_55_, 1);
lean_inc(v_snd_58_);
lean_dec(v_snd_55_);
v___x_59_ = l_Float_Model_UnpackedFloat_roundWithAccuracy(v_spec_46_, v_sign_50_, v_fst_56_, v_fst_57_, v_snd_58_);
lean_dec(v_snd_58_);
lean_dec(v_fst_57_);
return v___x_59_;
}
}
default: 
{
lean_inc(v_x_47_);
return v_x_47_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_sqrt___boxed(lean_object* v_spec_60_, lean_object* v_x_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Float_Model_UnpackedFloat_sqrt(v_spec_60_, v_x_61_);
lean_dec(v_x_61_);
lean_dec_ref(v_spec_60_);
return v_res_62_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Sqrt_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Sqrt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Sqrt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Unpacked_Operations_Sqrt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Model_Unpacked_Round(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Sqrt_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Unpacked_Operations_Sqrt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Model_Unpacked_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Sqrt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Sqrt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Unpacked_Operations_Sqrt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Unpacked_Operations_Sqrt(builtin);
}
#ifdef __cplusplus
}
#endif
