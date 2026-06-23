// Lean compiler output
// Module: Init.Data.Float.Model.Unpacked.Operations.OfScientific
// Imports: public import Init.Data.Float.Model.Unpacked.Operations.Mul public import Init.Data.Float.Model.Unpacked.Operations.Div public import Init.Data.Nat.Bitwise.Lemmas
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_log2(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_div(lean_object*, lean_object*, lean_object*);
lean_object* l_Float_Model_Format_mantissaBits(lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_Float_Model_UnpackedFloat_mul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_UnpackedFloat_ofScientific_spec__0(lean_object*);
static lean_once_cell_t l_Float_Model_UnpackedFloat_ofScientific___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_ofScientific___closed__0;
static lean_once_cell_t l_Float_Model_UnpackedFloat_ofScientific___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_Model_UnpackedFloat_ofScientific___closed__1;
static const lean_ctor_object l_Float_Model_UnpackedFloat_ofScientific___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 2}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_ofScientific___closed__2 = (const lean_object*)&l_Float_Model_UnpackedFloat_ofScientific___closed__2_value;
static const lean_ctor_object l_Float_Model_UnpackedFloat_ofScientific___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Float_Model_UnpackedFloat_ofScientific___closed__3 = (const lean_object*)&l_Float_Model_UnpackedFloat_ofScientific___closed__3_value;
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofScientific(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofScientific___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Float_Model_UnpackedFloat_ofScientific_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_ofScientific___closed__0(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(2u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Float_Model_UnpackedFloat_ofScientific___closed__1(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_nat_to_int(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofScientific(lean_object* v_spec_11_, lean_object* v_m_12_, lean_object* v_e_13_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = lean_nat_dec_eq(v_m_12_, v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v_exponentBits_16_; lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
v_exponentBits_16_ = lean_ctor_get(v_spec_11_, 1);
v___x_17_ = lean_obj_once(&l_Float_Model_UnpackedFloat_ofScientific___closed__0, &l_Float_Model_UnpackedFloat_ofScientific___closed__0_once, _init_l_Float_Model_UnpackedFloat_ofScientific___closed__0);
v___x_18_ = l_Int_pow(v___x_17_, v_exponentBits_16_);
v___x_19_ = lean_int_dec_lt(v___x_18_, v_e_13_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_20_ = lean_nat_log2(v_m_12_);
v___x_21_ = lean_nat_to_int(v___x_20_);
v___x_22_ = lean_int_add(v___x_18_, v___x_21_);
lean_dec(v___x_21_);
lean_dec(v___x_18_);
v___x_23_ = lean_int_neg(v___x_22_);
lean_dec(v___x_22_);
v___x_24_ = lean_int_dec_lt(v_e_13_, v___x_23_);
lean_dec(v___x_23_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_25_ = lean_obj_once(&l_Float_Model_UnpackedFloat_ofScientific___closed__1, &l_Float_Model_UnpackedFloat_ofScientific___closed__1_once, _init_l_Float_Model_UnpackedFloat_ofScientific___closed__1);
v___x_26_ = lean_int_dec_le(v___x_25_, v_e_13_);
if (v___x_26_ == 0)
{
uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_27_ = 1;
v___x_28_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_28_, 0, v_m_12_);
lean_ctor_set(v___x_28_, 1, v___x_25_);
lean_ctor_set_uint8(v___x_28_, sizeof(void*)*2, v___x_27_);
v___x_29_ = lean_unsigned_to_nat(10u);
v___x_30_ = lean_int_neg(v_e_13_);
v___x_31_ = l_Int_toNat(v___x_30_);
lean_dec(v___x_30_);
v___x_32_ = lean_nat_pow(v___x_29_, v___x_31_);
lean_dec(v___x_31_);
v___x_33_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v___x_25_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2, v___x_27_);
v___x_34_ = l_Float_Model_UnpackedFloat_div(v_spec_11_, v___x_28_, v___x_33_);
return v___x_34_;
}
else
{
uint8_t v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_35_ = 1;
v___x_36_ = l_Float_Model_Format_mantissaBits(v_spec_11_);
v___x_37_ = lean_nat_shiftl(v_m_12_, v___x_36_);
lean_dec(v_m_12_);
v___x_38_ = lean_nat_to_int(v___x_36_);
v___x_39_ = lean_int_neg(v___x_38_);
lean_dec(v___x_38_);
v___x_40_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_40_, 0, v___x_37_);
lean_ctor_set(v___x_40_, 1, v___x_39_);
lean_ctor_set_uint8(v___x_40_, sizeof(void*)*2, v___x_35_);
v___x_41_ = lean_unsigned_to_nat(10u);
v___x_42_ = l_Int_toNat(v_e_13_);
v___x_43_ = lean_nat_pow(v___x_41_, v___x_42_);
lean_dec(v___x_42_);
v___x_44_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v___x_25_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*2, v___x_35_);
v___x_45_ = l_Float_Model_UnpackedFloat_mul(v_spec_11_, v___x_40_, v___x_44_);
return v___x_45_;
}
}
else
{
lean_object* v___x_46_; 
lean_dec(v_m_12_);
v___x_46_ = ((lean_object*)(l_Float_Model_UnpackedFloat_ofScientific___closed__2));
return v___x_46_;
}
}
else
{
lean_object* v___x_47_; 
lean_dec(v___x_18_);
lean_dec(v_m_12_);
v___x_47_ = ((lean_object*)(l_Float_Model_UnpackedFloat_ofScientific___closed__3));
return v___x_47_;
}
}
else
{
lean_object* v___x_48_; 
lean_dec(v_m_12_);
v___x_48_ = ((lean_object*)(l_Float_Model_UnpackedFloat_ofScientific___closed__2));
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l_Float_Model_UnpackedFloat_ofScientific___boxed(lean_object* v_spec_49_, lean_object* v_m_50_, lean_object* v_e_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Float_Model_UnpackedFloat_ofScientific(v_spec_49_, v_m_50_, v_e_51_);
lean_dec(v_e_51_);
lean_dec_ref(v_spec_49_);
return v_res_52_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Mul(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Div(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_OfScientific(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Mul(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_Div(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Float_Model_Unpacked_Operations_OfScientific(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Model_Unpacked_Operations_Mul(uint8_t builtin);
lean_object* initialize_Init_Data_Float_Model_Unpacked_Operations_Div(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Bitwise_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Float_Model_Unpacked_Operations_OfScientific(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Model_Unpacked_Operations_Mul(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Float_Model_Unpacked_Operations_Div(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Float_Model_Unpacked_Operations_OfScientific(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Float_Model_Unpacked_Operations_OfScientific(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Float_Model_Unpacked_Operations_OfScientific(builtin);
}
#ifdef __cplusplus
}
#endif
