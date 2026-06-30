// Lean compiler output
// Module: Init.Data.Int.Bitwise.Basic
// Imports: public import Init.Data.Int.Basic public import Init.Data.Nat.Bitwise.Basic
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
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_neg_succ_of_nat(lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_once_cell_t l_Int_not___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_not___closed__0;
LEAN_EXPORT lean_object* l_Int_not(lean_object*);
LEAN_EXPORT lean_object* l_Int_not___boxed(lean_object*);
static const lean_closure_object l_Int_instComplement___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_not___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instComplement___closed__0 = (const lean_object*)&l_Int_instComplement___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_instComplement = (const lean_object*)&l_Int_instComplement___closed__0_value;
LEAN_EXPORT lean_object* l_Int_shiftRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_shiftRight___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_instHShiftRightNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_shiftRight___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instHShiftRightNat___closed__0 = (const lean_object*)&l_Int_instHShiftRightNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_instHShiftRightNat = (const lean_object*)&l_Int_instHShiftRightNat___closed__0_value;
LEAN_EXPORT lean_object* l_Int_shiftLeft(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_shiftLeft___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_instHShiftLeftNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_shiftLeft___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instHShiftLeftNat___closed__0 = (const lean_object*)&l_Int_instHShiftLeftNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_instHShiftLeftNat = (const lean_object*)&l_Int_instHShiftLeftNat___closed__0_value;
static lean_object* _init_l_Int_not___closed__0(void){
_start:
{
lean_object* v_natZero_1_; lean_object* v_intZero_2_; 
v_natZero_1_ = lean_unsigned_to_nat(0u);
v_intZero_2_ = lean_nat_to_int(v_natZero_1_);
return v_intZero_2_;
}
}
LEAN_EXPORT lean_object* l_Int_not(lean_object* v_x_3_){
_start:
{
lean_object* v_intZero_4_; uint8_t v_isNeg_5_; 
v_intZero_4_ = lean_obj_once(&l_Int_not___closed__0, &l_Int_not___closed__0_once, _init_l_Int_not___closed__0);
v_isNeg_5_ = lean_int_dec_lt(v_x_3_, v_intZero_4_);
if (v_isNeg_5_ == 0)
{
lean_object* v_a_6_; lean_object* v___x_7_; 
v_a_6_ = lean_nat_abs(v_x_3_);
v___x_7_ = lean_int_neg_succ_of_nat(v_a_6_);
return v___x_7_;
}
else
{
lean_object* v_abs_8_; lean_object* v_one_9_; lean_object* v_a_10_; lean_object* v___x_11_; 
v_abs_8_ = lean_nat_abs(v_x_3_);
v_one_9_ = lean_unsigned_to_nat(1u);
v_a_10_ = lean_nat_sub(v_abs_8_, v_one_9_);
lean_dec(v_abs_8_);
v___x_11_ = lean_nat_to_int(v_a_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Int_not___boxed(lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Int_not(v_x_12_);
lean_dec(v_x_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Int_shiftRight(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
lean_object* v_intZero_18_; uint8_t v_isNeg_19_; 
v_intZero_18_ = lean_obj_once(&l_Int_not___closed__0, &l_Int_not___closed__0_once, _init_l_Int_not___closed__0);
v_isNeg_19_ = lean_int_dec_lt(v_x_16_, v_intZero_18_);
if (v_isNeg_19_ == 0)
{
lean_object* v_a_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v_a_20_ = lean_nat_abs(v_x_16_);
v___x_21_ = lean_nat_shiftr(v_a_20_, v_x_17_);
lean_dec(v_a_20_);
v___x_22_ = lean_nat_to_int(v___x_21_);
return v___x_22_;
}
else
{
lean_object* v_abs_23_; lean_object* v_one_24_; lean_object* v_a_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v_abs_23_ = lean_nat_abs(v_x_16_);
v_one_24_ = lean_unsigned_to_nat(1u);
v_a_25_ = lean_nat_sub(v_abs_23_, v_one_24_);
lean_dec(v_abs_23_);
v___x_26_ = lean_nat_shiftr(v_a_25_, v_x_17_);
lean_dec(v_a_25_);
v___x_27_ = lean_int_neg_succ_of_nat(v___x_26_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l_Int_shiftRight___boxed(lean_object* v_x_28_, lean_object* v_x_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Int_shiftRight(v_x_28_, v_x_29_);
lean_dec(v_x_29_);
lean_dec(v_x_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Int_shiftLeft(lean_object* v_x_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_intZero_35_; uint8_t v_isNeg_36_; 
v_intZero_35_ = lean_obj_once(&l_Int_not___closed__0, &l_Int_not___closed__0_once, _init_l_Int_not___closed__0);
v_isNeg_36_ = lean_int_dec_lt(v_x_33_, v_intZero_35_);
if (v_isNeg_36_ == 0)
{
lean_object* v_a_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v_a_37_ = lean_nat_abs(v_x_33_);
v___x_38_ = lean_nat_shiftl(v_a_37_, v_x_34_);
lean_dec(v_a_37_);
v___x_39_ = lean_nat_to_int(v___x_38_);
return v___x_39_;
}
else
{
lean_object* v_abs_40_; lean_object* v_one_41_; lean_object* v_a_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v_abs_40_ = lean_nat_abs(v_x_33_);
v_one_41_ = lean_unsigned_to_nat(1u);
v_a_42_ = lean_nat_sub(v_abs_40_, v_one_41_);
lean_dec(v_abs_40_);
v___x_43_ = lean_nat_add(v_a_42_, v_one_41_);
lean_dec(v_a_42_);
v___x_44_ = lean_nat_shiftl(v___x_43_, v_x_34_);
lean_dec(v___x_43_);
v___x_45_ = lean_nat_sub(v___x_44_, v_one_41_);
lean_dec(v___x_44_);
v___x_46_ = lean_int_neg_succ_of_nat(v___x_45_);
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l_Int_shiftLeft___boxed(lean_object* v_x_47_, lean_object* v_x_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Int_shiftLeft(v_x_47_, v_x_48_);
lean_dec(v_x_48_);
lean_dec(v_x_47_);
return v_res_49_;
}
}
lean_object* runtime_initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Int_Bitwise_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Int_Bitwise_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_Bitwise_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Int_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Int_Bitwise_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
