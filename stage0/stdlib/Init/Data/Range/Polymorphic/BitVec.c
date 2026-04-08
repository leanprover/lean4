// Lean compiler output
// Module: Init.Data.Range.Polymorphic.BitVec
// Imports: public import Init.Data.Range.Polymorphic.Instances import Init.Omega import Init.Data.BitVec.Bootstrap import Init.Data.BitVec.Lemmas import Init.Data.Nat.Lemmas import Init.Data.Option.Lemmas
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxcHasSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxcHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_BitVec_instRxcHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_BitVec_instRxcHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_BitVec_instRxcHasSize___closed__0 = (const lean_object*)&l_BitVec_instRxcHasSize___closed__0_value;
LEAN_EXPORT lean_object* l_BitVec_instRxcHasSize(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxcHasSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxoHasSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxoHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_BitVec_instRxoHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_BitVec_instRxoHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_BitVec_instRxoHasSize___closed__0 = (const lean_object*)&l_BitVec_instRxoHasSize___closed__0_value;
LEAN_EXPORT lean_object* l_BitVec_instRxoHasSize(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxoHasSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxiHasSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxiHasSize___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instRxiHasSize(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable___lam__0(lean_object* v_n_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = l_BitVec_ofNat(v_n_1_, v___x_3_);
v___x_5_ = l_BitVec_add(v_n_1_, v_i_2_, v___x_4_);
lean_dec(v___x_4_);
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = l_BitVec_ofNat(v_n_1_, v___x_6_);
v___x_8_ = lean_nat_dec_eq(v___x_5_, v___x_7_);
lean_dec(v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; 
v___x_9_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_5_);
return v___x_9_;
}
else
{
lean_object* v___x_10_; 
lean_dec(v___x_5_);
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable___lam__0___boxed(lean_object* v_n_11_, lean_object* v_i_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_BitVec_instUpwardEnumerable___lam__0(v_n_11_, v_i_12_);
lean_dec(v_i_12_);
lean_dec(v_n_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable___lam__1(lean_object* v_n_14_, lean_object* v_m_15_, lean_object* v_i_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_17_ = lean_nat_add(v_i_16_, v_m_15_);
v___x_18_ = lean_unsigned_to_nat(2u);
v___x_19_ = lean_nat_pow(v___x_18_, v_n_14_);
v___x_20_ = lean_nat_dec_lt(v___x_17_, v___x_19_);
lean_dec(v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; 
lean_dec(v___x_17_);
v___x_21_ = lean_box(0);
return v___x_21_;
}
else
{
lean_object* v___x_22_; 
v___x_22_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_17_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_23_, lean_object* v_m_24_, lean_object* v_i_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_BitVec_instUpwardEnumerable___lam__1(v_n_23_, v_m_24_, v_i_25_);
lean_dec(v_i_25_);
lean_dec(v_m_24_);
lean_dec(v_n_23_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instUpwardEnumerable(lean_object* v_n_27_){
_start:
{
lean_object* v___f_28_; lean_object* v___f_29_; lean_object* v___x_30_; 
lean_inc(v_n_27_);
v___f_28_ = lean_alloc_closure((void*)(l_BitVec_instUpwardEnumerable___lam__0___boxed), 2, 1);
lean_closure_set(v___f_28_, 0, v_n_27_);
v___f_29_ = lean_alloc_closure((void*)(l_BitVec_instUpwardEnumerable___lam__1___boxed), 3, 1);
lean_closure_set(v___f_29_, 0, v_n_27_);
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v___f_28_);
lean_ctor_set(v___x_30_, 1, v___f_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxcHasSize___lam__0(lean_object* v_lo_31_, lean_object* v_hi_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_unsigned_to_nat(1u);
v___x_34_ = lean_nat_add(v_hi_32_, v___x_33_);
v___x_35_ = lean_nat_sub(v___x_34_, v_lo_31_);
lean_dec(v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxcHasSize___lam__0___boxed(lean_object* v_lo_36_, lean_object* v_hi_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_BitVec_instRxcHasSize___lam__0(v_lo_36_, v_hi_37_);
lean_dec(v_hi_37_);
lean_dec(v_lo_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxcHasSize(lean_object* v_n_40_){
_start:
{
lean_object* v___f_41_; 
v___f_41_ = ((lean_object*)(l_BitVec_instRxcHasSize___closed__0));
return v___f_41_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxcHasSize___boxed(lean_object* v_n_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_BitVec_instRxcHasSize(v_n_42_);
lean_dec(v_n_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxoHasSize___lam__0(lean_object* v_lo_44_, lean_object* v_hi_45_){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_46_ = lean_unsigned_to_nat(1u);
v___x_47_ = lean_nat_add(v_hi_45_, v___x_46_);
v___x_48_ = lean_nat_sub(v___x_47_, v_lo_44_);
lean_dec(v___x_47_);
v___x_49_ = lean_nat_sub(v___x_48_, v___x_46_);
lean_dec(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxoHasSize___lam__0___boxed(lean_object* v_lo_50_, lean_object* v_hi_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_BitVec_instRxoHasSize___lam__0(v_lo_50_, v_hi_51_);
lean_dec(v_hi_51_);
lean_dec(v_lo_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxoHasSize(lean_object* v_n_54_){
_start:
{
lean_object* v___f_55_; 
v___f_55_ = ((lean_object*)(l_BitVec_instRxoHasSize___closed__0));
return v___f_55_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxoHasSize___boxed(lean_object* v_n_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_BitVec_instRxoHasSize(v_n_56_);
lean_dec(v_n_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxiHasSize___lam__0(lean_object* v_n_58_, lean_object* v_lo_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_unsigned_to_nat(2u);
v___x_61_ = lean_nat_pow(v___x_60_, v_n_58_);
v___x_62_ = lean_nat_sub(v___x_61_, v_lo_59_);
lean_dec(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxiHasSize___lam__0___boxed(lean_object* v_n_63_, lean_object* v_lo_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_BitVec_instRxiHasSize___lam__0(v_n_63_, v_lo_64_);
lean_dec(v_lo_64_);
lean_dec(v_n_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_BitVec_instRxiHasSize(lean_object* v_n_66_){
_start:
{
lean_object* v___f_67_; 
v___f_67_ = lean_alloc_closure((void*)(l_BitVec_instRxiHasSize___lam__0___boxed), 2, 1);
lean_closure_set(v___f_67_, 0, v_n_66_);
return v___f_67_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_BitVec(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Range_Polymorphic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_BitVec(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_BitVec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_BitVec(builtin);
}
#ifdef __cplusplus
}
#endif
