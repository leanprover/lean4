// Lean compiler output
// Module: Init.Data.Int.Gcd
// Imports: public import Init.Data.Nat.Lcm public import Init.Data.Int.DivMod.Basic import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.Pow import Init.Data.Nat.Dvd import Init.Omega import Init.RCases
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
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Nat_dvdProdDvdOfDvdProd___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* l_Nat_lcm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_gcd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_gcd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_dvdProdDvdOfDvdProd_spec__0(lean_object*);
static lean_once_cell_t l_Int_dvdProdDvdOfDvdProd___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_dvdProdDvdOfDvdProd___redArg___closed__0;
LEAN_EXPORT lean_object* l_Int_dvdProdDvdOfDvdProd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_dvdProdDvdOfDvdProd___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_dvdProdDvdOfDvdProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_dvdProdDvdOfDvdProd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_lcm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_lcm___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_gcd(lean_object* v_m_1_, lean_object* v_n_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = lean_nat_abs(v_m_1_);
v___x_4_ = lean_nat_abs(v_n_2_);
v___x_5_ = lean_nat_gcd(v___x_3_, v___x_4_);
lean_dec(v___x_4_);
lean_dec(v___x_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Int_gcd___boxed(lean_object* v_m_6_, lean_object* v_n_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Int_gcd(v_m_6_, v_n_7_);
lean_dec(v_n_7_);
lean_dec(v_m_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_dvdProdDvdOfDvdProd_spec__0(lean_object* v_a_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_nat_to_int(v_a_9_);
return v___x_10_;
}
}
static lean_object* _init_l_Int_dvdProdDvdOfDvdProd___redArg___closed__0(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_nat_to_int(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Int_dvdProdDvdOfDvdProd___redArg(lean_object* v_k_13_, lean_object* v_m_14_, lean_object* v_n_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v_d_u2080_19_; lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_16_ = lean_nat_abs(v_k_13_);
v___x_17_ = lean_nat_abs(v_m_14_);
v___x_18_ = lean_nat_abs(v_n_15_);
v_d_u2080_19_ = l_Nat_dvdProdDvdOfDvdProd___redArg(v___x_16_, v___x_17_, v___x_18_);
lean_dec(v___x_17_);
lean_dec(v___x_16_);
v___x_20_ = lean_obj_once(&l_Int_dvdProdDvdOfDvdProd___redArg___closed__0, &l_Int_dvdProdDvdOfDvdProd___redArg___closed__0_once, _init_l_Int_dvdProdDvdOfDvdProd___redArg___closed__0);
v___x_21_ = lean_int_dec_le(v___x_20_, v_k_13_);
if (v___x_21_ == 0)
{
lean_object* v_fst_22_; lean_object* v_snd_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_33_; 
v_fst_22_ = lean_ctor_get(v_d_u2080_19_, 0);
v_snd_23_ = lean_ctor_get(v_d_u2080_19_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_d_u2080_19_);
if (v_isSharedCheck_33_ == 0)
{
v___x_25_ = v_d_u2080_19_;
v_isShared_26_ = v_isSharedCheck_33_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_snd_23_);
lean_inc(v_fst_22_);
lean_dec(v_d_u2080_19_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_33_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_31_; 
v___x_27_ = lean_nat_to_int(v_fst_22_);
v___x_28_ = lean_int_neg(v___x_27_);
lean_dec(v___x_27_);
v___x_29_ = lean_nat_to_int(v_snd_23_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 1, v___x_29_);
lean_ctor_set(v___x_25_, 0, v___x_28_);
v___x_31_ = v___x_25_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v___x_28_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v___x_29_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
else
{
lean_object* v_fst_34_; lean_object* v_snd_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_44_; 
v_fst_34_ = lean_ctor_get(v_d_u2080_19_, 0);
v_snd_35_ = lean_ctor_get(v_d_u2080_19_, 1);
v_isSharedCheck_44_ = !lean_is_exclusive(v_d_u2080_19_);
if (v_isSharedCheck_44_ == 0)
{
v___x_37_ = v_d_u2080_19_;
v_isShared_38_ = v_isSharedCheck_44_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_snd_35_);
lean_inc(v_fst_34_);
lean_dec(v_d_u2080_19_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_44_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_42_; 
v___x_39_ = lean_nat_to_int(v_fst_34_);
v___x_40_ = lean_nat_to_int(v_snd_35_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 1, v___x_40_);
lean_ctor_set(v___x_37_, 0, v___x_39_);
v___x_42_ = v___x_37_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v___x_40_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_dvdProdDvdOfDvdProd___redArg___boxed(lean_object* v_k_45_, lean_object* v_m_46_, lean_object* v_n_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Int_dvdProdDvdOfDvdProd___redArg(v_k_45_, v_m_46_, v_n_47_);
lean_dec(v_n_47_);
lean_dec(v_m_46_);
lean_dec(v_k_45_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Int_dvdProdDvdOfDvdProd(lean_object* v_k_49_, lean_object* v_m_50_, lean_object* v_n_51_, lean_object* v_h_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Int_dvdProdDvdOfDvdProd___redArg(v_k_49_, v_m_50_, v_n_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Int_dvdProdDvdOfDvdProd___boxed(lean_object* v_k_54_, lean_object* v_m_55_, lean_object* v_n_56_, lean_object* v_h_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Int_dvdProdDvdOfDvdProd(v_k_54_, v_m_55_, v_n_56_, v_h_57_);
lean_dec(v_n_56_);
lean_dec(v_m_55_);
lean_dec(v_k_54_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Int_lcm(lean_object* v_m_59_, lean_object* v_n_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_nat_abs(v_m_59_);
v___x_62_ = lean_nat_abs(v_n_60_);
v___x_63_ = l_Nat_lcm(v___x_61_, v___x_62_);
lean_dec(v___x_62_);
lean_dec(v___x_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Int_lcm___boxed(lean_object* v_m_64_, lean_object* v_n_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Int_lcm(v_m_64_, v_n_65_);
lean_dec(v_n_65_);
lean_dec(v_m_64_);
return v_res_66_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Lcm(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Int_Gcd(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Lcm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Int_Gcd(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Lcm(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_Gcd(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Lcm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Int_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Int_Gcd(builtin);
}
#ifdef __cplusplus
}
#endif
