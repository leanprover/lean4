// Lean compiler output
// Module: Init.Omega.Coeffs
// Imports: public import Init.Omega.IntList import all Init.Omega.IntList
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
lean_object* l_Lean_Omega_IntList_smul(lean_object*, lean_object*);
lean_object* l_Lean_Omega_IntList_sdiv(lean_object*, lean_object*);
lean_object* l_Lean_Omega_IntList_dot(lean_object*, lean_object*);
lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Omega_IntList_get(lean_object*, lean_object*);
lean_object* l_Lean_Omega_IntList_leading(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Omega_IntList_set(lean_object*, lean_object*, lean_object*);
lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(lean_object*, lean_object*);
lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(lean_object*, lean_object*);
lean_object* l_Int_bmod(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Lean_Omega_IntList_neg(lean_object*);
lean_object* l_List_findIdx_x3f_go___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Omega_IntList_gcd(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_toList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_toList___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_ofList___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_set___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_gcd(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_gcd___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_smul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_smul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_sdiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_sdiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_dot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_dot___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_combo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_combo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_length___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_leading(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_leading___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_map(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_findIdx_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_bmod___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_bmod___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_bmod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_bmod__dot__sub__dot__bmod(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_toList(lean_object* v_xs_1_){
_start:
{
lean_inc(v_xs_1_);
return v_xs_1_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_toList___boxed(lean_object* v_xs_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_Lean_Omega_Coeffs_toList(v_xs_2_);
lean_dec(v_xs_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_ofList(lean_object* v_xs_4_){
_start:
{
lean_inc(v_xs_4_);
return v_xs_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_ofList___boxed(lean_object* v_xs_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Omega_Coeffs_ofList(v_xs_5_);
lean_dec(v_xs_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_set(lean_object* v_xs_7_, lean_object* v_i_8_, lean_object* v_y_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Omega_IntList_set(v_xs_7_, v_i_8_, v_y_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_set___boxed(lean_object* v_xs_11_, lean_object* v_i_12_, lean_object* v_y_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_Omega_Coeffs_set(v_xs_11_, v_i_12_, v_y_13_);
lean_dec(v_i_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_get(lean_object* v_xs_15_, lean_object* v_i_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Omega_IntList_get(v_xs_15_, v_i_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_get___boxed(lean_object* v_xs_18_, lean_object* v_i_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Omega_Coeffs_get(v_xs_18_, v_i_19_);
lean_dec(v_xs_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_gcd(lean_object* v_xs_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Lean_Omega_IntList_gcd(v_xs_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_gcd___boxed(lean_object* v_xs_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Omega_Coeffs_gcd(v_xs_23_);
lean_dec(v_xs_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_smul(lean_object* v_xs_25_, lean_object* v_g_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Omega_IntList_smul(v_xs_25_, v_g_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_smul___boxed(lean_object* v_xs_28_, lean_object* v_g_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Omega_Coeffs_smul(v_xs_28_, v_g_29_);
lean_dec(v_g_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_sdiv(lean_object* v_xs_31_, lean_object* v_g_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Omega_IntList_sdiv(v_xs_31_, v_g_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_sdiv___boxed(lean_object* v_xs_34_, lean_object* v_g_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Omega_Coeffs_sdiv(v_xs_34_, v_g_35_);
lean_dec(v_g_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_dot(lean_object* v_xs_37_, lean_object* v_ys_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Omega_IntList_dot(v_xs_37_, v_ys_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_dot___boxed(lean_object* v_xs_40_, lean_object* v_ys_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Omega_Coeffs_dot(v_xs_40_, v_ys_41_);
lean_dec(v_xs_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_add(lean_object* v_xs_43_, lean_object* v_ys_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(v_xs_43_, v_ys_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_sub(lean_object* v_xs_46_, lean_object* v_ys_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(v_xs_46_, v_ys_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_neg(lean_object* v_xs_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Omega_IntList_neg(v_xs_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_combo(lean_object* v_a_51_, lean_object* v_xs_52_, lean_object* v_b_53_, lean_object* v_ys_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_51_, v_b_53_, v_xs_52_, v_ys_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_combo___boxed(lean_object* v_a_56_, lean_object* v_xs_57_, lean_object* v_b_58_, lean_object* v_ys_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Omega_Coeffs_combo(v_a_56_, v_xs_57_, v_b_58_, v_ys_59_);
lean_dec(v_b_58_);
lean_dec(v_a_56_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_length(lean_object* v_xs_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_List_lengthTR___redArg(v_xs_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_length___boxed(lean_object* v_xs_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Omega_Coeffs_length(v_xs_63_);
lean_dec(v_xs_63_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_leading(lean_object* v_xs_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Omega_IntList_leading(v_xs_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_leading___boxed(lean_object* v_xs_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Omega_Coeffs_leading(v_xs_67_);
lean_dec(v_xs_67_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_map(lean_object* v_f_69_, lean_object* v_xs_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_box(0);
v___x_72_ = l_List_mapTR_loop___redArg(v_f_69_, v_xs_70_, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_findIdx_x3f(lean_object* v_f_73_, lean_object* v_xs_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = l_List_findIdx_x3f_go___redArg(v_f_73_, v_xs_74_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_bmod___lam__0(lean_object* v_m_77_, lean_object* v_x_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Int_bmod(v_x_78_, v_m_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_bmod___lam__0___boxed(lean_object* v_m_80_, lean_object* v_x_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Omega_Coeffs_bmod___lam__0(v_m_80_, v_x_81_);
lean_dec(v_x_81_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_bmod(lean_object* v_x_83_, lean_object* v_m_84_){
_start:
{
lean_object* v___f_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___f_85_ = lean_alloc_closure((void*)(l_Lean_Omega_Coeffs_bmod___lam__0___boxed), 2, 1);
lean_closure_set(v___f_85_, 0, v_m_84_);
v___x_86_ = lean_box(0);
v___x_87_ = l_List_mapTR_loop___redArg(v___f_85_, v_x_83_, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_Coeffs_bmod__dot__sub__dot__bmod(lean_object* v_m_88_, lean_object* v_a_89_, lean_object* v_b_90_){
_start:
{
lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
lean_inc(v_m_88_);
v___f_91_ = lean_alloc_closure((void*)(l_Lean_Omega_Coeffs_bmod___lam__0___boxed), 2, 1);
lean_closure_set(v___f_91_, 0, v_m_88_);
lean_inc(v_b_90_);
v___x_92_ = l_Lean_Omega_IntList_dot(v_a_89_, v_b_90_);
v___x_93_ = l_Int_bmod(v___x_92_, v_m_88_);
lean_dec(v___x_92_);
v___x_94_ = lean_box(0);
v___x_95_ = l_List_mapTR_loop___redArg(v___f_91_, v_a_89_, v___x_94_);
v___x_96_ = l_Lean_Omega_IntList_dot(v___x_95_, v_b_90_);
lean_dec(v___x_95_);
v___x_97_ = lean_int_sub(v___x_93_, v___x_96_);
lean_dec(v___x_96_);
lean_dec(v___x_93_);
return v___x_97_;
}
}
lean_object* runtime_initialize_Init_Omega_IntList(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega_IntList(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Omega_Coeffs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Omega_IntList(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega_IntList(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Omega_Coeffs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Omega_IntList(uint8_t builtin);
lean_object* initialize_Init_Omega_IntList(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Omega_Coeffs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Omega_IntList(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega_IntList(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega_Coeffs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Omega_Coeffs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Omega_Coeffs(builtin);
}
#ifdef __cplusplus
}
#endif
