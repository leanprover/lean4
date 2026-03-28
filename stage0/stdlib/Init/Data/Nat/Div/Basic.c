// Lean compiler output
// Module: Init.Data.Nat.Div.Basic
// Imports: public import Init.Data.NeZero public import Init.WF meta import Init.MetaTypes import Init.WFTactics
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_instDvd;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_div_inductionOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_div_inductionOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div_exact(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_divExact___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_mod_inductionOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_mod_inductionOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Nat_instDvd(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___redArg(lean_object* v_fuel_2_, lean_object* v_h__1_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; lean_object* v_one_6_; lean_object* v_n_7_; lean_object* v___x_8_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_fuel_2_, v_zero_4_);
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_fuel_2_, v_one_6_);
v___x_8_ = lean_apply_2(v_h__1_3_, v_n_7_, lean_box(0));
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___redArg___boxed(lean_object* v_fuel_9_, lean_object* v_h__1_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___redArg(v_fuel_9_, v_h__1_10_);
lean_dec(v_fuel_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter(lean_object* v_x_12_, lean_object* v_motive_13_, lean_object* v_fuel_14_, lean_object* v_hfuel_15_, lean_object* v_h__1_16_){
_start:
{
lean_object* v_zero_17_; uint8_t v_isZero_18_; lean_object* v_one_19_; lean_object* v_n_20_; lean_object* v___x_21_; 
v_zero_17_ = lean_unsigned_to_nat(0u);
v_isZero_18_ = lean_nat_dec_eq(v_fuel_14_, v_zero_17_);
v_one_19_ = lean_unsigned_to_nat(1u);
v_n_20_ = lean_nat_sub(v_fuel_14_, v_one_19_);
v___x_21_ = lean_apply_2(v_h__1_16_, v_n_20_, lean_box(0));
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___boxed(lean_object* v_x_22_, lean_object* v_motive_23_, lean_object* v_fuel_24_, lean_object* v_hfuel_25_, lean_object* v_h__1_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter(v_x_22_, v_motive_23_, v_fuel_24_, v_hfuel_25_, v_h__1_26_);
lean_dec(v_fuel_24_);
lean_dec(v_x_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Nat_div_inductionOn___redArg(lean_object* v_x_28_, lean_object* v_y_29_, lean_object* v_ind_30_, lean_object* v_base_31_){
_start:
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = lean_unsigned_to_nat(0u);
v___x_33_ = lean_nat_dec_lt(v___x_32_, v_y_29_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; 
lean_dec(v_ind_30_);
v___x_34_ = lean_apply_3(v_base_31_, v_x_28_, v_y_29_, lean_box(0));
return v___x_34_;
}
else
{
uint8_t v___x_35_; 
v___x_35_ = lean_nat_dec_le(v_y_29_, v_x_28_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; 
lean_dec(v_ind_30_);
v___x_36_ = lean_apply_3(v_base_31_, v_x_28_, v_y_29_, lean_box(0));
return v___x_36_;
}
else
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_nat_sub(v_x_28_, v_y_29_);
lean_inc(v_ind_30_);
lean_inc(v_y_29_);
v___x_38_ = l_Nat_div_inductionOn___redArg(v___x_37_, v_y_29_, v_ind_30_, v_base_31_);
v___x_39_ = lean_apply_4(v_ind_30_, v_x_28_, v_y_29_, lean_box(0), v___x_38_);
return v___x_39_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_div_inductionOn(lean_object* v_motive_40_, lean_object* v_x_41_, lean_object* v_y_42_, lean_object* v_ind_43_, lean_object* v_base_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Nat_div_inductionOn___redArg(v_x_41_, v_y_42_, v_ind_43_, v_base_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Nat_divExact___boxed(lean_object* v_x_49_, lean_object* v_y_50_, lean_object* v_h_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = lean_nat_div_exact(v_x_49_, v_y_50_);
lean_dec(v_y_50_);
lean_dec(v_x_49_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg(lean_object* v_x_53_, lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_){
_start:
{
lean_object* v_zero_57_; uint8_t v_isZero_58_; 
v_zero_57_ = lean_unsigned_to_nat(0u);
v_isZero_58_ = lean_nat_dec_eq(v_x_53_, v_zero_57_);
if (v_isZero_58_ == 1)
{
lean_object* v___x_59_; 
lean_dec(v_h__2_56_);
v___x_59_ = lean_apply_1(v_h__1_55_, v_x_54_);
return v___x_59_;
}
else
{
lean_object* v_one_60_; lean_object* v_n_61_; lean_object* v___x_62_; 
lean_dec(v_h__1_55_);
v_one_60_ = lean_unsigned_to_nat(1u);
v_n_61_ = lean_nat_sub(v_x_53_, v_one_60_);
v___x_62_ = lean_apply_2(v_h__2_56_, v_n_61_, v_x_54_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg___boxed(lean_object* v_x_63_, lean_object* v_x_64_, lean_object* v_h__1_65_, lean_object* v_h__2_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg(v_x_63_, v_x_64_, v_h__1_65_, v_h__2_66_);
lean_dec(v_x_63_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter(lean_object* v_motive_68_, lean_object* v_x_69_, lean_object* v_x_70_, lean_object* v_h__1_71_, lean_object* v_h__2_72_){
_start:
{
lean_object* v_zero_73_; uint8_t v_isZero_74_; 
v_zero_73_ = lean_unsigned_to_nat(0u);
v_isZero_74_ = lean_nat_dec_eq(v_x_69_, v_zero_73_);
if (v_isZero_74_ == 1)
{
lean_object* v___x_75_; 
lean_dec(v_h__2_72_);
v___x_75_ = lean_apply_1(v_h__1_71_, v_x_70_);
return v___x_75_;
}
else
{
lean_object* v_one_76_; lean_object* v_n_77_; lean_object* v___x_78_; 
lean_dec(v_h__1_71_);
v_one_76_ = lean_unsigned_to_nat(1u);
v_n_77_ = lean_nat_sub(v_x_69_, v_one_76_);
v___x_78_ = lean_apply_2(v_h__2_72_, v_n_77_, v_x_70_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___boxed(lean_object* v_motive_79_, lean_object* v_x_80_, lean_object* v_x_81_, lean_object* v_h__1_82_, lean_object* v_h__2_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter(v_motive_79_, v_x_80_, v_x_81_, v_h__1_82_, v_h__2_83_);
lean_dec(v_x_80_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Nat_mod_inductionOn___redArg(lean_object* v_x_85_, lean_object* v_y_86_, lean_object* v_ind_87_, lean_object* v_base_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Nat_div_inductionOn___redArg(v_x_85_, v_y_86_, v_ind_87_, v_base_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Nat_mod_inductionOn(lean_object* v_motive_90_, lean_object* v_x_91_, lean_object* v_y_92_, lean_object* v_ind_93_, lean_object* v_base_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Nat_div_inductionOn___redArg(v_x_91_, v_y_92_, v_ind_93_, v_base_94_);
return v___x_95_;
}
}
lean_object* runtime_initialize_Init_Data_NeZero(uint8_t builtin);
lean_object* runtime_initialize_Init_WF(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_NeZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Nat_instDvd = _init_l_Nat_instDvd();
lean_mark_persistent(l_Nat_instDvd);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_NeZero(uint8_t builtin);
lean_object* initialize_Init_WF(uint8_t builtin);
lean_object* initialize_Init_MetaTypes(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_NeZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Nat_Div_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
