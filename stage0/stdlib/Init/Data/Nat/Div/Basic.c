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
uint8_t v___y_33_; lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_38_ = lean_unsigned_to_nat(0u);
v___x_39_ = lean_nat_dec_lt(v___x_38_, v_y_29_);
if (v___x_39_ == 0)
{
v___y_33_ = v___x_39_;
goto v___jp_32_;
}
else
{
uint8_t v___x_40_; 
v___x_40_ = lean_nat_dec_le(v_y_29_, v_x_28_);
v___y_33_ = v___x_40_;
goto v___jp_32_;
}
v___jp_32_:
{
if (v___y_33_ == 0)
{
lean_object* v___x_34_; 
lean_dec(v_ind_30_);
v___x_34_ = lean_apply_3(v_base_31_, v_x_28_, v_y_29_, lean_box(0));
return v___x_34_;
}
else
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_35_ = lean_nat_sub(v_x_28_, v_y_29_);
lean_inc(v_ind_30_);
lean_inc(v_y_29_);
v___x_36_ = l_Nat_div_inductionOn___redArg(v___x_35_, v_y_29_, v_ind_30_, v_base_31_);
v___x_37_ = lean_apply_4(v_ind_30_, v_x_28_, v_y_29_, lean_box(0), v___x_36_);
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_div_inductionOn(lean_object* v_motive_41_, lean_object* v_x_42_, lean_object* v_y_43_, lean_object* v_ind_44_, lean_object* v_base_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Nat_div_inductionOn___redArg(v_x_42_, v_y_43_, v_ind_44_, v_base_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Nat_divExact___boxed(lean_object* v_x_50_, lean_object* v_y_51_, lean_object* v_h_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = lean_nat_div_exact(v_x_50_, v_y_51_);
lean_dec(v_y_51_);
lean_dec(v_x_50_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg(lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_){
_start:
{
lean_object* v_zero_58_; uint8_t v_isZero_59_; 
v_zero_58_ = lean_unsigned_to_nat(0u);
v_isZero_59_ = lean_nat_dec_eq(v_x_54_, v_zero_58_);
if (v_isZero_59_ == 1)
{
lean_object* v___x_60_; 
lean_dec(v_h__2_57_);
v___x_60_ = lean_apply_1(v_h__1_56_, v_x_55_);
return v___x_60_;
}
else
{
lean_object* v_one_61_; lean_object* v_n_62_; lean_object* v___x_63_; 
lean_dec(v_h__1_56_);
v_one_61_ = lean_unsigned_to_nat(1u);
v_n_62_ = lean_nat_sub(v_x_54_, v_one_61_);
v___x_63_ = lean_apply_2(v_h__2_57_, v_n_62_, v_x_55_);
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg___boxed(lean_object* v_x_64_, lean_object* v_x_65_, lean_object* v_h__1_66_, lean_object* v_h__2_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg(v_x_64_, v_x_65_, v_h__1_66_, v_h__2_67_);
lean_dec(v_x_64_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter(lean_object* v_motive_69_, lean_object* v_x_70_, lean_object* v_x_71_, lean_object* v_h__1_72_, lean_object* v_h__2_73_){
_start:
{
lean_object* v_zero_74_; uint8_t v_isZero_75_; 
v_zero_74_ = lean_unsigned_to_nat(0u);
v_isZero_75_ = lean_nat_dec_eq(v_x_70_, v_zero_74_);
if (v_isZero_75_ == 1)
{
lean_object* v___x_76_; 
lean_dec(v_h__2_73_);
v___x_76_ = lean_apply_1(v_h__1_72_, v_x_71_);
return v___x_76_;
}
else
{
lean_object* v_one_77_; lean_object* v_n_78_; lean_object* v___x_79_; 
lean_dec(v_h__1_72_);
v_one_77_ = lean_unsigned_to_nat(1u);
v_n_78_ = lean_nat_sub(v_x_70_, v_one_77_);
v___x_79_ = lean_apply_2(v_h__2_73_, v_n_78_, v_x_71_);
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___boxed(lean_object* v_motive_80_, lean_object* v_x_81_, lean_object* v_x_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter(v_motive_80_, v_x_81_, v_x_82_, v_h__1_83_, v_h__2_84_);
lean_dec(v_x_81_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Nat_mod_inductionOn___redArg(lean_object* v_x_86_, lean_object* v_y_87_, lean_object* v_ind_88_, lean_object* v_base_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Nat_div_inductionOn___redArg(v_x_86_, v_y_87_, v_ind_88_, v_base_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Nat_mod_inductionOn(lean_object* v_motive_91_, lean_object* v_x_92_, lean_object* v_y_93_, lean_object* v_ind_94_, lean_object* v_base_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Nat_div_inductionOn___redArg(v_x_92_, v_y_93_, v_ind_94_, v_base_95_);
return v___x_96_;
}
}
lean_object* runtime_initialize_Init_Data_NeZero(uint8_t builtin);
lean_object* runtime_initialize_Init_WF(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
