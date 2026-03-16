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
lean_object* v___x_17_; 
v___x_17_ = l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___redArg(v_fuel_14_, v_h__1_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___boxed(lean_object* v_x_18_, lean_object* v_motive_19_, lean_object* v_fuel_20_, lean_object* v_hfuel_21_, lean_object* v_h__1_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter(v_x_18_, v_motive_19_, v_fuel_20_, v_hfuel_21_, v_h__1_22_);
lean_dec(v_fuel_20_);
lean_dec(v_x_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Nat_div_inductionOn___redArg(lean_object* v_x_24_, lean_object* v_y_25_, lean_object* v_ind_26_, lean_object* v_base_27_){
_start:
{
lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = lean_nat_dec_lt(v___x_28_, v_y_25_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; 
lean_dec(v_ind_26_);
v___x_30_ = lean_apply_3(v_base_27_, v_x_24_, v_y_25_, lean_box(0));
return v___x_30_;
}
else
{
uint8_t v___x_31_; 
v___x_31_ = lean_nat_dec_le(v_y_25_, v_x_24_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; 
lean_dec(v_ind_26_);
v___x_32_ = lean_apply_3(v_base_27_, v_x_24_, v_y_25_, lean_box(0));
return v___x_32_;
}
else
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_nat_sub(v_x_24_, v_y_25_);
lean_inc(v_ind_26_);
lean_inc(v_y_25_);
v___x_34_ = l_Nat_div_inductionOn___redArg(v___x_33_, v_y_25_, v_ind_26_, v_base_27_);
v___x_35_ = lean_apply_4(v_ind_26_, v_x_24_, v_y_25_, lean_box(0), v___x_34_);
return v___x_35_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_div_inductionOn(lean_object* v_motive_36_, lean_object* v_x_37_, lean_object* v_y_38_, lean_object* v_ind_39_, lean_object* v_base_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Nat_div_inductionOn___redArg(v_x_37_, v_y_38_, v_ind_39_, v_base_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Nat_divExact___boxed(lean_object* v_x_45_, lean_object* v_y_46_, lean_object* v_h_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lean_nat_div_exact(v_x_45_, v_y_46_);
lean_dec(v_y_46_);
lean_dec(v_x_45_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg(lean_object* v_x_49_, lean_object* v_x_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_){
_start:
{
lean_object* v_zero_53_; uint8_t v_isZero_54_; 
v_zero_53_ = lean_unsigned_to_nat(0u);
v_isZero_54_ = lean_nat_dec_eq(v_x_49_, v_zero_53_);
if (v_isZero_54_ == 1)
{
lean_object* v___x_55_; 
lean_dec(v_h__2_52_);
v___x_55_ = lean_apply_1(v_h__1_51_, v_x_50_);
return v___x_55_;
}
else
{
lean_object* v_one_56_; lean_object* v_n_57_; lean_object* v___x_58_; 
lean_dec(v_h__1_51_);
v_one_56_ = lean_unsigned_to_nat(1u);
v_n_57_ = lean_nat_sub(v_x_49_, v_one_56_);
v___x_58_ = lean_apply_2(v_h__2_52_, v_n_57_, v_x_50_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg___boxed(lean_object* v_x_59_, lean_object* v_x_60_, lean_object* v_h__1_61_, lean_object* v_h__2_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg(v_x_59_, v_x_60_, v_h__1_61_, v_h__2_62_);
lean_dec(v_x_59_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter(lean_object* v_motive_64_, lean_object* v_x_65_, lean_object* v_x_66_, lean_object* v_h__1_67_, lean_object* v_h__2_68_){
_start:
{
lean_object* v_zero_69_; uint8_t v_isZero_70_; 
v_zero_69_ = lean_unsigned_to_nat(0u);
v_isZero_70_ = lean_nat_dec_eq(v_x_65_, v_zero_69_);
if (v_isZero_70_ == 1)
{
lean_object* v___x_71_; 
lean_dec(v_h__2_68_);
v___x_71_ = lean_apply_1(v_h__1_67_, v_x_66_);
return v___x_71_;
}
else
{
lean_object* v_one_72_; lean_object* v_n_73_; lean_object* v___x_74_; 
lean_dec(v_h__1_67_);
v_one_72_ = lean_unsigned_to_nat(1u);
v_n_73_ = lean_nat_sub(v_x_65_, v_one_72_);
v___x_74_ = lean_apply_2(v_h__2_68_, v_n_73_, v_x_66_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___boxed(lean_object* v_motive_75_, lean_object* v_x_76_, lean_object* v_x_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter(v_motive_75_, v_x_76_, v_x_77_, v_h__1_78_, v_h__2_79_);
lean_dec(v_x_76_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Nat_mod_inductionOn___redArg(lean_object* v_x_81_, lean_object* v_y_82_, lean_object* v_ind_83_, lean_object* v_base_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Nat_div_inductionOn___redArg(v_x_81_, v_y_82_, v_ind_83_, v_base_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Nat_mod_inductionOn(lean_object* v_motive_86_, lean_object* v_x_87_, lean_object* v_y_88_, lean_object* v_ind_89_, lean_object* v_base_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Nat_div_inductionOn___redArg(v_x_87_, v_y_88_, v_ind_89_, v_base_90_);
return v___x_91_;
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
