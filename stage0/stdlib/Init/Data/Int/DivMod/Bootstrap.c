// Lean compiler output
// Module: Init.Data.Int.DivMod.Bootstrap
// Imports: public import Init.Data.Int.DivMod.Basic public import Init.Data.Nat.Div.Basic import Init.ByCases import Init.Data.Int.Lemmas import Init.Data.Int.Order import Init.Data.Nat.Dvd import Init.RCases
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_1_; lean_object* v_intZero_2_; 
v_natZero_1_ = lean_unsigned_to_nat(0u);
v_intZero_2_ = lean_nat_to_int(v_natZero_1_);
return v_intZero_2_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg(lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_h__1_5_, lean_object* v_h__2_6_, lean_object* v_h__3_7_, lean_object* v_h__4_8_, lean_object* v_h__5_9_){
_start:
{
lean_object* v_natZero_10_; lean_object* v_intZero_11_; uint8_t v_isNeg_12_; 
v_natZero_10_ = lean_unsigned_to_nat(0u);
v_intZero_11_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0);
v_isNeg_12_ = lean_int_dec_lt(v_x_3_, v_intZero_11_);
if (v_isNeg_12_ == 0)
{
lean_object* v_a_13_; uint8_t v_isNeg_14_; 
lean_dec(v_h__5_9_);
lean_dec(v_h__4_8_);
lean_dec(v_h__3_7_);
v_a_13_ = lean_nat_abs(v_x_3_);
v_isNeg_14_ = lean_int_dec_lt(v_x_4_, v_intZero_11_);
if (v_isNeg_14_ == 0)
{
lean_object* v_a_15_; lean_object* v___x_16_; 
lean_dec(v_h__2_6_);
v_a_15_ = lean_nat_abs(v_x_4_);
v___x_16_ = lean_apply_2(v_h__1_5_, v_a_13_, v_a_15_);
return v___x_16_;
}
else
{
lean_object* v_abs_17_; lean_object* v_one_18_; lean_object* v_a_19_; lean_object* v___x_20_; 
lean_dec(v_h__1_5_);
v_abs_17_ = lean_nat_abs(v_x_4_);
v_one_18_ = lean_unsigned_to_nat(1u);
v_a_19_ = lean_nat_sub(v_abs_17_, v_one_18_);
lean_dec(v_abs_17_);
v___x_20_ = lean_apply_2(v_h__2_6_, v_a_13_, v_a_19_);
return v___x_20_;
}
}
else
{
lean_object* v_abs_21_; lean_object* v_one_22_; lean_object* v_a_23_; uint8_t v_isNeg_24_; 
lean_dec(v_h__2_6_);
lean_dec(v_h__1_5_);
v_abs_21_ = lean_nat_abs(v_x_3_);
v_one_22_ = lean_unsigned_to_nat(1u);
v_a_23_ = lean_nat_sub(v_abs_21_, v_one_22_);
lean_dec(v_abs_21_);
v_isNeg_24_ = lean_int_dec_lt(v_x_4_, v_intZero_11_);
if (v_isNeg_24_ == 0)
{
lean_object* v_a_25_; uint8_t v_isZero_26_; 
lean_dec(v_h__5_9_);
v_a_25_ = lean_nat_abs(v_x_4_);
v_isZero_26_ = lean_nat_dec_eq(v_a_25_, v_natZero_10_);
if (v_isZero_26_ == 1)
{
lean_object* v___x_27_; 
lean_dec(v_a_25_);
lean_dec(v_h__4_8_);
v___x_27_ = lean_apply_1(v_h__3_7_, v_a_23_);
return v___x_27_;
}
else
{
lean_object* v_n_28_; lean_object* v___x_29_; 
lean_dec(v_h__3_7_);
v_n_28_ = lean_nat_sub(v_a_25_, v_one_22_);
lean_dec(v_a_25_);
v___x_29_ = lean_apply_2(v_h__4_8_, v_a_23_, v_n_28_);
return v___x_29_;
}
}
else
{
lean_object* v_abs_30_; lean_object* v_a_31_; lean_object* v___x_32_; 
lean_dec(v_h__4_8_);
lean_dec(v_h__3_7_);
v_abs_30_ = lean_nat_abs(v_x_4_);
v_a_31_ = lean_nat_sub(v_abs_30_, v_one_22_);
lean_dec(v_abs_30_);
v___x_32_ = lean_apply_2(v_h__5_9_, v_a_23_, v_a_31_);
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___boxed(lean_object* v_x_33_, lean_object* v_x_34_, lean_object* v_h__1_35_, lean_object* v_h__2_36_, lean_object* v_h__3_37_, lean_object* v_h__4_38_, lean_object* v_h__5_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg(v_x_33_, v_x_34_, v_h__1_35_, v_h__2_36_, v_h__3_37_, v_h__4_38_, v_h__5_39_);
lean_dec(v_x_34_);
lean_dec(v_x_33_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter(lean_object* v_motive_41_, lean_object* v_x_42_, lean_object* v_x_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_, lean_object* v_h__3_46_, lean_object* v_h__4_47_, lean_object* v_h__5_48_){
_start:
{
lean_object* v_natZero_49_; lean_object* v_intZero_50_; uint8_t v_isNeg_51_; 
v_natZero_49_ = lean_unsigned_to_nat(0u);
v_intZero_50_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0);
v_isNeg_51_ = lean_int_dec_lt(v_x_42_, v_intZero_50_);
if (v_isNeg_51_ == 0)
{
lean_object* v_a_52_; uint8_t v_isNeg_53_; 
lean_dec(v_h__5_48_);
lean_dec(v_h__4_47_);
lean_dec(v_h__3_46_);
v_a_52_ = lean_nat_abs(v_x_42_);
v_isNeg_53_ = lean_int_dec_lt(v_x_43_, v_intZero_50_);
if (v_isNeg_53_ == 0)
{
lean_object* v_a_54_; lean_object* v___x_55_; 
lean_dec(v_h__2_45_);
v_a_54_ = lean_nat_abs(v_x_43_);
v___x_55_ = lean_apply_2(v_h__1_44_, v_a_52_, v_a_54_);
return v___x_55_;
}
else
{
lean_object* v_abs_56_; lean_object* v_one_57_; lean_object* v_a_58_; lean_object* v___x_59_; 
lean_dec(v_h__1_44_);
v_abs_56_ = lean_nat_abs(v_x_43_);
v_one_57_ = lean_unsigned_to_nat(1u);
v_a_58_ = lean_nat_sub(v_abs_56_, v_one_57_);
lean_dec(v_abs_56_);
v___x_59_ = lean_apply_2(v_h__2_45_, v_a_52_, v_a_58_);
return v___x_59_;
}
}
else
{
lean_object* v_abs_60_; lean_object* v_one_61_; lean_object* v_a_62_; uint8_t v_isNeg_63_; 
lean_dec(v_h__2_45_);
lean_dec(v_h__1_44_);
v_abs_60_ = lean_nat_abs(v_x_42_);
v_one_61_ = lean_unsigned_to_nat(1u);
v_a_62_ = lean_nat_sub(v_abs_60_, v_one_61_);
lean_dec(v_abs_60_);
v_isNeg_63_ = lean_int_dec_lt(v_x_43_, v_intZero_50_);
if (v_isNeg_63_ == 0)
{
lean_object* v_a_64_; uint8_t v_isZero_65_; 
lean_dec(v_h__5_48_);
v_a_64_ = lean_nat_abs(v_x_43_);
v_isZero_65_ = lean_nat_dec_eq(v_a_64_, v_natZero_49_);
if (v_isZero_65_ == 1)
{
lean_object* v___x_66_; 
lean_dec(v_a_64_);
lean_dec(v_h__4_47_);
v___x_66_ = lean_apply_1(v_h__3_46_, v_a_62_);
return v___x_66_;
}
else
{
lean_object* v_n_67_; lean_object* v___x_68_; 
lean_dec(v_h__3_46_);
v_n_67_ = lean_nat_sub(v_a_64_, v_one_61_);
lean_dec(v_a_64_);
v___x_68_ = lean_apply_2(v_h__4_47_, v_a_62_, v_n_67_);
return v___x_68_;
}
}
else
{
lean_object* v_abs_69_; lean_object* v_a_70_; lean_object* v___x_71_; 
lean_dec(v_h__4_47_);
lean_dec(v_h__3_46_);
v_abs_69_ = lean_nat_abs(v_x_43_);
v_a_70_ = lean_nat_sub(v_abs_69_, v_one_61_);
lean_dec(v_abs_69_);
v___x_71_ = lean_apply_2(v_h__5_48_, v_a_62_, v_a_70_);
return v___x_71_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___boxed(lean_object* v_motive_72_, lean_object* v_x_73_, lean_object* v_x_74_, lean_object* v_h__1_75_, lean_object* v_h__2_76_, lean_object* v_h__3_77_, lean_object* v_h__4_78_, lean_object* v_h__5_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter(v_motive_72_, v_x_73_, v_x_74_, v_h__1_75_, v_h__2_76_, v_h__3_77_, v_h__4_78_, v_h__5_79_);
lean_dec(v_x_74_);
lean_dec(v_x_73_);
return v_res_80_;
}
}
lean_object* runtime_initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Int_DivMod_Bootstrap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Int_DivMod_Bootstrap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_DivMod_Bootstrap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Int_DivMod_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Int_DivMod_Bootstrap(builtin);
}
#ifdef __cplusplus
}
#endif
