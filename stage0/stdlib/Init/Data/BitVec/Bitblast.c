// Lean compiler output
// Module: Init.Data.BitVec.Bitblast
// Imports: import all Init.Data.Nat.Bitwise.Basic import all Init.Data.Int.DivMod import all Init.Data.BitVec.Basic public import Init.Data.BitVec.Folds public import Init.BinderPredicates public import Init.Data.BitVec.Lemmas public import Init.Data.Nat.Lemmas import Init.ByCases import Init.Data.BitVec.Bootstrap import Init.Data.BitVec.Decidable import Init.Data.Int.Pow import Init.Data.Nat.Div.Lemmas import Init.Data.Nat.Mod import Init.Data.Nat.Simproc import Init.TacticsExtra
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
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_BitVec_extractLsb_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_setWidth(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_BitVec_append___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_BitVec_twoPow(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* l_BitVec_sshiftRight(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
lean_object* l_BitVec_shiftConcat(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_BitVec_sub(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_bool_to_nat(uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_BitVec_shiftLeft(lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_xor(uint8_t, uint8_t);
lean_object* l_BitVec_iunfoldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Bool_atLeastTwo(uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Bool_atLeastTwo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_carry___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_carry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_carry(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_carry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_adcb(uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_adcb___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_adc___lam__0(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_adc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_adc(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BitVec_adc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_mulRec(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_mulRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_shiftLeftRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_shiftLeftRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_DivModState_init(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_divSubtractShift(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_divSubtractShift___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_divRec(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_divRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sshiftRightRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_sshiftRightRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_uppcRec___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_uppcRec___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_uppcRec(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_uppcRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_aandRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_aandRec___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_aandRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_aandRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_resRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_resRec___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_BitVec_resRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_resRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_BitVec_extractAndExtend___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_BitVec_extractAndExtend___closed__0;
LEAN_EXPORT lean_object* l_BitVec_extractAndExtend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_extractAndExtend___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cpopLayer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cpopTree(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cpopTree___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cpopRec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_cpopRec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Bool_atLeastTwo(uint8_t v_a_1_, uint8_t v_b_2_, uint8_t v_c_3_){
_start:
{
if (v_a_1_ == 0)
{
goto v___jp_4_;
}
else
{
if (v_b_2_ == 0)
{
goto v___jp_4_;
}
else
{
return v_b_2_;
}
}
v___jp_4_:
{
if (v_a_1_ == 0)
{
if (v_b_2_ == 0)
{
return v_b_2_;
}
else
{
return v_c_3_;
}
}
else
{
if (v_c_3_ == 0)
{
if (v_b_2_ == 0)
{
return v_b_2_;
}
else
{
return v_c_3_;
}
}
else
{
return v_c_3_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Bool_atLeastTwo___boxed(lean_object* v_a_5_, lean_object* v_b_6_, lean_object* v_c_7_){
_start:
{
uint8_t v_a_boxed_8_; uint8_t v_b_boxed_9_; uint8_t v_c_boxed_10_; uint8_t v_res_11_; lean_object* v_r_12_; 
v_a_boxed_8_ = lean_unbox(v_a_5_);
v_b_boxed_9_ = lean_unbox(v_b_6_);
v_c_boxed_10_ = lean_unbox(v_c_7_);
v_res_11_ = l_Bool_atLeastTwo(v_a_boxed_8_, v_b_boxed_9_, v_c_boxed_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t l_BitVec_carry___redArg(lean_object* v_i_13_, lean_object* v_x_14_, lean_object* v_y_15_, uint8_t v_c_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_17_ = lean_unsigned_to_nat(2u);
v___x_18_ = lean_nat_pow(v___x_17_, v_i_13_);
v___x_19_ = lean_nat_mod(v_x_14_, v___x_18_);
v___x_20_ = lean_nat_mod(v_y_15_, v___x_18_);
v___x_21_ = lean_nat_add(v___x_19_, v___x_20_);
lean_dec(v___x_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_bool_to_nat(v_c_16_);
v___x_23_ = lean_nat_add(v___x_21_, v___x_22_);
lean_dec(v___x_21_);
v___x_24_ = lean_nat_dec_le(v___x_18_, v___x_23_);
lean_dec(v___x_23_);
lean_dec(v___x_18_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_BitVec_carry___redArg___boxed(lean_object* v_i_25_, lean_object* v_x_26_, lean_object* v_y_27_, lean_object* v_c_28_){
_start:
{
uint8_t v_c_boxed_29_; uint8_t v_res_30_; lean_object* v_r_31_; 
v_c_boxed_29_ = lean_unbox(v_c_28_);
v_res_30_ = l_BitVec_carry___redArg(v_i_25_, v_x_26_, v_y_27_, v_c_boxed_29_);
lean_dec(v_y_27_);
lean_dec(v_x_26_);
lean_dec(v_i_25_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT uint8_t l_BitVec_carry(lean_object* v_w_32_, lean_object* v_i_33_, lean_object* v_x_34_, lean_object* v_y_35_, uint8_t v_c_36_){
_start:
{
uint8_t v___x_37_; 
v___x_37_ = l_BitVec_carry___redArg(v_i_33_, v_x_34_, v_y_35_, v_c_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_BitVec_carry___boxed(lean_object* v_w_38_, lean_object* v_i_39_, lean_object* v_x_40_, lean_object* v_y_41_, lean_object* v_c_42_){
_start:
{
uint8_t v_c_boxed_43_; uint8_t v_res_44_; lean_object* v_r_45_; 
v_c_boxed_43_ = lean_unbox(v_c_42_);
v_res_44_ = l_BitVec_carry(v_w_38_, v_i_39_, v_x_40_, v_y_41_, v_c_boxed_43_);
lean_dec(v_y_41_);
lean_dec(v_x_40_);
lean_dec(v_i_39_);
lean_dec(v_w_38_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
LEAN_EXPORT lean_object* l_BitVec_adcb(uint8_t v_x_46_, uint8_t v_y_47_, uint8_t v_c_48_){
_start:
{
uint8_t v___y_50_; 
if (v_x_46_ == 0)
{
goto v___jp_56_;
}
else
{
if (v_y_47_ == 0)
{
goto v___jp_56_;
}
else
{
v___y_50_ = v_y_47_;
goto v___jp_49_;
}
}
v___jp_49_:
{
uint8_t v___x_51_; uint8_t v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_51_ = lean_bool_xor(v_y_47_, v_c_48_);
v___x_52_ = lean_bool_xor(v_x_46_, v___x_51_);
v___x_53_ = lean_box(v___y_50_);
v___x_54_ = lean_box(v___x_52_);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_53_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
return v___x_55_;
}
v___jp_56_:
{
if (v_x_46_ == 0)
{
if (v_y_47_ == 0)
{
v___y_50_ = v_y_47_;
goto v___jp_49_;
}
else
{
v___y_50_ = v_c_48_;
goto v___jp_49_;
}
}
else
{
if (v_c_48_ == 0)
{
if (v_y_47_ == 0)
{
v___y_50_ = v_y_47_;
goto v___jp_49_;
}
else
{
v___y_50_ = v_c_48_;
goto v___jp_49_;
}
}
else
{
v___y_50_ = v_c_48_;
goto v___jp_49_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_adcb___boxed(lean_object* v_x_57_, lean_object* v_y_58_, lean_object* v_c_59_){
_start:
{
uint8_t v_x_boxed_60_; uint8_t v_y_boxed_61_; uint8_t v_c_boxed_62_; lean_object* v_res_63_; 
v_x_boxed_60_ = lean_unbox(v_x_57_);
v_y_boxed_61_ = lean_unbox(v_y_58_);
v_c_boxed_62_ = lean_unbox(v_c_59_);
v_res_63_ = l_BitVec_adcb(v_x_boxed_60_, v_y_boxed_61_, v_c_boxed_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_BitVec_adc___lam__0(lean_object* v_x_64_, lean_object* v_y_65_, lean_object* v_i_66_, uint8_t v_c_67_){
_start:
{
uint8_t v___x_68_; uint8_t v___x_69_; lean_object* v___x_70_; 
v___x_68_ = l_Nat_testBit(v_x_64_, v_i_66_);
v___x_69_ = l_Nat_testBit(v_y_65_, v_i_66_);
v___x_70_ = l_BitVec_adcb(v___x_68_, v___x_69_, v_c_67_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_BitVec_adc___lam__0___boxed(lean_object* v_x_71_, lean_object* v_y_72_, lean_object* v_i_73_, lean_object* v_c_74_){
_start:
{
uint8_t v_c_boxed_75_; lean_object* v_res_76_; 
v_c_boxed_75_ = lean_unbox(v_c_74_);
v_res_76_ = l_BitVec_adc___lam__0(v_x_71_, v_y_72_, v_i_73_, v_c_boxed_75_);
lean_dec(v_i_73_);
lean_dec(v_y_72_);
lean_dec(v_x_71_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_BitVec_adc(lean_object* v_w_77_, lean_object* v_x_78_, lean_object* v_y_79_, uint8_t v_s_80_){
_start:
{
lean_object* v___f_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___f_81_ = lean_alloc_closure((void*)(l_BitVec_adc___lam__0___boxed), 4, 2);
lean_closure_set(v___f_81_, 0, v_x_78_);
lean_closure_set(v___f_81_, 1, v_y_79_);
v___x_82_ = lean_box(v_s_80_);
v___x_83_ = l_BitVec_iunfoldr___redArg(v_w_77_, v___f_81_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_BitVec_adc___boxed(lean_object* v_w_84_, lean_object* v_x_85_, lean_object* v_y_86_, lean_object* v_s_87_){
_start:
{
uint8_t v_s_boxed_88_; lean_object* v_res_89_; 
v_s_boxed_88_ = lean_unbox(v_s_87_);
v_res_89_ = l_BitVec_adc(v_w_84_, v_x_85_, v_y_86_, v_s_boxed_88_);
lean_dec(v_w_84_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_BitVec_mulRec(lean_object* v_w_90_, lean_object* v_x_91_, lean_object* v_y_92_, lean_object* v_s_93_){
_start:
{
lean_object* v___y_95_; uint8_t v___x_102_; 
v___x_102_ = l_Nat_testBit(v_y_92_, v_s_93_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = l_BitVec_ofNat(v_w_90_, v___x_103_);
v___y_95_ = v___x_104_;
goto v___jp_94_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = l_BitVec_shiftLeft(v_w_90_, v_x_91_, v_s_93_);
v___y_95_ = v___x_105_;
goto v___jp_94_;
}
v___jp_94_:
{
lean_object* v_zero_96_; uint8_t v_isZero_97_; 
v_zero_96_ = lean_unsigned_to_nat(0u);
v_isZero_97_ = lean_nat_dec_eq(v_s_93_, v_zero_96_);
if (v_isZero_97_ == 1)
{
return v___y_95_;
}
else
{
lean_object* v_one_98_; lean_object* v_n_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v_one_98_ = lean_unsigned_to_nat(1u);
v_n_99_ = lean_nat_sub(v_s_93_, v_one_98_);
v___x_100_ = l_BitVec_mulRec(v_w_90_, v_x_91_, v_y_92_, v_n_99_);
lean_dec(v_n_99_);
v___x_101_ = l_BitVec_add(v_w_90_, v___x_100_, v___y_95_);
lean_dec(v___y_95_);
lean_dec(v___x_100_);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_mulRec___boxed(lean_object* v_w_106_, lean_object* v_x_107_, lean_object* v_y_108_, lean_object* v_s_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_BitVec_mulRec(v_w_106_, v_x_107_, v_y_108_, v_s_109_);
lean_dec(v_s_109_);
lean_dec(v_y_108_);
lean_dec(v_x_107_);
lean_dec(v_w_106_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___redArg(lean_object* v_s_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_){
_start:
{
lean_object* v_zero_114_; uint8_t v_isZero_115_; 
v_zero_114_ = lean_unsigned_to_nat(0u);
v_isZero_115_ = lean_nat_dec_eq(v_s_111_, v_zero_114_);
if (v_isZero_115_ == 1)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_dec(v_h__2_113_);
v___x_116_ = lean_box(0);
v___x_117_ = lean_apply_1(v_h__1_112_, v___x_116_);
return v___x_117_;
}
else
{
lean_object* v_one_118_; lean_object* v_n_119_; lean_object* v___x_120_; 
lean_dec(v_h__1_112_);
v_one_118_ = lean_unsigned_to_nat(1u);
v_n_119_ = lean_nat_sub(v_s_111_, v_one_118_);
v___x_120_ = lean_apply_1(v_h__2_113_, v_n_119_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___redArg___boxed(lean_object* v_s_121_, lean_object* v_h__1_122_, lean_object* v_h__2_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___redArg(v_s_121_, v_h__1_122_, v_h__2_123_);
lean_dec(v_s_121_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter(lean_object* v_motive_125_, lean_object* v_s_126_, lean_object* v_h__1_127_, lean_object* v_h__2_128_){
_start:
{
lean_object* v_zero_129_; uint8_t v_isZero_130_; 
v_zero_129_ = lean_unsigned_to_nat(0u);
v_isZero_130_ = lean_nat_dec_eq(v_s_126_, v_zero_129_);
if (v_isZero_130_ == 1)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
lean_dec(v_h__2_128_);
v___x_131_ = lean_box(0);
v___x_132_ = lean_apply_1(v_h__1_127_, v___x_131_);
return v___x_132_;
}
else
{
lean_object* v_one_133_; lean_object* v_n_134_; lean_object* v___x_135_; 
lean_dec(v_h__1_127_);
v_one_133_ = lean_unsigned_to_nat(1u);
v_n_134_ = lean_nat_sub(v_s_126_, v_one_133_);
v___x_135_ = lean_apply_1(v_h__2_128_, v_n_134_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___boxed(lean_object* v_motive_136_, lean_object* v_s_137_, lean_object* v_h__1_138_, lean_object* v_h__2_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter(v_motive_136_, v_s_137_, v_h__1_138_, v_h__2_139_);
lean_dec(v_s_137_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftRec(lean_object* v_w_u2081_141_, lean_object* v_w_u2082_142_, lean_object* v_x_143_, lean_object* v_y_144_, lean_object* v_n_145_){
_start:
{
lean_object* v___x_146_; lean_object* v_shiftAmt_147_; lean_object* v_zero_148_; uint8_t v_isZero_149_; 
v___x_146_ = l_BitVec_twoPow(v_w_u2082_142_, v_n_145_);
v_shiftAmt_147_ = lean_nat_land(v_y_144_, v___x_146_);
lean_dec(v___x_146_);
v_zero_148_ = lean_unsigned_to_nat(0u);
v_isZero_149_ = lean_nat_dec_eq(v_n_145_, v_zero_148_);
if (v_isZero_149_ == 1)
{
lean_object* v___x_150_; 
v___x_150_ = l_BitVec_shiftLeft(v_w_u2081_141_, v_x_143_, v_shiftAmt_147_);
lean_dec(v_shiftAmt_147_);
return v___x_150_;
}
else
{
lean_object* v_one_151_; lean_object* v_n_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_one_151_ = lean_unsigned_to_nat(1u);
v_n_152_ = lean_nat_sub(v_n_145_, v_one_151_);
v___x_153_ = l_BitVec_shiftLeftRec(v_w_u2081_141_, v_w_u2082_142_, v_x_143_, v_y_144_, v_n_152_);
lean_dec(v_n_152_);
v___x_154_ = l_BitVec_shiftLeft(v_w_u2081_141_, v___x_153_, v_shiftAmt_147_);
lean_dec(v_shiftAmt_147_);
lean_dec(v___x_153_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftRec___boxed(lean_object* v_w_u2081_155_, lean_object* v_w_u2082_156_, lean_object* v_x_157_, lean_object* v_y_158_, lean_object* v_n_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_BitVec_shiftLeftRec(v_w_u2081_155_, v_w_u2082_156_, v_x_157_, v_y_158_, v_n_159_);
lean_dec(v_n_159_);
lean_dec(v_y_158_);
lean_dec(v_x_157_);
lean_dec(v_w_u2082_156_);
lean_dec(v_w_u2081_155_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_BitVec_DivModState_init(lean_object* v_w_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = l_BitVec_ofNat(v_w_161_, v___x_162_);
lean_inc(v___x_163_);
v___x_164_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_164_, 0, v_w_161_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
lean_ctor_set(v___x_164_, 2, v___x_163_);
lean_ctor_set(v___x_164_, 3, v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_BitVec_divSubtractShift(lean_object* v_w_165_, lean_object* v_args_166_, lean_object* v_qr_167_){
_start:
{
lean_object* v_n_168_; lean_object* v_d_169_; lean_object* v_wn_170_; lean_object* v_wr_171_; lean_object* v_q_172_; lean_object* v_r_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_194_; 
v_n_168_ = lean_ctor_get(v_args_166_, 0);
v_d_169_ = lean_ctor_get(v_args_166_, 1);
v_wn_170_ = lean_ctor_get(v_qr_167_, 0);
v_wr_171_ = lean_ctor_get(v_qr_167_, 1);
v_q_172_ = lean_ctor_get(v_qr_167_, 2);
v_r_173_ = lean_ctor_get(v_qr_167_, 3);
v_isSharedCheck_194_ = !lean_is_exclusive(v_qr_167_);
if (v_isSharedCheck_194_ == 0)
{
v___x_175_ = v_qr_167_;
v_isShared_176_ = v_isSharedCheck_194_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_r_173_);
lean_inc(v_q_172_);
lean_inc(v_wr_171_);
lean_inc(v_wn_170_);
lean_dec(v_qr_167_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_194_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v_wn_178_; lean_object* v_wr_179_; uint8_t v___x_180_; lean_object* v_r_x27_181_; uint8_t v___x_182_; 
v___x_177_ = lean_unsigned_to_nat(1u);
v_wn_178_ = lean_nat_sub(v_wn_170_, v___x_177_);
lean_dec(v_wn_170_);
v_wr_179_ = lean_nat_add(v_wr_171_, v___x_177_);
lean_dec(v_wr_171_);
v___x_180_ = l_Nat_testBit(v_n_168_, v_wn_178_);
v_r_x27_181_ = l_BitVec_shiftConcat(v_w_165_, v_r_173_, v___x_180_);
lean_dec(v_r_173_);
v___x_182_ = lean_nat_dec_lt(v_r_x27_181_, v_d_169_);
if (v___x_182_ == 0)
{
uint8_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_183_ = 1;
v___x_184_ = l_BitVec_shiftConcat(v_w_165_, v_q_172_, v___x_183_);
lean_dec(v_q_172_);
v___x_185_ = l_BitVec_sub(v_w_165_, v_r_x27_181_, v_d_169_);
lean_dec(v_r_x27_181_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 3, v___x_185_);
lean_ctor_set(v___x_175_, 2, v___x_184_);
lean_ctor_set(v___x_175_, 1, v_wr_179_);
lean_ctor_set(v___x_175_, 0, v_wn_178_);
v___x_187_ = v___x_175_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_wn_178_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_wr_179_);
lean_ctor_set(v_reuseFailAlloc_188_, 2, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_188_, 3, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
else
{
uint8_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_189_ = 0;
v___x_190_ = l_BitVec_shiftConcat(v_w_165_, v_q_172_, v___x_189_);
lean_dec(v_q_172_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 3, v_r_x27_181_);
lean_ctor_set(v___x_175_, 2, v___x_190_);
lean_ctor_set(v___x_175_, 1, v_wr_179_);
lean_ctor_set(v___x_175_, 0, v_wn_178_);
v___x_192_ = v___x_175_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_wn_178_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_wr_179_);
lean_ctor_set(v_reuseFailAlloc_193_, 2, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_193_, 3, v_r_x27_181_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_divSubtractShift___boxed(lean_object* v_w_195_, lean_object* v_args_196_, lean_object* v_qr_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_BitVec_divSubtractShift(v_w_195_, v_args_196_, v_qr_197_);
lean_dec_ref(v_args_196_);
lean_dec(v_w_195_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter___redArg(lean_object* v_args_199_, lean_object* v_h__1_200_){
_start:
{
lean_object* v_n_201_; lean_object* v_d_202_; lean_object* v___x_203_; 
v_n_201_ = lean_ctor_get(v_args_199_, 0);
lean_inc(v_n_201_);
v_d_202_ = lean_ctor_get(v_args_199_, 1);
lean_inc(v_d_202_);
lean_dec_ref(v_args_199_);
v___x_203_ = lean_apply_2(v_h__1_200_, v_n_201_, v_d_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter(lean_object* v_w_204_, lean_object* v_motive_205_, lean_object* v_args_206_, lean_object* v_h__1_207_){
_start:
{
lean_object* v_n_208_; lean_object* v_d_209_; lean_object* v___x_210_; 
v_n_208_ = lean_ctor_get(v_args_206_, 0);
lean_inc(v_n_208_);
v_d_209_ = lean_ctor_get(v_args_206_, 1);
lean_inc(v_d_209_);
lean_dec_ref(v_args_206_);
v___x_210_ = lean_apply_2(v_h__1_207_, v_n_208_, v_d_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter___boxed(lean_object* v_w_211_, lean_object* v_motive_212_, lean_object* v_args_213_, lean_object* v_h__1_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter(v_w_211_, v_motive_212_, v_args_213_, v_h__1_214_);
lean_dec(v_w_211_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_BitVec_divRec(lean_object* v_w_216_, lean_object* v_m_217_, lean_object* v_args_218_, lean_object* v_qr_219_){
_start:
{
lean_object* v_zero_220_; uint8_t v_isZero_221_; 
v_zero_220_ = lean_unsigned_to_nat(0u);
v_isZero_221_ = lean_nat_dec_eq(v_m_217_, v_zero_220_);
if (v_isZero_221_ == 1)
{
lean_dec(v_m_217_);
return v_qr_219_;
}
else
{
lean_object* v_one_222_; lean_object* v_n_223_; lean_object* v___x_224_; 
v_one_222_ = lean_unsigned_to_nat(1u);
v_n_223_ = lean_nat_sub(v_m_217_, v_one_222_);
lean_dec(v_m_217_);
v___x_224_ = l_BitVec_divSubtractShift(v_w_216_, v_args_218_, v_qr_219_);
v_m_217_ = v_n_223_;
v_qr_219_ = v___x_224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_divRec___boxed(lean_object* v_w_226_, lean_object* v_m_227_, lean_object* v_args_228_, lean_object* v_qr_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_BitVec_divRec(v_w_226_, v_m_227_, v_args_228_, v_qr_229_);
lean_dec_ref(v_args_228_);
lean_dec(v_w_226_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRightRec(lean_object* v_w_u2081_231_, lean_object* v_w_u2082_232_, lean_object* v_x_233_, lean_object* v_y_234_, lean_object* v_n_235_){
_start:
{
lean_object* v___x_236_; lean_object* v_shiftAmt_237_; lean_object* v_zero_238_; uint8_t v_isZero_239_; 
v___x_236_ = l_BitVec_twoPow(v_w_u2082_232_, v_n_235_);
v_shiftAmt_237_ = lean_nat_land(v_y_234_, v___x_236_);
lean_dec(v___x_236_);
v_zero_238_ = lean_unsigned_to_nat(0u);
v_isZero_239_ = lean_nat_dec_eq(v_n_235_, v_zero_238_);
if (v_isZero_239_ == 1)
{
lean_object* v___x_240_; 
v___x_240_ = l_BitVec_sshiftRight(v_w_u2081_231_, v_x_233_, v_shiftAmt_237_);
lean_dec(v_shiftAmt_237_);
return v___x_240_;
}
else
{
lean_object* v_one_241_; lean_object* v_n_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_one_241_ = lean_unsigned_to_nat(1u);
v_n_242_ = lean_nat_sub(v_n_235_, v_one_241_);
v___x_243_ = l_BitVec_sshiftRightRec(v_w_u2081_231_, v_w_u2082_232_, v_x_233_, v_y_234_, v_n_242_);
lean_dec(v_n_242_);
v___x_244_ = l_BitVec_sshiftRight(v_w_u2081_231_, v___x_243_, v_shiftAmt_237_);
lean_dec(v_shiftAmt_237_);
return v___x_244_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRightRec___boxed(lean_object* v_w_u2081_245_, lean_object* v_w_u2082_246_, lean_object* v_x_247_, lean_object* v_y_248_, lean_object* v_n_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_BitVec_sshiftRightRec(v_w_u2081_245_, v_w_u2082_246_, v_x_247_, v_y_248_, v_n_249_);
lean_dec(v_n_249_);
lean_dec(v_y_248_);
lean_dec(v_w_u2082_246_);
lean_dec(v_w_u2081_245_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___redArg(lean_object* v_w_u2082_251_, lean_object* v_x_252_, lean_object* v_y_253_, lean_object* v_n_254_){
_start:
{
lean_object* v___x_255_; lean_object* v_shiftAmt_256_; lean_object* v_zero_257_; uint8_t v_isZero_258_; 
v___x_255_ = l_BitVec_twoPow(v_w_u2082_251_, v_n_254_);
v_shiftAmt_256_ = lean_nat_land(v_y_253_, v___x_255_);
lean_dec(v___x_255_);
v_zero_257_ = lean_unsigned_to_nat(0u);
v_isZero_258_ = lean_nat_dec_eq(v_n_254_, v_zero_257_);
if (v_isZero_258_ == 1)
{
lean_object* v___x_259_; 
v___x_259_ = lean_nat_shiftr(v_x_252_, v_shiftAmt_256_);
lean_dec(v_shiftAmt_256_);
return v___x_259_;
}
else
{
lean_object* v_one_260_; lean_object* v_n_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_one_260_ = lean_unsigned_to_nat(1u);
v_n_261_ = lean_nat_sub(v_n_254_, v_one_260_);
v___x_262_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_251_, v_x_252_, v_y_253_, v_n_261_);
lean_dec(v_n_261_);
v___x_263_ = lean_nat_shiftr(v___x_262_, v_shiftAmt_256_);
lean_dec(v_shiftAmt_256_);
lean_dec(v___x_262_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___redArg___boxed(lean_object* v_w_u2082_264_, lean_object* v_x_265_, lean_object* v_y_266_, lean_object* v_n_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_264_, v_x_265_, v_y_266_, v_n_267_);
lean_dec(v_n_267_);
lean_dec(v_y_266_);
lean_dec(v_x_265_);
lean_dec(v_w_u2082_264_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec(lean_object* v_w_u2081_269_, lean_object* v_w_u2082_270_, lean_object* v_x_271_, lean_object* v_y_272_, lean_object* v_n_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_270_, v_x_271_, v_y_272_, v_n_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___boxed(lean_object* v_w_u2081_275_, lean_object* v_w_u2082_276_, lean_object* v_x_277_, lean_object* v_y_278_, lean_object* v_n_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_BitVec_ushiftRightRec(v_w_u2081_275_, v_w_u2082_276_, v_x_277_, v_y_278_, v_n_279_);
lean_dec(v_n_279_);
lean_dec(v_y_278_);
lean_dec(v_x_277_);
lean_dec(v_w_u2082_276_);
lean_dec(v_w_u2081_275_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg(uint8_t v_x_281_, uint8_t v_x_282_, lean_object* v_h__1_283_, lean_object* v_h__2_284_, lean_object* v_h__3_285_, lean_object* v_h__4_286_){
_start:
{
if (v_x_281_ == 0)
{
lean_dec(v_h__4_286_);
lean_dec(v_h__3_285_);
if (v_x_282_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec(v_h__2_284_);
v___x_287_ = lean_box(0);
v___x_288_ = lean_apply_1(v_h__1_283_, v___x_287_);
return v___x_288_;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v_h__1_283_);
v___x_289_ = lean_box(0);
v___x_290_ = lean_apply_1(v_h__2_284_, v___x_289_);
return v___x_290_;
}
}
else
{
lean_dec(v_h__2_284_);
lean_dec(v_h__1_283_);
if (v_x_282_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec(v_h__4_286_);
v___x_291_ = lean_box(0);
v___x_292_ = lean_apply_1(v_h__3_285_, v___x_291_);
return v___x_292_;
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; 
lean_dec(v_h__3_285_);
v___x_293_ = lean_box(0);
v___x_294_ = lean_apply_1(v_h__4_286_, v___x_293_);
return v___x_294_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg___boxed(lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v_h__1_297_, lean_object* v_h__2_298_, lean_object* v_h__3_299_, lean_object* v_h__4_300_){
_start:
{
uint8_t v_x_46__boxed_301_; uint8_t v_x_47__boxed_302_; lean_object* v_res_303_; 
v_x_46__boxed_301_ = lean_unbox(v_x_295_);
v_x_47__boxed_302_ = lean_unbox(v_x_296_);
v_res_303_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg(v_x_46__boxed_301_, v_x_47__boxed_302_, v_h__1_297_, v_h__2_298_, v_h__3_299_, v_h__4_300_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter(lean_object* v_motive_304_, uint8_t v_x_305_, uint8_t v_x_306_, lean_object* v_h__1_307_, lean_object* v_h__2_308_, lean_object* v_h__3_309_, lean_object* v_h__4_310_){
_start:
{
if (v_x_305_ == 0)
{
lean_dec(v_h__4_310_);
lean_dec(v_h__3_309_);
if (v_x_306_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec(v_h__2_308_);
v___x_311_ = lean_box(0);
v___x_312_ = lean_apply_1(v_h__1_307_, v___x_311_);
return v___x_312_;
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec(v_h__1_307_);
v___x_313_ = lean_box(0);
v___x_314_ = lean_apply_1(v_h__2_308_, v___x_313_);
return v___x_314_;
}
}
else
{
lean_dec(v_h__2_308_);
lean_dec(v_h__1_307_);
if (v_x_306_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec(v_h__4_310_);
v___x_315_ = lean_box(0);
v___x_316_ = lean_apply_1(v_h__3_309_, v___x_315_);
return v___x_316_;
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v_h__3_309_);
v___x_317_ = lean_box(0);
v___x_318_ = lean_apply_1(v_h__4_310_, v___x_317_);
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___boxed(lean_object* v_motive_319_, lean_object* v_x_320_, lean_object* v_x_321_, lean_object* v_h__1_322_, lean_object* v_h__2_323_, lean_object* v_h__3_324_, lean_object* v_h__4_325_){
_start:
{
uint8_t v_x_68__boxed_326_; uint8_t v_x_69__boxed_327_; lean_object* v_res_328_; 
v_x_68__boxed_326_ = lean_unbox(v_x_320_);
v_x_69__boxed_327_ = lean_unbox(v_x_321_);
v_res_328_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter(v_motive_319_, v_x_68__boxed_326_, v_x_69__boxed_327_, v_h__1_322_, v_h__2_323_, v_h__3_324_, v_h__4_325_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg(uint8_t v_x_329_, uint8_t v_x_330_, lean_object* v_h__1_331_, lean_object* v_h__2_332_, lean_object* v_h__3_333_, lean_object* v_h__4_334_){
_start:
{
if (v_x_329_ == 0)
{
lean_dec(v_h__4_334_);
lean_dec(v_h__3_333_);
if (v_x_330_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec(v_h__2_332_);
v___x_335_ = lean_box(0);
v___x_336_ = lean_apply_1(v_h__1_331_, v___x_335_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v_h__1_331_);
v___x_337_ = lean_box(0);
v___x_338_ = lean_apply_1(v_h__2_332_, v___x_337_);
return v___x_338_;
}
}
else
{
lean_dec(v_h__2_332_);
lean_dec(v_h__1_331_);
if (v_x_330_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec(v_h__4_334_);
v___x_339_ = lean_box(0);
v___x_340_ = lean_apply_1(v_h__3_333_, v___x_339_);
return v___x_340_;
}
else
{
lean_object* v___x_341_; lean_object* v___x_342_; 
lean_dec(v_h__3_333_);
v___x_341_ = lean_box(0);
v___x_342_ = lean_apply_1(v_h__4_334_, v___x_341_);
return v___x_342_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg___boxed(lean_object* v_x_343_, lean_object* v_x_344_, lean_object* v_h__1_345_, lean_object* v_h__2_346_, lean_object* v_h__3_347_, lean_object* v_h__4_348_){
_start:
{
uint8_t v_x_46__boxed_349_; uint8_t v_x_47__boxed_350_; lean_object* v_res_351_; 
v_x_46__boxed_349_ = lean_unbox(v_x_343_);
v_x_47__boxed_350_ = lean_unbox(v_x_344_);
v_res_351_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg(v_x_46__boxed_349_, v_x_47__boxed_350_, v_h__1_345_, v_h__2_346_, v_h__3_347_, v_h__4_348_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter(lean_object* v_motive_352_, uint8_t v_x_353_, uint8_t v_x_354_, lean_object* v_h__1_355_, lean_object* v_h__2_356_, lean_object* v_h__3_357_, lean_object* v_h__4_358_){
_start:
{
if (v_x_353_ == 0)
{
lean_dec(v_h__4_358_);
lean_dec(v_h__3_357_);
if (v_x_354_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; 
lean_dec(v_h__2_356_);
v___x_359_ = lean_box(0);
v___x_360_ = lean_apply_1(v_h__1_355_, v___x_359_);
return v___x_360_;
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec(v_h__1_355_);
v___x_361_ = lean_box(0);
v___x_362_ = lean_apply_1(v_h__2_356_, v___x_361_);
return v___x_362_;
}
}
else
{
lean_dec(v_h__2_356_);
lean_dec(v_h__1_355_);
if (v_x_354_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec(v_h__4_358_);
v___x_363_ = lean_box(0);
v___x_364_ = lean_apply_1(v_h__3_357_, v___x_363_);
return v___x_364_;
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_dec(v_h__3_357_);
v___x_365_ = lean_box(0);
v___x_366_ = lean_apply_1(v_h__4_358_, v___x_365_);
return v___x_366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___boxed(lean_object* v_motive_367_, lean_object* v_x_368_, lean_object* v_x_369_, lean_object* v_h__1_370_, lean_object* v_h__2_371_, lean_object* v_h__3_372_, lean_object* v_h__4_373_){
_start:
{
uint8_t v_x_68__boxed_374_; uint8_t v_x_69__boxed_375_; lean_object* v_res_376_; 
v_x_68__boxed_374_ = lean_unbox(v_x_368_);
v_x_69__boxed_375_ = lean_unbox(v_x_369_);
v_res_376_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter(v_motive_367_, v_x_68__boxed_374_, v_x_69__boxed_375_, v_h__1_370_, v_h__2_371_, v_h__3_372_, v_h__4_373_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg(uint8_t v_x_377_, uint8_t v_x_378_, lean_object* v_h__1_379_, lean_object* v_h__2_380_, lean_object* v_h__3_381_, lean_object* v_h__4_382_){
_start:
{
if (v_x_377_ == 0)
{
lean_dec(v_h__4_382_);
lean_dec(v_h__3_381_);
if (v_x_378_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec(v_h__2_380_);
v___x_383_ = lean_box(0);
v___x_384_ = lean_apply_1(v_h__1_379_, v___x_383_);
return v___x_384_;
}
else
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v_h__1_379_);
v___x_385_ = lean_box(0);
v___x_386_ = lean_apply_1(v_h__2_380_, v___x_385_);
return v___x_386_;
}
}
else
{
lean_dec(v_h__2_380_);
lean_dec(v_h__1_379_);
if (v_x_378_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; 
lean_dec(v_h__4_382_);
v___x_387_ = lean_box(0);
v___x_388_ = lean_apply_1(v_h__3_381_, v___x_387_);
return v___x_388_;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_dec(v_h__3_381_);
v___x_389_ = lean_box(0);
v___x_390_ = lean_apply_1(v_h__4_382_, v___x_389_);
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg___boxed(lean_object* v_x_391_, lean_object* v_x_392_, lean_object* v_h__1_393_, lean_object* v_h__2_394_, lean_object* v_h__3_395_, lean_object* v_h__4_396_){
_start:
{
uint8_t v_x_46__boxed_397_; uint8_t v_x_47__boxed_398_; lean_object* v_res_399_; 
v_x_46__boxed_397_ = lean_unbox(v_x_391_);
v_x_47__boxed_398_ = lean_unbox(v_x_392_);
v_res_399_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg(v_x_46__boxed_397_, v_x_47__boxed_398_, v_h__1_393_, v_h__2_394_, v_h__3_395_, v_h__4_396_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter(lean_object* v_motive_400_, uint8_t v_x_401_, uint8_t v_x_402_, lean_object* v_h__1_403_, lean_object* v_h__2_404_, lean_object* v_h__3_405_, lean_object* v_h__4_406_){
_start:
{
if (v_x_401_ == 0)
{
lean_dec(v_h__4_406_);
lean_dec(v_h__3_405_);
if (v_x_402_ == 0)
{
lean_object* v___x_407_; lean_object* v___x_408_; 
lean_dec(v_h__2_404_);
v___x_407_ = lean_box(0);
v___x_408_ = lean_apply_1(v_h__1_403_, v___x_407_);
return v___x_408_;
}
else
{
lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec(v_h__1_403_);
v___x_409_ = lean_box(0);
v___x_410_ = lean_apply_1(v_h__2_404_, v___x_409_);
return v___x_410_;
}
}
else
{
lean_dec(v_h__2_404_);
lean_dec(v_h__1_403_);
if (v_x_402_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec(v_h__4_406_);
v___x_411_ = lean_box(0);
v___x_412_ = lean_apply_1(v_h__3_405_, v___x_411_);
return v___x_412_;
}
else
{
lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec(v_h__3_405_);
v___x_413_ = lean_box(0);
v___x_414_ = lean_apply_1(v_h__4_406_, v___x_413_);
return v___x_414_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___boxed(lean_object* v_motive_415_, lean_object* v_x_416_, lean_object* v_x_417_, lean_object* v_h__1_418_, lean_object* v_h__2_419_, lean_object* v_h__3_420_, lean_object* v_h__4_421_){
_start:
{
uint8_t v_x_68__boxed_422_; uint8_t v_x_69__boxed_423_; lean_object* v_res_424_; 
v_x_68__boxed_422_ = lean_unbox(v_x_416_);
v_x_69__boxed_423_ = lean_unbox(v_x_417_);
v_res_424_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter(v_motive_415_, v_x_68__boxed_422_, v_x_69__boxed_423_, v_h__1_418_, v_h__2_419_, v_h__3_420_, v_h__4_421_);
return v_res_424_;
}
}
LEAN_EXPORT uint8_t l_BitVec_uppcRec___redArg(lean_object* v_w_425_, lean_object* v_x_426_, lean_object* v_s_427_){
_start:
{
lean_object* v_zero_428_; uint8_t v_isZero_429_; 
v_zero_428_ = lean_unsigned_to_nat(0u);
v_isZero_429_ = lean_nat_dec_eq(v_s_427_, v_zero_428_);
if (v_isZero_429_ == 1)
{
uint8_t v___x_430_; 
lean_dec(v_s_427_);
v___x_430_ = lean_nat_dec_lt(v_zero_428_, v_w_425_);
if (v___x_430_ == 0)
{
return v___x_430_;
}
else
{
lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_431_ = lean_unsigned_to_nat(1u);
v___x_432_ = lean_nat_sub(v_w_425_, v___x_431_);
v___x_433_ = l_Nat_testBit(v_x_426_, v___x_432_);
lean_dec(v___x_432_);
return v___x_433_;
}
}
else
{
lean_object* v_one_434_; lean_object* v_n_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v_one_434_ = lean_unsigned_to_nat(1u);
v_n_435_ = lean_nat_sub(v_s_427_, v_one_434_);
lean_dec(v_s_427_);
v___x_436_ = lean_nat_sub(v_w_425_, v_one_434_);
v___x_437_ = lean_nat_sub(v___x_436_, v_n_435_);
lean_dec(v___x_436_);
v___x_438_ = l_Nat_testBit(v_x_426_, v___x_437_);
lean_dec(v___x_437_);
if (v___x_438_ == 0)
{
v_s_427_ = v_n_435_;
goto _start;
}
else
{
lean_dec(v_n_435_);
return v___x_438_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_uppcRec___redArg___boxed(lean_object* v_w_440_, lean_object* v_x_441_, lean_object* v_s_442_){
_start:
{
uint8_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_BitVec_uppcRec___redArg(v_w_440_, v_x_441_, v_s_442_);
lean_dec(v_x_441_);
lean_dec(v_w_440_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT uint8_t l_BitVec_uppcRec(lean_object* v_w_445_, lean_object* v_x_446_, lean_object* v_s_447_, lean_object* v_hs_448_){
_start:
{
uint8_t v___x_449_; 
v___x_449_ = l_BitVec_uppcRec___redArg(v_w_445_, v_x_446_, v_s_447_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_BitVec_uppcRec___boxed(lean_object* v_w_450_, lean_object* v_x_451_, lean_object* v_s_452_, lean_object* v_hs_453_){
_start:
{
uint8_t v_res_454_; lean_object* v_r_455_; 
v_res_454_ = l_BitVec_uppcRec(v_w_450_, v_x_451_, v_s_452_, v_hs_453_);
lean_dec(v_x_451_);
lean_dec(v_w_450_);
v_r_455_ = lean_box(v_res_454_);
return v_r_455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___redArg(lean_object* v_s_456_, lean_object* v_h__1_457_, lean_object* v_h__2_458_){
_start:
{
lean_object* v_zero_459_; uint8_t v_isZero_460_; 
v_zero_459_ = lean_unsigned_to_nat(0u);
v_isZero_460_ = lean_nat_dec_eq(v_s_456_, v_zero_459_);
if (v_isZero_460_ == 1)
{
lean_object* v___x_461_; 
lean_dec(v_h__2_458_);
v___x_461_ = lean_apply_1(v_h__1_457_, lean_box(0));
return v___x_461_;
}
else
{
lean_object* v_one_462_; lean_object* v_n_463_; lean_object* v___x_464_; 
lean_dec(v_h__1_457_);
v_one_462_ = lean_unsigned_to_nat(1u);
v_n_463_ = lean_nat_sub(v_s_456_, v_one_462_);
v___x_464_ = lean_apply_2(v_h__2_458_, v_n_463_, lean_box(0));
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___redArg___boxed(lean_object* v_s_465_, lean_object* v_h__1_466_, lean_object* v_h__2_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___redArg(v_s_465_, v_h__1_466_, v_h__2_467_);
lean_dec(v_s_465_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter(lean_object* v_w_469_, lean_object* v_motive_470_, lean_object* v_s_471_, lean_object* v_hs_472_, lean_object* v_h__1_473_, lean_object* v_h__2_474_){
_start:
{
lean_object* v_zero_475_; uint8_t v_isZero_476_; 
v_zero_475_ = lean_unsigned_to_nat(0u);
v_isZero_476_ = lean_nat_dec_eq(v_s_471_, v_zero_475_);
if (v_isZero_476_ == 1)
{
lean_object* v___x_477_; 
lean_dec(v_h__2_474_);
v___x_477_ = lean_apply_1(v_h__1_473_, lean_box(0));
return v___x_477_;
}
else
{
lean_object* v_one_478_; lean_object* v_n_479_; lean_object* v___x_480_; 
lean_dec(v_h__1_473_);
v_one_478_ = lean_unsigned_to_nat(1u);
v_n_479_ = lean_nat_sub(v_s_471_, v_one_478_);
v___x_480_ = lean_apply_2(v_h__2_474_, v_n_479_, lean_box(0));
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___boxed(lean_object* v_w_481_, lean_object* v_motive_482_, lean_object* v_s_483_, lean_object* v_hs_484_, lean_object* v_h__1_485_, lean_object* v_h__2_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter(v_w_481_, v_motive_482_, v_s_483_, v_hs_484_, v_h__1_485_, v_h__2_486_);
lean_dec(v_s_483_);
lean_dec(v_w_481_);
return v_res_487_;
}
}
LEAN_EXPORT uint8_t l_BitVec_aandRec___redArg(lean_object* v_w_488_, lean_object* v_x_489_, lean_object* v_y_490_, lean_object* v_s_491_){
_start:
{
uint8_t v___x_492_; 
v___x_492_ = l_Nat_testBit(v_y_490_, v_s_491_);
if (v___x_492_ == 0)
{
lean_dec(v_s_491_);
return v___x_492_;
}
else
{
uint8_t v___x_493_; 
v___x_493_ = l_BitVec_uppcRec___redArg(v_w_488_, v_x_489_, v_s_491_);
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_aandRec___redArg___boxed(lean_object* v_w_494_, lean_object* v_x_495_, lean_object* v_y_496_, lean_object* v_s_497_){
_start:
{
uint8_t v_res_498_; lean_object* v_r_499_; 
v_res_498_ = l_BitVec_aandRec___redArg(v_w_494_, v_x_495_, v_y_496_, v_s_497_);
lean_dec(v_y_496_);
lean_dec(v_x_495_);
lean_dec(v_w_494_);
v_r_499_ = lean_box(v_res_498_);
return v_r_499_;
}
}
LEAN_EXPORT uint8_t l_BitVec_aandRec(lean_object* v_w_500_, lean_object* v_x_501_, lean_object* v_y_502_, lean_object* v_s_503_, lean_object* v_hs_504_){
_start:
{
uint8_t v___x_505_; 
v___x_505_ = l_BitVec_aandRec___redArg(v_w_500_, v_x_501_, v_y_502_, v_s_503_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_BitVec_aandRec___boxed(lean_object* v_w_506_, lean_object* v_x_507_, lean_object* v_y_508_, lean_object* v_s_509_, lean_object* v_hs_510_){
_start:
{
uint8_t v_res_511_; lean_object* v_r_512_; 
v_res_511_ = l_BitVec_aandRec(v_w_506_, v_x_507_, v_y_508_, v_s_509_, v_hs_510_);
lean_dec(v_y_508_);
lean_dec(v_x_507_);
lean_dec(v_w_506_);
v_r_512_ = lean_box(v_res_511_);
return v_r_512_;
}
}
LEAN_EXPORT uint8_t l_BitVec_resRec___redArg(lean_object* v_w_513_, lean_object* v_x_514_, lean_object* v_y_515_, lean_object* v_s_516_){
_start:
{
lean_object* v_zero_517_; uint8_t v_isZero_518_; lean_object* v_one_519_; lean_object* v_n_520_; uint8_t v_isZero_521_; 
v_zero_517_ = lean_unsigned_to_nat(0u);
v_isZero_518_ = lean_nat_dec_eq(v_s_516_, v_zero_517_);
v_one_519_ = lean_unsigned_to_nat(1u);
v_n_520_ = lean_nat_sub(v_s_516_, v_one_519_);
v_isZero_521_ = lean_nat_dec_eq(v_n_520_, v_zero_517_);
if (v_isZero_521_ == 1)
{
uint8_t v___x_522_; 
lean_dec(v_n_520_);
lean_dec(v_s_516_);
v___x_522_ = l_BitVec_aandRec___redArg(v_w_513_, v_x_514_, v_y_515_, v_one_519_);
return v___x_522_;
}
else
{
uint8_t v___x_523_; 
v___x_523_ = l_BitVec_resRec___redArg(v_w_513_, v_x_514_, v_y_515_, v_n_520_);
if (v___x_523_ == 0)
{
uint8_t v___x_524_; 
v___x_524_ = l_BitVec_aandRec___redArg(v_w_513_, v_x_514_, v_y_515_, v_s_516_);
return v___x_524_;
}
else
{
lean_dec(v_s_516_);
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_resRec___redArg___boxed(lean_object* v_w_525_, lean_object* v_x_526_, lean_object* v_y_527_, lean_object* v_s_528_){
_start:
{
uint8_t v_res_529_; lean_object* v_r_530_; 
v_res_529_ = l_BitVec_resRec___redArg(v_w_525_, v_x_526_, v_y_527_, v_s_528_);
lean_dec(v_y_527_);
lean_dec(v_x_526_);
lean_dec(v_w_525_);
v_r_530_ = lean_box(v_res_529_);
return v_r_530_;
}
}
LEAN_EXPORT uint8_t l_BitVec_resRec(lean_object* v_w_531_, lean_object* v_x_532_, lean_object* v_y_533_, lean_object* v_s_534_, lean_object* v_hs_535_, lean_object* v_hslt_536_){
_start:
{
uint8_t v___x_537_; 
v___x_537_ = l_BitVec_resRec___redArg(v_w_531_, v_x_532_, v_y_533_, v_s_534_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_BitVec_resRec___boxed(lean_object* v_w_538_, lean_object* v_x_539_, lean_object* v_y_540_, lean_object* v_s_541_, lean_object* v_hs_542_, lean_object* v_hslt_543_){
_start:
{
uint8_t v_res_544_; lean_object* v_r_545_; 
v_res_544_ = l_BitVec_resRec(v_w_538_, v_x_539_, v_y_540_, v_s_541_, v_hs_542_, v_hslt_543_);
lean_dec(v_y_540_);
lean_dec(v_x_539_);
lean_dec(v_w_538_);
v_r_545_ = lean_box(v_res_544_);
return v_r_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg(lean_object* v_s_546_, lean_object* v_h__1_547_, lean_object* v_h__2_548_){
_start:
{
lean_object* v_zero_549_; uint8_t v_isZero_550_; 
v_zero_549_ = lean_unsigned_to_nat(0u);
v_isZero_550_ = lean_nat_dec_eq(v_s_546_, v_zero_549_);
if (v_isZero_550_ == 1)
{
lean_object* v___x_551_; 
lean_dec(v_h__2_548_);
v___x_551_ = lean_apply_3(v_h__1_547_, lean_box(0), lean_box(0), lean_box(0));
return v___x_551_;
}
else
{
lean_object* v_one_552_; lean_object* v_n_553_; lean_object* v___x_554_; 
lean_dec(v_h__1_547_);
v_one_552_ = lean_unsigned_to_nat(1u);
v_n_553_ = lean_nat_sub(v_s_546_, v_one_552_);
v___x_554_ = lean_apply_4(v_h__2_548_, v_n_553_, lean_box(0), lean_box(0), lean_box(0));
return v___x_554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg___boxed(lean_object* v_s_555_, lean_object* v_h__1_556_, lean_object* v_h__2_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg(v_s_555_, v_h__1_556_, v_h__2_557_);
lean_dec(v_s_555_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter(lean_object* v_w_559_, lean_object* v_motive_560_, lean_object* v_s_561_, lean_object* v_hs_562_, lean_object* v_hslt_563_, lean_object* v_h__1_564_, lean_object* v_h__2_565_){
_start:
{
lean_object* v_zero_566_; uint8_t v_isZero_567_; 
v_zero_566_ = lean_unsigned_to_nat(0u);
v_isZero_567_ = lean_nat_dec_eq(v_s_561_, v_zero_566_);
if (v_isZero_567_ == 1)
{
lean_object* v___x_568_; 
lean_dec(v_h__2_565_);
v___x_568_ = lean_apply_3(v_h__1_564_, lean_box(0), lean_box(0), lean_box(0));
return v___x_568_;
}
else
{
lean_object* v_one_569_; lean_object* v_n_570_; lean_object* v___x_571_; 
lean_dec(v_h__1_564_);
v_one_569_ = lean_unsigned_to_nat(1u);
v_n_570_ = lean_nat_sub(v_s_561_, v_one_569_);
v___x_571_ = lean_apply_4(v_h__2_565_, v_n_570_, lean_box(0), lean_box(0), lean_box(0));
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___boxed(lean_object* v_w_572_, lean_object* v_motive_573_, lean_object* v_s_574_, lean_object* v_hs_575_, lean_object* v_hslt_576_, lean_object* v_h__1_577_, lean_object* v_h__2_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter(v_w_572_, v_motive_573_, v_s_574_, v_hs_575_, v_hslt_576_, v_h__1_577_, v_h__2_578_);
lean_dec(v_s_574_);
lean_dec(v_w_572_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg(lean_object* v_s_x27_580_, lean_object* v_h__1_581_, lean_object* v_h__2_582_){
_start:
{
lean_object* v_zero_583_; uint8_t v_isZero_584_; 
v_zero_583_ = lean_unsigned_to_nat(0u);
v_isZero_584_ = lean_nat_dec_eq(v_s_x27_580_, v_zero_583_);
if (v_isZero_584_ == 1)
{
lean_object* v___x_585_; 
lean_dec(v_h__2_582_);
v___x_585_ = lean_apply_4(v_h__1_581_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_585_;
}
else
{
lean_object* v_one_586_; lean_object* v_n_587_; lean_object* v___x_588_; 
lean_dec(v_h__1_581_);
v_one_586_ = lean_unsigned_to_nat(1u);
v_n_587_ = lean_nat_sub(v_s_x27_580_, v_one_586_);
v___x_588_ = lean_apply_5(v_h__2_582_, v_n_587_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg___boxed(lean_object* v_s_x27_589_, lean_object* v_h__1_590_, lean_object* v_h__2_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg(v_s_x27_589_, v_h__1_590_, v_h__2_591_);
lean_dec(v_s_x27_589_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter(lean_object* v_w_593_, lean_object* v_s_594_, lean_object* v_motive_595_, lean_object* v_s_x27_596_, lean_object* v_hs_597_, lean_object* v_hslt_598_, lean_object* v_hs0_599_, lean_object* v_h__1_600_, lean_object* v_h__2_601_){
_start:
{
lean_object* v_zero_602_; uint8_t v_isZero_603_; 
v_zero_602_ = lean_unsigned_to_nat(0u);
v_isZero_603_ = lean_nat_dec_eq(v_s_x27_596_, v_zero_602_);
if (v_isZero_603_ == 1)
{
lean_object* v___x_604_; 
lean_dec(v_h__2_601_);
v___x_604_ = lean_apply_4(v_h__1_600_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_604_;
}
else
{
lean_object* v_one_605_; lean_object* v_n_606_; lean_object* v___x_607_; 
lean_dec(v_h__1_600_);
v_one_605_ = lean_unsigned_to_nat(1u);
v_n_606_ = lean_nat_sub(v_s_x27_596_, v_one_605_);
v___x_607_ = lean_apply_5(v_h__2_601_, v_n_606_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___boxed(lean_object* v_w_608_, lean_object* v_s_609_, lean_object* v_motive_610_, lean_object* v_s_x27_611_, lean_object* v_hs_612_, lean_object* v_hslt_613_, lean_object* v_hs0_614_, lean_object* v_h__1_615_, lean_object* v_h__2_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter(v_w_608_, v_s_609_, v_motive_610_, v_s_x27_611_, v_hs_612_, v_hslt_613_, v_hs0_614_, v_h__1_615_, v_h__2_616_);
lean_dec(v_s_x27_611_);
lean_dec(v_s_609_);
lean_dec(v_w_608_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___redArg(lean_object* v_idx_618_, lean_object* v_len_619_, lean_object* v_x_620_){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = lean_unsigned_to_nat(1u);
v___x_622_ = l_BitVec_extractLsb_x27___redArg(v_idx_618_, v___x_621_, v_x_620_);
v___x_623_ = l_BitVec_setWidth(v___x_621_, v_len_619_, v___x_622_);
lean_dec(v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___redArg___boxed(lean_object* v_idx_624_, lean_object* v_len_625_, lean_object* v_x_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_BitVec_extractAndExtendBit___redArg(v_idx_624_, v_len_625_, v_x_626_);
lean_dec(v_x_626_);
lean_dec(v_len_625_);
lean_dec(v_idx_624_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit(lean_object* v_w_628_, lean_object* v_idx_629_, lean_object* v_len_630_, lean_object* v_x_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_BitVec_extractAndExtendBit___redArg(v_idx_629_, v_len_630_, v_x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___boxed(lean_object* v_w_633_, lean_object* v_idx_634_, lean_object* v_len_635_, lean_object* v_x_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_BitVec_extractAndExtendBit(v_w_633_, v_idx_634_, v_len_635_, v_x_636_);
lean_dec(v_x_636_);
lean_dec(v_len_635_);
lean_dec(v_idx_634_);
lean_dec(v_w_633_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___redArg(lean_object* v_w_638_, lean_object* v_k_639_, lean_object* v_len_640_, lean_object* v_x_641_, lean_object* v_acc_642_){
_start:
{
lean_object* v___x_643_; lean_object* v_zero_644_; uint8_t v_isZero_645_; 
v___x_643_ = lean_nat_sub(v_w_638_, v_k_639_);
v_zero_644_ = lean_unsigned_to_nat(0u);
v_isZero_645_ = lean_nat_dec_eq(v___x_643_, v_zero_644_);
lean_dec(v___x_643_);
if (v_isZero_645_ == 1)
{
lean_dec(v_k_639_);
return v_acc_642_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v_acc_x27_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_646_ = lean_nat_mul(v_k_639_, v_len_640_);
v___x_647_ = l_BitVec_extractAndExtendBit___redArg(v_k_639_, v_len_640_, v_x_641_);
v_acc_x27_648_ = l_BitVec_append___redArg(v___x_646_, v___x_647_, v_acc_642_);
lean_dec(v_acc_642_);
lean_dec(v___x_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_nat_add(v_k_639_, v___x_649_);
lean_dec(v_k_639_);
v_k_639_ = v___x_650_;
v_acc_642_ = v_acc_x27_648_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___redArg___boxed(lean_object* v_w_652_, lean_object* v_k_653_, lean_object* v_len_654_, lean_object* v_x_655_, lean_object* v_acc_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_BitVec_extractAndExtendAux___redArg(v_w_652_, v_k_653_, v_len_654_, v_x_655_, v_acc_656_);
lean_dec(v_x_655_);
lean_dec(v_len_654_);
lean_dec(v_w_652_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux(lean_object* v_w_658_, lean_object* v_k_659_, lean_object* v_len_660_, lean_object* v_x_661_, lean_object* v_acc_662_, lean_object* v_hle_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_BitVec_extractAndExtendAux___redArg(v_w_658_, v_k_659_, v_len_660_, v_x_661_, v_acc_662_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___boxed(lean_object* v_w_665_, lean_object* v_k_666_, lean_object* v_len_667_, lean_object* v_x_668_, lean_object* v_acc_669_, lean_object* v_hle_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_BitVec_extractAndExtendAux(v_w_665_, v_k_666_, v_len_667_, v_x_668_, v_acc_669_, v_hle_670_);
lean_dec(v_x_668_);
lean_dec(v_len_667_);
lean_dec(v_w_665_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg(lean_object* v_x_672_, lean_object* v_h__1_673_, lean_object* v_h__2_674_){
_start:
{
lean_object* v_zero_675_; uint8_t v_isZero_676_; 
v_zero_675_ = lean_unsigned_to_nat(0u);
v_isZero_676_ = lean_nat_dec_eq(v_x_672_, v_zero_675_);
if (v_isZero_676_ == 1)
{
lean_object* v___x_677_; 
lean_dec(v_h__2_674_);
v___x_677_ = lean_apply_1(v_h__1_673_, lean_box(0));
return v___x_677_;
}
else
{
lean_object* v_one_678_; lean_object* v_n_679_; lean_object* v___x_680_; 
lean_dec(v_h__1_673_);
v_one_678_ = lean_unsigned_to_nat(1u);
v_n_679_ = lean_nat_sub(v_x_672_, v_one_678_);
v___x_680_ = lean_apply_2(v_h__2_674_, v_n_679_, lean_box(0));
return v___x_680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg___boxed(lean_object* v_x_681_, lean_object* v_h__1_682_, lean_object* v_h__2_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg(v_x_681_, v_h__1_682_, v_h__2_683_);
lean_dec(v_x_681_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter(lean_object* v_motive_685_, lean_object* v_x_686_, lean_object* v_h__1_687_, lean_object* v_h__2_688_){
_start:
{
lean_object* v_zero_689_; uint8_t v_isZero_690_; 
v_zero_689_ = lean_unsigned_to_nat(0u);
v_isZero_690_ = lean_nat_dec_eq(v_x_686_, v_zero_689_);
if (v_isZero_690_ == 1)
{
lean_object* v___x_691_; 
lean_dec(v_h__2_688_);
v___x_691_ = lean_apply_1(v_h__1_687_, lean_box(0));
return v___x_691_;
}
else
{
lean_object* v_one_692_; lean_object* v_n_693_; lean_object* v___x_694_; 
lean_dec(v_h__1_687_);
v_one_692_ = lean_unsigned_to_nat(1u);
v_n_693_ = lean_nat_sub(v_x_686_, v_one_692_);
v___x_694_ = lean_apply_2(v_h__2_688_, v_n_693_, lean_box(0));
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___boxed(lean_object* v_motive_695_, lean_object* v_x_696_, lean_object* v_h__1_697_, lean_object* v_h__2_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter(v_motive_695_, v_x_696_, v_h__1_697_, v_h__2_698_);
lean_dec(v_x_696_);
return v_res_699_;
}
}
static lean_object* _init_l_BitVec_extractAndExtend___closed__0(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = l_BitVec_ofNat(v___x_700_, v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtend(lean_object* v_w_702_, lean_object* v_len_703_, lean_object* v_x_704_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = lean_obj_once(&l_BitVec_extractAndExtend___closed__0, &l_BitVec_extractAndExtend___closed__0_once, _init_l_BitVec_extractAndExtend___closed__0);
v___x_707_ = l_BitVec_extractAndExtendAux___redArg(v_w_702_, v___x_705_, v_len_703_, v_x_704_, v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtend___boxed(lean_object* v_w_708_, lean_object* v_len_709_, lean_object* v_x_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_BitVec_extractAndExtend(v_w_708_, v_len_709_, v_x_710_);
lean_dec(v_x_710_);
lean_dec(v_len_709_);
lean_dec(v_w_708_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___redArg(lean_object* v_len_712_, lean_object* v_w_713_, lean_object* v_iterNum_714_, lean_object* v_oldLayer_715_, lean_object* v_newLayer_716_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_717_ = lean_unsigned_to_nat(2u);
v___x_718_ = lean_nat_mul(v_iterNum_714_, v___x_717_);
v___x_719_ = lean_nat_sub(v_len_712_, v___x_718_);
lean_dec(v___x_718_);
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = lean_nat_dec_eq(v___x_719_, v___x_720_);
lean_dec(v___x_719_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_op1_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v_op2_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v_newLayer_x27_731_; lean_object* v___x_732_; 
v___x_722_ = lean_nat_mul(v___x_717_, v_iterNum_714_);
v___x_723_ = lean_nat_mul(v___x_722_, v_w_713_);
v_op1_724_ = l_BitVec_extractLsb_x27___redArg(v___x_723_, v_w_713_, v_oldLayer_715_);
lean_dec(v___x_723_);
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_add(v___x_722_, v___x_725_);
lean_dec(v___x_722_);
v___x_727_ = lean_nat_mul(v___x_726_, v_w_713_);
lean_dec(v___x_726_);
v_op2_728_ = l_BitVec_extractLsb_x27___redArg(v___x_727_, v_w_713_, v_oldLayer_715_);
lean_dec(v___x_727_);
v___x_729_ = lean_nat_mul(v_iterNum_714_, v_w_713_);
v___x_730_ = l_BitVec_add(v_w_713_, v_op1_724_, v_op2_728_);
lean_dec(v_op2_728_);
lean_dec(v_op1_724_);
v_newLayer_x27_731_ = l_BitVec_append___redArg(v___x_729_, v___x_730_, v_newLayer_716_);
lean_dec(v_newLayer_716_);
lean_dec(v___x_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_nat_add(v_iterNum_714_, v___x_725_);
lean_dec(v_iterNum_714_);
v_iterNum_714_ = v___x_732_;
v_newLayer_716_ = v_newLayer_x27_731_;
goto _start;
}
else
{
lean_dec(v_iterNum_714_);
return v_newLayer_716_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___redArg___boxed(lean_object* v_len_734_, lean_object* v_w_735_, lean_object* v_iterNum_736_, lean_object* v_oldLayer_737_, lean_object* v_newLayer_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_BitVec_cpopLayer___redArg(v_len_734_, v_w_735_, v_iterNum_736_, v_oldLayer_737_, v_newLayer_738_);
lean_dec(v_oldLayer_737_);
lean_dec(v_w_735_);
lean_dec(v_len_734_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer(lean_object* v_len_740_, lean_object* v_w_741_, lean_object* v_iterNum_742_, lean_object* v_oldLayer_743_, lean_object* v_newLayer_744_, lean_object* v_hold_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_BitVec_cpopLayer___redArg(v_len_740_, v_w_741_, v_iterNum_742_, v_oldLayer_743_, v_newLayer_744_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___boxed(lean_object* v_len_747_, lean_object* v_w_748_, lean_object* v_iterNum_749_, lean_object* v_oldLayer_750_, lean_object* v_newLayer_751_, lean_object* v_hold_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_BitVec_cpopLayer(v_len_747_, v_w_748_, v_iterNum_749_, v_oldLayer_750_, v_newLayer_751_, v_hold_752_);
lean_dec(v_oldLayer_750_);
lean_dec(v_w_748_);
lean_dec(v_len_747_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopTree(lean_object* v_len_754_, lean_object* v_w_755_, lean_object* v_l_756_){
_start:
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = lean_nat_dec_eq(v_len_754_, v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = lean_unsigned_to_nat(1u);
v___x_760_ = lean_nat_dec_eq(v_len_754_, v___x_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_761_ = lean_nat_add(v_len_754_, v___x_759_);
v___x_762_ = lean_nat_shiftr(v___x_761_, v___x_759_);
lean_dec(v___x_761_);
v___x_763_ = lean_obj_once(&l_BitVec_extractAndExtend___closed__0, &l_BitVec_extractAndExtend___closed__0_once, _init_l_BitVec_extractAndExtend___closed__0);
v___x_764_ = l_BitVec_cpopLayer___redArg(v_len_754_, v_w_755_, v___x_757_, v_l_756_, v___x_763_);
lean_dec(v_l_756_);
lean_dec(v_len_754_);
v_len_754_ = v___x_762_;
v_l_756_ = v___x_764_;
goto _start;
}
else
{
lean_dec(v_len_754_);
return v_l_756_;
}
}
else
{
lean_object* v___x_766_; 
lean_dec(v_l_756_);
lean_dec(v_len_754_);
v___x_766_ = l_BitVec_ofNat(v_w_755_, v___x_757_);
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopTree___boxed(lean_object* v_len_767_, lean_object* v_w_768_, lean_object* v_l_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_BitVec_cpopTree(v_len_767_, v_w_768_, v_l_769_);
lean_dec(v_w_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopRec(lean_object* v_w_771_, lean_object* v_x_772_){
_start:
{
lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_773_ = lean_unsigned_to_nat(1u);
v___x_774_ = lean_nat_dec_lt(v___x_773_, v_w_771_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = lean_unsigned_to_nat(0u);
v___x_776_ = lean_nat_dec_lt(v___x_775_, v_w_771_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; 
v___x_777_ = l_BitVec_ofNat(v_w_771_, v___x_775_);
lean_dec(v_w_771_);
return v___x_777_;
}
else
{
lean_dec(v_w_771_);
lean_inc(v_x_772_);
return v_x_772_;
}
}
else
{
lean_object* v_extendedBits_778_; lean_object* v___x_779_; 
v_extendedBits_778_ = l_BitVec_extractAndExtend(v_w_771_, v_w_771_, v_x_772_);
lean_inc(v_w_771_);
v___x_779_ = l_BitVec_cpopTree(v_w_771_, v_w_771_, v_extendedBits_778_);
lean_dec(v_w_771_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopRec___boxed(lean_object* v_w_780_, lean_object* v_x_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_BitVec_cpopRec(v_w_780_, v_x_781_);
lean_dec(v_x_781_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(lean_object* v_w_783_, lean_object* v_x_784_, lean_object* v_rem_785_, lean_object* v_acc_786_){
_start:
{
lean_object* v_zero_787_; uint8_t v_isZero_788_; 
v_zero_787_ = lean_unsigned_to_nat(0u);
v_isZero_788_ = lean_nat_dec_eq(v_rem_785_, v_zero_787_);
if (v_isZero_788_ == 1)
{
lean_dec(v_rem_785_);
return v_acc_786_;
}
else
{
lean_object* v_one_789_; lean_object* v_n_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_one_789_ = lean_unsigned_to_nat(1u);
v_n_790_ = lean_nat_sub(v_rem_785_, v_one_789_);
lean_dec(v_rem_785_);
v___x_791_ = lean_nat_mul(v_n_790_, v_w_783_);
v___x_792_ = l_BitVec_extractLsb_x27___redArg(v___x_791_, v_w_783_, v_x_784_);
lean_dec(v___x_791_);
v___x_793_ = l_BitVec_add(v_w_783_, v_acc_786_, v___x_792_);
lean_dec(v___x_792_);
lean_dec(v_acc_786_);
v_rem_785_ = v_n_790_;
v_acc_786_ = v___x_793_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg___boxed(lean_object* v_w_795_, lean_object* v_x_796_, lean_object* v_rem_797_, lean_object* v_acc_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_795_, v_x_796_, v_rem_797_, v_acc_798_);
lean_dec(v_x_796_);
lean_dec(v_w_795_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux(lean_object* v_l_800_, lean_object* v_w_801_, lean_object* v_x_802_, lean_object* v_rem_803_, lean_object* v_acc_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_801_, v_x_802_, v_rem_803_, v_acc_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___boxed(lean_object* v_l_806_, lean_object* v_w_807_, lean_object* v_x_808_, lean_object* v_rem_809_, lean_object* v_acc_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux(v_l_806_, v_w_807_, v_x_808_, v_rem_809_, v_acc_810_);
lean_dec(v_x_808_);
lean_dec(v_w_807_);
lean_dec(v_l_806_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec(lean_object* v_l_812_, lean_object* v_w_813_, lean_object* v_x_814_){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = l_BitVec_ofNat(v_w_813_, v___x_815_);
v___x_817_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_813_, v_x_814_, v_l_812_, v___x_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec___boxed(lean_object* v_l_818_, lean_object* v_w_819_, lean_object* v_x_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec(v_l_818_, v_w_819_, v_x_820_);
lean_dec(v_x_820_);
lean_dec(v_w_819_);
return v_res_821_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Folds(uint8_t builtin);
lean_object* runtime_initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Decidable(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_BitVec_Bitblast(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Folds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Decidable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_BitVec_Bitblast(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Folds(uint8_t builtin);
lean_object* initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Decidable(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_BitVec_Bitblast(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Folds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Decidable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bitblast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_BitVec_Bitblast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_BitVec_Bitblast(builtin);
}
#ifdef __cplusplus
}
#endif
