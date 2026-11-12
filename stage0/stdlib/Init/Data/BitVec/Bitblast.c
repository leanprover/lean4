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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_BitVec_sub(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_BitVec_shiftLeft(lean_object*, lean_object*, lean_object*);
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
v___x_22_ = l_Bool_toNat(v_c_16_);
v___x_23_ = lean_nat_add(v___x_21_, v___x_22_);
lean_dec(v___x_22_);
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
uint8_t v___y_50_; uint8_t v___y_56_; uint8_t v___y_62_; uint8_t v___y_64_; uint8_t v___y_66_; 
if (v_x_46_ == 0)
{
goto v___jp_67_;
}
else
{
if (v_y_47_ == 0)
{
goto v___jp_67_;
}
else
{
v___y_66_ = v_y_47_;
goto v___jp_65_;
}
}
v___jp_49_:
{
uint8_t v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_51_ = 1;
v___x_52_ = lean_box(v___y_50_);
v___x_53_ = lean_box(v___x_51_);
v___x_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
return v___x_54_;
}
v___jp_55_:
{
uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = 0;
v___x_58_ = lean_box(v___y_56_);
v___x_59_ = lean_box(v___x_57_);
v___x_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
return v___x_60_;
}
v___jp_61_:
{
if (v_x_46_ == 0)
{
v___y_50_ = v___y_62_;
goto v___jp_49_;
}
else
{
v___y_56_ = v___y_62_;
goto v___jp_55_;
}
}
v___jp_63_:
{
if (v_x_46_ == 0)
{
v___y_56_ = v___y_64_;
goto v___jp_55_;
}
else
{
v___y_50_ = v___y_64_;
goto v___jp_49_;
}
}
v___jp_65_:
{
if (v_c_48_ == 0)
{
if (v_y_47_ == 0)
{
v___y_64_ = v___y_66_;
goto v___jp_63_;
}
else
{
v___y_62_ = v___y_66_;
goto v___jp_61_;
}
}
else
{
if (v_y_47_ == 0)
{
v___y_62_ = v___y_66_;
goto v___jp_61_;
}
else
{
v___y_64_ = v___y_66_;
goto v___jp_63_;
}
}
}
v___jp_67_:
{
if (v_x_46_ == 0)
{
if (v_y_47_ == 0)
{
v___y_66_ = v_y_47_;
goto v___jp_65_;
}
else
{
v___y_66_ = v_c_48_;
goto v___jp_65_;
}
}
else
{
if (v_c_48_ == 0)
{
if (v_y_47_ == 0)
{
v___y_66_ = v_y_47_;
goto v___jp_65_;
}
else
{
v___y_66_ = v_c_48_;
goto v___jp_65_;
}
}
else
{
v___y_66_ = v_c_48_;
goto v___jp_65_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_adcb___boxed(lean_object* v_x_68_, lean_object* v_y_69_, lean_object* v_c_70_){
_start:
{
uint8_t v_x_boxed_71_; uint8_t v_y_boxed_72_; uint8_t v_c_boxed_73_; lean_object* v_res_74_; 
v_x_boxed_71_ = lean_unbox(v_x_68_);
v_y_boxed_72_ = lean_unbox(v_y_69_);
v_c_boxed_73_ = lean_unbox(v_c_70_);
v_res_74_ = l_BitVec_adcb(v_x_boxed_71_, v_y_boxed_72_, v_c_boxed_73_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_BitVec_adc___lam__0(lean_object* v_x_75_, lean_object* v_y_76_, lean_object* v_i_77_, uint8_t v_c_78_){
_start:
{
uint8_t v___x_79_; uint8_t v___x_80_; lean_object* v___x_81_; 
v___x_79_ = l_Nat_testBit(v_x_75_, v_i_77_);
v___x_80_ = l_Nat_testBit(v_y_76_, v_i_77_);
v___x_81_ = l_BitVec_adcb(v___x_79_, v___x_80_, v_c_78_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_BitVec_adc___lam__0___boxed(lean_object* v_x_82_, lean_object* v_y_83_, lean_object* v_i_84_, lean_object* v_c_85_){
_start:
{
uint8_t v_c_boxed_86_; lean_object* v_res_87_; 
v_c_boxed_86_ = lean_unbox(v_c_85_);
v_res_87_ = l_BitVec_adc___lam__0(v_x_82_, v_y_83_, v_i_84_, v_c_boxed_86_);
lean_dec(v_i_84_);
lean_dec(v_y_83_);
lean_dec(v_x_82_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_BitVec_adc(lean_object* v_w_88_, lean_object* v_x_89_, lean_object* v_y_90_, uint8_t v_s_91_){
_start:
{
lean_object* v___f_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___f_92_ = lean_alloc_closure((void*)(l_BitVec_adc___lam__0___boxed), 4, 2);
lean_closure_set(v___f_92_, 0, v_x_89_);
lean_closure_set(v___f_92_, 1, v_y_90_);
v___x_93_ = lean_box(v_s_91_);
v___x_94_ = l_BitVec_iunfoldr___redArg(v_w_88_, v___f_92_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_BitVec_adc___boxed(lean_object* v_w_95_, lean_object* v_x_96_, lean_object* v_y_97_, lean_object* v_s_98_){
_start:
{
uint8_t v_s_boxed_99_; lean_object* v_res_100_; 
v_s_boxed_99_ = lean_unbox(v_s_98_);
v_res_100_ = l_BitVec_adc(v_w_95_, v_x_96_, v_y_97_, v_s_boxed_99_);
lean_dec(v_w_95_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_BitVec_mulRec(lean_object* v_w_101_, lean_object* v_x_102_, lean_object* v_y_103_, lean_object* v_s_104_){
_start:
{
lean_object* v___y_106_; uint8_t v___x_113_; 
v___x_113_ = l_Nat_testBit(v_y_103_, v_s_104_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = l_BitVec_ofNat(v_w_101_, v___x_114_);
v___y_106_ = v___x_115_;
goto v___jp_105_;
}
else
{
lean_object* v___x_116_; 
v___x_116_ = l_BitVec_shiftLeft(v_w_101_, v_x_102_, v_s_104_);
v___y_106_ = v___x_116_;
goto v___jp_105_;
}
v___jp_105_:
{
lean_object* v_zero_107_; uint8_t v_isZero_108_; 
v_zero_107_ = lean_unsigned_to_nat(0u);
v_isZero_108_ = lean_nat_dec_eq(v_s_104_, v_zero_107_);
if (v_isZero_108_ == 1)
{
return v___y_106_;
}
else
{
lean_object* v_one_109_; lean_object* v_n_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_one_109_ = lean_unsigned_to_nat(1u);
v_n_110_ = lean_nat_sub(v_s_104_, v_one_109_);
v___x_111_ = l_BitVec_mulRec(v_w_101_, v_x_102_, v_y_103_, v_n_110_);
lean_dec(v_n_110_);
v___x_112_ = l_BitVec_add(v_w_101_, v___x_111_, v___y_106_);
lean_dec(v___y_106_);
lean_dec(v___x_111_);
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_mulRec___boxed(lean_object* v_w_117_, lean_object* v_x_118_, lean_object* v_y_119_, lean_object* v_s_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_BitVec_mulRec(v_w_117_, v_x_118_, v_y_119_, v_s_120_);
lean_dec(v_s_120_);
lean_dec(v_y_119_);
lean_dec(v_x_118_);
lean_dec(v_w_117_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___redArg(lean_object* v_s_122_, lean_object* v_h__1_123_, lean_object* v_h__2_124_){
_start:
{
lean_object* v_zero_125_; uint8_t v_isZero_126_; 
v_zero_125_ = lean_unsigned_to_nat(0u);
v_isZero_126_ = lean_nat_dec_eq(v_s_122_, v_zero_125_);
if (v_isZero_126_ == 1)
{
lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec(v_h__2_124_);
v___x_127_ = lean_box(0);
v___x_128_ = lean_apply_1(v_h__1_123_, v___x_127_);
return v___x_128_;
}
else
{
lean_object* v_one_129_; lean_object* v_n_130_; lean_object* v___x_131_; 
lean_dec(v_h__1_123_);
v_one_129_ = lean_unsigned_to_nat(1u);
v_n_130_ = lean_nat_sub(v_s_122_, v_one_129_);
v___x_131_ = lean_apply_1(v_h__2_124_, v_n_130_);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___redArg___boxed(lean_object* v_s_132_, lean_object* v_h__1_133_, lean_object* v_h__2_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___redArg(v_s_132_, v_h__1_133_, v_h__2_134_);
lean_dec(v_s_132_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter(lean_object* v_motive_136_, lean_object* v_s_137_, lean_object* v_h__1_138_, lean_object* v_h__2_139_){
_start:
{
lean_object* v_zero_140_; uint8_t v_isZero_141_; 
v_zero_140_ = lean_unsigned_to_nat(0u);
v_isZero_141_ = lean_nat_dec_eq(v_s_137_, v_zero_140_);
if (v_isZero_141_ == 1)
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_h__2_139_);
v___x_142_ = lean_box(0);
v___x_143_ = lean_apply_1(v_h__1_138_, v___x_142_);
return v___x_143_;
}
else
{
lean_object* v_one_144_; lean_object* v_n_145_; lean_object* v___x_146_; 
lean_dec(v_h__1_138_);
v_one_144_ = lean_unsigned_to_nat(1u);
v_n_145_ = lean_nat_sub(v_s_137_, v_one_144_);
v___x_146_ = lean_apply_1(v_h__2_139_, v_n_145_);
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___boxed(lean_object* v_motive_147_, lean_object* v_s_148_, lean_object* v_h__1_149_, lean_object* v_h__2_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter(v_motive_147_, v_s_148_, v_h__1_149_, v_h__2_150_);
lean_dec(v_s_148_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftRec(lean_object* v_w_u2081_152_, lean_object* v_w_u2082_153_, lean_object* v_x_154_, lean_object* v_y_155_, lean_object* v_n_156_){
_start:
{
lean_object* v___x_157_; lean_object* v_shiftAmt_158_; lean_object* v_zero_159_; uint8_t v_isZero_160_; 
v___x_157_ = l_BitVec_twoPow(v_w_u2082_153_, v_n_156_);
v_shiftAmt_158_ = lean_nat_land(v_y_155_, v___x_157_);
lean_dec(v___x_157_);
v_zero_159_ = lean_unsigned_to_nat(0u);
v_isZero_160_ = lean_nat_dec_eq(v_n_156_, v_zero_159_);
if (v_isZero_160_ == 1)
{
lean_object* v___x_161_; 
v___x_161_ = l_BitVec_shiftLeft(v_w_u2081_152_, v_x_154_, v_shiftAmt_158_);
lean_dec(v_shiftAmt_158_);
return v___x_161_;
}
else
{
lean_object* v_one_162_; lean_object* v_n_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v_one_162_ = lean_unsigned_to_nat(1u);
v_n_163_ = lean_nat_sub(v_n_156_, v_one_162_);
v___x_164_ = l_BitVec_shiftLeftRec(v_w_u2081_152_, v_w_u2082_153_, v_x_154_, v_y_155_, v_n_163_);
lean_dec(v_n_163_);
v___x_165_ = l_BitVec_shiftLeft(v_w_u2081_152_, v___x_164_, v_shiftAmt_158_);
lean_dec(v_shiftAmt_158_);
lean_dec(v___x_164_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftRec___boxed(lean_object* v_w_u2081_166_, lean_object* v_w_u2082_167_, lean_object* v_x_168_, lean_object* v_y_169_, lean_object* v_n_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_BitVec_shiftLeftRec(v_w_u2081_166_, v_w_u2082_167_, v_x_168_, v_y_169_, v_n_170_);
lean_dec(v_n_170_);
lean_dec(v_y_169_);
lean_dec(v_x_168_);
lean_dec(v_w_u2082_167_);
lean_dec(v_w_u2081_166_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_BitVec_DivModState_init(lean_object* v_w_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = l_BitVec_ofNat(v_w_172_, v___x_173_);
lean_inc(v___x_174_);
v___x_175_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_175_, 0, v_w_172_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
lean_ctor_set(v___x_175_, 2, v___x_174_);
lean_ctor_set(v___x_175_, 3, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_BitVec_divSubtractShift(lean_object* v_w_176_, lean_object* v_args_177_, lean_object* v_qr_178_){
_start:
{
lean_object* v_n_179_; lean_object* v_d_180_; lean_object* v_wn_181_; lean_object* v_wr_182_; lean_object* v_q_183_; lean_object* v_r_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_206_; 
v_n_179_ = lean_ctor_get(v_args_177_, 0);
v_d_180_ = lean_ctor_get(v_args_177_, 1);
v_wn_181_ = lean_ctor_get(v_qr_178_, 0);
v_wr_182_ = lean_ctor_get(v_qr_178_, 1);
v_q_183_ = lean_ctor_get(v_qr_178_, 2);
v_r_184_ = lean_ctor_get(v_qr_178_, 3);
v_isSharedCheck_206_ = !lean_is_exclusive(v_qr_178_);
if (v_isSharedCheck_206_ == 0)
{
v___x_186_ = v_qr_178_;
v_isShared_187_ = v_isSharedCheck_206_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_r_184_);
lean_inc(v_q_183_);
lean_inc(v_wr_182_);
lean_inc(v_wn_181_);
lean_dec(v_qr_178_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_206_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v_wn_189_; lean_object* v_wr_190_; uint8_t v___x_191_; lean_object* v_r_x27_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_188_ = lean_unsigned_to_nat(1u);
v_wn_189_ = lean_nat_sub(v_wn_181_, v___x_188_);
lean_dec(v_wn_181_);
v_wr_190_ = lean_nat_add(v_wr_182_, v___x_188_);
lean_dec(v_wr_182_);
v___x_191_ = l_Nat_testBit(v_n_179_, v_wn_189_);
v_r_x27_192_ = l_BitVec_shiftConcat(v_w_176_, v_r_184_, v___x_191_);
lean_dec(v_r_184_);
v___x_193_ = lean_nat_add(v_r_x27_192_, v___x_188_);
v___x_194_ = lean_nat_dec_le(v___x_193_, v_d_180_);
lean_dec(v___x_193_);
if (v___x_194_ == 0)
{
uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_195_ = 1;
v___x_196_ = l_BitVec_shiftConcat(v_w_176_, v_q_183_, v___x_195_);
lean_dec(v_q_183_);
v___x_197_ = l_BitVec_sub(v_w_176_, v_r_x27_192_, v_d_180_);
lean_dec(v_r_x27_192_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 3, v___x_197_);
lean_ctor_set(v___x_186_, 2, v___x_196_);
lean_ctor_set(v___x_186_, 1, v_wr_190_);
lean_ctor_set(v___x_186_, 0, v_wn_189_);
v___x_199_ = v___x_186_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_wn_189_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_wr_190_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
else
{
uint8_t v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_201_ = 0;
v___x_202_ = l_BitVec_shiftConcat(v_w_176_, v_q_183_, v___x_201_);
lean_dec(v_q_183_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 3, v_r_x27_192_);
lean_ctor_set(v___x_186_, 2, v___x_202_);
lean_ctor_set(v___x_186_, 1, v_wr_190_);
lean_ctor_set(v___x_186_, 0, v_wn_189_);
v___x_204_ = v___x_186_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_wn_189_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_wr_190_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v_r_x27_192_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_divSubtractShift___boxed(lean_object* v_w_207_, lean_object* v_args_208_, lean_object* v_qr_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_BitVec_divSubtractShift(v_w_207_, v_args_208_, v_qr_209_);
lean_dec_ref(v_args_208_);
lean_dec(v_w_207_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter___redArg(lean_object* v_args_211_, lean_object* v_h__1_212_){
_start:
{
lean_object* v_n_213_; lean_object* v_d_214_; lean_object* v___x_215_; 
v_n_213_ = lean_ctor_get(v_args_211_, 0);
lean_inc(v_n_213_);
v_d_214_ = lean_ctor_get(v_args_211_, 1);
lean_inc(v_d_214_);
lean_dec_ref(v_args_211_);
v___x_215_ = lean_apply_2(v_h__1_212_, v_n_213_, v_d_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter(lean_object* v_w_216_, lean_object* v_motive_217_, lean_object* v_args_218_, lean_object* v_h__1_219_){
_start:
{
lean_object* v_n_220_; lean_object* v_d_221_; lean_object* v___x_222_; 
v_n_220_ = lean_ctor_get(v_args_218_, 0);
lean_inc(v_n_220_);
v_d_221_ = lean_ctor_get(v_args_218_, 1);
lean_inc(v_d_221_);
lean_dec_ref(v_args_218_);
v___x_222_ = lean_apply_2(v_h__1_219_, v_n_220_, v_d_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter___boxed(lean_object* v_w_223_, lean_object* v_motive_224_, lean_object* v_args_225_, lean_object* v_h__1_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter(v_w_223_, v_motive_224_, v_args_225_, v_h__1_226_);
lean_dec(v_w_223_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_BitVec_divRec(lean_object* v_w_228_, lean_object* v_m_229_, lean_object* v_args_230_, lean_object* v_qr_231_){
_start:
{
lean_object* v_zero_232_; uint8_t v_isZero_233_; 
v_zero_232_ = lean_unsigned_to_nat(0u);
v_isZero_233_ = lean_nat_dec_eq(v_m_229_, v_zero_232_);
if (v_isZero_233_ == 1)
{
lean_dec(v_m_229_);
return v_qr_231_;
}
else
{
lean_object* v_one_234_; lean_object* v_n_235_; lean_object* v___x_236_; 
v_one_234_ = lean_unsigned_to_nat(1u);
v_n_235_ = lean_nat_sub(v_m_229_, v_one_234_);
lean_dec(v_m_229_);
v___x_236_ = l_BitVec_divSubtractShift(v_w_228_, v_args_230_, v_qr_231_);
v_m_229_ = v_n_235_;
v_qr_231_ = v___x_236_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_divRec___boxed(lean_object* v_w_238_, lean_object* v_m_239_, lean_object* v_args_240_, lean_object* v_qr_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_BitVec_divRec(v_w_238_, v_m_239_, v_args_240_, v_qr_241_);
lean_dec_ref(v_args_240_);
lean_dec(v_w_238_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRightRec(lean_object* v_w_u2081_243_, lean_object* v_w_u2082_244_, lean_object* v_x_245_, lean_object* v_y_246_, lean_object* v_n_247_){
_start:
{
lean_object* v___x_248_; lean_object* v_shiftAmt_249_; lean_object* v_zero_250_; uint8_t v_isZero_251_; 
v___x_248_ = l_BitVec_twoPow(v_w_u2082_244_, v_n_247_);
v_shiftAmt_249_ = lean_nat_land(v_y_246_, v___x_248_);
lean_dec(v___x_248_);
v_zero_250_ = lean_unsigned_to_nat(0u);
v_isZero_251_ = lean_nat_dec_eq(v_n_247_, v_zero_250_);
if (v_isZero_251_ == 1)
{
lean_object* v___x_252_; 
v___x_252_ = l_BitVec_sshiftRight(v_w_u2081_243_, v_x_245_, v_shiftAmt_249_);
lean_dec(v_shiftAmt_249_);
return v___x_252_;
}
else
{
lean_object* v_one_253_; lean_object* v_n_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_one_253_ = lean_unsigned_to_nat(1u);
v_n_254_ = lean_nat_sub(v_n_247_, v_one_253_);
v___x_255_ = l_BitVec_sshiftRightRec(v_w_u2081_243_, v_w_u2082_244_, v_x_245_, v_y_246_, v_n_254_);
lean_dec(v_n_254_);
v___x_256_ = l_BitVec_sshiftRight(v_w_u2081_243_, v___x_255_, v_shiftAmt_249_);
lean_dec(v_shiftAmt_249_);
return v___x_256_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRightRec___boxed(lean_object* v_w_u2081_257_, lean_object* v_w_u2082_258_, lean_object* v_x_259_, lean_object* v_y_260_, lean_object* v_n_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_BitVec_sshiftRightRec(v_w_u2081_257_, v_w_u2082_258_, v_x_259_, v_y_260_, v_n_261_);
lean_dec(v_n_261_);
lean_dec(v_y_260_);
lean_dec(v_w_u2082_258_);
lean_dec(v_w_u2081_257_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___redArg(lean_object* v_w_u2082_263_, lean_object* v_x_264_, lean_object* v_y_265_, lean_object* v_n_266_){
_start:
{
lean_object* v___x_267_; lean_object* v_shiftAmt_268_; lean_object* v_zero_269_; uint8_t v_isZero_270_; 
v___x_267_ = l_BitVec_twoPow(v_w_u2082_263_, v_n_266_);
v_shiftAmt_268_ = lean_nat_land(v_y_265_, v___x_267_);
lean_dec(v___x_267_);
v_zero_269_ = lean_unsigned_to_nat(0u);
v_isZero_270_ = lean_nat_dec_eq(v_n_266_, v_zero_269_);
if (v_isZero_270_ == 1)
{
lean_object* v___x_271_; 
v___x_271_ = lean_nat_shiftr(v_x_264_, v_shiftAmt_268_);
lean_dec(v_shiftAmt_268_);
return v___x_271_;
}
else
{
lean_object* v_one_272_; lean_object* v_n_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v_one_272_ = lean_unsigned_to_nat(1u);
v_n_273_ = lean_nat_sub(v_n_266_, v_one_272_);
v___x_274_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_263_, v_x_264_, v_y_265_, v_n_273_);
lean_dec(v_n_273_);
v___x_275_ = lean_nat_shiftr(v___x_274_, v_shiftAmt_268_);
lean_dec(v_shiftAmt_268_);
lean_dec(v___x_274_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___redArg___boxed(lean_object* v_w_u2082_276_, lean_object* v_x_277_, lean_object* v_y_278_, lean_object* v_n_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_276_, v_x_277_, v_y_278_, v_n_279_);
lean_dec(v_n_279_);
lean_dec(v_y_278_);
lean_dec(v_x_277_);
lean_dec(v_w_u2082_276_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec(lean_object* v_w_u2081_281_, lean_object* v_w_u2082_282_, lean_object* v_x_283_, lean_object* v_y_284_, lean_object* v_n_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_282_, v_x_283_, v_y_284_, v_n_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___boxed(lean_object* v_w_u2081_287_, lean_object* v_w_u2082_288_, lean_object* v_x_289_, lean_object* v_y_290_, lean_object* v_n_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_BitVec_ushiftRightRec(v_w_u2081_287_, v_w_u2082_288_, v_x_289_, v_y_290_, v_n_291_);
lean_dec(v_n_291_);
lean_dec(v_y_290_);
lean_dec(v_x_289_);
lean_dec(v_w_u2082_288_);
lean_dec(v_w_u2081_287_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg(uint8_t v_x_293_, uint8_t v_x_294_, lean_object* v_h__1_295_, lean_object* v_h__2_296_, lean_object* v_h__3_297_, lean_object* v_h__4_298_){
_start:
{
if (v_x_293_ == 0)
{
lean_dec(v_h__4_298_);
lean_dec(v_h__3_297_);
if (v_x_294_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec(v_h__2_296_);
v___x_299_ = lean_box(0);
v___x_300_ = lean_apply_1(v_h__1_295_, v___x_299_);
return v___x_300_;
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec(v_h__1_295_);
v___x_301_ = lean_box(0);
v___x_302_ = lean_apply_1(v_h__2_296_, v___x_301_);
return v___x_302_;
}
}
else
{
lean_dec(v_h__2_296_);
lean_dec(v_h__1_295_);
if (v_x_294_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec(v_h__4_298_);
v___x_303_ = lean_box(0);
v___x_304_ = lean_apply_1(v_h__3_297_, v___x_303_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec(v_h__3_297_);
v___x_305_ = lean_box(0);
v___x_306_ = lean_apply_1(v_h__4_298_, v___x_305_);
return v___x_306_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg___boxed(lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_h__1_309_, lean_object* v_h__2_310_, lean_object* v_h__3_311_, lean_object* v_h__4_312_){
_start:
{
uint8_t v_x_46__boxed_313_; uint8_t v_x_47__boxed_314_; lean_object* v_res_315_; 
v_x_46__boxed_313_ = lean_unbox(v_x_307_);
v_x_47__boxed_314_ = lean_unbox(v_x_308_);
v_res_315_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg(v_x_46__boxed_313_, v_x_47__boxed_314_, v_h__1_309_, v_h__2_310_, v_h__3_311_, v_h__4_312_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter(lean_object* v_motive_316_, uint8_t v_x_317_, uint8_t v_x_318_, lean_object* v_h__1_319_, lean_object* v_h__2_320_, lean_object* v_h__3_321_, lean_object* v_h__4_322_){
_start:
{
if (v_x_317_ == 0)
{
lean_dec(v_h__4_322_);
lean_dec(v_h__3_321_);
if (v_x_318_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec(v_h__2_320_);
v___x_323_ = lean_box(0);
v___x_324_ = lean_apply_1(v_h__1_319_, v___x_323_);
return v___x_324_;
}
else
{
lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec(v_h__1_319_);
v___x_325_ = lean_box(0);
v___x_326_ = lean_apply_1(v_h__2_320_, v___x_325_);
return v___x_326_;
}
}
else
{
lean_dec(v_h__2_320_);
lean_dec(v_h__1_319_);
if (v_x_318_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec(v_h__4_322_);
v___x_327_ = lean_box(0);
v___x_328_ = lean_apply_1(v_h__3_321_, v___x_327_);
return v___x_328_;
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec(v_h__3_321_);
v___x_329_ = lean_box(0);
v___x_330_ = lean_apply_1(v_h__4_322_, v___x_329_);
return v___x_330_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___boxed(lean_object* v_motive_331_, lean_object* v_x_332_, lean_object* v_x_333_, lean_object* v_h__1_334_, lean_object* v_h__2_335_, lean_object* v_h__3_336_, lean_object* v_h__4_337_){
_start:
{
uint8_t v_x_68__boxed_338_; uint8_t v_x_69__boxed_339_; lean_object* v_res_340_; 
v_x_68__boxed_338_ = lean_unbox(v_x_332_);
v_x_69__boxed_339_ = lean_unbox(v_x_333_);
v_res_340_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter(v_motive_331_, v_x_68__boxed_338_, v_x_69__boxed_339_, v_h__1_334_, v_h__2_335_, v_h__3_336_, v_h__4_337_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg(uint8_t v_x_341_, uint8_t v_x_342_, lean_object* v_h__1_343_, lean_object* v_h__2_344_, lean_object* v_h__3_345_, lean_object* v_h__4_346_){
_start:
{
if (v_x_341_ == 0)
{
lean_dec(v_h__4_346_);
lean_dec(v_h__3_345_);
if (v_x_342_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec(v_h__2_344_);
v___x_347_ = lean_box(0);
v___x_348_ = lean_apply_1(v_h__1_343_, v___x_347_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec(v_h__1_343_);
v___x_349_ = lean_box(0);
v___x_350_ = lean_apply_1(v_h__2_344_, v___x_349_);
return v___x_350_;
}
}
else
{
lean_dec(v_h__2_344_);
lean_dec(v_h__1_343_);
if (v_x_342_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec(v_h__4_346_);
v___x_351_ = lean_box(0);
v___x_352_ = lean_apply_1(v_h__3_345_, v___x_351_);
return v___x_352_;
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec(v_h__3_345_);
v___x_353_ = lean_box(0);
v___x_354_ = lean_apply_1(v_h__4_346_, v___x_353_);
return v___x_354_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg___boxed(lean_object* v_x_355_, lean_object* v_x_356_, lean_object* v_h__1_357_, lean_object* v_h__2_358_, lean_object* v_h__3_359_, lean_object* v_h__4_360_){
_start:
{
uint8_t v_x_46__boxed_361_; uint8_t v_x_47__boxed_362_; lean_object* v_res_363_; 
v_x_46__boxed_361_ = lean_unbox(v_x_355_);
v_x_47__boxed_362_ = lean_unbox(v_x_356_);
v_res_363_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg(v_x_46__boxed_361_, v_x_47__boxed_362_, v_h__1_357_, v_h__2_358_, v_h__3_359_, v_h__4_360_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter(lean_object* v_motive_364_, uint8_t v_x_365_, uint8_t v_x_366_, lean_object* v_h__1_367_, lean_object* v_h__2_368_, lean_object* v_h__3_369_, lean_object* v_h__4_370_){
_start:
{
if (v_x_365_ == 0)
{
lean_dec(v_h__4_370_);
lean_dec(v_h__3_369_);
if (v_x_366_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec(v_h__2_368_);
v___x_371_ = lean_box(0);
v___x_372_ = lean_apply_1(v_h__1_367_, v___x_371_);
return v___x_372_;
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; 
lean_dec(v_h__1_367_);
v___x_373_ = lean_box(0);
v___x_374_ = lean_apply_1(v_h__2_368_, v___x_373_);
return v___x_374_;
}
}
else
{
lean_dec(v_h__2_368_);
lean_dec(v_h__1_367_);
if (v_x_366_ == 0)
{
lean_object* v___x_375_; lean_object* v___x_376_; 
lean_dec(v_h__4_370_);
v___x_375_ = lean_box(0);
v___x_376_ = lean_apply_1(v_h__3_369_, v___x_375_);
return v___x_376_;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec(v_h__3_369_);
v___x_377_ = lean_box(0);
v___x_378_ = lean_apply_1(v_h__4_370_, v___x_377_);
return v___x_378_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___boxed(lean_object* v_motive_379_, lean_object* v_x_380_, lean_object* v_x_381_, lean_object* v_h__1_382_, lean_object* v_h__2_383_, lean_object* v_h__3_384_, lean_object* v_h__4_385_){
_start:
{
uint8_t v_x_68__boxed_386_; uint8_t v_x_69__boxed_387_; lean_object* v_res_388_; 
v_x_68__boxed_386_ = lean_unbox(v_x_380_);
v_x_69__boxed_387_ = lean_unbox(v_x_381_);
v_res_388_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter(v_motive_379_, v_x_68__boxed_386_, v_x_69__boxed_387_, v_h__1_382_, v_h__2_383_, v_h__3_384_, v_h__4_385_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg(uint8_t v_x_389_, uint8_t v_x_390_, lean_object* v_h__1_391_, lean_object* v_h__2_392_, lean_object* v_h__3_393_, lean_object* v_h__4_394_){
_start:
{
if (v_x_389_ == 0)
{
lean_dec(v_h__4_394_);
lean_dec(v_h__3_393_);
if (v_x_390_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; 
lean_dec(v_h__2_392_);
v___x_395_ = lean_box(0);
v___x_396_ = lean_apply_1(v_h__1_391_, v___x_395_);
return v___x_396_;
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec(v_h__1_391_);
v___x_397_ = lean_box(0);
v___x_398_ = lean_apply_1(v_h__2_392_, v___x_397_);
return v___x_398_;
}
}
else
{
lean_dec(v_h__2_392_);
lean_dec(v_h__1_391_);
if (v_x_390_ == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; 
lean_dec(v_h__4_394_);
v___x_399_ = lean_box(0);
v___x_400_ = lean_apply_1(v_h__3_393_, v___x_399_);
return v___x_400_;
}
else
{
lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec(v_h__3_393_);
v___x_401_ = lean_box(0);
v___x_402_ = lean_apply_1(v_h__4_394_, v___x_401_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg___boxed(lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_h__1_405_, lean_object* v_h__2_406_, lean_object* v_h__3_407_, lean_object* v_h__4_408_){
_start:
{
uint8_t v_x_46__boxed_409_; uint8_t v_x_47__boxed_410_; lean_object* v_res_411_; 
v_x_46__boxed_409_ = lean_unbox(v_x_403_);
v_x_47__boxed_410_ = lean_unbox(v_x_404_);
v_res_411_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg(v_x_46__boxed_409_, v_x_47__boxed_410_, v_h__1_405_, v_h__2_406_, v_h__3_407_, v_h__4_408_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter(lean_object* v_motive_412_, uint8_t v_x_413_, uint8_t v_x_414_, lean_object* v_h__1_415_, lean_object* v_h__2_416_, lean_object* v_h__3_417_, lean_object* v_h__4_418_){
_start:
{
if (v_x_413_ == 0)
{
lean_dec(v_h__4_418_);
lean_dec(v_h__3_417_);
if (v_x_414_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec(v_h__2_416_);
v___x_419_ = lean_box(0);
v___x_420_ = lean_apply_1(v_h__1_415_, v___x_419_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec(v_h__1_415_);
v___x_421_ = lean_box(0);
v___x_422_ = lean_apply_1(v_h__2_416_, v___x_421_);
return v___x_422_;
}
}
else
{
lean_dec(v_h__2_416_);
lean_dec(v_h__1_415_);
if (v_x_414_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec(v_h__4_418_);
v___x_423_ = lean_box(0);
v___x_424_ = lean_apply_1(v_h__3_417_, v___x_423_);
return v___x_424_;
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec(v_h__3_417_);
v___x_425_ = lean_box(0);
v___x_426_ = lean_apply_1(v_h__4_418_, v___x_425_);
return v___x_426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___boxed(lean_object* v_motive_427_, lean_object* v_x_428_, lean_object* v_x_429_, lean_object* v_h__1_430_, lean_object* v_h__2_431_, lean_object* v_h__3_432_, lean_object* v_h__4_433_){
_start:
{
uint8_t v_x_68__boxed_434_; uint8_t v_x_69__boxed_435_; lean_object* v_res_436_; 
v_x_68__boxed_434_ = lean_unbox(v_x_428_);
v_x_69__boxed_435_ = lean_unbox(v_x_429_);
v_res_436_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter(v_motive_427_, v_x_68__boxed_434_, v_x_69__boxed_435_, v_h__1_430_, v_h__2_431_, v_h__3_432_, v_h__4_433_);
return v_res_436_;
}
}
LEAN_EXPORT uint8_t l_BitVec_uppcRec___redArg(lean_object* v_w_437_, lean_object* v_x_438_, lean_object* v_s_439_){
_start:
{
lean_object* v_zero_440_; uint8_t v_isZero_441_; 
v_zero_440_ = lean_unsigned_to_nat(0u);
v_isZero_441_ = lean_nat_dec_eq(v_s_439_, v_zero_440_);
if (v_isZero_441_ == 1)
{
uint8_t v___x_442_; 
lean_dec(v_s_439_);
v___x_442_ = lean_nat_dec_lt(v_zero_440_, v_w_437_);
if (v___x_442_ == 0)
{
return v___x_442_;
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_sub(v_w_437_, v___x_443_);
v___x_445_ = l_Nat_testBit(v_x_438_, v___x_444_);
lean_dec(v___x_444_);
return v___x_445_;
}
}
else
{
lean_object* v_one_446_; lean_object* v_n_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_one_446_ = lean_unsigned_to_nat(1u);
v_n_447_ = lean_nat_sub(v_s_439_, v_one_446_);
lean_dec(v_s_439_);
v___x_448_ = lean_nat_sub(v_w_437_, v_one_446_);
v___x_449_ = lean_nat_sub(v___x_448_, v_n_447_);
lean_dec(v___x_448_);
v___x_450_ = l_Nat_testBit(v_x_438_, v___x_449_);
lean_dec(v___x_449_);
if (v___x_450_ == 0)
{
v_s_439_ = v_n_447_;
goto _start;
}
else
{
lean_dec(v_n_447_);
return v___x_450_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_uppcRec___redArg___boxed(lean_object* v_w_452_, lean_object* v_x_453_, lean_object* v_s_454_){
_start:
{
uint8_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = l_BitVec_uppcRec___redArg(v_w_452_, v_x_453_, v_s_454_);
lean_dec(v_x_453_);
lean_dec(v_w_452_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT uint8_t l_BitVec_uppcRec(lean_object* v_w_457_, lean_object* v_x_458_, lean_object* v_s_459_, lean_object* v_hs_460_){
_start:
{
uint8_t v___x_461_; 
v___x_461_ = l_BitVec_uppcRec___redArg(v_w_457_, v_x_458_, v_s_459_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_BitVec_uppcRec___boxed(lean_object* v_w_462_, lean_object* v_x_463_, lean_object* v_s_464_, lean_object* v_hs_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_BitVec_uppcRec(v_w_462_, v_x_463_, v_s_464_, v_hs_465_);
lean_dec(v_x_463_);
lean_dec(v_w_462_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___redArg(lean_object* v_s_468_, lean_object* v_h__1_469_, lean_object* v_h__2_470_){
_start:
{
lean_object* v_zero_471_; uint8_t v_isZero_472_; 
v_zero_471_ = lean_unsigned_to_nat(0u);
v_isZero_472_ = lean_nat_dec_eq(v_s_468_, v_zero_471_);
if (v_isZero_472_ == 1)
{
lean_object* v___x_473_; 
lean_dec(v_h__2_470_);
v___x_473_ = lean_apply_1(v_h__1_469_, lean_box(0));
return v___x_473_;
}
else
{
lean_object* v_one_474_; lean_object* v_n_475_; lean_object* v___x_476_; 
lean_dec(v_h__1_469_);
v_one_474_ = lean_unsigned_to_nat(1u);
v_n_475_ = lean_nat_sub(v_s_468_, v_one_474_);
v___x_476_ = lean_apply_2(v_h__2_470_, v_n_475_, lean_box(0));
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___redArg___boxed(lean_object* v_s_477_, lean_object* v_h__1_478_, lean_object* v_h__2_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___redArg(v_s_477_, v_h__1_478_, v_h__2_479_);
lean_dec(v_s_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter(lean_object* v_w_481_, lean_object* v_motive_482_, lean_object* v_s_483_, lean_object* v_hs_484_, lean_object* v_h__1_485_, lean_object* v_h__2_486_){
_start:
{
lean_object* v_zero_487_; uint8_t v_isZero_488_; 
v_zero_487_ = lean_unsigned_to_nat(0u);
v_isZero_488_ = lean_nat_dec_eq(v_s_483_, v_zero_487_);
if (v_isZero_488_ == 1)
{
lean_object* v___x_489_; 
lean_dec(v_h__2_486_);
v___x_489_ = lean_apply_1(v_h__1_485_, lean_box(0));
return v___x_489_;
}
else
{
lean_object* v_one_490_; lean_object* v_n_491_; lean_object* v___x_492_; 
lean_dec(v_h__1_485_);
v_one_490_ = lean_unsigned_to_nat(1u);
v_n_491_ = lean_nat_sub(v_s_483_, v_one_490_);
v___x_492_ = lean_apply_2(v_h__2_486_, v_n_491_, lean_box(0));
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___boxed(lean_object* v_w_493_, lean_object* v_motive_494_, lean_object* v_s_495_, lean_object* v_hs_496_, lean_object* v_h__1_497_, lean_object* v_h__2_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter(v_w_493_, v_motive_494_, v_s_495_, v_hs_496_, v_h__1_497_, v_h__2_498_);
lean_dec(v_s_495_);
lean_dec(v_w_493_);
return v_res_499_;
}
}
LEAN_EXPORT uint8_t l_BitVec_aandRec___redArg(lean_object* v_w_500_, lean_object* v_x_501_, lean_object* v_y_502_, lean_object* v_s_503_){
_start:
{
uint8_t v___x_504_; 
v___x_504_ = l_Nat_testBit(v_y_502_, v_s_503_);
if (v___x_504_ == 0)
{
lean_dec(v_s_503_);
return v___x_504_;
}
else
{
uint8_t v___x_505_; 
v___x_505_ = l_BitVec_uppcRec___redArg(v_w_500_, v_x_501_, v_s_503_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_aandRec___redArg___boxed(lean_object* v_w_506_, lean_object* v_x_507_, lean_object* v_y_508_, lean_object* v_s_509_){
_start:
{
uint8_t v_res_510_; lean_object* v_r_511_; 
v_res_510_ = l_BitVec_aandRec___redArg(v_w_506_, v_x_507_, v_y_508_, v_s_509_);
lean_dec(v_y_508_);
lean_dec(v_x_507_);
lean_dec(v_w_506_);
v_r_511_ = lean_box(v_res_510_);
return v_r_511_;
}
}
LEAN_EXPORT uint8_t l_BitVec_aandRec(lean_object* v_w_512_, lean_object* v_x_513_, lean_object* v_y_514_, lean_object* v_s_515_, lean_object* v_hs_516_){
_start:
{
uint8_t v___x_517_; 
v___x_517_ = l_BitVec_aandRec___redArg(v_w_512_, v_x_513_, v_y_514_, v_s_515_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_BitVec_aandRec___boxed(lean_object* v_w_518_, lean_object* v_x_519_, lean_object* v_y_520_, lean_object* v_s_521_, lean_object* v_hs_522_){
_start:
{
uint8_t v_res_523_; lean_object* v_r_524_; 
v_res_523_ = l_BitVec_aandRec(v_w_518_, v_x_519_, v_y_520_, v_s_521_, v_hs_522_);
lean_dec(v_y_520_);
lean_dec(v_x_519_);
lean_dec(v_w_518_);
v_r_524_ = lean_box(v_res_523_);
return v_r_524_;
}
}
LEAN_EXPORT uint8_t l_BitVec_resRec___redArg(lean_object* v_w_525_, lean_object* v_x_526_, lean_object* v_y_527_, lean_object* v_s_528_){
_start:
{
lean_object* v_zero_529_; uint8_t v_isZero_530_; lean_object* v_one_531_; lean_object* v_n_532_; uint8_t v_isZero_533_; 
v_zero_529_ = lean_unsigned_to_nat(0u);
v_isZero_530_ = lean_nat_dec_eq(v_s_528_, v_zero_529_);
v_one_531_ = lean_unsigned_to_nat(1u);
v_n_532_ = lean_nat_sub(v_s_528_, v_one_531_);
v_isZero_533_ = lean_nat_dec_eq(v_n_532_, v_zero_529_);
if (v_isZero_533_ == 1)
{
uint8_t v___x_534_; 
lean_dec(v_n_532_);
lean_dec(v_s_528_);
v___x_534_ = l_BitVec_aandRec___redArg(v_w_525_, v_x_526_, v_y_527_, v_one_531_);
return v___x_534_;
}
else
{
uint8_t v___x_535_; 
v___x_535_ = l_BitVec_resRec___redArg(v_w_525_, v_x_526_, v_y_527_, v_n_532_);
if (v___x_535_ == 0)
{
uint8_t v___x_536_; 
v___x_536_ = l_BitVec_aandRec___redArg(v_w_525_, v_x_526_, v_y_527_, v_s_528_);
return v___x_536_;
}
else
{
lean_dec(v_s_528_);
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_resRec___redArg___boxed(lean_object* v_w_537_, lean_object* v_x_538_, lean_object* v_y_539_, lean_object* v_s_540_){
_start:
{
uint8_t v_res_541_; lean_object* v_r_542_; 
v_res_541_ = l_BitVec_resRec___redArg(v_w_537_, v_x_538_, v_y_539_, v_s_540_);
lean_dec(v_y_539_);
lean_dec(v_x_538_);
lean_dec(v_w_537_);
v_r_542_ = lean_box(v_res_541_);
return v_r_542_;
}
}
LEAN_EXPORT uint8_t l_BitVec_resRec(lean_object* v_w_543_, lean_object* v_x_544_, lean_object* v_y_545_, lean_object* v_s_546_, lean_object* v_hs_547_, lean_object* v_hslt_548_){
_start:
{
uint8_t v___x_549_; 
v___x_549_ = l_BitVec_resRec___redArg(v_w_543_, v_x_544_, v_y_545_, v_s_546_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_BitVec_resRec___boxed(lean_object* v_w_550_, lean_object* v_x_551_, lean_object* v_y_552_, lean_object* v_s_553_, lean_object* v_hs_554_, lean_object* v_hslt_555_){
_start:
{
uint8_t v_res_556_; lean_object* v_r_557_; 
v_res_556_ = l_BitVec_resRec(v_w_550_, v_x_551_, v_y_552_, v_s_553_, v_hs_554_, v_hslt_555_);
lean_dec(v_y_552_);
lean_dec(v_x_551_);
lean_dec(v_w_550_);
v_r_557_ = lean_box(v_res_556_);
return v_r_557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg(lean_object* v_s_558_, lean_object* v_h__1_559_, lean_object* v_h__2_560_){
_start:
{
lean_object* v_zero_561_; uint8_t v_isZero_562_; 
v_zero_561_ = lean_unsigned_to_nat(0u);
v_isZero_562_ = lean_nat_dec_eq(v_s_558_, v_zero_561_);
if (v_isZero_562_ == 1)
{
lean_object* v___x_563_; 
lean_dec(v_h__2_560_);
v___x_563_ = lean_apply_3(v_h__1_559_, lean_box(0), lean_box(0), lean_box(0));
return v___x_563_;
}
else
{
lean_object* v_one_564_; lean_object* v_n_565_; lean_object* v___x_566_; 
lean_dec(v_h__1_559_);
v_one_564_ = lean_unsigned_to_nat(1u);
v_n_565_ = lean_nat_sub(v_s_558_, v_one_564_);
v___x_566_ = lean_apply_4(v_h__2_560_, v_n_565_, lean_box(0), lean_box(0), lean_box(0));
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg___boxed(lean_object* v_s_567_, lean_object* v_h__1_568_, lean_object* v_h__2_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg(v_s_567_, v_h__1_568_, v_h__2_569_);
lean_dec(v_s_567_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter(lean_object* v_w_571_, lean_object* v_motive_572_, lean_object* v_s_573_, lean_object* v_hs_574_, lean_object* v_hslt_575_, lean_object* v_h__1_576_, lean_object* v_h__2_577_){
_start:
{
lean_object* v_zero_578_; uint8_t v_isZero_579_; 
v_zero_578_ = lean_unsigned_to_nat(0u);
v_isZero_579_ = lean_nat_dec_eq(v_s_573_, v_zero_578_);
if (v_isZero_579_ == 1)
{
lean_object* v___x_580_; 
lean_dec(v_h__2_577_);
v___x_580_ = lean_apply_3(v_h__1_576_, lean_box(0), lean_box(0), lean_box(0));
return v___x_580_;
}
else
{
lean_object* v_one_581_; lean_object* v_n_582_; lean_object* v___x_583_; 
lean_dec(v_h__1_576_);
v_one_581_ = lean_unsigned_to_nat(1u);
v_n_582_ = lean_nat_sub(v_s_573_, v_one_581_);
v___x_583_ = lean_apply_4(v_h__2_577_, v_n_582_, lean_box(0), lean_box(0), lean_box(0));
return v___x_583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___boxed(lean_object* v_w_584_, lean_object* v_motive_585_, lean_object* v_s_586_, lean_object* v_hs_587_, lean_object* v_hslt_588_, lean_object* v_h__1_589_, lean_object* v_h__2_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter(v_w_584_, v_motive_585_, v_s_586_, v_hs_587_, v_hslt_588_, v_h__1_589_, v_h__2_590_);
lean_dec(v_s_586_);
lean_dec(v_w_584_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg(lean_object* v_s_x27_592_, lean_object* v_h__1_593_, lean_object* v_h__2_594_){
_start:
{
lean_object* v_zero_595_; uint8_t v_isZero_596_; 
v_zero_595_ = lean_unsigned_to_nat(0u);
v_isZero_596_ = lean_nat_dec_eq(v_s_x27_592_, v_zero_595_);
if (v_isZero_596_ == 1)
{
lean_object* v___x_597_; 
lean_dec(v_h__2_594_);
v___x_597_ = lean_apply_4(v_h__1_593_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_597_;
}
else
{
lean_object* v_one_598_; lean_object* v_n_599_; lean_object* v___x_600_; 
lean_dec(v_h__1_593_);
v_one_598_ = lean_unsigned_to_nat(1u);
v_n_599_ = lean_nat_sub(v_s_x27_592_, v_one_598_);
v___x_600_ = lean_apply_5(v_h__2_594_, v_n_599_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg___boxed(lean_object* v_s_x27_601_, lean_object* v_h__1_602_, lean_object* v_h__2_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg(v_s_x27_601_, v_h__1_602_, v_h__2_603_);
lean_dec(v_s_x27_601_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter(lean_object* v_w_605_, lean_object* v_s_606_, lean_object* v_motive_607_, lean_object* v_s_x27_608_, lean_object* v_hs_609_, lean_object* v_hslt_610_, lean_object* v_hs0_611_, lean_object* v_h__1_612_, lean_object* v_h__2_613_){
_start:
{
lean_object* v_zero_614_; uint8_t v_isZero_615_; 
v_zero_614_ = lean_unsigned_to_nat(0u);
v_isZero_615_ = lean_nat_dec_eq(v_s_x27_608_, v_zero_614_);
if (v_isZero_615_ == 1)
{
lean_object* v___x_616_; 
lean_dec(v_h__2_613_);
v___x_616_ = lean_apply_4(v_h__1_612_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_616_;
}
else
{
lean_object* v_one_617_; lean_object* v_n_618_; lean_object* v___x_619_; 
lean_dec(v_h__1_612_);
v_one_617_ = lean_unsigned_to_nat(1u);
v_n_618_ = lean_nat_sub(v_s_x27_608_, v_one_617_);
v___x_619_ = lean_apply_5(v_h__2_613_, v_n_618_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___boxed(lean_object* v_w_620_, lean_object* v_s_621_, lean_object* v_motive_622_, lean_object* v_s_x27_623_, lean_object* v_hs_624_, lean_object* v_hslt_625_, lean_object* v_hs0_626_, lean_object* v_h__1_627_, lean_object* v_h__2_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter(v_w_620_, v_s_621_, v_motive_622_, v_s_x27_623_, v_hs_624_, v_hslt_625_, v_hs0_626_, v_h__1_627_, v_h__2_628_);
lean_dec(v_s_x27_623_);
lean_dec(v_s_621_);
lean_dec(v_w_620_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___redArg(lean_object* v_idx_630_, lean_object* v_len_631_, lean_object* v_x_632_){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = lean_unsigned_to_nat(1u);
v___x_634_ = l_BitVec_extractLsb_x27___redArg(v_idx_630_, v___x_633_, v_x_632_);
v___x_635_ = l_BitVec_setWidth(v___x_633_, v_len_631_, v___x_634_);
lean_dec(v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___redArg___boxed(lean_object* v_idx_636_, lean_object* v_len_637_, lean_object* v_x_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_BitVec_extractAndExtendBit___redArg(v_idx_636_, v_len_637_, v_x_638_);
lean_dec(v_x_638_);
lean_dec(v_len_637_);
lean_dec(v_idx_636_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit(lean_object* v_w_640_, lean_object* v_idx_641_, lean_object* v_len_642_, lean_object* v_x_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_BitVec_extractAndExtendBit___redArg(v_idx_641_, v_len_642_, v_x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___boxed(lean_object* v_w_645_, lean_object* v_idx_646_, lean_object* v_len_647_, lean_object* v_x_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_BitVec_extractAndExtendBit(v_w_645_, v_idx_646_, v_len_647_, v_x_648_);
lean_dec(v_x_648_);
lean_dec(v_len_647_);
lean_dec(v_idx_646_);
lean_dec(v_w_645_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___redArg(lean_object* v_w_650_, lean_object* v_k_651_, lean_object* v_len_652_, lean_object* v_x_653_, lean_object* v_acc_654_){
_start:
{
lean_object* v___x_655_; lean_object* v_zero_656_; uint8_t v_isZero_657_; 
v___x_655_ = lean_nat_sub(v_w_650_, v_k_651_);
v_zero_656_ = lean_unsigned_to_nat(0u);
v_isZero_657_ = lean_nat_dec_eq(v___x_655_, v_zero_656_);
lean_dec(v___x_655_);
if (v_isZero_657_ == 1)
{
lean_dec(v_k_651_);
return v_acc_654_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v_acc_x27_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_658_ = lean_nat_mul(v_k_651_, v_len_652_);
v___x_659_ = l_BitVec_extractAndExtendBit___redArg(v_k_651_, v_len_652_, v_x_653_);
v_acc_x27_660_ = l_BitVec_append___redArg(v___x_658_, v___x_659_, v_acc_654_);
lean_dec(v_acc_654_);
lean_dec(v___x_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_unsigned_to_nat(1u);
v___x_662_ = lean_nat_add(v_k_651_, v___x_661_);
lean_dec(v_k_651_);
v_k_651_ = v___x_662_;
v_acc_654_ = v_acc_x27_660_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___redArg___boxed(lean_object* v_w_664_, lean_object* v_k_665_, lean_object* v_len_666_, lean_object* v_x_667_, lean_object* v_acc_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_BitVec_extractAndExtendAux___redArg(v_w_664_, v_k_665_, v_len_666_, v_x_667_, v_acc_668_);
lean_dec(v_x_667_);
lean_dec(v_len_666_);
lean_dec(v_w_664_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux(lean_object* v_w_670_, lean_object* v_k_671_, lean_object* v_len_672_, lean_object* v_x_673_, lean_object* v_acc_674_, lean_object* v_hle_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_BitVec_extractAndExtendAux___redArg(v_w_670_, v_k_671_, v_len_672_, v_x_673_, v_acc_674_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___boxed(lean_object* v_w_677_, lean_object* v_k_678_, lean_object* v_len_679_, lean_object* v_x_680_, lean_object* v_acc_681_, lean_object* v_hle_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_BitVec_extractAndExtendAux(v_w_677_, v_k_678_, v_len_679_, v_x_680_, v_acc_681_, v_hle_682_);
lean_dec(v_x_680_);
lean_dec(v_len_679_);
lean_dec(v_w_677_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg(lean_object* v_x_684_, lean_object* v_h__1_685_, lean_object* v_h__2_686_){
_start:
{
lean_object* v_zero_687_; uint8_t v_isZero_688_; 
v_zero_687_ = lean_unsigned_to_nat(0u);
v_isZero_688_ = lean_nat_dec_eq(v_x_684_, v_zero_687_);
if (v_isZero_688_ == 1)
{
lean_object* v___x_689_; 
lean_dec(v_h__2_686_);
v___x_689_ = lean_apply_1(v_h__1_685_, lean_box(0));
return v___x_689_;
}
else
{
lean_object* v_one_690_; lean_object* v_n_691_; lean_object* v___x_692_; 
lean_dec(v_h__1_685_);
v_one_690_ = lean_unsigned_to_nat(1u);
v_n_691_ = lean_nat_sub(v_x_684_, v_one_690_);
v___x_692_ = lean_apply_2(v_h__2_686_, v_n_691_, lean_box(0));
return v___x_692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg___boxed(lean_object* v_x_693_, lean_object* v_h__1_694_, lean_object* v_h__2_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg(v_x_693_, v_h__1_694_, v_h__2_695_);
lean_dec(v_x_693_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter(lean_object* v_motive_697_, lean_object* v_x_698_, lean_object* v_h__1_699_, lean_object* v_h__2_700_){
_start:
{
lean_object* v_zero_701_; uint8_t v_isZero_702_; 
v_zero_701_ = lean_unsigned_to_nat(0u);
v_isZero_702_ = lean_nat_dec_eq(v_x_698_, v_zero_701_);
if (v_isZero_702_ == 1)
{
lean_object* v___x_703_; 
lean_dec(v_h__2_700_);
v___x_703_ = lean_apply_1(v_h__1_699_, lean_box(0));
return v___x_703_;
}
else
{
lean_object* v_one_704_; lean_object* v_n_705_; lean_object* v___x_706_; 
lean_dec(v_h__1_699_);
v_one_704_ = lean_unsigned_to_nat(1u);
v_n_705_ = lean_nat_sub(v_x_698_, v_one_704_);
v___x_706_ = lean_apply_2(v_h__2_700_, v_n_705_, lean_box(0));
return v___x_706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___boxed(lean_object* v_motive_707_, lean_object* v_x_708_, lean_object* v_h__1_709_, lean_object* v_h__2_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter(v_motive_707_, v_x_708_, v_h__1_709_, v_h__2_710_);
lean_dec(v_x_708_);
return v_res_711_;
}
}
static lean_object* _init_l_BitVec_extractAndExtend___closed__0(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = l_BitVec_ofNat(v___x_712_, v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtend(lean_object* v_w_714_, lean_object* v_len_715_, lean_object* v_x_716_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = lean_obj_once(&l_BitVec_extractAndExtend___closed__0, &l_BitVec_extractAndExtend___closed__0_once, _init_l_BitVec_extractAndExtend___closed__0);
v___x_719_ = l_BitVec_extractAndExtendAux___redArg(v_w_714_, v___x_717_, v_len_715_, v_x_716_, v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtend___boxed(lean_object* v_w_720_, lean_object* v_len_721_, lean_object* v_x_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_BitVec_extractAndExtend(v_w_720_, v_len_721_, v_x_722_);
lean_dec(v_x_722_);
lean_dec(v_len_721_);
lean_dec(v_w_720_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___redArg(lean_object* v_len_724_, lean_object* v_w_725_, lean_object* v_iterNum_726_, lean_object* v_oldLayer_727_, lean_object* v_newLayer_728_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_729_ = lean_unsigned_to_nat(2u);
v___x_730_ = lean_nat_mul(v_iterNum_726_, v___x_729_);
v___x_731_ = lean_nat_sub(v_len_724_, v___x_730_);
lean_dec(v___x_730_);
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = lean_nat_dec_eq(v___x_731_, v___x_732_);
lean_dec(v___x_731_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v_op1_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v_op2_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v_newLayer_x27_743_; lean_object* v___x_744_; 
v___x_734_ = lean_nat_mul(v___x_729_, v_iterNum_726_);
v___x_735_ = lean_nat_mul(v___x_734_, v_w_725_);
v_op1_736_ = l_BitVec_extractLsb_x27___redArg(v___x_735_, v_w_725_, v_oldLayer_727_);
lean_dec(v___x_735_);
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = lean_nat_add(v___x_734_, v___x_737_);
lean_dec(v___x_734_);
v___x_739_ = lean_nat_mul(v___x_738_, v_w_725_);
lean_dec(v___x_738_);
v_op2_740_ = l_BitVec_extractLsb_x27___redArg(v___x_739_, v_w_725_, v_oldLayer_727_);
lean_dec(v___x_739_);
v___x_741_ = lean_nat_mul(v_iterNum_726_, v_w_725_);
v___x_742_ = l_BitVec_add(v_w_725_, v_op1_736_, v_op2_740_);
lean_dec(v_op2_740_);
lean_dec(v_op1_736_);
v_newLayer_x27_743_ = l_BitVec_append___redArg(v___x_741_, v___x_742_, v_newLayer_728_);
lean_dec(v_newLayer_728_);
lean_dec(v___x_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_nat_add(v_iterNum_726_, v___x_737_);
lean_dec(v_iterNum_726_);
v_iterNum_726_ = v___x_744_;
v_newLayer_728_ = v_newLayer_x27_743_;
goto _start;
}
else
{
lean_dec(v_iterNum_726_);
return v_newLayer_728_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___redArg___boxed(lean_object* v_len_746_, lean_object* v_w_747_, lean_object* v_iterNum_748_, lean_object* v_oldLayer_749_, lean_object* v_newLayer_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_BitVec_cpopLayer___redArg(v_len_746_, v_w_747_, v_iterNum_748_, v_oldLayer_749_, v_newLayer_750_);
lean_dec(v_oldLayer_749_);
lean_dec(v_w_747_);
lean_dec(v_len_746_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer(lean_object* v_len_752_, lean_object* v_w_753_, lean_object* v_iterNum_754_, lean_object* v_oldLayer_755_, lean_object* v_newLayer_756_, lean_object* v_hold_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_BitVec_cpopLayer___redArg(v_len_752_, v_w_753_, v_iterNum_754_, v_oldLayer_755_, v_newLayer_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___boxed(lean_object* v_len_759_, lean_object* v_w_760_, lean_object* v_iterNum_761_, lean_object* v_oldLayer_762_, lean_object* v_newLayer_763_, lean_object* v_hold_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_BitVec_cpopLayer(v_len_759_, v_w_760_, v_iterNum_761_, v_oldLayer_762_, v_newLayer_763_, v_hold_764_);
lean_dec(v_oldLayer_762_);
lean_dec(v_w_760_);
lean_dec(v_len_759_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopTree(lean_object* v_len_766_, lean_object* v_w_767_, lean_object* v_l_768_){
_start:
{
lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = lean_nat_dec_eq(v_len_766_, v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = lean_nat_dec_eq(v_len_766_, v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_773_ = lean_nat_add(v_len_766_, v___x_771_);
v___x_774_ = lean_nat_shiftr(v___x_773_, v___x_771_);
lean_dec(v___x_773_);
v___x_775_ = lean_obj_once(&l_BitVec_extractAndExtend___closed__0, &l_BitVec_extractAndExtend___closed__0_once, _init_l_BitVec_extractAndExtend___closed__0);
v___x_776_ = l_BitVec_cpopLayer___redArg(v_len_766_, v_w_767_, v___x_769_, v_l_768_, v___x_775_);
lean_dec(v_l_768_);
lean_dec(v_len_766_);
v_len_766_ = v___x_774_;
v_l_768_ = v___x_776_;
goto _start;
}
else
{
lean_dec(v_len_766_);
return v_l_768_;
}
}
else
{
lean_object* v___x_778_; 
lean_dec(v_l_768_);
lean_dec(v_len_766_);
v___x_778_ = l_BitVec_ofNat(v_w_767_, v___x_769_);
return v___x_778_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopTree___boxed(lean_object* v_len_779_, lean_object* v_w_780_, lean_object* v_l_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_BitVec_cpopTree(v_len_779_, v_w_780_, v_l_781_);
lean_dec(v_w_780_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopRec(lean_object* v_w_783_, lean_object* v_x_784_){
_start:
{
lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_785_ = lean_unsigned_to_nat(1u);
v___x_786_ = lean_nat_dec_lt(v___x_785_, v_w_783_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = lean_nat_dec_lt(v___x_787_, v_w_783_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
v___x_789_ = l_BitVec_ofNat(v_w_783_, v___x_787_);
lean_dec(v_w_783_);
return v___x_789_;
}
else
{
lean_dec(v_w_783_);
lean_inc(v_x_784_);
return v_x_784_;
}
}
else
{
lean_object* v_extendedBits_790_; lean_object* v___x_791_; 
v_extendedBits_790_ = l_BitVec_extractAndExtend(v_w_783_, v_w_783_, v_x_784_);
lean_inc(v_w_783_);
v___x_791_ = l_BitVec_cpopTree(v_w_783_, v_w_783_, v_extendedBits_790_);
lean_dec(v_w_783_);
return v___x_791_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopRec___boxed(lean_object* v_w_792_, lean_object* v_x_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_BitVec_cpopRec(v_w_792_, v_x_793_);
lean_dec(v_x_793_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(lean_object* v_w_795_, lean_object* v_x_796_, lean_object* v_rem_797_, lean_object* v_acc_798_){
_start:
{
lean_object* v_zero_799_; uint8_t v_isZero_800_; 
v_zero_799_ = lean_unsigned_to_nat(0u);
v_isZero_800_ = lean_nat_dec_eq(v_rem_797_, v_zero_799_);
if (v_isZero_800_ == 1)
{
lean_dec(v_rem_797_);
return v_acc_798_;
}
else
{
lean_object* v_one_801_; lean_object* v_n_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_one_801_ = lean_unsigned_to_nat(1u);
v_n_802_ = lean_nat_sub(v_rem_797_, v_one_801_);
lean_dec(v_rem_797_);
v___x_803_ = lean_nat_mul(v_n_802_, v_w_795_);
v___x_804_ = l_BitVec_extractLsb_x27___redArg(v___x_803_, v_w_795_, v_x_796_);
lean_dec(v___x_803_);
v___x_805_ = l_BitVec_add(v_w_795_, v_acc_798_, v___x_804_);
lean_dec(v___x_804_);
lean_dec(v_acc_798_);
v_rem_797_ = v_n_802_;
v_acc_798_ = v___x_805_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg___boxed(lean_object* v_w_807_, lean_object* v_x_808_, lean_object* v_rem_809_, lean_object* v_acc_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_807_, v_x_808_, v_rem_809_, v_acc_810_);
lean_dec(v_x_808_);
lean_dec(v_w_807_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux(lean_object* v_l_812_, lean_object* v_w_813_, lean_object* v_x_814_, lean_object* v_rem_815_, lean_object* v_acc_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_813_, v_x_814_, v_rem_815_, v_acc_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___boxed(lean_object* v_l_818_, lean_object* v_w_819_, lean_object* v_x_820_, lean_object* v_rem_821_, lean_object* v_acc_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux(v_l_818_, v_w_819_, v_x_820_, v_rem_821_, v_acc_822_);
lean_dec(v_x_820_);
lean_dec(v_w_819_);
lean_dec(v_l_818_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec(lean_object* v_l_824_, lean_object* v_w_825_, lean_object* v_x_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = l_BitVec_ofNat(v_w_825_, v___x_827_);
v___x_829_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_825_, v_x_826_, v_l_824_, v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec___boxed(lean_object* v_l_830_, lean_object* v_w_831_, lean_object* v_x_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec(v_l_830_, v_w_831_, v_x_832_);
lean_dec(v_x_832_);
lean_dec(v_w_831_);
return v_res_833_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_BitVec_Bitblast(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
