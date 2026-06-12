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
uint8_t v___y_50_; uint8_t v___y_56_; uint8_t v___y_62_; uint8_t v___y_63_; uint8_t v___y_65_; uint8_t v___y_68_; uint8_t v___y_71_; 
if (v_x_46_ == 0)
{
goto v___jp_72_;
}
else
{
if (v_y_47_ == 0)
{
goto v___jp_72_;
}
else
{
v___y_71_ = v_y_47_;
goto v___jp_70_;
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
if (v___y_63_ == 0)
{
v___y_56_ = v___y_62_;
goto v___jp_55_;
}
else
{
v___y_50_ = v___y_62_;
goto v___jp_49_;
}
}
else
{
if (v___y_63_ == 0)
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
}
v___jp_64_:
{
uint8_t v___x_66_; 
v___x_66_ = 1;
v___y_62_ = v___y_65_;
v___y_63_ = v___x_66_;
goto v___jp_61_;
}
v___jp_67_:
{
uint8_t v___x_69_; 
v___x_69_ = 0;
v___y_62_ = v___y_68_;
v___y_63_ = v___x_69_;
goto v___jp_61_;
}
v___jp_70_:
{
if (v_y_47_ == 0)
{
if (v_c_48_ == 0)
{
v___y_68_ = v___y_71_;
goto v___jp_67_;
}
else
{
v___y_65_ = v___y_71_;
goto v___jp_64_;
}
}
else
{
if (v_c_48_ == 0)
{
v___y_65_ = v___y_71_;
goto v___jp_64_;
}
else
{
v___y_68_ = v___y_71_;
goto v___jp_67_;
}
}
}
v___jp_72_:
{
if (v_x_46_ == 0)
{
if (v_y_47_ == 0)
{
v___y_71_ = v_y_47_;
goto v___jp_70_;
}
else
{
v___y_71_ = v_c_48_;
goto v___jp_70_;
}
}
else
{
if (v_c_48_ == 0)
{
if (v_y_47_ == 0)
{
v___y_71_ = v_y_47_;
goto v___jp_70_;
}
else
{
v___y_71_ = v_c_48_;
goto v___jp_70_;
}
}
else
{
v___y_71_ = v_c_48_;
goto v___jp_70_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_adcb___boxed(lean_object* v_x_73_, lean_object* v_y_74_, lean_object* v_c_75_){
_start:
{
uint8_t v_x_boxed_76_; uint8_t v_y_boxed_77_; uint8_t v_c_boxed_78_; lean_object* v_res_79_; 
v_x_boxed_76_ = lean_unbox(v_x_73_);
v_y_boxed_77_ = lean_unbox(v_y_74_);
v_c_boxed_78_ = lean_unbox(v_c_75_);
v_res_79_ = l_BitVec_adcb(v_x_boxed_76_, v_y_boxed_77_, v_c_boxed_78_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_BitVec_adc___lam__0(lean_object* v_x_80_, lean_object* v_y_81_, lean_object* v_i_82_, uint8_t v_c_83_){
_start:
{
uint8_t v___x_84_; uint8_t v___x_85_; lean_object* v___x_86_; 
v___x_84_ = l_Nat_testBit(v_x_80_, v_i_82_);
v___x_85_ = l_Nat_testBit(v_y_81_, v_i_82_);
v___x_86_ = l_BitVec_adcb(v___x_84_, v___x_85_, v_c_83_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_BitVec_adc___lam__0___boxed(lean_object* v_x_87_, lean_object* v_y_88_, lean_object* v_i_89_, lean_object* v_c_90_){
_start:
{
uint8_t v_c_boxed_91_; lean_object* v_res_92_; 
v_c_boxed_91_ = lean_unbox(v_c_90_);
v_res_92_ = l_BitVec_adc___lam__0(v_x_87_, v_y_88_, v_i_89_, v_c_boxed_91_);
lean_dec(v_i_89_);
lean_dec(v_y_88_);
lean_dec(v_x_87_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_BitVec_adc(lean_object* v_w_93_, lean_object* v_x_94_, lean_object* v_y_95_, uint8_t v_s_96_){
_start:
{
lean_object* v___f_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___f_97_ = lean_alloc_closure((void*)(l_BitVec_adc___lam__0___boxed), 4, 2);
lean_closure_set(v___f_97_, 0, v_x_94_);
lean_closure_set(v___f_97_, 1, v_y_95_);
v___x_98_ = lean_box(v_s_96_);
v___x_99_ = l_BitVec_iunfoldr___redArg(v_w_93_, v___f_97_, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_BitVec_adc___boxed(lean_object* v_w_100_, lean_object* v_x_101_, lean_object* v_y_102_, lean_object* v_s_103_){
_start:
{
uint8_t v_s_boxed_104_; lean_object* v_res_105_; 
v_s_boxed_104_ = lean_unbox(v_s_103_);
v_res_105_ = l_BitVec_adc(v_w_100_, v_x_101_, v_y_102_, v_s_boxed_104_);
lean_dec(v_w_100_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_BitVec_mulRec(lean_object* v_w_106_, lean_object* v_x_107_, lean_object* v_y_108_, lean_object* v_s_109_){
_start:
{
lean_object* v___y_111_; uint8_t v___x_118_; 
v___x_118_ = l_Nat_testBit(v_y_108_, v_s_109_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = l_BitVec_ofNat(v_w_106_, v___x_119_);
v___y_111_ = v___x_120_;
goto v___jp_110_;
}
else
{
lean_object* v___x_121_; 
v___x_121_ = l_BitVec_shiftLeft(v_w_106_, v_x_107_, v_s_109_);
v___y_111_ = v___x_121_;
goto v___jp_110_;
}
v___jp_110_:
{
lean_object* v_zero_112_; uint8_t v_isZero_113_; 
v_zero_112_ = lean_unsigned_to_nat(0u);
v_isZero_113_ = lean_nat_dec_eq(v_s_109_, v_zero_112_);
if (v_isZero_113_ == 1)
{
return v___y_111_;
}
else
{
lean_object* v_one_114_; lean_object* v_n_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_one_114_ = lean_unsigned_to_nat(1u);
v_n_115_ = lean_nat_sub(v_s_109_, v_one_114_);
v___x_116_ = l_BitVec_mulRec(v_w_106_, v_x_107_, v_y_108_, v_n_115_);
lean_dec(v_n_115_);
v___x_117_ = l_BitVec_add(v_w_106_, v___x_116_, v___y_111_);
lean_dec(v___y_111_);
lean_dec(v___x_116_);
return v___x_117_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_mulRec___boxed(lean_object* v_w_122_, lean_object* v_x_123_, lean_object* v_y_124_, lean_object* v_s_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_BitVec_mulRec(v_w_122_, v_x_123_, v_y_124_, v_s_125_);
lean_dec(v_s_125_);
lean_dec(v_y_124_);
lean_dec(v_x_123_);
lean_dec(v_w_122_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___redArg(lean_object* v_s_127_, lean_object* v_h__1_128_, lean_object* v_h__2_129_){
_start:
{
lean_object* v_zero_130_; uint8_t v_isZero_131_; 
v_zero_130_ = lean_unsigned_to_nat(0u);
v_isZero_131_ = lean_nat_dec_eq(v_s_127_, v_zero_130_);
if (v_isZero_131_ == 1)
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec(v_h__2_129_);
v___x_132_ = lean_box(0);
v___x_133_ = lean_apply_1(v_h__1_128_, v___x_132_);
return v___x_133_;
}
else
{
lean_object* v_one_134_; lean_object* v_n_135_; lean_object* v___x_136_; 
lean_dec(v_h__1_128_);
v_one_134_ = lean_unsigned_to_nat(1u);
v_n_135_ = lean_nat_sub(v_s_127_, v_one_134_);
v___x_136_ = lean_apply_1(v_h__2_129_, v_n_135_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___redArg___boxed(lean_object* v_s_137_, lean_object* v_h__1_138_, lean_object* v_h__2_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___redArg(v_s_137_, v_h__1_138_, v_h__2_139_);
lean_dec(v_s_137_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter(lean_object* v_motive_141_, lean_object* v_s_142_, lean_object* v_h__1_143_, lean_object* v_h__2_144_){
_start:
{
lean_object* v_zero_145_; uint8_t v_isZero_146_; 
v_zero_145_ = lean_unsigned_to_nat(0u);
v_isZero_146_ = lean_nat_dec_eq(v_s_142_, v_zero_145_);
if (v_isZero_146_ == 1)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v_h__2_144_);
v___x_147_ = lean_box(0);
v___x_148_ = lean_apply_1(v_h__1_143_, v___x_147_);
return v___x_148_;
}
else
{
lean_object* v_one_149_; lean_object* v_n_150_; lean_object* v___x_151_; 
lean_dec(v_h__1_143_);
v_one_149_ = lean_unsigned_to_nat(1u);
v_n_150_ = lean_nat_sub(v_s_142_, v_one_149_);
v___x_151_ = lean_apply_1(v_h__2_144_, v_n_150_);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___boxed(lean_object* v_motive_152_, lean_object* v_s_153_, lean_object* v_h__1_154_, lean_object* v_h__2_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter(v_motive_152_, v_s_153_, v_h__1_154_, v_h__2_155_);
lean_dec(v_s_153_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftRec(lean_object* v_w_u2081_157_, lean_object* v_w_u2082_158_, lean_object* v_x_159_, lean_object* v_y_160_, lean_object* v_n_161_){
_start:
{
lean_object* v___x_162_; lean_object* v_shiftAmt_163_; lean_object* v_zero_164_; uint8_t v_isZero_165_; 
v___x_162_ = l_BitVec_twoPow(v_w_u2082_158_, v_n_161_);
v_shiftAmt_163_ = lean_nat_land(v_y_160_, v___x_162_);
lean_dec(v___x_162_);
v_zero_164_ = lean_unsigned_to_nat(0u);
v_isZero_165_ = lean_nat_dec_eq(v_n_161_, v_zero_164_);
if (v_isZero_165_ == 1)
{
lean_object* v___x_166_; 
v___x_166_ = l_BitVec_shiftLeft(v_w_u2081_157_, v_x_159_, v_shiftAmt_163_);
lean_dec(v_shiftAmt_163_);
return v___x_166_;
}
else
{
lean_object* v_one_167_; lean_object* v_n_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_one_167_ = lean_unsigned_to_nat(1u);
v_n_168_ = lean_nat_sub(v_n_161_, v_one_167_);
v___x_169_ = l_BitVec_shiftLeftRec(v_w_u2081_157_, v_w_u2082_158_, v_x_159_, v_y_160_, v_n_168_);
lean_dec(v_n_168_);
v___x_170_ = l_BitVec_shiftLeft(v_w_u2081_157_, v___x_169_, v_shiftAmt_163_);
lean_dec(v_shiftAmt_163_);
lean_dec(v___x_169_);
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftRec___boxed(lean_object* v_w_u2081_171_, lean_object* v_w_u2082_172_, lean_object* v_x_173_, lean_object* v_y_174_, lean_object* v_n_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_BitVec_shiftLeftRec(v_w_u2081_171_, v_w_u2082_172_, v_x_173_, v_y_174_, v_n_175_);
lean_dec(v_n_175_);
lean_dec(v_y_174_);
lean_dec(v_x_173_);
lean_dec(v_w_u2082_172_);
lean_dec(v_w_u2081_171_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_BitVec_DivModState_init(lean_object* v_w_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = l_BitVec_ofNat(v_w_177_, v___x_178_);
lean_inc(v___x_179_);
v___x_180_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_180_, 0, v_w_177_);
lean_ctor_set(v___x_180_, 1, v___x_178_);
lean_ctor_set(v___x_180_, 2, v___x_179_);
lean_ctor_set(v___x_180_, 3, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_BitVec_divSubtractShift(lean_object* v_w_181_, lean_object* v_args_182_, lean_object* v_qr_183_){
_start:
{
lean_object* v_n_184_; lean_object* v_d_185_; lean_object* v_wn_186_; lean_object* v_wr_187_; lean_object* v_q_188_; lean_object* v_r_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_210_; 
v_n_184_ = lean_ctor_get(v_args_182_, 0);
v_d_185_ = lean_ctor_get(v_args_182_, 1);
v_wn_186_ = lean_ctor_get(v_qr_183_, 0);
v_wr_187_ = lean_ctor_get(v_qr_183_, 1);
v_q_188_ = lean_ctor_get(v_qr_183_, 2);
v_r_189_ = lean_ctor_get(v_qr_183_, 3);
v_isSharedCheck_210_ = !lean_is_exclusive(v_qr_183_);
if (v_isSharedCheck_210_ == 0)
{
v___x_191_ = v_qr_183_;
v_isShared_192_ = v_isSharedCheck_210_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_r_189_);
lean_inc(v_q_188_);
lean_inc(v_wr_187_);
lean_inc(v_wn_186_);
lean_dec(v_qr_183_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_210_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v_wn_194_; lean_object* v_wr_195_; uint8_t v___x_196_; lean_object* v_r_x27_197_; uint8_t v___x_198_; 
v___x_193_ = lean_unsigned_to_nat(1u);
v_wn_194_ = lean_nat_sub(v_wn_186_, v___x_193_);
lean_dec(v_wn_186_);
v_wr_195_ = lean_nat_add(v_wr_187_, v___x_193_);
lean_dec(v_wr_187_);
v___x_196_ = l_Nat_testBit(v_n_184_, v_wn_194_);
v_r_x27_197_ = l_BitVec_shiftConcat(v_w_181_, v_r_189_, v___x_196_);
lean_dec(v_r_189_);
v___x_198_ = lean_nat_dec_lt(v_r_x27_197_, v_d_185_);
if (v___x_198_ == 0)
{
uint8_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_199_ = 1;
v___x_200_ = l_BitVec_shiftConcat(v_w_181_, v_q_188_, v___x_199_);
lean_dec(v_q_188_);
v___x_201_ = l_BitVec_sub(v_w_181_, v_r_x27_197_, v_d_185_);
lean_dec(v_r_x27_197_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 3, v___x_201_);
lean_ctor_set(v___x_191_, 2, v___x_200_);
lean_ctor_set(v___x_191_, 1, v_wr_195_);
lean_ctor_set(v___x_191_, 0, v_wn_194_);
v___x_203_ = v___x_191_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_wn_194_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_wr_195_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_204_, 3, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
else
{
uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_205_ = 0;
v___x_206_ = l_BitVec_shiftConcat(v_w_181_, v_q_188_, v___x_205_);
lean_dec(v_q_188_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 3, v_r_x27_197_);
lean_ctor_set(v___x_191_, 2, v___x_206_);
lean_ctor_set(v___x_191_, 1, v_wr_195_);
lean_ctor_set(v___x_191_, 0, v_wn_194_);
v___x_208_ = v___x_191_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_wn_194_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_wr_195_);
lean_ctor_set(v_reuseFailAlloc_209_, 2, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_209_, 3, v_r_x27_197_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_divSubtractShift___boxed(lean_object* v_w_211_, lean_object* v_args_212_, lean_object* v_qr_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_BitVec_divSubtractShift(v_w_211_, v_args_212_, v_qr_213_);
lean_dec_ref(v_args_212_);
lean_dec(v_w_211_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter___redArg(lean_object* v_args_215_, lean_object* v_h__1_216_){
_start:
{
lean_object* v_n_217_; lean_object* v_d_218_; lean_object* v___x_219_; 
v_n_217_ = lean_ctor_get(v_args_215_, 0);
lean_inc(v_n_217_);
v_d_218_ = lean_ctor_get(v_args_215_, 1);
lean_inc(v_d_218_);
lean_dec_ref(v_args_215_);
v___x_219_ = lean_apply_2(v_h__1_216_, v_n_217_, v_d_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter(lean_object* v_w_220_, lean_object* v_motive_221_, lean_object* v_args_222_, lean_object* v_h__1_223_){
_start:
{
lean_object* v_n_224_; lean_object* v_d_225_; lean_object* v___x_226_; 
v_n_224_ = lean_ctor_get(v_args_222_, 0);
lean_inc(v_n_224_);
v_d_225_ = lean_ctor_get(v_args_222_, 1);
lean_inc(v_d_225_);
lean_dec_ref(v_args_222_);
v___x_226_ = lean_apply_2(v_h__1_223_, v_n_224_, v_d_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter___boxed(lean_object* v_w_227_, lean_object* v_motive_228_, lean_object* v_args_229_, lean_object* v_h__1_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter(v_w_227_, v_motive_228_, v_args_229_, v_h__1_230_);
lean_dec(v_w_227_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_BitVec_divRec(lean_object* v_w_232_, lean_object* v_m_233_, lean_object* v_args_234_, lean_object* v_qr_235_){
_start:
{
lean_object* v_zero_236_; uint8_t v_isZero_237_; 
v_zero_236_ = lean_unsigned_to_nat(0u);
v_isZero_237_ = lean_nat_dec_eq(v_m_233_, v_zero_236_);
if (v_isZero_237_ == 1)
{
lean_dec(v_m_233_);
return v_qr_235_;
}
else
{
lean_object* v_one_238_; lean_object* v_n_239_; lean_object* v___x_240_; 
v_one_238_ = lean_unsigned_to_nat(1u);
v_n_239_ = lean_nat_sub(v_m_233_, v_one_238_);
lean_dec(v_m_233_);
v___x_240_ = l_BitVec_divSubtractShift(v_w_232_, v_args_234_, v_qr_235_);
v_m_233_ = v_n_239_;
v_qr_235_ = v___x_240_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_divRec___boxed(lean_object* v_w_242_, lean_object* v_m_243_, lean_object* v_args_244_, lean_object* v_qr_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_BitVec_divRec(v_w_242_, v_m_243_, v_args_244_, v_qr_245_);
lean_dec_ref(v_args_244_);
lean_dec(v_w_242_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRightRec(lean_object* v_w_u2081_247_, lean_object* v_w_u2082_248_, lean_object* v_x_249_, lean_object* v_y_250_, lean_object* v_n_251_){
_start:
{
lean_object* v___x_252_; lean_object* v_shiftAmt_253_; lean_object* v_zero_254_; uint8_t v_isZero_255_; 
v___x_252_ = l_BitVec_twoPow(v_w_u2082_248_, v_n_251_);
v_shiftAmt_253_ = lean_nat_land(v_y_250_, v___x_252_);
lean_dec(v___x_252_);
v_zero_254_ = lean_unsigned_to_nat(0u);
v_isZero_255_ = lean_nat_dec_eq(v_n_251_, v_zero_254_);
if (v_isZero_255_ == 1)
{
lean_object* v___x_256_; 
v___x_256_ = l_BitVec_sshiftRight(v_w_u2081_247_, v_x_249_, v_shiftAmt_253_);
lean_dec(v_shiftAmt_253_);
return v___x_256_;
}
else
{
lean_object* v_one_257_; lean_object* v_n_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_one_257_ = lean_unsigned_to_nat(1u);
v_n_258_ = lean_nat_sub(v_n_251_, v_one_257_);
v___x_259_ = l_BitVec_sshiftRightRec(v_w_u2081_247_, v_w_u2082_248_, v_x_249_, v_y_250_, v_n_258_);
lean_dec(v_n_258_);
v___x_260_ = l_BitVec_sshiftRight(v_w_u2081_247_, v___x_259_, v_shiftAmt_253_);
lean_dec(v_shiftAmt_253_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRightRec___boxed(lean_object* v_w_u2081_261_, lean_object* v_w_u2082_262_, lean_object* v_x_263_, lean_object* v_y_264_, lean_object* v_n_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_BitVec_sshiftRightRec(v_w_u2081_261_, v_w_u2082_262_, v_x_263_, v_y_264_, v_n_265_);
lean_dec(v_n_265_);
lean_dec(v_y_264_);
lean_dec(v_w_u2082_262_);
lean_dec(v_w_u2081_261_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___redArg(lean_object* v_w_u2082_267_, lean_object* v_x_268_, lean_object* v_y_269_, lean_object* v_n_270_){
_start:
{
lean_object* v___x_271_; lean_object* v_shiftAmt_272_; lean_object* v_zero_273_; uint8_t v_isZero_274_; 
v___x_271_ = l_BitVec_twoPow(v_w_u2082_267_, v_n_270_);
v_shiftAmt_272_ = lean_nat_land(v_y_269_, v___x_271_);
lean_dec(v___x_271_);
v_zero_273_ = lean_unsigned_to_nat(0u);
v_isZero_274_ = lean_nat_dec_eq(v_n_270_, v_zero_273_);
if (v_isZero_274_ == 1)
{
lean_object* v___x_275_; 
v___x_275_ = lean_nat_shiftr(v_x_268_, v_shiftAmt_272_);
lean_dec(v_shiftAmt_272_);
return v___x_275_;
}
else
{
lean_object* v_one_276_; lean_object* v_n_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_one_276_ = lean_unsigned_to_nat(1u);
v_n_277_ = lean_nat_sub(v_n_270_, v_one_276_);
v___x_278_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_267_, v_x_268_, v_y_269_, v_n_277_);
lean_dec(v_n_277_);
v___x_279_ = lean_nat_shiftr(v___x_278_, v_shiftAmt_272_);
lean_dec(v_shiftAmt_272_);
lean_dec(v___x_278_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___redArg___boxed(lean_object* v_w_u2082_280_, lean_object* v_x_281_, lean_object* v_y_282_, lean_object* v_n_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_280_, v_x_281_, v_y_282_, v_n_283_);
lean_dec(v_n_283_);
lean_dec(v_y_282_);
lean_dec(v_x_281_);
lean_dec(v_w_u2082_280_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec(lean_object* v_w_u2081_285_, lean_object* v_w_u2082_286_, lean_object* v_x_287_, lean_object* v_y_288_, lean_object* v_n_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_286_, v_x_287_, v_y_288_, v_n_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___boxed(lean_object* v_w_u2081_291_, lean_object* v_w_u2082_292_, lean_object* v_x_293_, lean_object* v_y_294_, lean_object* v_n_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_BitVec_ushiftRightRec(v_w_u2081_291_, v_w_u2082_292_, v_x_293_, v_y_294_, v_n_295_);
lean_dec(v_n_295_);
lean_dec(v_y_294_);
lean_dec(v_x_293_);
lean_dec(v_w_u2082_292_);
lean_dec(v_w_u2081_291_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg(uint8_t v_x_297_, uint8_t v_x_298_, lean_object* v_h__1_299_, lean_object* v_h__2_300_, lean_object* v_h__3_301_, lean_object* v_h__4_302_){
_start:
{
if (v_x_297_ == 0)
{
lean_dec(v_h__4_302_);
lean_dec(v_h__3_301_);
if (v_x_298_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec(v_h__2_300_);
v___x_303_ = lean_box(0);
v___x_304_ = lean_apply_1(v_h__1_299_, v___x_303_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec(v_h__1_299_);
v___x_305_ = lean_box(0);
v___x_306_ = lean_apply_1(v_h__2_300_, v___x_305_);
return v___x_306_;
}
}
else
{
lean_dec(v_h__2_300_);
lean_dec(v_h__1_299_);
if (v_x_298_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec(v_h__4_302_);
v___x_307_ = lean_box(0);
v___x_308_ = lean_apply_1(v_h__3_301_, v___x_307_);
return v___x_308_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec(v_h__3_301_);
v___x_309_ = lean_box(0);
v___x_310_ = lean_apply_1(v_h__4_302_, v___x_309_);
return v___x_310_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg___boxed(lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v_h__1_313_, lean_object* v_h__2_314_, lean_object* v_h__3_315_, lean_object* v_h__4_316_){
_start:
{
uint8_t v_x_50__boxed_317_; uint8_t v_x_51__boxed_318_; lean_object* v_res_319_; 
v_x_50__boxed_317_ = lean_unbox(v_x_311_);
v_x_51__boxed_318_ = lean_unbox(v_x_312_);
v_res_319_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg(v_x_50__boxed_317_, v_x_51__boxed_318_, v_h__1_313_, v_h__2_314_, v_h__3_315_, v_h__4_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter(lean_object* v_motive_320_, uint8_t v_x_321_, uint8_t v_x_322_, lean_object* v_h__1_323_, lean_object* v_h__2_324_, lean_object* v_h__3_325_, lean_object* v_h__4_326_){
_start:
{
if (v_x_321_ == 0)
{
lean_dec(v_h__4_326_);
lean_dec(v_h__3_325_);
if (v_x_322_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec(v_h__2_324_);
v___x_327_ = lean_box(0);
v___x_328_ = lean_apply_1(v_h__1_323_, v___x_327_);
return v___x_328_;
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec(v_h__1_323_);
v___x_329_ = lean_box(0);
v___x_330_ = lean_apply_1(v_h__2_324_, v___x_329_);
return v___x_330_;
}
}
else
{
lean_dec(v_h__2_324_);
lean_dec(v_h__1_323_);
if (v_x_322_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec(v_h__4_326_);
v___x_331_ = lean_box(0);
v___x_332_ = lean_apply_1(v_h__3_325_, v___x_331_);
return v___x_332_;
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec(v_h__3_325_);
v___x_333_ = lean_box(0);
v___x_334_ = lean_apply_1(v_h__4_326_, v___x_333_);
return v___x_334_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___boxed(lean_object* v_motive_335_, lean_object* v_x_336_, lean_object* v_x_337_, lean_object* v_h__1_338_, lean_object* v_h__2_339_, lean_object* v_h__3_340_, lean_object* v_h__4_341_){
_start:
{
uint8_t v_x_72__boxed_342_; uint8_t v_x_73__boxed_343_; lean_object* v_res_344_; 
v_x_72__boxed_342_ = lean_unbox(v_x_336_);
v_x_73__boxed_343_ = lean_unbox(v_x_337_);
v_res_344_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter(v_motive_335_, v_x_72__boxed_342_, v_x_73__boxed_343_, v_h__1_338_, v_h__2_339_, v_h__3_340_, v_h__4_341_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg(uint8_t v_x_345_, uint8_t v_x_346_, lean_object* v_h__1_347_, lean_object* v_h__2_348_, lean_object* v_h__3_349_, lean_object* v_h__4_350_){
_start:
{
if (v_x_345_ == 0)
{
lean_dec(v_h__4_350_);
lean_dec(v_h__3_349_);
if (v_x_346_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec(v_h__2_348_);
v___x_351_ = lean_box(0);
v___x_352_ = lean_apply_1(v_h__1_347_, v___x_351_);
return v___x_352_;
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec(v_h__1_347_);
v___x_353_ = lean_box(0);
v___x_354_ = lean_apply_1(v_h__2_348_, v___x_353_);
return v___x_354_;
}
}
else
{
lean_dec(v_h__2_348_);
lean_dec(v_h__1_347_);
if (v_x_346_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; 
lean_dec(v_h__4_350_);
v___x_355_ = lean_box(0);
v___x_356_ = lean_apply_1(v_h__3_349_, v___x_355_);
return v___x_356_;
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec(v_h__3_349_);
v___x_357_ = lean_box(0);
v___x_358_ = lean_apply_1(v_h__4_350_, v___x_357_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg___boxed(lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v_h__1_361_, lean_object* v_h__2_362_, lean_object* v_h__3_363_, lean_object* v_h__4_364_){
_start:
{
uint8_t v_x_50__boxed_365_; uint8_t v_x_51__boxed_366_; lean_object* v_res_367_; 
v_x_50__boxed_365_ = lean_unbox(v_x_359_);
v_x_51__boxed_366_ = lean_unbox(v_x_360_);
v_res_367_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg(v_x_50__boxed_365_, v_x_51__boxed_366_, v_h__1_361_, v_h__2_362_, v_h__3_363_, v_h__4_364_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter(lean_object* v_motive_368_, uint8_t v_x_369_, uint8_t v_x_370_, lean_object* v_h__1_371_, lean_object* v_h__2_372_, lean_object* v_h__3_373_, lean_object* v_h__4_374_){
_start:
{
if (v_x_369_ == 0)
{
lean_dec(v_h__4_374_);
lean_dec(v_h__3_373_);
if (v_x_370_ == 0)
{
lean_object* v___x_375_; lean_object* v___x_376_; 
lean_dec(v_h__2_372_);
v___x_375_ = lean_box(0);
v___x_376_ = lean_apply_1(v_h__1_371_, v___x_375_);
return v___x_376_;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec(v_h__1_371_);
v___x_377_ = lean_box(0);
v___x_378_ = lean_apply_1(v_h__2_372_, v___x_377_);
return v___x_378_;
}
}
else
{
lean_dec(v_h__2_372_);
lean_dec(v_h__1_371_);
if (v_x_370_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_dec(v_h__4_374_);
v___x_379_ = lean_box(0);
v___x_380_ = lean_apply_1(v_h__3_373_, v___x_379_);
return v___x_380_;
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; 
lean_dec(v_h__3_373_);
v___x_381_ = lean_box(0);
v___x_382_ = lean_apply_1(v_h__4_374_, v___x_381_);
return v___x_382_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___boxed(lean_object* v_motive_383_, lean_object* v_x_384_, lean_object* v_x_385_, lean_object* v_h__1_386_, lean_object* v_h__2_387_, lean_object* v_h__3_388_, lean_object* v_h__4_389_){
_start:
{
uint8_t v_x_72__boxed_390_; uint8_t v_x_73__boxed_391_; lean_object* v_res_392_; 
v_x_72__boxed_390_ = lean_unbox(v_x_384_);
v_x_73__boxed_391_ = lean_unbox(v_x_385_);
v_res_392_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter(v_motive_383_, v_x_72__boxed_390_, v_x_73__boxed_391_, v_h__1_386_, v_h__2_387_, v_h__3_388_, v_h__4_389_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg(uint8_t v_x_393_, uint8_t v_x_394_, lean_object* v_h__1_395_, lean_object* v_h__2_396_, lean_object* v_h__3_397_, lean_object* v_h__4_398_){
_start:
{
if (v_x_393_ == 0)
{
lean_dec(v_h__4_398_);
lean_dec(v_h__3_397_);
if (v_x_394_ == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; 
lean_dec(v_h__2_396_);
v___x_399_ = lean_box(0);
v___x_400_ = lean_apply_1(v_h__1_395_, v___x_399_);
return v___x_400_;
}
else
{
lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec(v_h__1_395_);
v___x_401_ = lean_box(0);
v___x_402_ = lean_apply_1(v_h__2_396_, v___x_401_);
return v___x_402_;
}
}
else
{
lean_dec(v_h__2_396_);
lean_dec(v_h__1_395_);
if (v_x_394_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec(v_h__4_398_);
v___x_403_ = lean_box(0);
v___x_404_ = lean_apply_1(v_h__3_397_, v___x_403_);
return v___x_404_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec(v_h__3_397_);
v___x_405_ = lean_box(0);
v___x_406_ = lean_apply_1(v_h__4_398_, v___x_405_);
return v___x_406_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg___boxed(lean_object* v_x_407_, lean_object* v_x_408_, lean_object* v_h__1_409_, lean_object* v_h__2_410_, lean_object* v_h__3_411_, lean_object* v_h__4_412_){
_start:
{
uint8_t v_x_50__boxed_413_; uint8_t v_x_51__boxed_414_; lean_object* v_res_415_; 
v_x_50__boxed_413_ = lean_unbox(v_x_407_);
v_x_51__boxed_414_ = lean_unbox(v_x_408_);
v_res_415_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg(v_x_50__boxed_413_, v_x_51__boxed_414_, v_h__1_409_, v_h__2_410_, v_h__3_411_, v_h__4_412_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter(lean_object* v_motive_416_, uint8_t v_x_417_, uint8_t v_x_418_, lean_object* v_h__1_419_, lean_object* v_h__2_420_, lean_object* v_h__3_421_, lean_object* v_h__4_422_){
_start:
{
if (v_x_417_ == 0)
{
lean_dec(v_h__4_422_);
lean_dec(v_h__3_421_);
if (v_x_418_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec(v_h__2_420_);
v___x_423_ = lean_box(0);
v___x_424_ = lean_apply_1(v_h__1_419_, v___x_423_);
return v___x_424_;
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec(v_h__1_419_);
v___x_425_ = lean_box(0);
v___x_426_ = lean_apply_1(v_h__2_420_, v___x_425_);
return v___x_426_;
}
}
else
{
lean_dec(v_h__2_420_);
lean_dec(v_h__1_419_);
if (v_x_418_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec(v_h__4_422_);
v___x_427_ = lean_box(0);
v___x_428_ = lean_apply_1(v_h__3_421_, v___x_427_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec(v_h__3_421_);
v___x_429_ = lean_box(0);
v___x_430_ = lean_apply_1(v_h__4_422_, v___x_429_);
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___boxed(lean_object* v_motive_431_, lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_h__1_434_, lean_object* v_h__2_435_, lean_object* v_h__3_436_, lean_object* v_h__4_437_){
_start:
{
uint8_t v_x_72__boxed_438_; uint8_t v_x_73__boxed_439_; lean_object* v_res_440_; 
v_x_72__boxed_438_ = lean_unbox(v_x_432_);
v_x_73__boxed_439_ = lean_unbox(v_x_433_);
v_res_440_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter(v_motive_431_, v_x_72__boxed_438_, v_x_73__boxed_439_, v_h__1_434_, v_h__2_435_, v_h__3_436_, v_h__4_437_);
return v_res_440_;
}
}
LEAN_EXPORT uint8_t l_BitVec_uppcRec___redArg(lean_object* v_w_441_, lean_object* v_x_442_, lean_object* v_s_443_){
_start:
{
lean_object* v_zero_444_; uint8_t v_isZero_445_; 
v_zero_444_ = lean_unsigned_to_nat(0u);
v_isZero_445_ = lean_nat_dec_eq(v_s_443_, v_zero_444_);
if (v_isZero_445_ == 1)
{
uint8_t v___x_446_; 
lean_dec(v_s_443_);
v___x_446_ = lean_nat_dec_lt(v_zero_444_, v_w_441_);
if (v___x_446_ == 0)
{
return v___x_446_;
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_nat_sub(v_w_441_, v___x_447_);
v___x_449_ = l_Nat_testBit(v_x_442_, v___x_448_);
lean_dec(v___x_448_);
return v___x_449_;
}
}
else
{
lean_object* v_one_450_; lean_object* v_n_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v_one_450_ = lean_unsigned_to_nat(1u);
v_n_451_ = lean_nat_sub(v_s_443_, v_one_450_);
lean_dec(v_s_443_);
v___x_452_ = lean_nat_sub(v_w_441_, v_one_450_);
v___x_453_ = lean_nat_sub(v___x_452_, v_n_451_);
lean_dec(v___x_452_);
v___x_454_ = l_Nat_testBit(v_x_442_, v___x_453_);
lean_dec(v___x_453_);
if (v___x_454_ == 0)
{
v_s_443_ = v_n_451_;
goto _start;
}
else
{
lean_dec(v_n_451_);
return v___x_454_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_uppcRec___redArg___boxed(lean_object* v_w_456_, lean_object* v_x_457_, lean_object* v_s_458_){
_start:
{
uint8_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l_BitVec_uppcRec___redArg(v_w_456_, v_x_457_, v_s_458_);
lean_dec(v_x_457_);
lean_dec(v_w_456_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT uint8_t l_BitVec_uppcRec(lean_object* v_w_461_, lean_object* v_x_462_, lean_object* v_s_463_, lean_object* v_hs_464_){
_start:
{
uint8_t v___x_465_; 
v___x_465_ = l_BitVec_uppcRec___redArg(v_w_461_, v_x_462_, v_s_463_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_BitVec_uppcRec___boxed(lean_object* v_w_466_, lean_object* v_x_467_, lean_object* v_s_468_, lean_object* v_hs_469_){
_start:
{
uint8_t v_res_470_; lean_object* v_r_471_; 
v_res_470_ = l_BitVec_uppcRec(v_w_466_, v_x_467_, v_s_468_, v_hs_469_);
lean_dec(v_x_467_);
lean_dec(v_w_466_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___redArg(lean_object* v_s_472_, lean_object* v_h__1_473_, lean_object* v_h__2_474_){
_start:
{
lean_object* v_zero_475_; uint8_t v_isZero_476_; 
v_zero_475_ = lean_unsigned_to_nat(0u);
v_isZero_476_ = lean_nat_dec_eq(v_s_472_, v_zero_475_);
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
v_n_479_ = lean_nat_sub(v_s_472_, v_one_478_);
v___x_480_ = lean_apply_2(v_h__2_474_, v_n_479_, lean_box(0));
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___redArg___boxed(lean_object* v_s_481_, lean_object* v_h__1_482_, lean_object* v_h__2_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___redArg(v_s_481_, v_h__1_482_, v_h__2_483_);
lean_dec(v_s_481_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter(lean_object* v_w_485_, lean_object* v_motive_486_, lean_object* v_s_487_, lean_object* v_hs_488_, lean_object* v_h__1_489_, lean_object* v_h__2_490_){
_start:
{
lean_object* v_zero_491_; uint8_t v_isZero_492_; 
v_zero_491_ = lean_unsigned_to_nat(0u);
v_isZero_492_ = lean_nat_dec_eq(v_s_487_, v_zero_491_);
if (v_isZero_492_ == 1)
{
lean_object* v___x_493_; 
lean_dec(v_h__2_490_);
v___x_493_ = lean_apply_1(v_h__1_489_, lean_box(0));
return v___x_493_;
}
else
{
lean_object* v_one_494_; lean_object* v_n_495_; lean_object* v___x_496_; 
lean_dec(v_h__1_489_);
v_one_494_ = lean_unsigned_to_nat(1u);
v_n_495_ = lean_nat_sub(v_s_487_, v_one_494_);
v___x_496_ = lean_apply_2(v_h__2_490_, v_n_495_, lean_box(0));
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___boxed(lean_object* v_w_497_, lean_object* v_motive_498_, lean_object* v_s_499_, lean_object* v_hs_500_, lean_object* v_h__1_501_, lean_object* v_h__2_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter(v_w_497_, v_motive_498_, v_s_499_, v_hs_500_, v_h__1_501_, v_h__2_502_);
lean_dec(v_s_499_);
lean_dec(v_w_497_);
return v_res_503_;
}
}
LEAN_EXPORT uint8_t l_BitVec_aandRec___redArg(lean_object* v_w_504_, lean_object* v_x_505_, lean_object* v_y_506_, lean_object* v_s_507_){
_start:
{
uint8_t v___x_508_; 
v___x_508_ = l_Nat_testBit(v_y_506_, v_s_507_);
if (v___x_508_ == 0)
{
lean_dec(v_s_507_);
return v___x_508_;
}
else
{
uint8_t v___x_509_; 
v___x_509_ = l_BitVec_uppcRec___redArg(v_w_504_, v_x_505_, v_s_507_);
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_aandRec___redArg___boxed(lean_object* v_w_510_, lean_object* v_x_511_, lean_object* v_y_512_, lean_object* v_s_513_){
_start:
{
uint8_t v_res_514_; lean_object* v_r_515_; 
v_res_514_ = l_BitVec_aandRec___redArg(v_w_510_, v_x_511_, v_y_512_, v_s_513_);
lean_dec(v_y_512_);
lean_dec(v_x_511_);
lean_dec(v_w_510_);
v_r_515_ = lean_box(v_res_514_);
return v_r_515_;
}
}
LEAN_EXPORT uint8_t l_BitVec_aandRec(lean_object* v_w_516_, lean_object* v_x_517_, lean_object* v_y_518_, lean_object* v_s_519_, lean_object* v_hs_520_){
_start:
{
uint8_t v___x_521_; 
v___x_521_ = l_BitVec_aandRec___redArg(v_w_516_, v_x_517_, v_y_518_, v_s_519_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_BitVec_aandRec___boxed(lean_object* v_w_522_, lean_object* v_x_523_, lean_object* v_y_524_, lean_object* v_s_525_, lean_object* v_hs_526_){
_start:
{
uint8_t v_res_527_; lean_object* v_r_528_; 
v_res_527_ = l_BitVec_aandRec(v_w_522_, v_x_523_, v_y_524_, v_s_525_, v_hs_526_);
lean_dec(v_y_524_);
lean_dec(v_x_523_);
lean_dec(v_w_522_);
v_r_528_ = lean_box(v_res_527_);
return v_r_528_;
}
}
LEAN_EXPORT uint8_t l_BitVec_resRec___redArg(lean_object* v_w_529_, lean_object* v_x_530_, lean_object* v_y_531_, lean_object* v_s_532_){
_start:
{
lean_object* v_zero_533_; uint8_t v_isZero_534_; lean_object* v_one_535_; lean_object* v_n_536_; uint8_t v_isZero_537_; 
v_zero_533_ = lean_unsigned_to_nat(0u);
v_isZero_534_ = lean_nat_dec_eq(v_s_532_, v_zero_533_);
v_one_535_ = lean_unsigned_to_nat(1u);
v_n_536_ = lean_nat_sub(v_s_532_, v_one_535_);
v_isZero_537_ = lean_nat_dec_eq(v_n_536_, v_zero_533_);
if (v_isZero_537_ == 1)
{
uint8_t v___x_538_; 
lean_dec(v_n_536_);
lean_dec(v_s_532_);
v___x_538_ = l_BitVec_aandRec___redArg(v_w_529_, v_x_530_, v_y_531_, v_one_535_);
return v___x_538_;
}
else
{
uint8_t v___x_539_; 
v___x_539_ = l_BitVec_resRec___redArg(v_w_529_, v_x_530_, v_y_531_, v_n_536_);
if (v___x_539_ == 0)
{
uint8_t v___x_540_; 
v___x_540_ = l_BitVec_aandRec___redArg(v_w_529_, v_x_530_, v_y_531_, v_s_532_);
return v___x_540_;
}
else
{
lean_dec(v_s_532_);
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_resRec___redArg___boxed(lean_object* v_w_541_, lean_object* v_x_542_, lean_object* v_y_543_, lean_object* v_s_544_){
_start:
{
uint8_t v_res_545_; lean_object* v_r_546_; 
v_res_545_ = l_BitVec_resRec___redArg(v_w_541_, v_x_542_, v_y_543_, v_s_544_);
lean_dec(v_y_543_);
lean_dec(v_x_542_);
lean_dec(v_w_541_);
v_r_546_ = lean_box(v_res_545_);
return v_r_546_;
}
}
LEAN_EXPORT uint8_t l_BitVec_resRec(lean_object* v_w_547_, lean_object* v_x_548_, lean_object* v_y_549_, lean_object* v_s_550_, lean_object* v_hs_551_, lean_object* v_hslt_552_){
_start:
{
uint8_t v___x_553_; 
v___x_553_ = l_BitVec_resRec___redArg(v_w_547_, v_x_548_, v_y_549_, v_s_550_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_BitVec_resRec___boxed(lean_object* v_w_554_, lean_object* v_x_555_, lean_object* v_y_556_, lean_object* v_s_557_, lean_object* v_hs_558_, lean_object* v_hslt_559_){
_start:
{
uint8_t v_res_560_; lean_object* v_r_561_; 
v_res_560_ = l_BitVec_resRec(v_w_554_, v_x_555_, v_y_556_, v_s_557_, v_hs_558_, v_hslt_559_);
lean_dec(v_y_556_);
lean_dec(v_x_555_);
lean_dec(v_w_554_);
v_r_561_ = lean_box(v_res_560_);
return v_r_561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg(lean_object* v_s_562_, lean_object* v_h__1_563_, lean_object* v_h__2_564_){
_start:
{
lean_object* v_zero_565_; uint8_t v_isZero_566_; 
v_zero_565_ = lean_unsigned_to_nat(0u);
v_isZero_566_ = lean_nat_dec_eq(v_s_562_, v_zero_565_);
if (v_isZero_566_ == 1)
{
lean_object* v___x_567_; 
lean_dec(v_h__2_564_);
v___x_567_ = lean_apply_3(v_h__1_563_, lean_box(0), lean_box(0), lean_box(0));
return v___x_567_;
}
else
{
lean_object* v_one_568_; lean_object* v_n_569_; lean_object* v___x_570_; 
lean_dec(v_h__1_563_);
v_one_568_ = lean_unsigned_to_nat(1u);
v_n_569_ = lean_nat_sub(v_s_562_, v_one_568_);
v___x_570_ = lean_apply_4(v_h__2_564_, v_n_569_, lean_box(0), lean_box(0), lean_box(0));
return v___x_570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg___boxed(lean_object* v_s_571_, lean_object* v_h__1_572_, lean_object* v_h__2_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg(v_s_571_, v_h__1_572_, v_h__2_573_);
lean_dec(v_s_571_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter(lean_object* v_w_575_, lean_object* v_motive_576_, lean_object* v_s_577_, lean_object* v_hs_578_, lean_object* v_hslt_579_, lean_object* v_h__1_580_, lean_object* v_h__2_581_){
_start:
{
lean_object* v_zero_582_; uint8_t v_isZero_583_; 
v_zero_582_ = lean_unsigned_to_nat(0u);
v_isZero_583_ = lean_nat_dec_eq(v_s_577_, v_zero_582_);
if (v_isZero_583_ == 1)
{
lean_object* v___x_584_; 
lean_dec(v_h__2_581_);
v___x_584_ = lean_apply_3(v_h__1_580_, lean_box(0), lean_box(0), lean_box(0));
return v___x_584_;
}
else
{
lean_object* v_one_585_; lean_object* v_n_586_; lean_object* v___x_587_; 
lean_dec(v_h__1_580_);
v_one_585_ = lean_unsigned_to_nat(1u);
v_n_586_ = lean_nat_sub(v_s_577_, v_one_585_);
v___x_587_ = lean_apply_4(v_h__2_581_, v_n_586_, lean_box(0), lean_box(0), lean_box(0));
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___boxed(lean_object* v_w_588_, lean_object* v_motive_589_, lean_object* v_s_590_, lean_object* v_hs_591_, lean_object* v_hslt_592_, lean_object* v_h__1_593_, lean_object* v_h__2_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter(v_w_588_, v_motive_589_, v_s_590_, v_hs_591_, v_hslt_592_, v_h__1_593_, v_h__2_594_);
lean_dec(v_s_590_);
lean_dec(v_w_588_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg(lean_object* v_s_x27_596_, lean_object* v_h__1_597_, lean_object* v_h__2_598_){
_start:
{
lean_object* v_zero_599_; uint8_t v_isZero_600_; 
v_zero_599_ = lean_unsigned_to_nat(0u);
v_isZero_600_ = lean_nat_dec_eq(v_s_x27_596_, v_zero_599_);
if (v_isZero_600_ == 1)
{
lean_object* v___x_601_; 
lean_dec(v_h__2_598_);
v___x_601_ = lean_apply_4(v_h__1_597_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_601_;
}
else
{
lean_object* v_one_602_; lean_object* v_n_603_; lean_object* v___x_604_; 
lean_dec(v_h__1_597_);
v_one_602_ = lean_unsigned_to_nat(1u);
v_n_603_ = lean_nat_sub(v_s_x27_596_, v_one_602_);
v___x_604_ = lean_apply_5(v_h__2_598_, v_n_603_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg___boxed(lean_object* v_s_x27_605_, lean_object* v_h__1_606_, lean_object* v_h__2_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg(v_s_x27_605_, v_h__1_606_, v_h__2_607_);
lean_dec(v_s_x27_605_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter(lean_object* v_w_609_, lean_object* v_s_610_, lean_object* v_motive_611_, lean_object* v_s_x27_612_, lean_object* v_hs_613_, lean_object* v_hslt_614_, lean_object* v_hs0_615_, lean_object* v_h__1_616_, lean_object* v_h__2_617_){
_start:
{
lean_object* v_zero_618_; uint8_t v_isZero_619_; 
v_zero_618_ = lean_unsigned_to_nat(0u);
v_isZero_619_ = lean_nat_dec_eq(v_s_x27_612_, v_zero_618_);
if (v_isZero_619_ == 1)
{
lean_object* v___x_620_; 
lean_dec(v_h__2_617_);
v___x_620_ = lean_apply_4(v_h__1_616_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_620_;
}
else
{
lean_object* v_one_621_; lean_object* v_n_622_; lean_object* v___x_623_; 
lean_dec(v_h__1_616_);
v_one_621_ = lean_unsigned_to_nat(1u);
v_n_622_ = lean_nat_sub(v_s_x27_612_, v_one_621_);
v___x_623_ = lean_apply_5(v_h__2_617_, v_n_622_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___boxed(lean_object* v_w_624_, lean_object* v_s_625_, lean_object* v_motive_626_, lean_object* v_s_x27_627_, lean_object* v_hs_628_, lean_object* v_hslt_629_, lean_object* v_hs0_630_, lean_object* v_h__1_631_, lean_object* v_h__2_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter(v_w_624_, v_s_625_, v_motive_626_, v_s_x27_627_, v_hs_628_, v_hslt_629_, v_hs0_630_, v_h__1_631_, v_h__2_632_);
lean_dec(v_s_x27_627_);
lean_dec(v_s_625_);
lean_dec(v_w_624_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___redArg(lean_object* v_idx_634_, lean_object* v_len_635_, lean_object* v_x_636_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_unsigned_to_nat(1u);
v___x_638_ = l_BitVec_extractLsb_x27___redArg(v_idx_634_, v___x_637_, v_x_636_);
v___x_639_ = l_BitVec_setWidth(v___x_637_, v_len_635_, v___x_638_);
lean_dec(v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___redArg___boxed(lean_object* v_idx_640_, lean_object* v_len_641_, lean_object* v_x_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_BitVec_extractAndExtendBit___redArg(v_idx_640_, v_len_641_, v_x_642_);
lean_dec(v_x_642_);
lean_dec(v_len_641_);
lean_dec(v_idx_640_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit(lean_object* v_w_644_, lean_object* v_idx_645_, lean_object* v_len_646_, lean_object* v_x_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_BitVec_extractAndExtendBit___redArg(v_idx_645_, v_len_646_, v_x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___boxed(lean_object* v_w_649_, lean_object* v_idx_650_, lean_object* v_len_651_, lean_object* v_x_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_BitVec_extractAndExtendBit(v_w_649_, v_idx_650_, v_len_651_, v_x_652_);
lean_dec(v_x_652_);
lean_dec(v_len_651_);
lean_dec(v_idx_650_);
lean_dec(v_w_649_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___redArg(lean_object* v_w_654_, lean_object* v_k_655_, lean_object* v_len_656_, lean_object* v_x_657_, lean_object* v_acc_658_){
_start:
{
lean_object* v___x_659_; lean_object* v_zero_660_; uint8_t v_isZero_661_; 
v___x_659_ = lean_nat_sub(v_w_654_, v_k_655_);
v_zero_660_ = lean_unsigned_to_nat(0u);
v_isZero_661_ = lean_nat_dec_eq(v___x_659_, v_zero_660_);
lean_dec(v___x_659_);
if (v_isZero_661_ == 1)
{
lean_dec(v_k_655_);
return v_acc_658_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v_acc_x27_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_662_ = lean_nat_mul(v_k_655_, v_len_656_);
v___x_663_ = l_BitVec_extractAndExtendBit___redArg(v_k_655_, v_len_656_, v_x_657_);
v_acc_x27_664_ = l_BitVec_append___redArg(v___x_662_, v___x_663_, v_acc_658_);
lean_dec(v_acc_658_);
lean_dec(v___x_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = lean_nat_add(v_k_655_, v___x_665_);
lean_dec(v_k_655_);
v_k_655_ = v___x_666_;
v_acc_658_ = v_acc_x27_664_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___redArg___boxed(lean_object* v_w_668_, lean_object* v_k_669_, lean_object* v_len_670_, lean_object* v_x_671_, lean_object* v_acc_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_BitVec_extractAndExtendAux___redArg(v_w_668_, v_k_669_, v_len_670_, v_x_671_, v_acc_672_);
lean_dec(v_x_671_);
lean_dec(v_len_670_);
lean_dec(v_w_668_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux(lean_object* v_w_674_, lean_object* v_k_675_, lean_object* v_len_676_, lean_object* v_x_677_, lean_object* v_acc_678_, lean_object* v_hle_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_BitVec_extractAndExtendAux___redArg(v_w_674_, v_k_675_, v_len_676_, v_x_677_, v_acc_678_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___boxed(lean_object* v_w_681_, lean_object* v_k_682_, lean_object* v_len_683_, lean_object* v_x_684_, lean_object* v_acc_685_, lean_object* v_hle_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_BitVec_extractAndExtendAux(v_w_681_, v_k_682_, v_len_683_, v_x_684_, v_acc_685_, v_hle_686_);
lean_dec(v_x_684_);
lean_dec(v_len_683_);
lean_dec(v_w_681_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg(lean_object* v_x_688_, lean_object* v_h__1_689_, lean_object* v_h__2_690_){
_start:
{
lean_object* v_zero_691_; uint8_t v_isZero_692_; 
v_zero_691_ = lean_unsigned_to_nat(0u);
v_isZero_692_ = lean_nat_dec_eq(v_x_688_, v_zero_691_);
if (v_isZero_692_ == 1)
{
lean_object* v___x_693_; 
lean_dec(v_h__2_690_);
v___x_693_ = lean_apply_1(v_h__1_689_, lean_box(0));
return v___x_693_;
}
else
{
lean_object* v_one_694_; lean_object* v_n_695_; lean_object* v___x_696_; 
lean_dec(v_h__1_689_);
v_one_694_ = lean_unsigned_to_nat(1u);
v_n_695_ = lean_nat_sub(v_x_688_, v_one_694_);
v___x_696_ = lean_apply_2(v_h__2_690_, v_n_695_, lean_box(0));
return v___x_696_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg___boxed(lean_object* v_x_697_, lean_object* v_h__1_698_, lean_object* v_h__2_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg(v_x_697_, v_h__1_698_, v_h__2_699_);
lean_dec(v_x_697_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter(lean_object* v_motive_701_, lean_object* v_x_702_, lean_object* v_h__1_703_, lean_object* v_h__2_704_){
_start:
{
lean_object* v_zero_705_; uint8_t v_isZero_706_; 
v_zero_705_ = lean_unsigned_to_nat(0u);
v_isZero_706_ = lean_nat_dec_eq(v_x_702_, v_zero_705_);
if (v_isZero_706_ == 1)
{
lean_object* v___x_707_; 
lean_dec(v_h__2_704_);
v___x_707_ = lean_apply_1(v_h__1_703_, lean_box(0));
return v___x_707_;
}
else
{
lean_object* v_one_708_; lean_object* v_n_709_; lean_object* v___x_710_; 
lean_dec(v_h__1_703_);
v_one_708_ = lean_unsigned_to_nat(1u);
v_n_709_ = lean_nat_sub(v_x_702_, v_one_708_);
v___x_710_ = lean_apply_2(v_h__2_704_, v_n_709_, lean_box(0));
return v___x_710_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___boxed(lean_object* v_motive_711_, lean_object* v_x_712_, lean_object* v_h__1_713_, lean_object* v_h__2_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter(v_motive_711_, v_x_712_, v_h__1_713_, v_h__2_714_);
lean_dec(v_x_712_);
return v_res_715_;
}
}
static lean_object* _init_l_BitVec_extractAndExtend___closed__0(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = l_BitVec_ofNat(v___x_716_, v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtend(lean_object* v_w_718_, lean_object* v_len_719_, lean_object* v_x_720_){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = lean_obj_once(&l_BitVec_extractAndExtend___closed__0, &l_BitVec_extractAndExtend___closed__0_once, _init_l_BitVec_extractAndExtend___closed__0);
v___x_723_ = l_BitVec_extractAndExtendAux___redArg(v_w_718_, v___x_721_, v_len_719_, v_x_720_, v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtend___boxed(lean_object* v_w_724_, lean_object* v_len_725_, lean_object* v_x_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_BitVec_extractAndExtend(v_w_724_, v_len_725_, v_x_726_);
lean_dec(v_x_726_);
lean_dec(v_len_725_);
lean_dec(v_w_724_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___redArg(lean_object* v_len_728_, lean_object* v_w_729_, lean_object* v_iterNum_730_, lean_object* v_oldLayer_731_, lean_object* v_newLayer_732_){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_733_ = lean_unsigned_to_nat(2u);
v___x_734_ = lean_nat_mul(v_iterNum_730_, v___x_733_);
v___x_735_ = lean_nat_sub(v_len_728_, v___x_734_);
lean_dec(v___x_734_);
v___x_736_ = lean_unsigned_to_nat(0u);
v___x_737_ = lean_nat_dec_eq(v___x_735_, v___x_736_);
lean_dec(v___x_735_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v_op1_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v_op2_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v_newLayer_x27_747_; lean_object* v___x_748_; 
v___x_738_ = lean_nat_mul(v___x_733_, v_iterNum_730_);
v___x_739_ = lean_nat_mul(v___x_738_, v_w_729_);
v_op1_740_ = l_BitVec_extractLsb_x27___redArg(v___x_739_, v_w_729_, v_oldLayer_731_);
lean_dec(v___x_739_);
v___x_741_ = lean_unsigned_to_nat(1u);
v___x_742_ = lean_nat_add(v___x_738_, v___x_741_);
lean_dec(v___x_738_);
v___x_743_ = lean_nat_mul(v___x_742_, v_w_729_);
lean_dec(v___x_742_);
v_op2_744_ = l_BitVec_extractLsb_x27___redArg(v___x_743_, v_w_729_, v_oldLayer_731_);
lean_dec(v___x_743_);
v___x_745_ = lean_nat_mul(v_iterNum_730_, v_w_729_);
v___x_746_ = l_BitVec_add(v_w_729_, v_op1_740_, v_op2_744_);
lean_dec(v_op2_744_);
lean_dec(v_op1_740_);
v_newLayer_x27_747_ = l_BitVec_append___redArg(v___x_745_, v___x_746_, v_newLayer_732_);
lean_dec(v_newLayer_732_);
lean_dec(v___x_746_);
lean_dec(v___x_745_);
v___x_748_ = lean_nat_add(v_iterNum_730_, v___x_741_);
lean_dec(v_iterNum_730_);
v_iterNum_730_ = v___x_748_;
v_newLayer_732_ = v_newLayer_x27_747_;
goto _start;
}
else
{
lean_dec(v_iterNum_730_);
return v_newLayer_732_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___redArg___boxed(lean_object* v_len_750_, lean_object* v_w_751_, lean_object* v_iterNum_752_, lean_object* v_oldLayer_753_, lean_object* v_newLayer_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_BitVec_cpopLayer___redArg(v_len_750_, v_w_751_, v_iterNum_752_, v_oldLayer_753_, v_newLayer_754_);
lean_dec(v_oldLayer_753_);
lean_dec(v_w_751_);
lean_dec(v_len_750_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer(lean_object* v_len_756_, lean_object* v_w_757_, lean_object* v_iterNum_758_, lean_object* v_oldLayer_759_, lean_object* v_newLayer_760_, lean_object* v_hold_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_BitVec_cpopLayer___redArg(v_len_756_, v_w_757_, v_iterNum_758_, v_oldLayer_759_, v_newLayer_760_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___boxed(lean_object* v_len_763_, lean_object* v_w_764_, lean_object* v_iterNum_765_, lean_object* v_oldLayer_766_, lean_object* v_newLayer_767_, lean_object* v_hold_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_BitVec_cpopLayer(v_len_763_, v_w_764_, v_iterNum_765_, v_oldLayer_766_, v_newLayer_767_, v_hold_768_);
lean_dec(v_oldLayer_766_);
lean_dec(v_w_764_);
lean_dec(v_len_763_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopTree(lean_object* v_len_770_, lean_object* v_w_771_, lean_object* v_l_772_){
_start:
{
lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = lean_nat_dec_eq(v_len_770_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = lean_unsigned_to_nat(1u);
v___x_776_ = lean_nat_dec_eq(v_len_770_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_777_ = lean_nat_add(v_len_770_, v___x_775_);
v___x_778_ = lean_nat_shiftr(v___x_777_, v___x_775_);
lean_dec(v___x_777_);
v___x_779_ = lean_obj_once(&l_BitVec_extractAndExtend___closed__0, &l_BitVec_extractAndExtend___closed__0_once, _init_l_BitVec_extractAndExtend___closed__0);
v___x_780_ = l_BitVec_cpopLayer___redArg(v_len_770_, v_w_771_, v___x_773_, v_l_772_, v___x_779_);
lean_dec(v_l_772_);
lean_dec(v_len_770_);
v_len_770_ = v___x_778_;
v_l_772_ = v___x_780_;
goto _start;
}
else
{
lean_dec(v_len_770_);
return v_l_772_;
}
}
else
{
lean_object* v___x_782_; 
lean_dec(v_l_772_);
lean_dec(v_len_770_);
v___x_782_ = l_BitVec_ofNat(v_w_771_, v___x_773_);
return v___x_782_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopTree___boxed(lean_object* v_len_783_, lean_object* v_w_784_, lean_object* v_l_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_BitVec_cpopTree(v_len_783_, v_w_784_, v_l_785_);
lean_dec(v_w_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopRec(lean_object* v_w_787_, lean_object* v_x_788_){
_start:
{
lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_dec_lt(v___x_789_, v_w_787_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_791_ = lean_unsigned_to_nat(0u);
v___x_792_ = lean_nat_dec_lt(v___x_791_, v_w_787_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; 
v___x_793_ = l_BitVec_ofNat(v_w_787_, v___x_791_);
lean_dec(v_w_787_);
return v___x_793_;
}
else
{
lean_dec(v_w_787_);
lean_inc(v_x_788_);
return v_x_788_;
}
}
else
{
lean_object* v_extendedBits_794_; lean_object* v___x_795_; 
v_extendedBits_794_ = l_BitVec_extractAndExtend(v_w_787_, v_w_787_, v_x_788_);
lean_inc(v_w_787_);
v___x_795_ = l_BitVec_cpopTree(v_w_787_, v_w_787_, v_extendedBits_794_);
lean_dec(v_w_787_);
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopRec___boxed(lean_object* v_w_796_, lean_object* v_x_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_BitVec_cpopRec(v_w_796_, v_x_797_);
lean_dec(v_x_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(lean_object* v_w_799_, lean_object* v_x_800_, lean_object* v_rem_801_, lean_object* v_acc_802_){
_start:
{
lean_object* v_zero_803_; uint8_t v_isZero_804_; 
v_zero_803_ = lean_unsigned_to_nat(0u);
v_isZero_804_ = lean_nat_dec_eq(v_rem_801_, v_zero_803_);
if (v_isZero_804_ == 1)
{
lean_dec(v_rem_801_);
return v_acc_802_;
}
else
{
lean_object* v_one_805_; lean_object* v_n_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_one_805_ = lean_unsigned_to_nat(1u);
v_n_806_ = lean_nat_sub(v_rem_801_, v_one_805_);
lean_dec(v_rem_801_);
v___x_807_ = lean_nat_mul(v_n_806_, v_w_799_);
v___x_808_ = l_BitVec_extractLsb_x27___redArg(v___x_807_, v_w_799_, v_x_800_);
lean_dec(v___x_807_);
v___x_809_ = l_BitVec_add(v_w_799_, v_acc_802_, v___x_808_);
lean_dec(v___x_808_);
lean_dec(v_acc_802_);
v_rem_801_ = v_n_806_;
v_acc_802_ = v___x_809_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg___boxed(lean_object* v_w_811_, lean_object* v_x_812_, lean_object* v_rem_813_, lean_object* v_acc_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_811_, v_x_812_, v_rem_813_, v_acc_814_);
lean_dec(v_x_812_);
lean_dec(v_w_811_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux(lean_object* v_l_816_, lean_object* v_w_817_, lean_object* v_x_818_, lean_object* v_rem_819_, lean_object* v_acc_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_817_, v_x_818_, v_rem_819_, v_acc_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___boxed(lean_object* v_l_822_, lean_object* v_w_823_, lean_object* v_x_824_, lean_object* v_rem_825_, lean_object* v_acc_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux(v_l_822_, v_w_823_, v_x_824_, v_rem_825_, v_acc_826_);
lean_dec(v_x_824_);
lean_dec(v_w_823_);
lean_dec(v_l_822_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec(lean_object* v_l_828_, lean_object* v_w_829_, lean_object* v_x_830_){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = lean_unsigned_to_nat(0u);
v___x_832_ = l_BitVec_ofNat(v_w_829_, v___x_831_);
v___x_833_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_829_, v_x_830_, v_l_828_, v___x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec___boxed(lean_object* v_l_834_, lean_object* v_w_835_, lean_object* v_x_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec(v_l_834_, v_w_835_, v_x_836_);
lean_dec(v_x_836_);
lean_dec(v_w_835_);
return v_res_837_;
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
