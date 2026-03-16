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
lean_object* v___x_145_; 
v___x_145_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___redArg(v_s_142_, v_h__1_143_, v_h__2_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___boxed(lean_object* v_motive_146_, lean_object* v_s_147_, lean_object* v_h__1_148_, lean_object* v_h__2_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter(v_motive_146_, v_s_147_, v_h__1_148_, v_h__2_149_);
lean_dec(v_s_147_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftRec(lean_object* v_w_u2081_151_, lean_object* v_w_u2082_152_, lean_object* v_x_153_, lean_object* v_y_154_, lean_object* v_n_155_){
_start:
{
lean_object* v___x_156_; lean_object* v_shiftAmt_157_; lean_object* v_zero_158_; uint8_t v_isZero_159_; 
v___x_156_ = l_BitVec_twoPow(v_w_u2082_152_, v_n_155_);
v_shiftAmt_157_ = lean_nat_land(v_y_154_, v___x_156_);
lean_dec(v___x_156_);
v_zero_158_ = lean_unsigned_to_nat(0u);
v_isZero_159_ = lean_nat_dec_eq(v_n_155_, v_zero_158_);
if (v_isZero_159_ == 1)
{
lean_object* v___x_160_; 
v___x_160_ = l_BitVec_shiftLeft(v_w_u2081_151_, v_x_153_, v_shiftAmt_157_);
lean_dec(v_shiftAmt_157_);
return v___x_160_;
}
else
{
lean_object* v_one_161_; lean_object* v_n_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_one_161_ = lean_unsigned_to_nat(1u);
v_n_162_ = lean_nat_sub(v_n_155_, v_one_161_);
v___x_163_ = l_BitVec_shiftLeftRec(v_w_u2081_151_, v_w_u2082_152_, v_x_153_, v_y_154_, v_n_162_);
lean_dec(v_n_162_);
v___x_164_ = l_BitVec_shiftLeft(v_w_u2081_151_, v___x_163_, v_shiftAmt_157_);
lean_dec(v_shiftAmt_157_);
lean_dec(v___x_163_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftRec___boxed(lean_object* v_w_u2081_165_, lean_object* v_w_u2082_166_, lean_object* v_x_167_, lean_object* v_y_168_, lean_object* v_n_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_BitVec_shiftLeftRec(v_w_u2081_165_, v_w_u2082_166_, v_x_167_, v_y_168_, v_n_169_);
lean_dec(v_n_169_);
lean_dec(v_y_168_);
lean_dec(v_x_167_);
lean_dec(v_w_u2082_166_);
lean_dec(v_w_u2081_165_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_BitVec_DivModState_init(lean_object* v_w_171_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = l_BitVec_ofNat(v_w_171_, v___x_172_);
lean_inc(v___x_173_);
v___x_174_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_174_, 0, v_w_171_);
lean_ctor_set(v___x_174_, 1, v___x_172_);
lean_ctor_set(v___x_174_, 2, v___x_173_);
lean_ctor_set(v___x_174_, 3, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_BitVec_divSubtractShift(lean_object* v_w_175_, lean_object* v_args_176_, lean_object* v_qr_177_){
_start:
{
lean_object* v_n_178_; lean_object* v_d_179_; lean_object* v_wn_180_; lean_object* v_wr_181_; lean_object* v_q_182_; lean_object* v_r_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_204_; 
v_n_178_ = lean_ctor_get(v_args_176_, 0);
v_d_179_ = lean_ctor_get(v_args_176_, 1);
v_wn_180_ = lean_ctor_get(v_qr_177_, 0);
v_wr_181_ = lean_ctor_get(v_qr_177_, 1);
v_q_182_ = lean_ctor_get(v_qr_177_, 2);
v_r_183_ = lean_ctor_get(v_qr_177_, 3);
v_isSharedCheck_204_ = !lean_is_exclusive(v_qr_177_);
if (v_isSharedCheck_204_ == 0)
{
v___x_185_ = v_qr_177_;
v_isShared_186_ = v_isSharedCheck_204_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_r_183_);
lean_inc(v_q_182_);
lean_inc(v_wr_181_);
lean_inc(v_wn_180_);
lean_dec(v_qr_177_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_204_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v_wn_188_; lean_object* v_wr_189_; uint8_t v___x_190_; lean_object* v_r_x27_191_; uint8_t v___x_192_; 
v___x_187_ = lean_unsigned_to_nat(1u);
v_wn_188_ = lean_nat_sub(v_wn_180_, v___x_187_);
lean_dec(v_wn_180_);
v_wr_189_ = lean_nat_add(v_wr_181_, v___x_187_);
lean_dec(v_wr_181_);
v___x_190_ = l_Nat_testBit(v_n_178_, v_wn_188_);
v_r_x27_191_ = l_BitVec_shiftConcat(v_w_175_, v_r_183_, v___x_190_);
lean_dec(v_r_183_);
v___x_192_ = lean_nat_dec_lt(v_r_x27_191_, v_d_179_);
if (v___x_192_ == 0)
{
uint8_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_193_ = 1;
v___x_194_ = l_BitVec_shiftConcat(v_w_175_, v_q_182_, v___x_193_);
lean_dec(v_q_182_);
v___x_195_ = l_BitVec_sub(v_w_175_, v_r_x27_191_, v_d_179_);
lean_dec(v_r_x27_191_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 3, v___x_195_);
lean_ctor_set(v___x_185_, 2, v___x_194_);
lean_ctor_set(v___x_185_, 1, v_wr_189_);
lean_ctor_set(v___x_185_, 0, v_wn_188_);
v___x_197_ = v___x_185_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_wn_188_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_wr_189_);
lean_ctor_set(v_reuseFailAlloc_198_, 2, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_198_, 3, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
else
{
uint8_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_199_ = 0;
v___x_200_ = l_BitVec_shiftConcat(v_w_175_, v_q_182_, v___x_199_);
lean_dec(v_q_182_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 3, v_r_x27_191_);
lean_ctor_set(v___x_185_, 2, v___x_200_);
lean_ctor_set(v___x_185_, 1, v_wr_189_);
lean_ctor_set(v___x_185_, 0, v_wn_188_);
v___x_202_ = v___x_185_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_wn_188_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_wr_189_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_203_, 3, v_r_x27_191_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_divSubtractShift___boxed(lean_object* v_w_205_, lean_object* v_args_206_, lean_object* v_qr_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_BitVec_divSubtractShift(v_w_205_, v_args_206_, v_qr_207_);
lean_dec_ref(v_args_206_);
lean_dec(v_w_205_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter___redArg(lean_object* v_args_209_, lean_object* v_h__1_210_){
_start:
{
lean_object* v_n_211_; lean_object* v_d_212_; lean_object* v___x_213_; 
v_n_211_ = lean_ctor_get(v_args_209_, 0);
lean_inc(v_n_211_);
v_d_212_ = lean_ctor_get(v_args_209_, 1);
lean_inc(v_d_212_);
lean_dec_ref(v_args_209_);
v___x_213_ = lean_apply_2(v_h__1_210_, v_n_211_, v_d_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter(lean_object* v_w_214_, lean_object* v_motive_215_, lean_object* v_args_216_, lean_object* v_h__1_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter___redArg(v_args_216_, v_h__1_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter___boxed(lean_object* v_w_219_, lean_object* v_motive_220_, lean_object* v_args_221_, lean_object* v_h__1_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter(v_w_219_, v_motive_220_, v_args_221_, v_h__1_222_);
lean_dec(v_w_219_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_BitVec_divRec(lean_object* v_w_224_, lean_object* v_m_225_, lean_object* v_args_226_, lean_object* v_qr_227_){
_start:
{
lean_object* v_zero_228_; uint8_t v_isZero_229_; 
v_zero_228_ = lean_unsigned_to_nat(0u);
v_isZero_229_ = lean_nat_dec_eq(v_m_225_, v_zero_228_);
if (v_isZero_229_ == 1)
{
lean_dec(v_m_225_);
return v_qr_227_;
}
else
{
lean_object* v_one_230_; lean_object* v_n_231_; lean_object* v___x_232_; 
v_one_230_ = lean_unsigned_to_nat(1u);
v_n_231_ = lean_nat_sub(v_m_225_, v_one_230_);
lean_dec(v_m_225_);
v___x_232_ = l_BitVec_divSubtractShift(v_w_224_, v_args_226_, v_qr_227_);
v_m_225_ = v_n_231_;
v_qr_227_ = v___x_232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_divRec___boxed(lean_object* v_w_234_, lean_object* v_m_235_, lean_object* v_args_236_, lean_object* v_qr_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_BitVec_divRec(v_w_234_, v_m_235_, v_args_236_, v_qr_237_);
lean_dec_ref(v_args_236_);
lean_dec(v_w_234_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRightRec(lean_object* v_w_u2081_239_, lean_object* v_w_u2082_240_, lean_object* v_x_241_, lean_object* v_y_242_, lean_object* v_n_243_){
_start:
{
lean_object* v___x_244_; lean_object* v_shiftAmt_245_; lean_object* v_zero_246_; uint8_t v_isZero_247_; 
v___x_244_ = l_BitVec_twoPow(v_w_u2082_240_, v_n_243_);
v_shiftAmt_245_ = lean_nat_land(v_y_242_, v___x_244_);
lean_dec(v___x_244_);
v_zero_246_ = lean_unsigned_to_nat(0u);
v_isZero_247_ = lean_nat_dec_eq(v_n_243_, v_zero_246_);
if (v_isZero_247_ == 1)
{
lean_object* v___x_248_; 
v___x_248_ = l_BitVec_sshiftRight(v_w_u2081_239_, v_x_241_, v_shiftAmt_245_);
lean_dec(v_shiftAmt_245_);
return v___x_248_;
}
else
{
lean_object* v_one_249_; lean_object* v_n_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_one_249_ = lean_unsigned_to_nat(1u);
v_n_250_ = lean_nat_sub(v_n_243_, v_one_249_);
v___x_251_ = l_BitVec_sshiftRightRec(v_w_u2081_239_, v_w_u2082_240_, v_x_241_, v_y_242_, v_n_250_);
lean_dec(v_n_250_);
v___x_252_ = l_BitVec_sshiftRight(v_w_u2081_239_, v___x_251_, v_shiftAmt_245_);
lean_dec(v_shiftAmt_245_);
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRightRec___boxed(lean_object* v_w_u2081_253_, lean_object* v_w_u2082_254_, lean_object* v_x_255_, lean_object* v_y_256_, lean_object* v_n_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_BitVec_sshiftRightRec(v_w_u2081_253_, v_w_u2082_254_, v_x_255_, v_y_256_, v_n_257_);
lean_dec(v_n_257_);
lean_dec(v_y_256_);
lean_dec(v_w_u2082_254_);
lean_dec(v_w_u2081_253_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___redArg(lean_object* v_w_u2082_259_, lean_object* v_x_260_, lean_object* v_y_261_, lean_object* v_n_262_){
_start:
{
lean_object* v___x_263_; lean_object* v_shiftAmt_264_; lean_object* v_zero_265_; uint8_t v_isZero_266_; 
v___x_263_ = l_BitVec_twoPow(v_w_u2082_259_, v_n_262_);
v_shiftAmt_264_ = lean_nat_land(v_y_261_, v___x_263_);
lean_dec(v___x_263_);
v_zero_265_ = lean_unsigned_to_nat(0u);
v_isZero_266_ = lean_nat_dec_eq(v_n_262_, v_zero_265_);
if (v_isZero_266_ == 1)
{
lean_object* v___x_267_; 
v___x_267_ = lean_nat_shiftr(v_x_260_, v_shiftAmt_264_);
lean_dec(v_shiftAmt_264_);
return v___x_267_;
}
else
{
lean_object* v_one_268_; lean_object* v_n_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_one_268_ = lean_unsigned_to_nat(1u);
v_n_269_ = lean_nat_sub(v_n_262_, v_one_268_);
v___x_270_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_259_, v_x_260_, v_y_261_, v_n_269_);
lean_dec(v_n_269_);
v___x_271_ = lean_nat_shiftr(v___x_270_, v_shiftAmt_264_);
lean_dec(v_shiftAmt_264_);
lean_dec(v___x_270_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___redArg___boxed(lean_object* v_w_u2082_272_, lean_object* v_x_273_, lean_object* v_y_274_, lean_object* v_n_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_272_, v_x_273_, v_y_274_, v_n_275_);
lean_dec(v_n_275_);
lean_dec(v_y_274_);
lean_dec(v_x_273_);
lean_dec(v_w_u2082_272_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec(lean_object* v_w_u2081_277_, lean_object* v_w_u2082_278_, lean_object* v_x_279_, lean_object* v_y_280_, lean_object* v_n_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_278_, v_x_279_, v_y_280_, v_n_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___boxed(lean_object* v_w_u2081_283_, lean_object* v_w_u2082_284_, lean_object* v_x_285_, lean_object* v_y_286_, lean_object* v_n_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_BitVec_ushiftRightRec(v_w_u2081_283_, v_w_u2082_284_, v_x_285_, v_y_286_, v_n_287_);
lean_dec(v_n_287_);
lean_dec(v_y_286_);
lean_dec(v_x_285_);
lean_dec(v_w_u2082_284_);
lean_dec(v_w_u2081_283_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg(uint8_t v_x_289_, uint8_t v_x_290_, lean_object* v_h__1_291_, lean_object* v_h__2_292_, lean_object* v_h__3_293_, lean_object* v_h__4_294_){
_start:
{
if (v_x_289_ == 0)
{
lean_dec(v_h__4_294_);
lean_dec(v_h__3_293_);
if (v_x_290_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec(v_h__2_292_);
v___x_295_ = lean_box(0);
v___x_296_ = lean_apply_1(v_h__1_291_, v___x_295_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec(v_h__1_291_);
v___x_297_ = lean_box(0);
v___x_298_ = lean_apply_1(v_h__2_292_, v___x_297_);
return v___x_298_;
}
}
else
{
lean_dec(v_h__2_292_);
lean_dec(v_h__1_291_);
if (v_x_290_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec(v_h__4_294_);
v___x_299_ = lean_box(0);
v___x_300_ = lean_apply_1(v_h__3_293_, v___x_299_);
return v___x_300_;
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec(v_h__3_293_);
v___x_301_ = lean_box(0);
v___x_302_ = lean_apply_1(v_h__4_294_, v___x_301_);
return v___x_302_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg___boxed(lean_object* v_x_303_, lean_object* v_x_304_, lean_object* v_h__1_305_, lean_object* v_h__2_306_, lean_object* v_h__3_307_, lean_object* v_h__4_308_){
_start:
{
uint8_t v_x_42__boxed_309_; uint8_t v_x_43__boxed_310_; lean_object* v_res_311_; 
v_x_42__boxed_309_ = lean_unbox(v_x_303_);
v_x_43__boxed_310_ = lean_unbox(v_x_304_);
v_res_311_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg(v_x_42__boxed_309_, v_x_43__boxed_310_, v_h__1_305_, v_h__2_306_, v_h__3_307_, v_h__4_308_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter(lean_object* v_motive_312_, uint8_t v_x_313_, uint8_t v_x_314_, lean_object* v_h__1_315_, lean_object* v_h__2_316_, lean_object* v_h__3_317_, lean_object* v_h__4_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg(v_x_313_, v_x_314_, v_h__1_315_, v_h__2_316_, v_h__3_317_, v_h__4_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___boxed(lean_object* v_motive_320_, lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_h__1_323_, lean_object* v_h__2_324_, lean_object* v_h__3_325_, lean_object* v_h__4_326_){
_start:
{
uint8_t v_x_64__boxed_327_; uint8_t v_x_65__boxed_328_; lean_object* v_res_329_; 
v_x_64__boxed_327_ = lean_unbox(v_x_321_);
v_x_65__boxed_328_ = lean_unbox(v_x_322_);
v_res_329_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter(v_motive_320_, v_x_64__boxed_327_, v_x_65__boxed_328_, v_h__1_323_, v_h__2_324_, v_h__3_325_, v_h__4_326_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg(uint8_t v_x_330_, uint8_t v_x_331_, lean_object* v_h__1_332_, lean_object* v_h__2_333_, lean_object* v_h__3_334_, lean_object* v_h__4_335_){
_start:
{
if (v_x_330_ == 0)
{
lean_dec(v_h__4_335_);
lean_dec(v_h__3_334_);
if (v_x_331_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec(v_h__2_333_);
v___x_336_ = lean_box(0);
v___x_337_ = lean_apply_1(v_h__1_332_, v___x_336_);
return v___x_337_;
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec(v_h__1_332_);
v___x_338_ = lean_box(0);
v___x_339_ = lean_apply_1(v_h__2_333_, v___x_338_);
return v___x_339_;
}
}
else
{
lean_dec(v_h__2_333_);
lean_dec(v_h__1_332_);
if (v_x_331_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec(v_h__4_335_);
v___x_340_ = lean_box(0);
v___x_341_ = lean_apply_1(v_h__3_334_, v___x_340_);
return v___x_341_;
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec(v_h__3_334_);
v___x_342_ = lean_box(0);
v___x_343_ = lean_apply_1(v_h__4_335_, v___x_342_);
return v___x_343_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg___boxed(lean_object* v_x_344_, lean_object* v_x_345_, lean_object* v_h__1_346_, lean_object* v_h__2_347_, lean_object* v_h__3_348_, lean_object* v_h__4_349_){
_start:
{
uint8_t v_x_42__boxed_350_; uint8_t v_x_43__boxed_351_; lean_object* v_res_352_; 
v_x_42__boxed_350_ = lean_unbox(v_x_344_);
v_x_43__boxed_351_ = lean_unbox(v_x_345_);
v_res_352_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg(v_x_42__boxed_350_, v_x_43__boxed_351_, v_h__1_346_, v_h__2_347_, v_h__3_348_, v_h__4_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter(lean_object* v_motive_353_, uint8_t v_x_354_, uint8_t v_x_355_, lean_object* v_h__1_356_, lean_object* v_h__2_357_, lean_object* v_h__3_358_, lean_object* v_h__4_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg(v_x_354_, v_x_355_, v_h__1_356_, v_h__2_357_, v_h__3_358_, v_h__4_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___boxed(lean_object* v_motive_361_, lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v_h__1_364_, lean_object* v_h__2_365_, lean_object* v_h__3_366_, lean_object* v_h__4_367_){
_start:
{
uint8_t v_x_64__boxed_368_; uint8_t v_x_65__boxed_369_; lean_object* v_res_370_; 
v_x_64__boxed_368_ = lean_unbox(v_x_362_);
v_x_65__boxed_369_ = lean_unbox(v_x_363_);
v_res_370_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter(v_motive_361_, v_x_64__boxed_368_, v_x_65__boxed_369_, v_h__1_364_, v_h__2_365_, v_h__3_366_, v_h__4_367_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg(uint8_t v_x_371_, uint8_t v_x_372_, lean_object* v_h__1_373_, lean_object* v_h__2_374_, lean_object* v_h__3_375_, lean_object* v_h__4_376_){
_start:
{
if (v_x_371_ == 0)
{
lean_dec(v_h__4_376_);
lean_dec(v_h__3_375_);
if (v_x_372_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec(v_h__2_374_);
v___x_377_ = lean_box(0);
v___x_378_ = lean_apply_1(v_h__1_373_, v___x_377_);
return v___x_378_;
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_dec(v_h__1_373_);
v___x_379_ = lean_box(0);
v___x_380_ = lean_apply_1(v_h__2_374_, v___x_379_);
return v___x_380_;
}
}
else
{
lean_dec(v_h__2_374_);
lean_dec(v_h__1_373_);
if (v_x_372_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_382_; 
lean_dec(v_h__4_376_);
v___x_381_ = lean_box(0);
v___x_382_ = lean_apply_1(v_h__3_375_, v___x_381_);
return v___x_382_;
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec(v_h__3_375_);
v___x_383_ = lean_box(0);
v___x_384_ = lean_apply_1(v_h__4_376_, v___x_383_);
return v___x_384_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg___boxed(lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v_h__1_387_, lean_object* v_h__2_388_, lean_object* v_h__3_389_, lean_object* v_h__4_390_){
_start:
{
uint8_t v_x_42__boxed_391_; uint8_t v_x_43__boxed_392_; lean_object* v_res_393_; 
v_x_42__boxed_391_ = lean_unbox(v_x_385_);
v_x_43__boxed_392_ = lean_unbox(v_x_386_);
v_res_393_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg(v_x_42__boxed_391_, v_x_43__boxed_392_, v_h__1_387_, v_h__2_388_, v_h__3_389_, v_h__4_390_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter(lean_object* v_motive_394_, uint8_t v_x_395_, uint8_t v_x_396_, lean_object* v_h__1_397_, lean_object* v_h__2_398_, lean_object* v_h__3_399_, lean_object* v_h__4_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg(v_x_395_, v_x_396_, v_h__1_397_, v_h__2_398_, v_h__3_399_, v_h__4_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___boxed(lean_object* v_motive_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_h__1_405_, lean_object* v_h__2_406_, lean_object* v_h__3_407_, lean_object* v_h__4_408_){
_start:
{
uint8_t v_x_64__boxed_409_; uint8_t v_x_65__boxed_410_; lean_object* v_res_411_; 
v_x_64__boxed_409_ = lean_unbox(v_x_403_);
v_x_65__boxed_410_ = lean_unbox(v_x_404_);
v_res_411_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter(v_motive_402_, v_x_64__boxed_409_, v_x_65__boxed_410_, v_h__1_405_, v_h__2_406_, v_h__3_407_, v_h__4_408_);
return v_res_411_;
}
}
LEAN_EXPORT uint8_t l_BitVec_uppcRec___redArg(lean_object* v_w_412_, lean_object* v_x_413_, lean_object* v_s_414_){
_start:
{
lean_object* v_zero_415_; uint8_t v_isZero_416_; 
v_zero_415_ = lean_unsigned_to_nat(0u);
v_isZero_416_ = lean_nat_dec_eq(v_s_414_, v_zero_415_);
if (v_isZero_416_ == 1)
{
uint8_t v___x_417_; 
lean_dec(v_s_414_);
v___x_417_ = lean_nat_dec_lt(v_zero_415_, v_w_412_);
if (v___x_417_ == 0)
{
return v___x_417_;
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_418_ = lean_unsigned_to_nat(1u);
v___x_419_ = lean_nat_sub(v_w_412_, v___x_418_);
v___x_420_ = l_Nat_testBit(v_x_413_, v___x_419_);
lean_dec(v___x_419_);
return v___x_420_;
}
}
else
{
lean_object* v_one_421_; lean_object* v_n_422_; lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v_one_421_ = lean_unsigned_to_nat(1u);
v_n_422_ = lean_nat_sub(v_s_414_, v_one_421_);
lean_dec(v_s_414_);
v___x_423_ = lean_nat_sub(v_w_412_, v_one_421_);
v___x_424_ = lean_nat_sub(v___x_423_, v_n_422_);
lean_dec(v___x_423_);
v___x_425_ = l_Nat_testBit(v_x_413_, v___x_424_);
lean_dec(v___x_424_);
if (v___x_425_ == 0)
{
v_s_414_ = v_n_422_;
goto _start;
}
else
{
lean_dec(v_n_422_);
return v___x_425_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_uppcRec___redArg___boxed(lean_object* v_w_427_, lean_object* v_x_428_, lean_object* v_s_429_){
_start:
{
uint8_t v_res_430_; lean_object* v_r_431_; 
v_res_430_ = l_BitVec_uppcRec___redArg(v_w_427_, v_x_428_, v_s_429_);
lean_dec(v_x_428_);
lean_dec(v_w_427_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT uint8_t l_BitVec_uppcRec(lean_object* v_w_432_, lean_object* v_x_433_, lean_object* v_s_434_, lean_object* v_hs_435_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = l_BitVec_uppcRec___redArg(v_w_432_, v_x_433_, v_s_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_BitVec_uppcRec___boxed(lean_object* v_w_437_, lean_object* v_x_438_, lean_object* v_s_439_, lean_object* v_hs_440_){
_start:
{
uint8_t v_res_441_; lean_object* v_r_442_; 
v_res_441_ = l_BitVec_uppcRec(v_w_437_, v_x_438_, v_s_439_, v_hs_440_);
lean_dec(v_x_438_);
lean_dec(v_w_437_);
v_r_442_ = lean_box(v_res_441_);
return v_r_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___redArg(lean_object* v_s_443_, lean_object* v_h__1_444_, lean_object* v_h__2_445_){
_start:
{
lean_object* v_zero_446_; uint8_t v_isZero_447_; 
v_zero_446_ = lean_unsigned_to_nat(0u);
v_isZero_447_ = lean_nat_dec_eq(v_s_443_, v_zero_446_);
if (v_isZero_447_ == 1)
{
lean_object* v___x_448_; 
lean_dec(v_h__2_445_);
v___x_448_ = lean_apply_1(v_h__1_444_, lean_box(0));
return v___x_448_;
}
else
{
lean_object* v_one_449_; lean_object* v_n_450_; lean_object* v___x_451_; 
lean_dec(v_h__1_444_);
v_one_449_ = lean_unsigned_to_nat(1u);
v_n_450_ = lean_nat_sub(v_s_443_, v_one_449_);
v___x_451_ = lean_apply_2(v_h__2_445_, v_n_450_, lean_box(0));
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___redArg___boxed(lean_object* v_s_452_, lean_object* v_h__1_453_, lean_object* v_h__2_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___redArg(v_s_452_, v_h__1_453_, v_h__2_454_);
lean_dec(v_s_452_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter(lean_object* v_w_456_, lean_object* v_motive_457_, lean_object* v_s_458_, lean_object* v_hs_459_, lean_object* v_h__1_460_, lean_object* v_h__2_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___redArg(v_s_458_, v_h__1_460_, v_h__2_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___boxed(lean_object* v_w_463_, lean_object* v_motive_464_, lean_object* v_s_465_, lean_object* v_hs_466_, lean_object* v_h__1_467_, lean_object* v_h__2_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter(v_w_463_, v_motive_464_, v_s_465_, v_hs_466_, v_h__1_467_, v_h__2_468_);
lean_dec(v_s_465_);
lean_dec(v_w_463_);
return v_res_469_;
}
}
LEAN_EXPORT uint8_t l_BitVec_aandRec___redArg(lean_object* v_w_470_, lean_object* v_x_471_, lean_object* v_y_472_, lean_object* v_s_473_){
_start:
{
uint8_t v___x_474_; 
v___x_474_ = l_Nat_testBit(v_y_472_, v_s_473_);
if (v___x_474_ == 0)
{
lean_dec(v_s_473_);
return v___x_474_;
}
else
{
uint8_t v___x_475_; 
v___x_475_ = l_BitVec_uppcRec___redArg(v_w_470_, v_x_471_, v_s_473_);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_aandRec___redArg___boxed(lean_object* v_w_476_, lean_object* v_x_477_, lean_object* v_y_478_, lean_object* v_s_479_){
_start:
{
uint8_t v_res_480_; lean_object* v_r_481_; 
v_res_480_ = l_BitVec_aandRec___redArg(v_w_476_, v_x_477_, v_y_478_, v_s_479_);
lean_dec(v_y_478_);
lean_dec(v_x_477_);
lean_dec(v_w_476_);
v_r_481_ = lean_box(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT uint8_t l_BitVec_aandRec(lean_object* v_w_482_, lean_object* v_x_483_, lean_object* v_y_484_, lean_object* v_s_485_, lean_object* v_hs_486_){
_start:
{
uint8_t v___x_487_; 
v___x_487_ = l_BitVec_aandRec___redArg(v_w_482_, v_x_483_, v_y_484_, v_s_485_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_BitVec_aandRec___boxed(lean_object* v_w_488_, lean_object* v_x_489_, lean_object* v_y_490_, lean_object* v_s_491_, lean_object* v_hs_492_){
_start:
{
uint8_t v_res_493_; lean_object* v_r_494_; 
v_res_493_ = l_BitVec_aandRec(v_w_488_, v_x_489_, v_y_490_, v_s_491_, v_hs_492_);
lean_dec(v_y_490_);
lean_dec(v_x_489_);
lean_dec(v_w_488_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT uint8_t l_BitVec_resRec___redArg(lean_object* v_w_495_, lean_object* v_x_496_, lean_object* v_y_497_, lean_object* v_s_498_){
_start:
{
lean_object* v_zero_499_; uint8_t v_isZero_500_; lean_object* v_one_501_; lean_object* v_n_502_; uint8_t v_isZero_503_; 
v_zero_499_ = lean_unsigned_to_nat(0u);
v_isZero_500_ = lean_nat_dec_eq(v_s_498_, v_zero_499_);
v_one_501_ = lean_unsigned_to_nat(1u);
v_n_502_ = lean_nat_sub(v_s_498_, v_one_501_);
v_isZero_503_ = lean_nat_dec_eq(v_n_502_, v_zero_499_);
if (v_isZero_503_ == 1)
{
uint8_t v___x_504_; 
lean_dec(v_n_502_);
lean_dec(v_s_498_);
v___x_504_ = l_BitVec_aandRec___redArg(v_w_495_, v_x_496_, v_y_497_, v_one_501_);
return v___x_504_;
}
else
{
uint8_t v___x_505_; 
v___x_505_ = l_BitVec_resRec___redArg(v_w_495_, v_x_496_, v_y_497_, v_n_502_);
if (v___x_505_ == 0)
{
uint8_t v___x_506_; 
v___x_506_ = l_BitVec_aandRec___redArg(v_w_495_, v_x_496_, v_y_497_, v_s_498_);
return v___x_506_;
}
else
{
lean_dec(v_s_498_);
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_resRec___redArg___boxed(lean_object* v_w_507_, lean_object* v_x_508_, lean_object* v_y_509_, lean_object* v_s_510_){
_start:
{
uint8_t v_res_511_; lean_object* v_r_512_; 
v_res_511_ = l_BitVec_resRec___redArg(v_w_507_, v_x_508_, v_y_509_, v_s_510_);
lean_dec(v_y_509_);
lean_dec(v_x_508_);
lean_dec(v_w_507_);
v_r_512_ = lean_box(v_res_511_);
return v_r_512_;
}
}
LEAN_EXPORT uint8_t l_BitVec_resRec(lean_object* v_w_513_, lean_object* v_x_514_, lean_object* v_y_515_, lean_object* v_s_516_, lean_object* v_hs_517_, lean_object* v_hslt_518_){
_start:
{
uint8_t v___x_519_; 
v___x_519_ = l_BitVec_resRec___redArg(v_w_513_, v_x_514_, v_y_515_, v_s_516_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_BitVec_resRec___boxed(lean_object* v_w_520_, lean_object* v_x_521_, lean_object* v_y_522_, lean_object* v_s_523_, lean_object* v_hs_524_, lean_object* v_hslt_525_){
_start:
{
uint8_t v_res_526_; lean_object* v_r_527_; 
v_res_526_ = l_BitVec_resRec(v_w_520_, v_x_521_, v_y_522_, v_s_523_, v_hs_524_, v_hslt_525_);
lean_dec(v_y_522_);
lean_dec(v_x_521_);
lean_dec(v_w_520_);
v_r_527_ = lean_box(v_res_526_);
return v_r_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg(lean_object* v_s_528_, lean_object* v_h__1_529_, lean_object* v_h__2_530_){
_start:
{
lean_object* v_zero_531_; uint8_t v_isZero_532_; 
v_zero_531_ = lean_unsigned_to_nat(0u);
v_isZero_532_ = lean_nat_dec_eq(v_s_528_, v_zero_531_);
if (v_isZero_532_ == 1)
{
lean_object* v___x_533_; 
lean_dec(v_h__2_530_);
v___x_533_ = lean_apply_3(v_h__1_529_, lean_box(0), lean_box(0), lean_box(0));
return v___x_533_;
}
else
{
lean_object* v_one_534_; lean_object* v_n_535_; lean_object* v___x_536_; 
lean_dec(v_h__1_529_);
v_one_534_ = lean_unsigned_to_nat(1u);
v_n_535_ = lean_nat_sub(v_s_528_, v_one_534_);
v___x_536_ = lean_apply_4(v_h__2_530_, v_n_535_, lean_box(0), lean_box(0), lean_box(0));
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg___boxed(lean_object* v_s_537_, lean_object* v_h__1_538_, lean_object* v_h__2_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg(v_s_537_, v_h__1_538_, v_h__2_539_);
lean_dec(v_s_537_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter(lean_object* v_w_541_, lean_object* v_motive_542_, lean_object* v_s_543_, lean_object* v_hs_544_, lean_object* v_hslt_545_, lean_object* v_h__1_546_, lean_object* v_h__2_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg(v_s_543_, v_h__1_546_, v_h__2_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___boxed(lean_object* v_w_549_, lean_object* v_motive_550_, lean_object* v_s_551_, lean_object* v_hs_552_, lean_object* v_hslt_553_, lean_object* v_h__1_554_, lean_object* v_h__2_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter(v_w_549_, v_motive_550_, v_s_551_, v_hs_552_, v_hslt_553_, v_h__1_554_, v_h__2_555_);
lean_dec(v_s_551_);
lean_dec(v_w_549_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg(lean_object* v_s_x27_557_, lean_object* v_h__1_558_, lean_object* v_h__2_559_){
_start:
{
lean_object* v_zero_560_; uint8_t v_isZero_561_; 
v_zero_560_ = lean_unsigned_to_nat(0u);
v_isZero_561_ = lean_nat_dec_eq(v_s_x27_557_, v_zero_560_);
if (v_isZero_561_ == 1)
{
lean_object* v___x_562_; 
lean_dec(v_h__2_559_);
v___x_562_ = lean_apply_4(v_h__1_558_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_562_;
}
else
{
lean_object* v_one_563_; lean_object* v_n_564_; lean_object* v___x_565_; 
lean_dec(v_h__1_558_);
v_one_563_ = lean_unsigned_to_nat(1u);
v_n_564_ = lean_nat_sub(v_s_x27_557_, v_one_563_);
v___x_565_ = lean_apply_5(v_h__2_559_, v_n_564_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg___boxed(lean_object* v_s_x27_566_, lean_object* v_h__1_567_, lean_object* v_h__2_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg(v_s_x27_566_, v_h__1_567_, v_h__2_568_);
lean_dec(v_s_x27_566_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter(lean_object* v_w_570_, lean_object* v_s_571_, lean_object* v_motive_572_, lean_object* v_s_x27_573_, lean_object* v_hs_574_, lean_object* v_hslt_575_, lean_object* v_hs0_576_, lean_object* v_h__1_577_, lean_object* v_h__2_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg(v_s_x27_573_, v_h__1_577_, v_h__2_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___boxed(lean_object* v_w_580_, lean_object* v_s_581_, lean_object* v_motive_582_, lean_object* v_s_x27_583_, lean_object* v_hs_584_, lean_object* v_hslt_585_, lean_object* v_hs0_586_, lean_object* v_h__1_587_, lean_object* v_h__2_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter(v_w_580_, v_s_581_, v_motive_582_, v_s_x27_583_, v_hs_584_, v_hslt_585_, v_hs0_586_, v_h__1_587_, v_h__2_588_);
lean_dec(v_s_x27_583_);
lean_dec(v_s_581_);
lean_dec(v_w_580_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___redArg(lean_object* v_idx_590_, lean_object* v_len_591_, lean_object* v_x_592_){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = l_BitVec_extractLsb_x27___redArg(v_idx_590_, v___x_593_, v_x_592_);
v___x_595_ = l_BitVec_setWidth(v___x_593_, v_len_591_, v___x_594_);
lean_dec(v___x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___redArg___boxed(lean_object* v_idx_596_, lean_object* v_len_597_, lean_object* v_x_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_BitVec_extractAndExtendBit___redArg(v_idx_596_, v_len_597_, v_x_598_);
lean_dec(v_x_598_);
lean_dec(v_len_597_);
lean_dec(v_idx_596_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit(lean_object* v_w_600_, lean_object* v_idx_601_, lean_object* v_len_602_, lean_object* v_x_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_BitVec_extractAndExtendBit___redArg(v_idx_601_, v_len_602_, v_x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___boxed(lean_object* v_w_605_, lean_object* v_idx_606_, lean_object* v_len_607_, lean_object* v_x_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_BitVec_extractAndExtendBit(v_w_605_, v_idx_606_, v_len_607_, v_x_608_);
lean_dec(v_x_608_);
lean_dec(v_len_607_);
lean_dec(v_idx_606_);
lean_dec(v_w_605_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___redArg(lean_object* v_w_610_, lean_object* v_k_611_, lean_object* v_len_612_, lean_object* v_x_613_, lean_object* v_acc_614_){
_start:
{
lean_object* v___x_615_; lean_object* v_zero_616_; uint8_t v_isZero_617_; 
v___x_615_ = lean_nat_sub(v_w_610_, v_k_611_);
v_zero_616_ = lean_unsigned_to_nat(0u);
v_isZero_617_ = lean_nat_dec_eq(v___x_615_, v_zero_616_);
lean_dec(v___x_615_);
if (v_isZero_617_ == 1)
{
lean_dec(v_k_611_);
return v_acc_614_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v_acc_x27_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_618_ = lean_nat_mul(v_k_611_, v_len_612_);
v___x_619_ = l_BitVec_extractAndExtendBit___redArg(v_k_611_, v_len_612_, v_x_613_);
v_acc_x27_620_ = l_BitVec_append___redArg(v___x_618_, v___x_619_, v_acc_614_);
lean_dec(v_acc_614_);
lean_dec(v___x_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_unsigned_to_nat(1u);
v___x_622_ = lean_nat_add(v_k_611_, v___x_621_);
lean_dec(v_k_611_);
v_k_611_ = v___x_622_;
v_acc_614_ = v_acc_x27_620_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___redArg___boxed(lean_object* v_w_624_, lean_object* v_k_625_, lean_object* v_len_626_, lean_object* v_x_627_, lean_object* v_acc_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_BitVec_extractAndExtendAux___redArg(v_w_624_, v_k_625_, v_len_626_, v_x_627_, v_acc_628_);
lean_dec(v_x_627_);
lean_dec(v_len_626_);
lean_dec(v_w_624_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux(lean_object* v_w_630_, lean_object* v_k_631_, lean_object* v_len_632_, lean_object* v_x_633_, lean_object* v_acc_634_, lean_object* v_hle_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_BitVec_extractAndExtendAux___redArg(v_w_630_, v_k_631_, v_len_632_, v_x_633_, v_acc_634_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___boxed(lean_object* v_w_637_, lean_object* v_k_638_, lean_object* v_len_639_, lean_object* v_x_640_, lean_object* v_acc_641_, lean_object* v_hle_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_BitVec_extractAndExtendAux(v_w_637_, v_k_638_, v_len_639_, v_x_640_, v_acc_641_, v_hle_642_);
lean_dec(v_x_640_);
lean_dec(v_len_639_);
lean_dec(v_w_637_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg(lean_object* v_x_644_, lean_object* v_h__1_645_, lean_object* v_h__2_646_){
_start:
{
lean_object* v_zero_647_; uint8_t v_isZero_648_; 
v_zero_647_ = lean_unsigned_to_nat(0u);
v_isZero_648_ = lean_nat_dec_eq(v_x_644_, v_zero_647_);
if (v_isZero_648_ == 1)
{
lean_object* v___x_649_; 
lean_dec(v_h__2_646_);
v___x_649_ = lean_apply_1(v_h__1_645_, lean_box(0));
return v___x_649_;
}
else
{
lean_object* v_one_650_; lean_object* v_n_651_; lean_object* v___x_652_; 
lean_dec(v_h__1_645_);
v_one_650_ = lean_unsigned_to_nat(1u);
v_n_651_ = lean_nat_sub(v_x_644_, v_one_650_);
v___x_652_ = lean_apply_2(v_h__2_646_, v_n_651_, lean_box(0));
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg___boxed(lean_object* v_x_653_, lean_object* v_h__1_654_, lean_object* v_h__2_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg(v_x_653_, v_h__1_654_, v_h__2_655_);
lean_dec(v_x_653_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter(lean_object* v_motive_657_, lean_object* v_x_658_, lean_object* v_h__1_659_, lean_object* v_h__2_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg(v_x_658_, v_h__1_659_, v_h__2_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___boxed(lean_object* v_motive_662_, lean_object* v_x_663_, lean_object* v_h__1_664_, lean_object* v_h__2_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter(v_motive_662_, v_x_663_, v_h__1_664_, v_h__2_665_);
lean_dec(v_x_663_);
return v_res_666_;
}
}
static lean_object* _init_l_BitVec_extractAndExtend___closed__0(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = l_BitVec_ofNat(v___x_667_, v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtend(lean_object* v_w_669_, lean_object* v_len_670_, lean_object* v_x_671_){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_672_ = lean_unsigned_to_nat(0u);
v___x_673_ = lean_obj_once(&l_BitVec_extractAndExtend___closed__0, &l_BitVec_extractAndExtend___closed__0_once, _init_l_BitVec_extractAndExtend___closed__0);
v___x_674_ = l_BitVec_extractAndExtendAux___redArg(v_w_669_, v___x_672_, v_len_670_, v_x_671_, v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtend___boxed(lean_object* v_w_675_, lean_object* v_len_676_, lean_object* v_x_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_BitVec_extractAndExtend(v_w_675_, v_len_676_, v_x_677_);
lean_dec(v_x_677_);
lean_dec(v_len_676_);
lean_dec(v_w_675_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___redArg(lean_object* v_len_679_, lean_object* v_w_680_, lean_object* v_iterNum_681_, lean_object* v_oldLayer_682_, lean_object* v_newLayer_683_){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_684_ = lean_unsigned_to_nat(2u);
v___x_685_ = lean_nat_mul(v_iterNum_681_, v___x_684_);
v___x_686_ = lean_nat_sub(v_len_679_, v___x_685_);
lean_dec(v___x_685_);
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = lean_nat_dec_eq(v___x_686_, v___x_687_);
lean_dec(v___x_686_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v_op1_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v_op2_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v_newLayer_x27_698_; lean_object* v___x_699_; 
v___x_689_ = lean_nat_mul(v___x_684_, v_iterNum_681_);
v___x_690_ = lean_nat_mul(v___x_689_, v_w_680_);
v_op1_691_ = l_BitVec_extractLsb_x27___redArg(v___x_690_, v_w_680_, v_oldLayer_682_);
lean_dec(v___x_690_);
v___x_692_ = lean_unsigned_to_nat(1u);
v___x_693_ = lean_nat_add(v___x_689_, v___x_692_);
lean_dec(v___x_689_);
v___x_694_ = lean_nat_mul(v___x_693_, v_w_680_);
lean_dec(v___x_693_);
v_op2_695_ = l_BitVec_extractLsb_x27___redArg(v___x_694_, v_w_680_, v_oldLayer_682_);
lean_dec(v___x_694_);
v___x_696_ = lean_nat_mul(v_iterNum_681_, v_w_680_);
v___x_697_ = l_BitVec_add(v_w_680_, v_op1_691_, v_op2_695_);
lean_dec(v_op2_695_);
lean_dec(v_op1_691_);
v_newLayer_x27_698_ = l_BitVec_append___redArg(v___x_696_, v___x_697_, v_newLayer_683_);
lean_dec(v_newLayer_683_);
lean_dec(v___x_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_nat_add(v_iterNum_681_, v___x_692_);
lean_dec(v_iterNum_681_);
v_iterNum_681_ = v___x_699_;
v_newLayer_683_ = v_newLayer_x27_698_;
goto _start;
}
else
{
lean_dec(v_iterNum_681_);
return v_newLayer_683_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___redArg___boxed(lean_object* v_len_701_, lean_object* v_w_702_, lean_object* v_iterNum_703_, lean_object* v_oldLayer_704_, lean_object* v_newLayer_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_BitVec_cpopLayer___redArg(v_len_701_, v_w_702_, v_iterNum_703_, v_oldLayer_704_, v_newLayer_705_);
lean_dec(v_oldLayer_704_);
lean_dec(v_w_702_);
lean_dec(v_len_701_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer(lean_object* v_len_707_, lean_object* v_w_708_, lean_object* v_iterNum_709_, lean_object* v_oldLayer_710_, lean_object* v_newLayer_711_, lean_object* v_hold_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_BitVec_cpopLayer___redArg(v_len_707_, v_w_708_, v_iterNum_709_, v_oldLayer_710_, v_newLayer_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___boxed(lean_object* v_len_714_, lean_object* v_w_715_, lean_object* v_iterNum_716_, lean_object* v_oldLayer_717_, lean_object* v_newLayer_718_, lean_object* v_hold_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_BitVec_cpopLayer(v_len_714_, v_w_715_, v_iterNum_716_, v_oldLayer_717_, v_newLayer_718_, v_hold_719_);
lean_dec(v_oldLayer_717_);
lean_dec(v_w_715_);
lean_dec(v_len_714_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopTree(lean_object* v_len_721_, lean_object* v_w_722_, lean_object* v_l_723_){
_start:
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = lean_nat_dec_eq(v_len_721_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = lean_unsigned_to_nat(1u);
v___x_727_ = lean_nat_dec_eq(v_len_721_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_728_ = lean_nat_add(v_len_721_, v___x_726_);
v___x_729_ = lean_nat_shiftr(v___x_728_, v___x_726_);
lean_dec(v___x_728_);
v___x_730_ = lean_obj_once(&l_BitVec_extractAndExtend___closed__0, &l_BitVec_extractAndExtend___closed__0_once, _init_l_BitVec_extractAndExtend___closed__0);
v___x_731_ = l_BitVec_cpopLayer___redArg(v_len_721_, v_w_722_, v___x_724_, v_l_723_, v___x_730_);
lean_dec(v_l_723_);
lean_dec(v_len_721_);
v_len_721_ = v___x_729_;
v_l_723_ = v___x_731_;
goto _start;
}
else
{
lean_dec(v_len_721_);
return v_l_723_;
}
}
else
{
lean_object* v___x_733_; 
lean_dec(v_l_723_);
lean_dec(v_len_721_);
v___x_733_ = l_BitVec_ofNat(v_w_722_, v___x_724_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopTree___boxed(lean_object* v_len_734_, lean_object* v_w_735_, lean_object* v_l_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_BitVec_cpopTree(v_len_734_, v_w_735_, v_l_736_);
lean_dec(v_w_735_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopRec(lean_object* v_w_738_, lean_object* v_x_739_){
_start:
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_nat_dec_lt(v___x_740_, v_w_738_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_nat_dec_lt(v___x_742_, v_w_738_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; 
v___x_744_ = l_BitVec_ofNat(v_w_738_, v___x_742_);
lean_dec(v_w_738_);
return v___x_744_;
}
else
{
lean_dec(v_w_738_);
lean_inc(v_x_739_);
return v_x_739_;
}
}
else
{
lean_object* v_extendedBits_745_; lean_object* v___x_746_; 
v_extendedBits_745_ = l_BitVec_extractAndExtend(v_w_738_, v_w_738_, v_x_739_);
lean_inc(v_w_738_);
v___x_746_ = l_BitVec_cpopTree(v_w_738_, v_w_738_, v_extendedBits_745_);
lean_dec(v_w_738_);
return v___x_746_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopRec___boxed(lean_object* v_w_747_, lean_object* v_x_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_BitVec_cpopRec(v_w_747_, v_x_748_);
lean_dec(v_x_748_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(lean_object* v_w_750_, lean_object* v_x_751_, lean_object* v_rem_752_, lean_object* v_acc_753_){
_start:
{
lean_object* v_zero_754_; uint8_t v_isZero_755_; 
v_zero_754_ = lean_unsigned_to_nat(0u);
v_isZero_755_ = lean_nat_dec_eq(v_rem_752_, v_zero_754_);
if (v_isZero_755_ == 1)
{
lean_dec(v_rem_752_);
return v_acc_753_;
}
else
{
lean_object* v_one_756_; lean_object* v_n_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_one_756_ = lean_unsigned_to_nat(1u);
v_n_757_ = lean_nat_sub(v_rem_752_, v_one_756_);
lean_dec(v_rem_752_);
v___x_758_ = lean_nat_mul(v_n_757_, v_w_750_);
v___x_759_ = l_BitVec_extractLsb_x27___redArg(v___x_758_, v_w_750_, v_x_751_);
lean_dec(v___x_758_);
v___x_760_ = l_BitVec_add(v_w_750_, v_acc_753_, v___x_759_);
lean_dec(v___x_759_);
lean_dec(v_acc_753_);
v_rem_752_ = v_n_757_;
v_acc_753_ = v___x_760_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg___boxed(lean_object* v_w_762_, lean_object* v_x_763_, lean_object* v_rem_764_, lean_object* v_acc_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_762_, v_x_763_, v_rem_764_, v_acc_765_);
lean_dec(v_x_763_);
lean_dec(v_w_762_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux(lean_object* v_l_767_, lean_object* v_w_768_, lean_object* v_x_769_, lean_object* v_rem_770_, lean_object* v_acc_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_768_, v_x_769_, v_rem_770_, v_acc_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___boxed(lean_object* v_l_773_, lean_object* v_w_774_, lean_object* v_x_775_, lean_object* v_rem_776_, lean_object* v_acc_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux(v_l_773_, v_w_774_, v_x_775_, v_rem_776_, v_acc_777_);
lean_dec(v_x_775_);
lean_dec(v_w_774_);
lean_dec(v_l_773_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec(lean_object* v_l_779_, lean_object* v_w_780_, lean_object* v_x_781_){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = l_BitVec_ofNat(v_w_780_, v___x_782_);
v___x_784_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_780_, v_x_781_, v_l_779_, v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec___boxed(lean_object* v_l_785_, lean_object* v_w_786_, lean_object* v_x_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec(v_l_785_, v_w_786_, v_x_787_);
lean_dec(v_x_787_);
lean_dec(v_w_786_);
return v_res_788_;
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
