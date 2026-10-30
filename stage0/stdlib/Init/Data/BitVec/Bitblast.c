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
lean_object* l_BitVec_twoPow(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_BitVec_sshiftRight(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_BitVec_append___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_BitVec_shiftLeftRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_shiftLeftRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_DivModState_init(lean_object*);
LEAN_EXPORT lean_object* l_BitVec_divSubtractShift(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_divSubtractShift___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_BitVec_shiftLeftRec(lean_object* v_w_u2081_122_, lean_object* v_w_u2082_123_, lean_object* v_x_124_, lean_object* v_y_125_, lean_object* v_n_126_){
_start:
{
lean_object* v___x_127_; lean_object* v_shiftAmt_128_; lean_object* v_zero_129_; uint8_t v_isZero_130_; 
v___x_127_ = l_BitVec_twoPow(v_w_u2082_123_, v_n_126_);
v_shiftAmt_128_ = lean_nat_land(v_y_125_, v___x_127_);
lean_dec(v___x_127_);
v_zero_129_ = lean_unsigned_to_nat(0u);
v_isZero_130_ = lean_nat_dec_eq(v_n_126_, v_zero_129_);
if (v_isZero_130_ == 1)
{
lean_object* v___x_131_; 
v___x_131_ = l_BitVec_shiftLeft(v_w_u2081_122_, v_x_124_, v_shiftAmt_128_);
lean_dec(v_shiftAmt_128_);
return v___x_131_;
}
else
{
lean_object* v_one_132_; lean_object* v_n_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_one_132_ = lean_unsigned_to_nat(1u);
v_n_133_ = lean_nat_sub(v_n_126_, v_one_132_);
v___x_134_ = l_BitVec_shiftLeftRec(v_w_u2081_122_, v_w_u2082_123_, v_x_124_, v_y_125_, v_n_133_);
lean_dec(v_n_133_);
v___x_135_ = l_BitVec_shiftLeft(v_w_u2081_122_, v___x_134_, v_shiftAmt_128_);
lean_dec(v_shiftAmt_128_);
lean_dec(v___x_134_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftRec___boxed(lean_object* v_w_u2081_136_, lean_object* v_w_u2082_137_, lean_object* v_x_138_, lean_object* v_y_139_, lean_object* v_n_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_BitVec_shiftLeftRec(v_w_u2081_136_, v_w_u2082_137_, v_x_138_, v_y_139_, v_n_140_);
lean_dec(v_n_140_);
lean_dec(v_y_139_);
lean_dec(v_x_138_);
lean_dec(v_w_u2082_137_);
lean_dec(v_w_u2081_136_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_BitVec_DivModState_init(lean_object* v_w_142_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = l_BitVec_ofNat(v_w_142_, v___x_143_);
lean_inc(v___x_144_);
v___x_145_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_145_, 0, v_w_142_);
lean_ctor_set(v___x_145_, 1, v___x_143_);
lean_ctor_set(v___x_145_, 2, v___x_144_);
lean_ctor_set(v___x_145_, 3, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_BitVec_divSubtractShift(lean_object* v_w_146_, lean_object* v_args_147_, lean_object* v_qr_148_){
_start:
{
lean_object* v_n_149_; lean_object* v_d_150_; lean_object* v_wn_151_; lean_object* v_wr_152_; lean_object* v_q_153_; lean_object* v_r_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_176_; 
v_n_149_ = lean_ctor_get(v_args_147_, 0);
v_d_150_ = lean_ctor_get(v_args_147_, 1);
v_wn_151_ = lean_ctor_get(v_qr_148_, 0);
v_wr_152_ = lean_ctor_get(v_qr_148_, 1);
v_q_153_ = lean_ctor_get(v_qr_148_, 2);
v_r_154_ = lean_ctor_get(v_qr_148_, 3);
v_isSharedCheck_176_ = !lean_is_exclusive(v_qr_148_);
if (v_isSharedCheck_176_ == 0)
{
v___x_156_ = v_qr_148_;
v_isShared_157_ = v_isSharedCheck_176_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_r_154_);
lean_inc(v_q_153_);
lean_inc(v_wr_152_);
lean_inc(v_wn_151_);
lean_dec(v_qr_148_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_176_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v_wn_159_; lean_object* v_wr_160_; uint8_t v___x_161_; lean_object* v_r_x27_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_158_ = lean_unsigned_to_nat(1u);
v_wn_159_ = lean_nat_sub(v_wn_151_, v___x_158_);
lean_dec(v_wn_151_);
v_wr_160_ = lean_nat_add(v_wr_152_, v___x_158_);
lean_dec(v_wr_152_);
v___x_161_ = l_Nat_testBit(v_n_149_, v_wn_159_);
v_r_x27_162_ = l_BitVec_shiftConcat(v_w_146_, v_r_154_, v___x_161_);
lean_dec(v_r_154_);
v___x_163_ = lean_nat_add(v_r_x27_162_, v___x_158_);
v___x_164_ = lean_nat_dec_le(v___x_163_, v_d_150_);
lean_dec(v___x_163_);
if (v___x_164_ == 0)
{
uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_165_ = 1;
v___x_166_ = l_BitVec_shiftConcat(v_w_146_, v_q_153_, v___x_165_);
lean_dec(v_q_153_);
v___x_167_ = l_BitVec_sub(v_w_146_, v_r_x27_162_, v_d_150_);
lean_dec(v_r_x27_162_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 3, v___x_167_);
lean_ctor_set(v___x_156_, 2, v___x_166_);
lean_ctor_set(v___x_156_, 1, v_wr_160_);
lean_ctor_set(v___x_156_, 0, v_wn_159_);
v___x_169_ = v___x_156_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_wn_159_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_wr_160_);
lean_ctor_set(v_reuseFailAlloc_170_, 2, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_170_, 3, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
else
{
uint8_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_171_ = 0;
v___x_172_ = l_BitVec_shiftConcat(v_w_146_, v_q_153_, v___x_171_);
lean_dec(v_q_153_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 3, v_r_x27_162_);
lean_ctor_set(v___x_156_, 2, v___x_172_);
lean_ctor_set(v___x_156_, 1, v_wr_160_);
lean_ctor_set(v___x_156_, 0, v_wn_159_);
v___x_174_ = v___x_156_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_wn_159_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_wr_160_);
lean_ctor_set(v_reuseFailAlloc_175_, 2, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_175_, 3, v_r_x27_162_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_divSubtractShift___boxed(lean_object* v_w_177_, lean_object* v_args_178_, lean_object* v_qr_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_BitVec_divSubtractShift(v_w_177_, v_args_178_, v_qr_179_);
lean_dec_ref(v_args_178_);
lean_dec(v_w_177_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_BitVec_divRec(lean_object* v_w_181_, lean_object* v_m_182_, lean_object* v_args_183_, lean_object* v_qr_184_){
_start:
{
lean_object* v_zero_185_; uint8_t v_isZero_186_; 
v_zero_185_ = lean_unsigned_to_nat(0u);
v_isZero_186_ = lean_nat_dec_eq(v_m_182_, v_zero_185_);
if (v_isZero_186_ == 1)
{
lean_dec(v_m_182_);
return v_qr_184_;
}
else
{
lean_object* v_one_187_; lean_object* v_n_188_; lean_object* v___x_189_; 
v_one_187_ = lean_unsigned_to_nat(1u);
v_n_188_ = lean_nat_sub(v_m_182_, v_one_187_);
lean_dec(v_m_182_);
v___x_189_ = l_BitVec_divSubtractShift(v_w_181_, v_args_183_, v_qr_184_);
v_m_182_ = v_n_188_;
v_qr_184_ = v___x_189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_divRec___boxed(lean_object* v_w_191_, lean_object* v_m_192_, lean_object* v_args_193_, lean_object* v_qr_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_BitVec_divRec(v_w_191_, v_m_192_, v_args_193_, v_qr_194_);
lean_dec_ref(v_args_193_);
lean_dec(v_w_191_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRightRec(lean_object* v_w_u2081_196_, lean_object* v_w_u2082_197_, lean_object* v_x_198_, lean_object* v_y_199_, lean_object* v_n_200_){
_start:
{
lean_object* v___x_201_; lean_object* v_shiftAmt_202_; lean_object* v_zero_203_; uint8_t v_isZero_204_; 
v___x_201_ = l_BitVec_twoPow(v_w_u2082_197_, v_n_200_);
v_shiftAmt_202_ = lean_nat_land(v_y_199_, v___x_201_);
lean_dec(v___x_201_);
v_zero_203_ = lean_unsigned_to_nat(0u);
v_isZero_204_ = lean_nat_dec_eq(v_n_200_, v_zero_203_);
if (v_isZero_204_ == 1)
{
lean_object* v___x_205_; 
v___x_205_ = l_BitVec_sshiftRight(v_w_u2081_196_, v_x_198_, v_shiftAmt_202_);
lean_dec(v_shiftAmt_202_);
return v___x_205_;
}
else
{
lean_object* v_one_206_; lean_object* v_n_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_one_206_ = lean_unsigned_to_nat(1u);
v_n_207_ = lean_nat_sub(v_n_200_, v_one_206_);
v___x_208_ = l_BitVec_sshiftRightRec(v_w_u2081_196_, v_w_u2082_197_, v_x_198_, v_y_199_, v_n_207_);
lean_dec(v_n_207_);
v___x_209_ = l_BitVec_sshiftRight(v_w_u2081_196_, v___x_208_, v_shiftAmt_202_);
lean_dec(v_shiftAmt_202_);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRightRec___boxed(lean_object* v_w_u2081_210_, lean_object* v_w_u2082_211_, lean_object* v_x_212_, lean_object* v_y_213_, lean_object* v_n_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_BitVec_sshiftRightRec(v_w_u2081_210_, v_w_u2082_211_, v_x_212_, v_y_213_, v_n_214_);
lean_dec(v_n_214_);
lean_dec(v_y_213_);
lean_dec(v_w_u2082_211_);
lean_dec(v_w_u2081_210_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___redArg(lean_object* v_w_u2082_216_, lean_object* v_x_217_, lean_object* v_y_218_, lean_object* v_n_219_){
_start:
{
lean_object* v___x_220_; lean_object* v_shiftAmt_221_; lean_object* v_zero_222_; uint8_t v_isZero_223_; 
v___x_220_ = l_BitVec_twoPow(v_w_u2082_216_, v_n_219_);
v_shiftAmt_221_ = lean_nat_land(v_y_218_, v___x_220_);
lean_dec(v___x_220_);
v_zero_222_ = lean_unsigned_to_nat(0u);
v_isZero_223_ = lean_nat_dec_eq(v_n_219_, v_zero_222_);
if (v_isZero_223_ == 1)
{
lean_object* v___x_224_; 
v___x_224_ = lean_nat_shiftr(v_x_217_, v_shiftAmt_221_);
lean_dec(v_shiftAmt_221_);
return v___x_224_;
}
else
{
lean_object* v_one_225_; lean_object* v_n_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_one_225_ = lean_unsigned_to_nat(1u);
v_n_226_ = lean_nat_sub(v_n_219_, v_one_225_);
v___x_227_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_216_, v_x_217_, v_y_218_, v_n_226_);
lean_dec(v_n_226_);
v___x_228_ = lean_nat_shiftr(v___x_227_, v_shiftAmt_221_);
lean_dec(v_shiftAmt_221_);
lean_dec(v___x_227_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___redArg___boxed(lean_object* v_w_u2082_229_, lean_object* v_x_230_, lean_object* v_y_231_, lean_object* v_n_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_229_, v_x_230_, v_y_231_, v_n_232_);
lean_dec(v_n_232_);
lean_dec(v_y_231_);
lean_dec(v_x_230_);
lean_dec(v_w_u2082_229_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec(lean_object* v_w_u2081_234_, lean_object* v_w_u2082_235_, lean_object* v_x_236_, lean_object* v_y_237_, lean_object* v_n_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_235_, v_x_236_, v_y_237_, v_n_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___boxed(lean_object* v_w_u2081_240_, lean_object* v_w_u2082_241_, lean_object* v_x_242_, lean_object* v_y_243_, lean_object* v_n_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_BitVec_ushiftRightRec(v_w_u2081_240_, v_w_u2082_241_, v_x_242_, v_y_243_, v_n_244_);
lean_dec(v_n_244_);
lean_dec(v_y_243_);
lean_dec(v_x_242_);
lean_dec(v_w_u2082_241_);
lean_dec(v_w_u2081_240_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg(uint8_t v_x_246_, uint8_t v_x_247_, lean_object* v_h__1_248_, lean_object* v_h__2_249_, lean_object* v_h__3_250_, lean_object* v_h__4_251_){
_start:
{
if (v_x_246_ == 0)
{
lean_dec(v_h__4_251_);
lean_dec(v_h__3_250_);
if (v_x_247_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec(v_h__2_249_);
v___x_252_ = lean_box(0);
v___x_253_ = lean_apply_1(v_h__1_248_, v___x_252_);
return v___x_253_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v_h__1_248_);
v___x_254_ = lean_box(0);
v___x_255_ = lean_apply_1(v_h__2_249_, v___x_254_);
return v___x_255_;
}
}
else
{
lean_dec(v_h__2_249_);
lean_dec(v_h__1_248_);
if (v_x_247_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec(v_h__4_251_);
v___x_256_ = lean_box(0);
v___x_257_ = lean_apply_1(v_h__3_250_, v___x_256_);
return v___x_257_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec(v_h__3_250_);
v___x_258_ = lean_box(0);
v___x_259_ = lean_apply_1(v_h__4_251_, v___x_258_);
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg___boxed(lean_object* v_x_260_, lean_object* v_x_261_, lean_object* v_h__1_262_, lean_object* v_h__2_263_, lean_object* v_h__3_264_, lean_object* v_h__4_265_){
_start:
{
uint8_t v_x_46__boxed_266_; uint8_t v_x_47__boxed_267_; lean_object* v_res_268_; 
v_x_46__boxed_266_ = lean_unbox(v_x_260_);
v_x_47__boxed_267_ = lean_unbox(v_x_261_);
v_res_268_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg(v_x_46__boxed_266_, v_x_47__boxed_267_, v_h__1_262_, v_h__2_263_, v_h__3_264_, v_h__4_265_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter(lean_object* v_motive_269_, uint8_t v_x_270_, uint8_t v_x_271_, lean_object* v_h__1_272_, lean_object* v_h__2_273_, lean_object* v_h__3_274_, lean_object* v_h__4_275_){
_start:
{
if (v_x_270_ == 0)
{
lean_dec(v_h__4_275_);
lean_dec(v_h__3_274_);
if (v_x_271_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec(v_h__2_273_);
v___x_276_ = lean_box(0);
v___x_277_ = lean_apply_1(v_h__1_272_, v___x_276_);
return v___x_277_;
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec(v_h__1_272_);
v___x_278_ = lean_box(0);
v___x_279_ = lean_apply_1(v_h__2_273_, v___x_278_);
return v___x_279_;
}
}
else
{
lean_dec(v_h__2_273_);
lean_dec(v_h__1_272_);
if (v_x_271_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec(v_h__4_275_);
v___x_280_ = lean_box(0);
v___x_281_ = lean_apply_1(v_h__3_274_, v___x_280_);
return v___x_281_;
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec(v_h__3_274_);
v___x_282_ = lean_box(0);
v___x_283_ = lean_apply_1(v_h__4_275_, v___x_282_);
return v___x_283_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___boxed(lean_object* v_motive_284_, lean_object* v_x_285_, lean_object* v_x_286_, lean_object* v_h__1_287_, lean_object* v_h__2_288_, lean_object* v_h__3_289_, lean_object* v_h__4_290_){
_start:
{
uint8_t v_x_68__boxed_291_; uint8_t v_x_69__boxed_292_; lean_object* v_res_293_; 
v_x_68__boxed_291_ = lean_unbox(v_x_285_);
v_x_69__boxed_292_ = lean_unbox(v_x_286_);
v_res_293_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter(v_motive_284_, v_x_68__boxed_291_, v_x_69__boxed_292_, v_h__1_287_, v_h__2_288_, v_h__3_289_, v_h__4_290_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg(uint8_t v_x_294_, uint8_t v_x_295_, lean_object* v_h__1_296_, lean_object* v_h__2_297_, lean_object* v_h__3_298_, lean_object* v_h__4_299_){
_start:
{
if (v_x_294_ == 0)
{
lean_dec(v_h__4_299_);
lean_dec(v_h__3_298_);
if (v_x_295_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_h__2_297_);
v___x_300_ = lean_box(0);
v___x_301_ = lean_apply_1(v_h__1_296_, v___x_300_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v_h__1_296_);
v___x_302_ = lean_box(0);
v___x_303_ = lean_apply_1(v_h__2_297_, v___x_302_);
return v___x_303_;
}
}
else
{
lean_dec(v_h__2_297_);
lean_dec(v_h__1_296_);
if (v_x_295_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec(v_h__4_299_);
v___x_304_ = lean_box(0);
v___x_305_ = lean_apply_1(v_h__3_298_, v___x_304_);
return v___x_305_;
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec(v_h__3_298_);
v___x_306_ = lean_box(0);
v___x_307_ = lean_apply_1(v_h__4_299_, v___x_306_);
return v___x_307_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg___boxed(lean_object* v_x_308_, lean_object* v_x_309_, lean_object* v_h__1_310_, lean_object* v_h__2_311_, lean_object* v_h__3_312_, lean_object* v_h__4_313_){
_start:
{
uint8_t v_x_46__boxed_314_; uint8_t v_x_47__boxed_315_; lean_object* v_res_316_; 
v_x_46__boxed_314_ = lean_unbox(v_x_308_);
v_x_47__boxed_315_ = lean_unbox(v_x_309_);
v_res_316_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg(v_x_46__boxed_314_, v_x_47__boxed_315_, v_h__1_310_, v_h__2_311_, v_h__3_312_, v_h__4_313_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter(lean_object* v_motive_317_, uint8_t v_x_318_, uint8_t v_x_319_, lean_object* v_h__1_320_, lean_object* v_h__2_321_, lean_object* v_h__3_322_, lean_object* v_h__4_323_){
_start:
{
if (v_x_318_ == 0)
{
lean_dec(v_h__4_323_);
lean_dec(v_h__3_322_);
if (v_x_319_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec(v_h__2_321_);
v___x_324_ = lean_box(0);
v___x_325_ = lean_apply_1(v_h__1_320_, v___x_324_);
return v___x_325_;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; 
lean_dec(v_h__1_320_);
v___x_326_ = lean_box(0);
v___x_327_ = lean_apply_1(v_h__2_321_, v___x_326_);
return v___x_327_;
}
}
else
{
lean_dec(v_h__2_321_);
lean_dec(v_h__1_320_);
if (v_x_319_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec(v_h__4_323_);
v___x_328_ = lean_box(0);
v___x_329_ = lean_apply_1(v_h__3_322_, v___x_328_);
return v___x_329_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_h__3_322_);
v___x_330_ = lean_box(0);
v___x_331_ = lean_apply_1(v_h__4_323_, v___x_330_);
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___boxed(lean_object* v_motive_332_, lean_object* v_x_333_, lean_object* v_x_334_, lean_object* v_h__1_335_, lean_object* v_h__2_336_, lean_object* v_h__3_337_, lean_object* v_h__4_338_){
_start:
{
uint8_t v_x_68__boxed_339_; uint8_t v_x_69__boxed_340_; lean_object* v_res_341_; 
v_x_68__boxed_339_ = lean_unbox(v_x_333_);
v_x_69__boxed_340_ = lean_unbox(v_x_334_);
v_res_341_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter(v_motive_332_, v_x_68__boxed_339_, v_x_69__boxed_340_, v_h__1_335_, v_h__2_336_, v_h__3_337_, v_h__4_338_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg(uint8_t v_x_342_, uint8_t v_x_343_, lean_object* v_h__1_344_, lean_object* v_h__2_345_, lean_object* v_h__3_346_, lean_object* v_h__4_347_){
_start:
{
if (v_x_342_ == 0)
{
lean_dec(v_h__4_347_);
lean_dec(v_h__3_346_);
if (v_x_343_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec(v_h__2_345_);
v___x_348_ = lean_box(0);
v___x_349_ = lean_apply_1(v_h__1_344_, v___x_348_);
return v___x_349_;
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec(v_h__1_344_);
v___x_350_ = lean_box(0);
v___x_351_ = lean_apply_1(v_h__2_345_, v___x_350_);
return v___x_351_;
}
}
else
{
lean_dec(v_h__2_345_);
lean_dec(v_h__1_344_);
if (v_x_343_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; 
lean_dec(v_h__4_347_);
v___x_352_ = lean_box(0);
v___x_353_ = lean_apply_1(v_h__3_346_, v___x_352_);
return v___x_353_;
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v_h__3_346_);
v___x_354_ = lean_box(0);
v___x_355_ = lean_apply_1(v_h__4_347_, v___x_354_);
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg___boxed(lean_object* v_x_356_, lean_object* v_x_357_, lean_object* v_h__1_358_, lean_object* v_h__2_359_, lean_object* v_h__3_360_, lean_object* v_h__4_361_){
_start:
{
uint8_t v_x_46__boxed_362_; uint8_t v_x_47__boxed_363_; lean_object* v_res_364_; 
v_x_46__boxed_362_ = lean_unbox(v_x_356_);
v_x_47__boxed_363_ = lean_unbox(v_x_357_);
v_res_364_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg(v_x_46__boxed_362_, v_x_47__boxed_363_, v_h__1_358_, v_h__2_359_, v_h__3_360_, v_h__4_361_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter(lean_object* v_motive_365_, uint8_t v_x_366_, uint8_t v_x_367_, lean_object* v_h__1_368_, lean_object* v_h__2_369_, lean_object* v_h__3_370_, lean_object* v_h__4_371_){
_start:
{
if (v_x_366_ == 0)
{
lean_dec(v_h__4_371_);
lean_dec(v_h__3_370_);
if (v_x_367_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; 
lean_dec(v_h__2_369_);
v___x_372_ = lean_box(0);
v___x_373_ = lean_apply_1(v_h__1_368_, v___x_372_);
return v___x_373_;
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; 
lean_dec(v_h__1_368_);
v___x_374_ = lean_box(0);
v___x_375_ = lean_apply_1(v_h__2_369_, v___x_374_);
return v___x_375_;
}
}
else
{
lean_dec(v_h__2_369_);
lean_dec(v_h__1_368_);
if (v_x_367_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec(v_h__4_371_);
v___x_376_ = lean_box(0);
v___x_377_ = lean_apply_1(v_h__3_370_, v___x_376_);
return v___x_377_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec(v_h__3_370_);
v___x_378_ = lean_box(0);
v___x_379_ = lean_apply_1(v_h__4_371_, v___x_378_);
return v___x_379_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___boxed(lean_object* v_motive_380_, lean_object* v_x_381_, lean_object* v_x_382_, lean_object* v_h__1_383_, lean_object* v_h__2_384_, lean_object* v_h__3_385_, lean_object* v_h__4_386_){
_start:
{
uint8_t v_x_68__boxed_387_; uint8_t v_x_69__boxed_388_; lean_object* v_res_389_; 
v_x_68__boxed_387_ = lean_unbox(v_x_381_);
v_x_69__boxed_388_ = lean_unbox(v_x_382_);
v_res_389_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter(v_motive_380_, v_x_68__boxed_387_, v_x_69__boxed_388_, v_h__1_383_, v_h__2_384_, v_h__3_385_, v_h__4_386_);
return v_res_389_;
}
}
LEAN_EXPORT uint8_t l_BitVec_uppcRec___redArg(lean_object* v_w_390_, lean_object* v_x_391_, lean_object* v_s_392_){
_start:
{
lean_object* v_zero_393_; uint8_t v_isZero_394_; 
v_zero_393_ = lean_unsigned_to_nat(0u);
v_isZero_394_ = lean_nat_dec_eq(v_s_392_, v_zero_393_);
if (v_isZero_394_ == 1)
{
uint8_t v___x_395_; 
lean_dec(v_s_392_);
v___x_395_ = lean_nat_dec_lt(v_zero_393_, v_w_390_);
if (v___x_395_ == 0)
{
return v___x_395_;
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_nat_sub(v_w_390_, v___x_396_);
v___x_398_ = l_Nat_testBit(v_x_391_, v___x_397_);
lean_dec(v___x_397_);
return v___x_398_;
}
}
else
{
lean_object* v_one_399_; lean_object* v_n_400_; lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v_one_399_ = lean_unsigned_to_nat(1u);
v_n_400_ = lean_nat_sub(v_s_392_, v_one_399_);
lean_dec(v_s_392_);
v___x_401_ = lean_nat_sub(v_w_390_, v_one_399_);
v___x_402_ = lean_nat_sub(v___x_401_, v_n_400_);
lean_dec(v___x_401_);
v___x_403_ = l_Nat_testBit(v_x_391_, v___x_402_);
lean_dec(v___x_402_);
if (v___x_403_ == 0)
{
v_s_392_ = v_n_400_;
goto _start;
}
else
{
lean_dec(v_n_400_);
return v___x_403_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_uppcRec___redArg___boxed(lean_object* v_w_405_, lean_object* v_x_406_, lean_object* v_s_407_){
_start:
{
uint8_t v_res_408_; lean_object* v_r_409_; 
v_res_408_ = l_BitVec_uppcRec___redArg(v_w_405_, v_x_406_, v_s_407_);
lean_dec(v_x_406_);
lean_dec(v_w_405_);
v_r_409_ = lean_box(v_res_408_);
return v_r_409_;
}
}
LEAN_EXPORT uint8_t l_BitVec_uppcRec(lean_object* v_w_410_, lean_object* v_x_411_, lean_object* v_s_412_, lean_object* v_hs_413_){
_start:
{
uint8_t v___x_414_; 
v___x_414_ = l_BitVec_uppcRec___redArg(v_w_410_, v_x_411_, v_s_412_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_BitVec_uppcRec___boxed(lean_object* v_w_415_, lean_object* v_x_416_, lean_object* v_s_417_, lean_object* v_hs_418_){
_start:
{
uint8_t v_res_419_; lean_object* v_r_420_; 
v_res_419_ = l_BitVec_uppcRec(v_w_415_, v_x_416_, v_s_417_, v_hs_418_);
lean_dec(v_x_416_);
lean_dec(v_w_415_);
v_r_420_ = lean_box(v_res_419_);
return v_r_420_;
}
}
LEAN_EXPORT uint8_t l_BitVec_aandRec___redArg(lean_object* v_w_421_, lean_object* v_x_422_, lean_object* v_y_423_, lean_object* v_s_424_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = l_Nat_testBit(v_y_423_, v_s_424_);
if (v___x_425_ == 0)
{
lean_dec(v_s_424_);
return v___x_425_;
}
else
{
uint8_t v___x_426_; 
v___x_426_ = l_BitVec_uppcRec___redArg(v_w_421_, v_x_422_, v_s_424_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_aandRec___redArg___boxed(lean_object* v_w_427_, lean_object* v_x_428_, lean_object* v_y_429_, lean_object* v_s_430_){
_start:
{
uint8_t v_res_431_; lean_object* v_r_432_; 
v_res_431_ = l_BitVec_aandRec___redArg(v_w_427_, v_x_428_, v_y_429_, v_s_430_);
lean_dec(v_y_429_);
lean_dec(v_x_428_);
lean_dec(v_w_427_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
LEAN_EXPORT uint8_t l_BitVec_aandRec(lean_object* v_w_433_, lean_object* v_x_434_, lean_object* v_y_435_, lean_object* v_s_436_, lean_object* v_hs_437_){
_start:
{
uint8_t v___x_438_; 
v___x_438_ = l_BitVec_aandRec___redArg(v_w_433_, v_x_434_, v_y_435_, v_s_436_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_BitVec_aandRec___boxed(lean_object* v_w_439_, lean_object* v_x_440_, lean_object* v_y_441_, lean_object* v_s_442_, lean_object* v_hs_443_){
_start:
{
uint8_t v_res_444_; lean_object* v_r_445_; 
v_res_444_ = l_BitVec_aandRec(v_w_439_, v_x_440_, v_y_441_, v_s_442_, v_hs_443_);
lean_dec(v_y_441_);
lean_dec(v_x_440_);
lean_dec(v_w_439_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT uint8_t l_BitVec_resRec___redArg(lean_object* v_w_446_, lean_object* v_x_447_, lean_object* v_y_448_, lean_object* v_s_449_){
_start:
{
lean_object* v_zero_450_; uint8_t v_isZero_451_; lean_object* v_one_452_; lean_object* v_n_453_; uint8_t v_isZero_454_; 
v_zero_450_ = lean_unsigned_to_nat(0u);
v_isZero_451_ = lean_nat_dec_eq(v_s_449_, v_zero_450_);
v_one_452_ = lean_unsigned_to_nat(1u);
v_n_453_ = lean_nat_sub(v_s_449_, v_one_452_);
v_isZero_454_ = lean_nat_dec_eq(v_n_453_, v_zero_450_);
if (v_isZero_454_ == 1)
{
uint8_t v___x_455_; 
lean_dec(v_n_453_);
lean_dec(v_s_449_);
v___x_455_ = l_BitVec_aandRec___redArg(v_w_446_, v_x_447_, v_y_448_, v_one_452_);
return v___x_455_;
}
else
{
uint8_t v___x_456_; 
v___x_456_ = l_BitVec_resRec___redArg(v_w_446_, v_x_447_, v_y_448_, v_n_453_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; 
v___x_457_ = l_BitVec_aandRec___redArg(v_w_446_, v_x_447_, v_y_448_, v_s_449_);
return v___x_457_;
}
else
{
lean_dec(v_s_449_);
return v___x_456_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_resRec___redArg___boxed(lean_object* v_w_458_, lean_object* v_x_459_, lean_object* v_y_460_, lean_object* v_s_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l_BitVec_resRec___redArg(v_w_458_, v_x_459_, v_y_460_, v_s_461_);
lean_dec(v_y_460_);
lean_dec(v_x_459_);
lean_dec(v_w_458_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
LEAN_EXPORT uint8_t l_BitVec_resRec(lean_object* v_w_464_, lean_object* v_x_465_, lean_object* v_y_466_, lean_object* v_s_467_, lean_object* v_hs_468_, lean_object* v_hslt_469_){
_start:
{
uint8_t v___x_470_; 
v___x_470_ = l_BitVec_resRec___redArg(v_w_464_, v_x_465_, v_y_466_, v_s_467_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_BitVec_resRec___boxed(lean_object* v_w_471_, lean_object* v_x_472_, lean_object* v_y_473_, lean_object* v_s_474_, lean_object* v_hs_475_, lean_object* v_hslt_476_){
_start:
{
uint8_t v_res_477_; lean_object* v_r_478_; 
v_res_477_ = l_BitVec_resRec(v_w_471_, v_x_472_, v_y_473_, v_s_474_, v_hs_475_, v_hslt_476_);
lean_dec(v_y_473_);
lean_dec(v_x_472_);
lean_dec(v_w_471_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg(lean_object* v_s_479_, lean_object* v_h__1_480_, lean_object* v_h__2_481_){
_start:
{
lean_object* v_zero_482_; uint8_t v_isZero_483_; 
v_zero_482_ = lean_unsigned_to_nat(0u);
v_isZero_483_ = lean_nat_dec_eq(v_s_479_, v_zero_482_);
if (v_isZero_483_ == 1)
{
lean_object* v___x_484_; 
lean_dec(v_h__2_481_);
v___x_484_ = lean_apply_3(v_h__1_480_, lean_box(0), lean_box(0), lean_box(0));
return v___x_484_;
}
else
{
lean_object* v_one_485_; lean_object* v_n_486_; lean_object* v___x_487_; 
lean_dec(v_h__1_480_);
v_one_485_ = lean_unsigned_to_nat(1u);
v_n_486_ = lean_nat_sub(v_s_479_, v_one_485_);
v___x_487_ = lean_apply_4(v_h__2_481_, v_n_486_, lean_box(0), lean_box(0), lean_box(0));
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg___boxed(lean_object* v_s_488_, lean_object* v_h__1_489_, lean_object* v_h__2_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg(v_s_488_, v_h__1_489_, v_h__2_490_);
lean_dec(v_s_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter(lean_object* v_w_492_, lean_object* v_motive_493_, lean_object* v_s_494_, lean_object* v_hs_495_, lean_object* v_hslt_496_, lean_object* v_h__1_497_, lean_object* v_h__2_498_){
_start:
{
lean_object* v_zero_499_; uint8_t v_isZero_500_; 
v_zero_499_ = lean_unsigned_to_nat(0u);
v_isZero_500_ = lean_nat_dec_eq(v_s_494_, v_zero_499_);
if (v_isZero_500_ == 1)
{
lean_object* v___x_501_; 
lean_dec(v_h__2_498_);
v___x_501_ = lean_apply_3(v_h__1_497_, lean_box(0), lean_box(0), lean_box(0));
return v___x_501_;
}
else
{
lean_object* v_one_502_; lean_object* v_n_503_; lean_object* v___x_504_; 
lean_dec(v_h__1_497_);
v_one_502_ = lean_unsigned_to_nat(1u);
v_n_503_ = lean_nat_sub(v_s_494_, v_one_502_);
v___x_504_ = lean_apply_4(v_h__2_498_, v_n_503_, lean_box(0), lean_box(0), lean_box(0));
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___boxed(lean_object* v_w_505_, lean_object* v_motive_506_, lean_object* v_s_507_, lean_object* v_hs_508_, lean_object* v_hslt_509_, lean_object* v_h__1_510_, lean_object* v_h__2_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter(v_w_505_, v_motive_506_, v_s_507_, v_hs_508_, v_hslt_509_, v_h__1_510_, v_h__2_511_);
lean_dec(v_s_507_);
lean_dec(v_w_505_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg(lean_object* v_s_x27_513_, lean_object* v_h__1_514_, lean_object* v_h__2_515_){
_start:
{
lean_object* v_zero_516_; uint8_t v_isZero_517_; 
v_zero_516_ = lean_unsigned_to_nat(0u);
v_isZero_517_ = lean_nat_dec_eq(v_s_x27_513_, v_zero_516_);
if (v_isZero_517_ == 1)
{
lean_object* v___x_518_; 
lean_dec(v_h__2_515_);
v___x_518_ = lean_apply_4(v_h__1_514_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_518_;
}
else
{
lean_object* v_one_519_; lean_object* v_n_520_; lean_object* v___x_521_; 
lean_dec(v_h__1_514_);
v_one_519_ = lean_unsigned_to_nat(1u);
v_n_520_ = lean_nat_sub(v_s_x27_513_, v_one_519_);
v___x_521_ = lean_apply_5(v_h__2_515_, v_n_520_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg___boxed(lean_object* v_s_x27_522_, lean_object* v_h__1_523_, lean_object* v_h__2_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg(v_s_x27_522_, v_h__1_523_, v_h__2_524_);
lean_dec(v_s_x27_522_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter(lean_object* v_w_526_, lean_object* v_s_527_, lean_object* v_motive_528_, lean_object* v_s_x27_529_, lean_object* v_hs_530_, lean_object* v_hslt_531_, lean_object* v_hs0_532_, lean_object* v_h__1_533_, lean_object* v_h__2_534_){
_start:
{
lean_object* v_zero_535_; uint8_t v_isZero_536_; 
v_zero_535_ = lean_unsigned_to_nat(0u);
v_isZero_536_ = lean_nat_dec_eq(v_s_x27_529_, v_zero_535_);
if (v_isZero_536_ == 1)
{
lean_object* v___x_537_; 
lean_dec(v_h__2_534_);
v___x_537_ = lean_apply_4(v_h__1_533_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_537_;
}
else
{
lean_object* v_one_538_; lean_object* v_n_539_; lean_object* v___x_540_; 
lean_dec(v_h__1_533_);
v_one_538_ = lean_unsigned_to_nat(1u);
v_n_539_ = lean_nat_sub(v_s_x27_529_, v_one_538_);
v___x_540_ = lean_apply_5(v_h__2_534_, v_n_539_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___boxed(lean_object* v_w_541_, lean_object* v_s_542_, lean_object* v_motive_543_, lean_object* v_s_x27_544_, lean_object* v_hs_545_, lean_object* v_hslt_546_, lean_object* v_hs0_547_, lean_object* v_h__1_548_, lean_object* v_h__2_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter(v_w_541_, v_s_542_, v_motive_543_, v_s_x27_544_, v_hs_545_, v_hslt_546_, v_hs0_547_, v_h__1_548_, v_h__2_549_);
lean_dec(v_s_x27_544_);
lean_dec(v_s_542_);
lean_dec(v_w_541_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___redArg(lean_object* v_idx_551_, lean_object* v_len_552_, lean_object* v_x_553_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = l_BitVec_extractLsb_x27___redArg(v_idx_551_, v___x_554_, v_x_553_);
v___x_556_ = l_BitVec_setWidth(v___x_554_, v_len_552_, v___x_555_);
lean_dec(v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___redArg___boxed(lean_object* v_idx_557_, lean_object* v_len_558_, lean_object* v_x_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_BitVec_extractAndExtendBit___redArg(v_idx_557_, v_len_558_, v_x_559_);
lean_dec(v_x_559_);
lean_dec(v_len_558_);
lean_dec(v_idx_557_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit(lean_object* v_w_561_, lean_object* v_idx_562_, lean_object* v_len_563_, lean_object* v_x_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_BitVec_extractAndExtendBit___redArg(v_idx_562_, v_len_563_, v_x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___boxed(lean_object* v_w_566_, lean_object* v_idx_567_, lean_object* v_len_568_, lean_object* v_x_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_BitVec_extractAndExtendBit(v_w_566_, v_idx_567_, v_len_568_, v_x_569_);
lean_dec(v_x_569_);
lean_dec(v_len_568_);
lean_dec(v_idx_567_);
lean_dec(v_w_566_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___redArg(lean_object* v_w_571_, lean_object* v_k_572_, lean_object* v_len_573_, lean_object* v_x_574_, lean_object* v_acc_575_){
_start:
{
lean_object* v___x_576_; lean_object* v_zero_577_; uint8_t v_isZero_578_; 
v___x_576_ = lean_nat_sub(v_w_571_, v_k_572_);
v_zero_577_ = lean_unsigned_to_nat(0u);
v_isZero_578_ = lean_nat_dec_eq(v___x_576_, v_zero_577_);
lean_dec(v___x_576_);
if (v_isZero_578_ == 1)
{
lean_dec(v_k_572_);
return v_acc_575_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v_acc_x27_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_579_ = lean_nat_mul(v_k_572_, v_len_573_);
v___x_580_ = l_BitVec_extractAndExtendBit___redArg(v_k_572_, v_len_573_, v_x_574_);
v_acc_x27_581_ = l_BitVec_append___redArg(v___x_579_, v___x_580_, v_acc_575_);
lean_dec(v_acc_575_);
lean_dec(v___x_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_unsigned_to_nat(1u);
v___x_583_ = lean_nat_add(v_k_572_, v___x_582_);
lean_dec(v_k_572_);
v_k_572_ = v___x_583_;
v_acc_575_ = v_acc_x27_581_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___redArg___boxed(lean_object* v_w_585_, lean_object* v_k_586_, lean_object* v_len_587_, lean_object* v_x_588_, lean_object* v_acc_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_BitVec_extractAndExtendAux___redArg(v_w_585_, v_k_586_, v_len_587_, v_x_588_, v_acc_589_);
lean_dec(v_x_588_);
lean_dec(v_len_587_);
lean_dec(v_w_585_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux(lean_object* v_w_591_, lean_object* v_k_592_, lean_object* v_len_593_, lean_object* v_x_594_, lean_object* v_acc_595_, lean_object* v_hle_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_BitVec_extractAndExtendAux___redArg(v_w_591_, v_k_592_, v_len_593_, v_x_594_, v_acc_595_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___boxed(lean_object* v_w_598_, lean_object* v_k_599_, lean_object* v_len_600_, lean_object* v_x_601_, lean_object* v_acc_602_, lean_object* v_hle_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_BitVec_extractAndExtendAux(v_w_598_, v_k_599_, v_len_600_, v_x_601_, v_acc_602_, v_hle_603_);
lean_dec(v_x_601_);
lean_dec(v_len_600_);
lean_dec(v_w_598_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg(lean_object* v_x_605_, lean_object* v_h__1_606_, lean_object* v_h__2_607_){
_start:
{
lean_object* v_zero_608_; uint8_t v_isZero_609_; 
v_zero_608_ = lean_unsigned_to_nat(0u);
v_isZero_609_ = lean_nat_dec_eq(v_x_605_, v_zero_608_);
if (v_isZero_609_ == 1)
{
lean_object* v___x_610_; 
lean_dec(v_h__2_607_);
v___x_610_ = lean_apply_1(v_h__1_606_, lean_box(0));
return v___x_610_;
}
else
{
lean_object* v_one_611_; lean_object* v_n_612_; lean_object* v___x_613_; 
lean_dec(v_h__1_606_);
v_one_611_ = lean_unsigned_to_nat(1u);
v_n_612_ = lean_nat_sub(v_x_605_, v_one_611_);
v___x_613_ = lean_apply_2(v_h__2_607_, v_n_612_, lean_box(0));
return v___x_613_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg___boxed(lean_object* v_x_614_, lean_object* v_h__1_615_, lean_object* v_h__2_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg(v_x_614_, v_h__1_615_, v_h__2_616_);
lean_dec(v_x_614_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter(lean_object* v_motive_618_, lean_object* v_x_619_, lean_object* v_h__1_620_, lean_object* v_h__2_621_){
_start:
{
lean_object* v_zero_622_; uint8_t v_isZero_623_; 
v_zero_622_ = lean_unsigned_to_nat(0u);
v_isZero_623_ = lean_nat_dec_eq(v_x_619_, v_zero_622_);
if (v_isZero_623_ == 1)
{
lean_object* v___x_624_; 
lean_dec(v_h__2_621_);
v___x_624_ = lean_apply_1(v_h__1_620_, lean_box(0));
return v___x_624_;
}
else
{
lean_object* v_one_625_; lean_object* v_n_626_; lean_object* v___x_627_; 
lean_dec(v_h__1_620_);
v_one_625_ = lean_unsigned_to_nat(1u);
v_n_626_ = lean_nat_sub(v_x_619_, v_one_625_);
v___x_627_ = lean_apply_2(v_h__2_621_, v_n_626_, lean_box(0));
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___boxed(lean_object* v_motive_628_, lean_object* v_x_629_, lean_object* v_h__1_630_, lean_object* v_h__2_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter(v_motive_628_, v_x_629_, v_h__1_630_, v_h__2_631_);
lean_dec(v_x_629_);
return v_res_632_;
}
}
static lean_object* _init_l_BitVec_extractAndExtend___closed__0(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = l_BitVec_ofNat(v___x_633_, v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtend(lean_object* v_w_635_, lean_object* v_len_636_, lean_object* v_x_637_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = lean_obj_once(&l_BitVec_extractAndExtend___closed__0, &l_BitVec_extractAndExtend___closed__0_once, _init_l_BitVec_extractAndExtend___closed__0);
v___x_640_ = l_BitVec_extractAndExtendAux___redArg(v_w_635_, v___x_638_, v_len_636_, v_x_637_, v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtend___boxed(lean_object* v_w_641_, lean_object* v_len_642_, lean_object* v_x_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_BitVec_extractAndExtend(v_w_641_, v_len_642_, v_x_643_);
lean_dec(v_x_643_);
lean_dec(v_len_642_);
lean_dec(v_w_641_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___redArg(lean_object* v_len_645_, lean_object* v_w_646_, lean_object* v_iterNum_647_, lean_object* v_oldLayer_648_, lean_object* v_newLayer_649_){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_650_ = lean_unsigned_to_nat(2u);
v___x_651_ = lean_nat_mul(v_iterNum_647_, v___x_650_);
v___x_652_ = lean_nat_sub(v_len_645_, v___x_651_);
lean_dec(v___x_651_);
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = lean_nat_dec_eq(v___x_652_, v___x_653_);
lean_dec(v___x_652_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v_op1_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v_op2_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v_newLayer_x27_664_; lean_object* v___x_665_; 
v___x_655_ = lean_nat_mul(v___x_650_, v_iterNum_647_);
v___x_656_ = lean_nat_mul(v___x_655_, v_w_646_);
v_op1_657_ = l_BitVec_extractLsb_x27___redArg(v___x_656_, v_w_646_, v_oldLayer_648_);
lean_dec(v___x_656_);
v___x_658_ = lean_unsigned_to_nat(1u);
v___x_659_ = lean_nat_add(v___x_655_, v___x_658_);
lean_dec(v___x_655_);
v___x_660_ = lean_nat_mul(v___x_659_, v_w_646_);
lean_dec(v___x_659_);
v_op2_661_ = l_BitVec_extractLsb_x27___redArg(v___x_660_, v_w_646_, v_oldLayer_648_);
lean_dec(v___x_660_);
v___x_662_ = lean_nat_mul(v_iterNum_647_, v_w_646_);
v___x_663_ = l_BitVec_add(v_w_646_, v_op1_657_, v_op2_661_);
lean_dec(v_op2_661_);
lean_dec(v_op1_657_);
v_newLayer_x27_664_ = l_BitVec_append___redArg(v___x_662_, v___x_663_, v_newLayer_649_);
lean_dec(v_newLayer_649_);
lean_dec(v___x_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_nat_add(v_iterNum_647_, v___x_658_);
lean_dec(v_iterNum_647_);
v_iterNum_647_ = v___x_665_;
v_newLayer_649_ = v_newLayer_x27_664_;
goto _start;
}
else
{
lean_dec(v_iterNum_647_);
return v_newLayer_649_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___redArg___boxed(lean_object* v_len_667_, lean_object* v_w_668_, lean_object* v_iterNum_669_, lean_object* v_oldLayer_670_, lean_object* v_newLayer_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_BitVec_cpopLayer___redArg(v_len_667_, v_w_668_, v_iterNum_669_, v_oldLayer_670_, v_newLayer_671_);
lean_dec(v_oldLayer_670_);
lean_dec(v_w_668_);
lean_dec(v_len_667_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer(lean_object* v_len_673_, lean_object* v_w_674_, lean_object* v_iterNum_675_, lean_object* v_oldLayer_676_, lean_object* v_newLayer_677_, lean_object* v_hold_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_BitVec_cpopLayer___redArg(v_len_673_, v_w_674_, v_iterNum_675_, v_oldLayer_676_, v_newLayer_677_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___boxed(lean_object* v_len_680_, lean_object* v_w_681_, lean_object* v_iterNum_682_, lean_object* v_oldLayer_683_, lean_object* v_newLayer_684_, lean_object* v_hold_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_BitVec_cpopLayer(v_len_680_, v_w_681_, v_iterNum_682_, v_oldLayer_683_, v_newLayer_684_, v_hold_685_);
lean_dec(v_oldLayer_683_);
lean_dec(v_w_681_);
lean_dec(v_len_680_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopTree(lean_object* v_len_687_, lean_object* v_w_688_, lean_object* v_l_689_){
_start:
{
lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_nat_dec_eq(v_len_687_, v___x_690_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = lean_unsigned_to_nat(1u);
v___x_693_ = lean_nat_dec_eq(v_len_687_, v___x_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_694_ = lean_nat_add(v_len_687_, v___x_692_);
v___x_695_ = lean_nat_shiftr(v___x_694_, v___x_692_);
lean_dec(v___x_694_);
v___x_696_ = lean_obj_once(&l_BitVec_extractAndExtend___closed__0, &l_BitVec_extractAndExtend___closed__0_once, _init_l_BitVec_extractAndExtend___closed__0);
v___x_697_ = l_BitVec_cpopLayer___redArg(v_len_687_, v_w_688_, v___x_690_, v_l_689_, v___x_696_);
lean_dec(v_l_689_);
lean_dec(v_len_687_);
v_len_687_ = v___x_695_;
v_l_689_ = v___x_697_;
goto _start;
}
else
{
lean_dec(v_len_687_);
return v_l_689_;
}
}
else
{
lean_object* v___x_699_; 
lean_dec(v_l_689_);
lean_dec(v_len_687_);
v___x_699_ = l_BitVec_ofNat(v_w_688_, v___x_690_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopTree___boxed(lean_object* v_len_700_, lean_object* v_w_701_, lean_object* v_l_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_BitVec_cpopTree(v_len_700_, v_w_701_, v_l_702_);
lean_dec(v_w_701_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopRec(lean_object* v_w_704_, lean_object* v_x_705_){
_start:
{
lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = lean_unsigned_to_nat(1u);
v___x_707_ = lean_nat_dec_lt(v___x_706_, v_w_704_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_nat_dec_lt(v___x_708_, v_w_704_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; 
v___x_710_ = l_BitVec_ofNat(v_w_704_, v___x_708_);
lean_dec(v_w_704_);
return v___x_710_;
}
else
{
lean_dec(v_w_704_);
lean_inc(v_x_705_);
return v_x_705_;
}
}
else
{
lean_object* v_extendedBits_711_; lean_object* v___x_712_; 
v_extendedBits_711_ = l_BitVec_extractAndExtend(v_w_704_, v_w_704_, v_x_705_);
lean_inc(v_w_704_);
v___x_712_ = l_BitVec_cpopTree(v_w_704_, v_w_704_, v_extendedBits_711_);
lean_dec(v_w_704_);
return v___x_712_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopRec___boxed(lean_object* v_w_713_, lean_object* v_x_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_BitVec_cpopRec(v_w_713_, v_x_714_);
lean_dec(v_x_714_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(lean_object* v_w_716_, lean_object* v_x_717_, lean_object* v_rem_718_, lean_object* v_acc_719_){
_start:
{
lean_object* v_zero_720_; uint8_t v_isZero_721_; 
v_zero_720_ = lean_unsigned_to_nat(0u);
v_isZero_721_ = lean_nat_dec_eq(v_rem_718_, v_zero_720_);
if (v_isZero_721_ == 1)
{
lean_dec(v_rem_718_);
return v_acc_719_;
}
else
{
lean_object* v_one_722_; lean_object* v_n_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_one_722_ = lean_unsigned_to_nat(1u);
v_n_723_ = lean_nat_sub(v_rem_718_, v_one_722_);
lean_dec(v_rem_718_);
v___x_724_ = lean_nat_mul(v_n_723_, v_w_716_);
v___x_725_ = l_BitVec_extractLsb_x27___redArg(v___x_724_, v_w_716_, v_x_717_);
lean_dec(v___x_724_);
v___x_726_ = l_BitVec_add(v_w_716_, v_acc_719_, v___x_725_);
lean_dec(v___x_725_);
lean_dec(v_acc_719_);
v_rem_718_ = v_n_723_;
v_acc_719_ = v___x_726_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg___boxed(lean_object* v_w_728_, lean_object* v_x_729_, lean_object* v_rem_730_, lean_object* v_acc_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_728_, v_x_729_, v_rem_730_, v_acc_731_);
lean_dec(v_x_729_);
lean_dec(v_w_728_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux(lean_object* v_l_733_, lean_object* v_w_734_, lean_object* v_x_735_, lean_object* v_rem_736_, lean_object* v_acc_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_734_, v_x_735_, v_rem_736_, v_acc_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___boxed(lean_object* v_l_739_, lean_object* v_w_740_, lean_object* v_x_741_, lean_object* v_rem_742_, lean_object* v_acc_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux(v_l_739_, v_w_740_, v_x_741_, v_rem_742_, v_acc_743_);
lean_dec(v_x_741_);
lean_dec(v_w_740_);
lean_dec(v_l_739_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec(lean_object* v_l_745_, lean_object* v_w_746_, lean_object* v_x_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = l_BitVec_ofNat(v_w_746_, v___x_748_);
v___x_750_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_746_, v_x_747_, v_l_745_, v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec___boxed(lean_object* v_l_751_, lean_object* v_w_752_, lean_object* v_x_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec(v_l_751_, v_w_752_, v_x_753_);
lean_dec(v_x_753_);
lean_dec(v_w_752_);
return v_res_754_;
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
