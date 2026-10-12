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
uint8_t l_Bool_atLeastTwo(uint8_t v_a_1_, uint8_t v_b_2_, uint8_t v_c_3_){
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
LEAN_EXPORT void l_Bool_atLeastTwo_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_1_ = stack[0].m_num;
uint8_t v_b_2_ = stack[1].m_num;
uint8_t v_c_3_ = stack[2].m_num;
uint8_t v_res_5_;
v_res_5_ = l_Bool_atLeastTwo(v_a_1_, v_b_2_, v_c_3_);
stack->m_num = v_res_5_;
}
LEAN_EXPORT lean_object* l_Bool_atLeastTwo___boxed(lean_object* v_a_6_, lean_object* v_b_7_, lean_object* v_c_8_){
_start:
{
uint8_t v_a_boxed_9_; uint8_t v_b_boxed_10_; uint8_t v_c_boxed_11_; uint8_t v_res_12_; lean_object* v_r_13_; 
v_a_boxed_9_ = lean_unbox(v_a_6_);
v_b_boxed_10_ = lean_unbox(v_b_7_);
v_c_boxed_11_ = lean_unbox(v_c_8_);
v_res_12_ = l_Bool_atLeastTwo(v_a_boxed_9_, v_b_boxed_10_, v_c_boxed_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
uint8_t l_BitVec_carry___redArg(lean_object* v_i_14_, lean_object* v_x_15_, lean_object* v_y_16_, uint8_t v_c_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_18_ = lean_unsigned_to_nat(2u);
v___x_19_ = lean_nat_pow(v___x_18_, v_i_14_);
v___x_20_ = lean_nat_mod(v_x_15_, v___x_19_);
v___x_21_ = lean_nat_mod(v_y_16_, v___x_19_);
v___x_22_ = lean_nat_add(v___x_20_, v___x_21_);
lean_dec(v___x_21_);
lean_dec(v___x_20_);
v___x_23_ = l_Bool_toNat(v_c_17_);
v___x_24_ = lean_nat_add(v___x_22_, v___x_23_);
lean_dec(v___x_23_);
lean_dec(v___x_22_);
v___x_25_ = lean_nat_dec_le(v___x_19_, v___x_24_);
lean_dec(v___x_24_);
lean_dec(v___x_19_);
return v___x_25_;
}
}
LEAN_EXPORT void l_BitVec_carry___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_14_ = stack[0].m_obj;
lean_object* v_x_15_ = stack[1].m_obj;
lean_object* v_y_16_ = stack[2].m_obj;
uint8_t v_c_17_ = stack[3].m_num;
uint8_t v_res_26_;
v_res_26_ = l_BitVec_carry___redArg(v_i_14_, v_x_15_, v_y_16_, v_c_17_);
stack->m_num = v_res_26_;
}
LEAN_EXPORT lean_object* l_BitVec_carry___redArg___boxed(lean_object* v_i_27_, lean_object* v_x_28_, lean_object* v_y_29_, lean_object* v_c_30_){
_start:
{
uint8_t v_c_boxed_31_; uint8_t v_res_32_; lean_object* v_r_33_; 
v_c_boxed_31_ = lean_unbox(v_c_30_);
v_res_32_ = l_BitVec_carry___redArg(v_i_27_, v_x_28_, v_y_29_, v_c_boxed_31_);
lean_dec(v_y_29_);
lean_dec(v_x_28_);
lean_dec(v_i_27_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
uint8_t l_BitVec_carry(lean_object* v_w_34_, lean_object* v_i_35_, lean_object* v_x_36_, lean_object* v_y_37_, uint8_t v_c_38_){
_start:
{
uint8_t v___x_39_; 
v___x_39_ = l_BitVec_carry___redArg(v_i_35_, v_x_36_, v_y_37_, v_c_38_);
return v___x_39_;
}
}
LEAN_EXPORT void l_BitVec_carry_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_34_ = stack[0].m_obj;
lean_object* v_i_35_ = stack[1].m_obj;
lean_object* v_x_36_ = stack[2].m_obj;
lean_object* v_y_37_ = stack[3].m_obj;
uint8_t v_c_38_ = stack[4].m_num;
uint8_t v_res_40_;
v_res_40_ = l_BitVec_carry(v_w_34_, v_i_35_, v_x_36_, v_y_37_, v_c_38_);
stack->m_num = v_res_40_;
}
LEAN_EXPORT lean_object* l_BitVec_carry___boxed(lean_object* v_w_41_, lean_object* v_i_42_, lean_object* v_x_43_, lean_object* v_y_44_, lean_object* v_c_45_){
_start:
{
uint8_t v_c_boxed_46_; uint8_t v_res_47_; lean_object* v_r_48_; 
v_c_boxed_46_ = lean_unbox(v_c_45_);
v_res_47_ = l_BitVec_carry(v_w_41_, v_i_42_, v_x_43_, v_y_44_, v_c_boxed_46_);
lean_dec(v_y_44_);
lean_dec(v_x_43_);
lean_dec(v_i_42_);
lean_dec(v_w_41_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
lean_object* l_BitVec_adcb(uint8_t v_x_49_, uint8_t v_y_50_, uint8_t v_c_51_){
_start:
{
uint8_t v___y_53_; uint8_t v___y_59_; uint8_t v___y_65_; uint8_t v___y_67_; uint8_t v___y_69_; 
if (v_x_49_ == 0)
{
goto v___jp_70_;
}
else
{
if (v_y_50_ == 0)
{
goto v___jp_70_;
}
else
{
v___y_69_ = v_y_50_;
goto v___jp_68_;
}
}
v___jp_52_:
{
uint8_t v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = 1;
v___x_55_ = lean_box(v___y_53_);
v___x_56_ = lean_box(v___x_54_);
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
return v___x_57_;
}
v___jp_58_:
{
uint8_t v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_60_ = 0;
v___x_61_ = lean_box(v___y_59_);
v___x_62_ = lean_box(v___x_60_);
v___x_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_61_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
return v___x_63_;
}
v___jp_64_:
{
if (v_x_49_ == 0)
{
v___y_53_ = v___y_65_;
goto v___jp_52_;
}
else
{
v___y_59_ = v___y_65_;
goto v___jp_58_;
}
}
v___jp_66_:
{
if (v_x_49_ == 0)
{
v___y_59_ = v___y_67_;
goto v___jp_58_;
}
else
{
v___y_53_ = v___y_67_;
goto v___jp_52_;
}
}
v___jp_68_:
{
if (v_c_51_ == 0)
{
if (v_y_50_ == 0)
{
v___y_67_ = v___y_69_;
goto v___jp_66_;
}
else
{
v___y_65_ = v___y_69_;
goto v___jp_64_;
}
}
else
{
if (v_y_50_ == 0)
{
v___y_65_ = v___y_69_;
goto v___jp_64_;
}
else
{
v___y_67_ = v___y_69_;
goto v___jp_66_;
}
}
}
v___jp_70_:
{
if (v_x_49_ == 0)
{
if (v_y_50_ == 0)
{
v___y_69_ = v_y_50_;
goto v___jp_68_;
}
else
{
v___y_69_ = v_c_51_;
goto v___jp_68_;
}
}
else
{
if (v_c_51_ == 0)
{
if (v_y_50_ == 0)
{
v___y_69_ = v_y_50_;
goto v___jp_68_;
}
else
{
v___y_69_ = v_c_51_;
goto v___jp_68_;
}
}
else
{
v___y_69_ = v_c_51_;
goto v___jp_68_;
}
}
}
}
}
LEAN_EXPORT void l_BitVec_adcb_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_49_ = stack[0].m_num;
uint8_t v_y_50_ = stack[1].m_num;
uint8_t v_c_51_ = stack[2].m_num;
lean_object* v_res_71_;
v_res_71_ = l_BitVec_adcb(v_x_49_, v_y_50_, v_c_51_);
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l_BitVec_adcb___boxed(lean_object* v_x_72_, lean_object* v_y_73_, lean_object* v_c_74_){
_start:
{
uint8_t v_x_boxed_75_; uint8_t v_y_boxed_76_; uint8_t v_c_boxed_77_; lean_object* v_res_78_; 
v_x_boxed_75_ = lean_unbox(v_x_72_);
v_y_boxed_76_ = lean_unbox(v_y_73_);
v_c_boxed_77_ = lean_unbox(v_c_74_);
v_res_78_ = l_BitVec_adcb(v_x_boxed_75_, v_y_boxed_76_, v_c_boxed_77_);
return v_res_78_;
}
}
lean_object* l_BitVec_adc___lam__0(lean_object* v_x_79_, lean_object* v_y_80_, lean_object* v_i_81_, uint8_t v_c_82_){
_start:
{
uint8_t v___x_83_; uint8_t v___x_84_; lean_object* v___x_85_; 
v___x_83_ = l_Nat_testBit(v_x_79_, v_i_81_);
v___x_84_ = l_Nat_testBit(v_y_80_, v_i_81_);
v___x_85_ = l_BitVec_adcb(v___x_83_, v___x_84_, v_c_82_);
return v___x_85_;
}
}
LEAN_EXPORT void l_BitVec_adc___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_79_ = stack[0].m_obj;
lean_object* v_y_80_ = stack[1].m_obj;
lean_object* v_i_81_ = stack[2].m_obj;
uint8_t v_c_82_ = stack[3].m_num;
lean_object* v_res_86_;
v_res_86_ = l_BitVec_adc___lam__0(v_x_79_, v_y_80_, v_i_81_, v_c_82_);
stack->m_obj
 = v_res_86_;
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
lean_object* l_BitVec_adc(lean_object* v_w_93_, lean_object* v_x_94_, lean_object* v_y_95_, uint8_t v_s_96_){
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
LEAN_EXPORT void l_BitVec_adc_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_93_ = stack[0].m_obj;
lean_object* v_x_94_ = stack[1].m_obj;
lean_object* v_y_95_ = stack[2].m_obj;
uint8_t v_s_96_ = stack[3].m_num;
lean_object* v_res_100_;
v_res_100_ = l_BitVec_adc(v_w_93_, v_x_94_, v_y_95_, v_s_96_);
stack->m_obj
 = v_res_100_;
}
LEAN_EXPORT lean_object* l_BitVec_adc___boxed(lean_object* v_w_101_, lean_object* v_x_102_, lean_object* v_y_103_, lean_object* v_s_104_){
_start:
{
uint8_t v_s_boxed_105_; lean_object* v_res_106_; 
v_s_boxed_105_ = lean_unbox(v_s_104_);
v_res_106_ = l_BitVec_adc(v_w_101_, v_x_102_, v_y_103_, v_s_boxed_105_);
lean_dec(v_w_101_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_BitVec_mulRec(lean_object* v_w_107_, lean_object* v_x_108_, lean_object* v_y_109_, lean_object* v_s_110_){
_start:
{
lean_object* v___y_112_; uint8_t v___x_119_; 
v___x_119_ = l_Nat_testBit(v_y_109_, v_s_110_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = l_BitVec_ofNat(v_w_107_, v___x_120_);
v___y_112_ = v___x_121_;
goto v___jp_111_;
}
else
{
lean_object* v___x_122_; 
v___x_122_ = l_BitVec_shiftLeft(v_w_107_, v_x_108_, v_s_110_);
v___y_112_ = v___x_122_;
goto v___jp_111_;
}
v___jp_111_:
{
lean_object* v_zero_113_; uint8_t v_isZero_114_; 
v_zero_113_ = lean_unsigned_to_nat(0u);
v_isZero_114_ = lean_nat_dec_eq(v_s_110_, v_zero_113_);
if (v_isZero_114_ == 1)
{
return v___y_112_;
}
else
{
lean_object* v_one_115_; lean_object* v_n_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_one_115_ = lean_unsigned_to_nat(1u);
v_n_116_ = lean_nat_sub(v_s_110_, v_one_115_);
v___x_117_ = l_BitVec_mulRec(v_w_107_, v_x_108_, v_y_109_, v_n_116_);
lean_dec(v_n_116_);
v___x_118_ = l_BitVec_add(v_w_107_, v___x_117_, v___y_112_);
lean_dec(v___y_112_);
lean_dec(v___x_117_);
return v___x_118_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_mulRec___boxed(lean_object* v_w_123_, lean_object* v_x_124_, lean_object* v_y_125_, lean_object* v_s_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_BitVec_mulRec(v_w_123_, v_x_124_, v_y_125_, v_s_126_);
lean_dec(v_s_126_);
lean_dec(v_y_125_);
lean_dec(v_x_124_);
lean_dec(v_w_123_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftRec(lean_object* v_w_u2081_128_, lean_object* v_w_u2082_129_, lean_object* v_x_130_, lean_object* v_y_131_, lean_object* v_n_132_){
_start:
{
lean_object* v___x_133_; lean_object* v_shiftAmt_134_; lean_object* v_zero_135_; uint8_t v_isZero_136_; 
v___x_133_ = l_BitVec_twoPow(v_w_u2082_129_, v_n_132_);
v_shiftAmt_134_ = lean_nat_land(v_y_131_, v___x_133_);
lean_dec(v___x_133_);
v_zero_135_ = lean_unsigned_to_nat(0u);
v_isZero_136_ = lean_nat_dec_eq(v_n_132_, v_zero_135_);
if (v_isZero_136_ == 1)
{
lean_object* v___x_137_; 
v___x_137_ = l_BitVec_shiftLeft(v_w_u2081_128_, v_x_130_, v_shiftAmt_134_);
lean_dec(v_shiftAmt_134_);
return v___x_137_;
}
else
{
lean_object* v_one_138_; lean_object* v_n_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_one_138_ = lean_unsigned_to_nat(1u);
v_n_139_ = lean_nat_sub(v_n_132_, v_one_138_);
v___x_140_ = l_BitVec_shiftLeftRec(v_w_u2081_128_, v_w_u2082_129_, v_x_130_, v_y_131_, v_n_139_);
lean_dec(v_n_139_);
v___x_141_ = l_BitVec_shiftLeft(v_w_u2081_128_, v___x_140_, v_shiftAmt_134_);
lean_dec(v_shiftAmt_134_);
lean_dec(v___x_140_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftRec___boxed(lean_object* v_w_u2081_142_, lean_object* v_w_u2082_143_, lean_object* v_x_144_, lean_object* v_y_145_, lean_object* v_n_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_BitVec_shiftLeftRec(v_w_u2081_142_, v_w_u2082_143_, v_x_144_, v_y_145_, v_n_146_);
lean_dec(v_n_146_);
lean_dec(v_y_145_);
lean_dec(v_x_144_);
lean_dec(v_w_u2082_143_);
lean_dec(v_w_u2081_142_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_BitVec_DivModState_init(lean_object* v_w_148_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = l_BitVec_ofNat(v_w_148_, v___x_149_);
lean_inc(v___x_150_);
v___x_151_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_151_, 0, v_w_148_);
lean_ctor_set(v___x_151_, 1, v___x_149_);
lean_ctor_set(v___x_151_, 2, v___x_150_);
lean_ctor_set(v___x_151_, 3, v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_BitVec_divSubtractShift(lean_object* v_w_152_, lean_object* v_args_153_, lean_object* v_qr_154_){
_start:
{
lean_object* v_n_155_; lean_object* v_d_156_; lean_object* v_wn_157_; lean_object* v_wr_158_; lean_object* v_q_159_; lean_object* v_r_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_182_; 
v_n_155_ = lean_ctor_get(v_args_153_, 0);
v_d_156_ = lean_ctor_get(v_args_153_, 1);
v_wn_157_ = lean_ctor_get(v_qr_154_, 0);
v_wr_158_ = lean_ctor_get(v_qr_154_, 1);
v_q_159_ = lean_ctor_get(v_qr_154_, 2);
v_r_160_ = lean_ctor_get(v_qr_154_, 3);
v_isSharedCheck_182_ = !lean_is_exclusive(v_qr_154_);
if (v_isSharedCheck_182_ == 0)
{
v___x_162_ = v_qr_154_;
v_isShared_163_ = v_isSharedCheck_182_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_r_160_);
lean_inc(v_q_159_);
lean_inc(v_wr_158_);
lean_inc(v_wn_157_);
lean_dec(v_qr_154_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_182_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v_wn_165_; lean_object* v_wr_166_; uint8_t v___x_167_; lean_object* v_r_x27_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_164_ = lean_unsigned_to_nat(1u);
v_wn_165_ = lean_nat_sub(v_wn_157_, v___x_164_);
lean_dec(v_wn_157_);
v_wr_166_ = lean_nat_add(v_wr_158_, v___x_164_);
lean_dec(v_wr_158_);
v___x_167_ = l_Nat_testBit(v_n_155_, v_wn_165_);
v_r_x27_168_ = l_BitVec_shiftConcat(v_w_152_, v_r_160_, v___x_167_);
lean_dec(v_r_160_);
v___x_169_ = lean_nat_add(v_r_x27_168_, v___x_164_);
v___x_170_ = lean_nat_dec_le(v___x_169_, v_d_156_);
lean_dec(v___x_169_);
if (v___x_170_ == 0)
{
uint8_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_171_ = 1;
v___x_172_ = l_BitVec_shiftConcat(v_w_152_, v_q_159_, v___x_171_);
lean_dec(v_q_159_);
v___x_173_ = l_BitVec_sub(v_w_152_, v_r_x27_168_, v_d_156_);
lean_dec(v_r_x27_168_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 3, v___x_173_);
lean_ctor_set(v___x_162_, 2, v___x_172_);
lean_ctor_set(v___x_162_, 1, v_wr_166_);
lean_ctor_set(v___x_162_, 0, v_wn_165_);
v___x_175_ = v___x_162_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_wn_165_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_wr_166_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_176_, 3, v___x_173_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
else
{
uint8_t v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_177_ = 0;
v___x_178_ = l_BitVec_shiftConcat(v_w_152_, v_q_159_, v___x_177_);
lean_dec(v_q_159_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 3, v_r_x27_168_);
lean_ctor_set(v___x_162_, 2, v___x_178_);
lean_ctor_set(v___x_162_, 1, v_wr_166_);
lean_ctor_set(v___x_162_, 0, v_wn_165_);
v___x_180_ = v___x_162_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_wn_165_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_wr_166_);
lean_ctor_set(v_reuseFailAlloc_181_, 2, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_181_, 3, v_r_x27_168_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_divSubtractShift___boxed(lean_object* v_w_183_, lean_object* v_args_184_, lean_object* v_qr_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_BitVec_divSubtractShift(v_w_183_, v_args_184_, v_qr_185_);
lean_dec_ref(v_args_184_);
lean_dec(v_w_183_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_BitVec_divRec(lean_object* v_w_187_, lean_object* v_m_188_, lean_object* v_args_189_, lean_object* v_qr_190_){
_start:
{
lean_object* v_zero_191_; uint8_t v_isZero_192_; 
v_zero_191_ = lean_unsigned_to_nat(0u);
v_isZero_192_ = lean_nat_dec_eq(v_m_188_, v_zero_191_);
if (v_isZero_192_ == 1)
{
lean_dec(v_m_188_);
return v_qr_190_;
}
else
{
lean_object* v_one_193_; lean_object* v_n_194_; lean_object* v___x_195_; 
v_one_193_ = lean_unsigned_to_nat(1u);
v_n_194_ = lean_nat_sub(v_m_188_, v_one_193_);
lean_dec(v_m_188_);
v___x_195_ = l_BitVec_divSubtractShift(v_w_187_, v_args_189_, v_qr_190_);
v_m_188_ = v_n_194_;
v_qr_190_ = v___x_195_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_divRec___boxed(lean_object* v_w_197_, lean_object* v_m_198_, lean_object* v_args_199_, lean_object* v_qr_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_BitVec_divRec(v_w_197_, v_m_198_, v_args_199_, v_qr_200_);
lean_dec_ref(v_args_199_);
lean_dec(v_w_197_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRightRec(lean_object* v_w_u2081_202_, lean_object* v_w_u2082_203_, lean_object* v_x_204_, lean_object* v_y_205_, lean_object* v_n_206_){
_start:
{
lean_object* v___x_207_; lean_object* v_shiftAmt_208_; lean_object* v_zero_209_; uint8_t v_isZero_210_; 
v___x_207_ = l_BitVec_twoPow(v_w_u2082_203_, v_n_206_);
v_shiftAmt_208_ = lean_nat_land(v_y_205_, v___x_207_);
lean_dec(v___x_207_);
v_zero_209_ = lean_unsigned_to_nat(0u);
v_isZero_210_ = lean_nat_dec_eq(v_n_206_, v_zero_209_);
if (v_isZero_210_ == 1)
{
lean_object* v___x_211_; 
v___x_211_ = l_BitVec_sshiftRight(v_w_u2081_202_, v_x_204_, v_shiftAmt_208_);
lean_dec(v_shiftAmt_208_);
return v___x_211_;
}
else
{
lean_object* v_one_212_; lean_object* v_n_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_one_212_ = lean_unsigned_to_nat(1u);
v_n_213_ = lean_nat_sub(v_n_206_, v_one_212_);
v___x_214_ = l_BitVec_sshiftRightRec(v_w_u2081_202_, v_w_u2082_203_, v_x_204_, v_y_205_, v_n_213_);
lean_dec(v_n_213_);
v___x_215_ = l_BitVec_sshiftRight(v_w_u2081_202_, v___x_214_, v_shiftAmt_208_);
lean_dec(v_shiftAmt_208_);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRightRec___boxed(lean_object* v_w_u2081_216_, lean_object* v_w_u2082_217_, lean_object* v_x_218_, lean_object* v_y_219_, lean_object* v_n_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_BitVec_sshiftRightRec(v_w_u2081_216_, v_w_u2082_217_, v_x_218_, v_y_219_, v_n_220_);
lean_dec(v_n_220_);
lean_dec(v_y_219_);
lean_dec(v_w_u2082_217_);
lean_dec(v_w_u2081_216_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___redArg(lean_object* v_w_u2082_222_, lean_object* v_x_223_, lean_object* v_y_224_, lean_object* v_n_225_){
_start:
{
lean_object* v___x_226_; lean_object* v_shiftAmt_227_; lean_object* v_zero_228_; uint8_t v_isZero_229_; 
v___x_226_ = l_BitVec_twoPow(v_w_u2082_222_, v_n_225_);
v_shiftAmt_227_ = lean_nat_land(v_y_224_, v___x_226_);
lean_dec(v___x_226_);
v_zero_228_ = lean_unsigned_to_nat(0u);
v_isZero_229_ = lean_nat_dec_eq(v_n_225_, v_zero_228_);
if (v_isZero_229_ == 1)
{
lean_object* v___x_230_; 
v___x_230_ = lean_nat_shiftr(v_x_223_, v_shiftAmt_227_);
lean_dec(v_shiftAmt_227_);
return v___x_230_;
}
else
{
lean_object* v_one_231_; lean_object* v_n_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_one_231_ = lean_unsigned_to_nat(1u);
v_n_232_ = lean_nat_sub(v_n_225_, v_one_231_);
v___x_233_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_222_, v_x_223_, v_y_224_, v_n_232_);
lean_dec(v_n_232_);
v___x_234_ = lean_nat_shiftr(v___x_233_, v_shiftAmt_227_);
lean_dec(v_shiftAmt_227_);
lean_dec(v___x_233_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___redArg___boxed(lean_object* v_w_u2082_235_, lean_object* v_x_236_, lean_object* v_y_237_, lean_object* v_n_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_235_, v_x_236_, v_y_237_, v_n_238_);
lean_dec(v_n_238_);
lean_dec(v_y_237_);
lean_dec(v_x_236_);
lean_dec(v_w_u2082_235_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec(lean_object* v_w_u2081_240_, lean_object* v_w_u2082_241_, lean_object* v_x_242_, lean_object* v_y_243_, lean_object* v_n_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_241_, v_x_242_, v_y_243_, v_n_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___boxed(lean_object* v_w_u2081_246_, lean_object* v_w_u2082_247_, lean_object* v_x_248_, lean_object* v_y_249_, lean_object* v_n_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_BitVec_ushiftRightRec(v_w_u2081_246_, v_w_u2082_247_, v_x_248_, v_y_249_, v_n_250_);
lean_dec(v_n_250_);
lean_dec(v_y_249_);
lean_dec(v_x_248_);
lean_dec(v_w_u2082_247_);
lean_dec(v_w_u2081_246_);
return v_res_251_;
}
}
lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg(uint8_t v_x_252_, uint8_t v_x_253_, lean_object* v_h__1_254_, lean_object* v_h__2_255_, lean_object* v_h__3_256_, lean_object* v_h__4_257_){
_start:
{
if (v_x_252_ == 0)
{
lean_dec(v_h__4_257_);
lean_dec(v_h__3_256_);
if (v_x_253_ == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec(v_h__2_255_);
v___x_258_ = lean_box(0);
v___x_259_ = lean_apply_1(v_h__1_254_, v___x_258_);
return v___x_259_;
}
else
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v_h__1_254_);
v___x_260_ = lean_box(0);
v___x_261_ = lean_apply_1(v_h__2_255_, v___x_260_);
return v___x_261_;
}
}
else
{
lean_dec(v_h__2_255_);
lean_dec(v_h__1_254_);
if (v_x_253_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec(v_h__4_257_);
v___x_262_ = lean_box(0);
v___x_263_ = lean_apply_1(v_h__3_256_, v___x_262_);
return v___x_263_;
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v_h__3_256_);
v___x_264_ = lean_box(0);
v___x_265_ = lean_apply_1(v_h__4_257_, v___x_264_);
return v___x_265_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_252_ = stack[0].m_num;
uint8_t v_x_253_ = stack[1].m_num;
lean_object* v_h__1_254_ = stack[2].m_obj;
lean_object* v_h__2_255_ = stack[3].m_obj;
lean_object* v_h__3_256_ = stack[4].m_obj;
lean_object* v_h__4_257_ = stack[5].m_obj;
lean_object* v_res_266_;
v_res_266_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg(v_x_252_, v_x_253_, v_h__1_254_, v_h__2_255_, v_h__3_256_, v_h__4_257_);
stack->m_obj
 = v_res_266_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg___boxed(lean_object* v_x_267_, lean_object* v_x_268_, lean_object* v_h__1_269_, lean_object* v_h__2_270_, lean_object* v_h__3_271_, lean_object* v_h__4_272_){
_start:
{
uint8_t v_x_46__boxed_273_; uint8_t v_x_47__boxed_274_; lean_object* v_res_275_; 
v_x_46__boxed_273_ = lean_unbox(v_x_267_);
v_x_47__boxed_274_ = lean_unbox(v_x_268_);
v_res_275_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg(v_x_46__boxed_273_, v_x_47__boxed_274_, v_h__1_269_, v_h__2_270_, v_h__3_271_, v_h__4_272_);
return v_res_275_;
}
}
lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter(lean_object* v_motive_276_, uint8_t v_x_277_, uint8_t v_x_278_, lean_object* v_h__1_279_, lean_object* v_h__2_280_, lean_object* v_h__3_281_, lean_object* v_h__4_282_){
_start:
{
if (v_x_277_ == 0)
{
lean_dec(v_h__4_282_);
lean_dec(v_h__3_281_);
if (v_x_278_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec(v_h__2_280_);
v___x_283_ = lean_box(0);
v___x_284_ = lean_apply_1(v_h__1_279_, v___x_283_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec(v_h__1_279_);
v___x_285_ = lean_box(0);
v___x_286_ = lean_apply_1(v_h__2_280_, v___x_285_);
return v___x_286_;
}
}
else
{
lean_dec(v_h__2_280_);
lean_dec(v_h__1_279_);
if (v_x_278_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec(v_h__4_282_);
v___x_287_ = lean_box(0);
v___x_288_ = lean_apply_1(v_h__3_281_, v___x_287_);
return v___x_288_;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v_h__3_281_);
v___x_289_ = lean_box(0);
v___x_290_ = lean_apply_1(v_h__4_282_, v___x_289_);
return v___x_290_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_277_ = stack[1].m_num;
uint8_t v_x_278_ = stack[2].m_num;
lean_object* v_h__1_279_ = stack[3].m_obj;
lean_object* v_h__2_280_ = stack[4].m_obj;
lean_object* v_h__3_281_ = stack[5].m_obj;
lean_object* v_h__4_282_ = stack[6].m_obj;
lean_object* v_res_291_;
v_res_291_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter(lean_box(0), v_x_277_, v_x_278_, v_h__1_279_, v_h__2_280_, v_h__3_281_, v_h__4_282_);
stack->m_obj
 = v_res_291_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___boxed(lean_object* v_motive_292_, lean_object* v_x_293_, lean_object* v_x_294_, lean_object* v_h__1_295_, lean_object* v_h__2_296_, lean_object* v_h__3_297_, lean_object* v_h__4_298_){
_start:
{
uint8_t v_x_80__boxed_299_; uint8_t v_x_81__boxed_300_; lean_object* v_res_301_; 
v_x_80__boxed_299_ = lean_unbox(v_x_293_);
v_x_81__boxed_300_ = lean_unbox(v_x_294_);
v_res_301_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter(v_motive_292_, v_x_80__boxed_299_, v_x_81__boxed_300_, v_h__1_295_, v_h__2_296_, v_h__3_297_, v_h__4_298_);
return v_res_301_;
}
}
lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg(uint8_t v_x_302_, uint8_t v_x_303_, lean_object* v_h__1_304_, lean_object* v_h__2_305_, lean_object* v_h__3_306_, lean_object* v_h__4_307_){
_start:
{
if (v_x_302_ == 0)
{
lean_dec(v_h__4_307_);
lean_dec(v_h__3_306_);
if (v_x_303_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec(v_h__2_305_);
v___x_308_ = lean_box(0);
v___x_309_ = lean_apply_1(v_h__1_304_, v___x_308_);
return v___x_309_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec(v_h__1_304_);
v___x_310_ = lean_box(0);
v___x_311_ = lean_apply_1(v_h__2_305_, v___x_310_);
return v___x_311_;
}
}
else
{
lean_dec(v_h__2_305_);
lean_dec(v_h__1_304_);
if (v_x_303_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec(v_h__4_307_);
v___x_312_ = lean_box(0);
v___x_313_ = lean_apply_1(v_h__3_306_, v___x_312_);
return v___x_313_;
}
else
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_h__3_306_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_apply_1(v_h__4_307_, v___x_314_);
return v___x_315_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_302_ = stack[0].m_num;
uint8_t v_x_303_ = stack[1].m_num;
lean_object* v_h__1_304_ = stack[2].m_obj;
lean_object* v_h__2_305_ = stack[3].m_obj;
lean_object* v_h__3_306_ = stack[4].m_obj;
lean_object* v_h__4_307_ = stack[5].m_obj;
lean_object* v_res_316_;
v_res_316_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg(v_x_302_, v_x_303_, v_h__1_304_, v_h__2_305_, v_h__3_306_, v_h__4_307_);
stack->m_obj
 = v_res_316_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg___boxed(lean_object* v_x_317_, lean_object* v_x_318_, lean_object* v_h__1_319_, lean_object* v_h__2_320_, lean_object* v_h__3_321_, lean_object* v_h__4_322_){
_start:
{
uint8_t v_x_46__boxed_323_; uint8_t v_x_47__boxed_324_; lean_object* v_res_325_; 
v_x_46__boxed_323_ = lean_unbox(v_x_317_);
v_x_47__boxed_324_ = lean_unbox(v_x_318_);
v_res_325_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg(v_x_46__boxed_323_, v_x_47__boxed_324_, v_h__1_319_, v_h__2_320_, v_h__3_321_, v_h__4_322_);
return v_res_325_;
}
}
lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter(lean_object* v_motive_326_, uint8_t v_x_327_, uint8_t v_x_328_, lean_object* v_h__1_329_, lean_object* v_h__2_330_, lean_object* v_h__3_331_, lean_object* v_h__4_332_){
_start:
{
if (v_x_327_ == 0)
{
lean_dec(v_h__4_332_);
lean_dec(v_h__3_331_);
if (v_x_328_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec(v_h__2_330_);
v___x_333_ = lean_box(0);
v___x_334_ = lean_apply_1(v_h__1_329_, v___x_333_);
return v___x_334_;
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec(v_h__1_329_);
v___x_335_ = lean_box(0);
v___x_336_ = lean_apply_1(v_h__2_330_, v___x_335_);
return v___x_336_;
}
}
else
{
lean_dec(v_h__2_330_);
lean_dec(v_h__1_329_);
if (v_x_328_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v_h__4_332_);
v___x_337_ = lean_box(0);
v___x_338_ = lean_apply_1(v_h__3_331_, v___x_337_);
return v___x_338_;
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec(v_h__3_331_);
v___x_339_ = lean_box(0);
v___x_340_ = lean_apply_1(v_h__4_332_, v___x_339_);
return v___x_340_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_327_ = stack[1].m_num;
uint8_t v_x_328_ = stack[2].m_num;
lean_object* v_h__1_329_ = stack[3].m_obj;
lean_object* v_h__2_330_ = stack[4].m_obj;
lean_object* v_h__3_331_ = stack[5].m_obj;
lean_object* v_h__4_332_ = stack[6].m_obj;
lean_object* v_res_341_;
v_res_341_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter(lean_box(0), v_x_327_, v_x_328_, v_h__1_329_, v_h__2_330_, v_h__3_331_, v_h__4_332_);
stack->m_obj
 = v_res_341_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___boxed(lean_object* v_motive_342_, lean_object* v_x_343_, lean_object* v_x_344_, lean_object* v_h__1_345_, lean_object* v_h__2_346_, lean_object* v_h__3_347_, lean_object* v_h__4_348_){
_start:
{
uint8_t v_x_80__boxed_349_; uint8_t v_x_81__boxed_350_; lean_object* v_res_351_; 
v_x_80__boxed_349_ = lean_unbox(v_x_343_);
v_x_81__boxed_350_ = lean_unbox(v_x_344_);
v_res_351_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter(v_motive_342_, v_x_80__boxed_349_, v_x_81__boxed_350_, v_h__1_345_, v_h__2_346_, v_h__3_347_, v_h__4_348_);
return v_res_351_;
}
}
lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg(uint8_t v_x_352_, uint8_t v_x_353_, lean_object* v_h__1_354_, lean_object* v_h__2_355_, lean_object* v_h__3_356_, lean_object* v_h__4_357_){
_start:
{
if (v_x_352_ == 0)
{
lean_dec(v_h__4_357_);
lean_dec(v_h__3_356_);
if (v_x_353_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec(v_h__2_355_);
v___x_358_ = lean_box(0);
v___x_359_ = lean_apply_1(v_h__1_354_, v___x_358_);
return v___x_359_;
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v_h__1_354_);
v___x_360_ = lean_box(0);
v___x_361_ = lean_apply_1(v_h__2_355_, v___x_360_);
return v___x_361_;
}
}
else
{
lean_dec(v_h__2_355_);
lean_dec(v_h__1_354_);
if (v_x_353_ == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; 
lean_dec(v_h__4_357_);
v___x_362_ = lean_box(0);
v___x_363_ = lean_apply_1(v_h__3_356_, v___x_362_);
return v___x_363_;
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec(v_h__3_356_);
v___x_364_ = lean_box(0);
v___x_365_ = lean_apply_1(v_h__4_357_, v___x_364_);
return v___x_365_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_352_ = stack[0].m_num;
uint8_t v_x_353_ = stack[1].m_num;
lean_object* v_h__1_354_ = stack[2].m_obj;
lean_object* v_h__2_355_ = stack[3].m_obj;
lean_object* v_h__3_356_ = stack[4].m_obj;
lean_object* v_h__4_357_ = stack[5].m_obj;
lean_object* v_res_366_;
v_res_366_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg(v_x_352_, v_x_353_, v_h__1_354_, v_h__2_355_, v_h__3_356_, v_h__4_357_);
stack->m_obj
 = v_res_366_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg___boxed(lean_object* v_x_367_, lean_object* v_x_368_, lean_object* v_h__1_369_, lean_object* v_h__2_370_, lean_object* v_h__3_371_, lean_object* v_h__4_372_){
_start:
{
uint8_t v_x_46__boxed_373_; uint8_t v_x_47__boxed_374_; lean_object* v_res_375_; 
v_x_46__boxed_373_ = lean_unbox(v_x_367_);
v_x_47__boxed_374_ = lean_unbox(v_x_368_);
v_res_375_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg(v_x_46__boxed_373_, v_x_47__boxed_374_, v_h__1_369_, v_h__2_370_, v_h__3_371_, v_h__4_372_);
return v_res_375_;
}
}
lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter(lean_object* v_motive_376_, uint8_t v_x_377_, uint8_t v_x_378_, lean_object* v_h__1_379_, lean_object* v_h__2_380_, lean_object* v_h__3_381_, lean_object* v_h__4_382_){
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
LEAN_EXPORT void l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_377_ = stack[1].m_num;
uint8_t v_x_378_ = stack[2].m_num;
lean_object* v_h__1_379_ = stack[3].m_obj;
lean_object* v_h__2_380_ = stack[4].m_obj;
lean_object* v_h__3_381_ = stack[5].m_obj;
lean_object* v_h__4_382_ = stack[6].m_obj;
lean_object* v_res_391_;
v_res_391_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter(lean_box(0), v_x_377_, v_x_378_, v_h__1_379_, v_h__2_380_, v_h__3_381_, v_h__4_382_);
stack->m_obj
 = v_res_391_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___boxed(lean_object* v_motive_392_, lean_object* v_x_393_, lean_object* v_x_394_, lean_object* v_h__1_395_, lean_object* v_h__2_396_, lean_object* v_h__3_397_, lean_object* v_h__4_398_){
_start:
{
uint8_t v_x_80__boxed_399_; uint8_t v_x_81__boxed_400_; lean_object* v_res_401_; 
v_x_80__boxed_399_ = lean_unbox(v_x_393_);
v_x_81__boxed_400_ = lean_unbox(v_x_394_);
v_res_401_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter(v_motive_392_, v_x_80__boxed_399_, v_x_81__boxed_400_, v_h__1_395_, v_h__2_396_, v_h__3_397_, v_h__4_398_);
return v_res_401_;
}
}
uint8_t l_BitVec_uppcRec___redArg(lean_object* v_w_402_, lean_object* v_x_403_, lean_object* v_s_404_){
_start:
{
lean_object* v_zero_405_; uint8_t v_isZero_406_; 
v_zero_405_ = lean_unsigned_to_nat(0u);
v_isZero_406_ = lean_nat_dec_eq(v_s_404_, v_zero_405_);
if (v_isZero_406_ == 1)
{
uint8_t v___x_407_; 
lean_dec(v_s_404_);
v___x_407_ = lean_nat_dec_lt(v_zero_405_, v_w_402_);
if (v___x_407_ == 0)
{
return v___x_407_;
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_408_ = lean_unsigned_to_nat(1u);
v___x_409_ = lean_nat_sub(v_w_402_, v___x_408_);
v___x_410_ = l_Nat_testBit(v_x_403_, v___x_409_);
lean_dec(v___x_409_);
return v___x_410_;
}
}
else
{
lean_object* v_one_411_; lean_object* v_n_412_; lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v_one_411_ = lean_unsigned_to_nat(1u);
v_n_412_ = lean_nat_sub(v_s_404_, v_one_411_);
lean_dec(v_s_404_);
v___x_413_ = lean_nat_sub(v_w_402_, v_one_411_);
v___x_414_ = lean_nat_sub(v___x_413_, v_n_412_);
lean_dec(v___x_413_);
v___x_415_ = l_Nat_testBit(v_x_403_, v___x_414_);
lean_dec(v___x_414_);
if (v___x_415_ == 0)
{
v_s_404_ = v_n_412_;
goto _start;
}
else
{
lean_dec(v_n_412_);
return v___x_415_;
}
}
}
}
LEAN_EXPORT void l_BitVec_uppcRec___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_402_ = stack[0].m_obj;
lean_object* v_x_403_ = stack[1].m_obj;
lean_object* v_s_404_ = stack[2].m_obj;
uint8_t v_res_417_;
v_res_417_ = l_BitVec_uppcRec___redArg(v_w_402_, v_x_403_, v_s_404_);
stack->m_num = v_res_417_;
}
LEAN_EXPORT lean_object* l_BitVec_uppcRec___redArg___boxed(lean_object* v_w_418_, lean_object* v_x_419_, lean_object* v_s_420_){
_start:
{
uint8_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l_BitVec_uppcRec___redArg(v_w_418_, v_x_419_, v_s_420_);
lean_dec(v_x_419_);
lean_dec(v_w_418_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
uint8_t l_BitVec_uppcRec(lean_object* v_w_423_, lean_object* v_x_424_, lean_object* v_s_425_, lean_object* v_hs_426_){
_start:
{
uint8_t v___x_427_; 
v___x_427_ = l_BitVec_uppcRec___redArg(v_w_423_, v_x_424_, v_s_425_);
return v___x_427_;
}
}
LEAN_EXPORT void l_BitVec_uppcRec_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_423_ = stack[0].m_obj;
lean_object* v_x_424_ = stack[1].m_obj;
lean_object* v_s_425_ = stack[2].m_obj;
uint8_t v_res_428_;
v_res_428_ = l_BitVec_uppcRec(v_w_423_, v_x_424_, v_s_425_, lean_box(0));
stack->m_num = v_res_428_;
}
LEAN_EXPORT lean_object* l_BitVec_uppcRec___boxed(lean_object* v_w_429_, lean_object* v_x_430_, lean_object* v_s_431_, lean_object* v_hs_432_){
_start:
{
uint8_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = l_BitVec_uppcRec(v_w_429_, v_x_430_, v_s_431_, v_hs_432_);
lean_dec(v_x_430_);
lean_dec(v_w_429_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
uint8_t l_BitVec_aandRec___redArg(lean_object* v_w_435_, lean_object* v_x_436_, lean_object* v_y_437_, lean_object* v_s_438_){
_start:
{
uint8_t v___x_439_; 
v___x_439_ = l_Nat_testBit(v_y_437_, v_s_438_);
if (v___x_439_ == 0)
{
lean_dec(v_s_438_);
return v___x_439_;
}
else
{
uint8_t v___x_440_; 
v___x_440_ = l_BitVec_uppcRec___redArg(v_w_435_, v_x_436_, v_s_438_);
return v___x_440_;
}
}
}
LEAN_EXPORT void l_BitVec_aandRec___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_435_ = stack[0].m_obj;
lean_object* v_x_436_ = stack[1].m_obj;
lean_object* v_y_437_ = stack[2].m_obj;
lean_object* v_s_438_ = stack[3].m_obj;
uint8_t v_res_441_;
v_res_441_ = l_BitVec_aandRec___redArg(v_w_435_, v_x_436_, v_y_437_, v_s_438_);
stack->m_num = v_res_441_;
}
LEAN_EXPORT lean_object* l_BitVec_aandRec___redArg___boxed(lean_object* v_w_442_, lean_object* v_x_443_, lean_object* v_y_444_, lean_object* v_s_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l_BitVec_aandRec___redArg(v_w_442_, v_x_443_, v_y_444_, v_s_445_);
lean_dec(v_y_444_);
lean_dec(v_x_443_);
lean_dec(v_w_442_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
uint8_t l_BitVec_aandRec(lean_object* v_w_448_, lean_object* v_x_449_, lean_object* v_y_450_, lean_object* v_s_451_, lean_object* v_hs_452_){
_start:
{
uint8_t v___x_453_; 
v___x_453_ = l_BitVec_aandRec___redArg(v_w_448_, v_x_449_, v_y_450_, v_s_451_);
return v___x_453_;
}
}
LEAN_EXPORT void l_BitVec_aandRec_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_448_ = stack[0].m_obj;
lean_object* v_x_449_ = stack[1].m_obj;
lean_object* v_y_450_ = stack[2].m_obj;
lean_object* v_s_451_ = stack[3].m_obj;
uint8_t v_res_454_;
v_res_454_ = l_BitVec_aandRec(v_w_448_, v_x_449_, v_y_450_, v_s_451_, lean_box(0));
stack->m_num = v_res_454_;
}
LEAN_EXPORT lean_object* l_BitVec_aandRec___boxed(lean_object* v_w_455_, lean_object* v_x_456_, lean_object* v_y_457_, lean_object* v_s_458_, lean_object* v_hs_459_){
_start:
{
uint8_t v_res_460_; lean_object* v_r_461_; 
v_res_460_ = l_BitVec_aandRec(v_w_455_, v_x_456_, v_y_457_, v_s_458_, v_hs_459_);
lean_dec(v_y_457_);
lean_dec(v_x_456_);
lean_dec(v_w_455_);
v_r_461_ = lean_box(v_res_460_);
return v_r_461_;
}
}
uint8_t l_BitVec_resRec___redArg(lean_object* v_w_462_, lean_object* v_x_463_, lean_object* v_y_464_, lean_object* v_s_465_){
_start:
{
lean_object* v_zero_466_; uint8_t v_isZero_467_; lean_object* v_one_468_; lean_object* v_n_469_; uint8_t v_isZero_470_; 
v_zero_466_ = lean_unsigned_to_nat(0u);
v_isZero_467_ = lean_nat_dec_eq(v_s_465_, v_zero_466_);
v_one_468_ = lean_unsigned_to_nat(1u);
v_n_469_ = lean_nat_sub(v_s_465_, v_one_468_);
v_isZero_470_ = lean_nat_dec_eq(v_n_469_, v_zero_466_);
if (v_isZero_470_ == 1)
{
uint8_t v___x_471_; 
lean_dec(v_n_469_);
lean_dec(v_s_465_);
v___x_471_ = l_BitVec_aandRec___redArg(v_w_462_, v_x_463_, v_y_464_, v_one_468_);
return v___x_471_;
}
else
{
uint8_t v___x_472_; 
v___x_472_ = l_BitVec_resRec___redArg(v_w_462_, v_x_463_, v_y_464_, v_n_469_);
if (v___x_472_ == 0)
{
uint8_t v___x_473_; 
v___x_473_ = l_BitVec_aandRec___redArg(v_w_462_, v_x_463_, v_y_464_, v_s_465_);
return v___x_473_;
}
else
{
lean_dec(v_s_465_);
return v___x_472_;
}
}
}
}
LEAN_EXPORT void l_BitVec_resRec___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_462_ = stack[0].m_obj;
lean_object* v_x_463_ = stack[1].m_obj;
lean_object* v_y_464_ = stack[2].m_obj;
lean_object* v_s_465_ = stack[3].m_obj;
uint8_t v_res_474_;
v_res_474_ = l_BitVec_resRec___redArg(v_w_462_, v_x_463_, v_y_464_, v_s_465_);
stack->m_num = v_res_474_;
}
LEAN_EXPORT lean_object* l_BitVec_resRec___redArg___boxed(lean_object* v_w_475_, lean_object* v_x_476_, lean_object* v_y_477_, lean_object* v_s_478_){
_start:
{
uint8_t v_res_479_; lean_object* v_r_480_; 
v_res_479_ = l_BitVec_resRec___redArg(v_w_475_, v_x_476_, v_y_477_, v_s_478_);
lean_dec(v_y_477_);
lean_dec(v_x_476_);
lean_dec(v_w_475_);
v_r_480_ = lean_box(v_res_479_);
return v_r_480_;
}
}
uint8_t l_BitVec_resRec(lean_object* v_w_481_, lean_object* v_x_482_, lean_object* v_y_483_, lean_object* v_s_484_, lean_object* v_hs_485_, lean_object* v_hslt_486_){
_start:
{
uint8_t v___x_487_; 
v___x_487_ = l_BitVec_resRec___redArg(v_w_481_, v_x_482_, v_y_483_, v_s_484_);
return v___x_487_;
}
}
LEAN_EXPORT void l_BitVec_resRec_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_481_ = stack[0].m_obj;
lean_object* v_x_482_ = stack[1].m_obj;
lean_object* v_y_483_ = stack[2].m_obj;
lean_object* v_s_484_ = stack[3].m_obj;
uint8_t v_res_488_;
v_res_488_ = l_BitVec_resRec(v_w_481_, v_x_482_, v_y_483_, v_s_484_, lean_box(0), lean_box(0));
stack->m_num = v_res_488_;
}
LEAN_EXPORT lean_object* l_BitVec_resRec___boxed(lean_object* v_w_489_, lean_object* v_x_490_, lean_object* v_y_491_, lean_object* v_s_492_, lean_object* v_hs_493_, lean_object* v_hslt_494_){
_start:
{
uint8_t v_res_495_; lean_object* v_r_496_; 
v_res_495_ = l_BitVec_resRec(v_w_489_, v_x_490_, v_y_491_, v_s_492_, v_hs_493_, v_hslt_494_);
lean_dec(v_y_491_);
lean_dec(v_x_490_);
lean_dec(v_w_489_);
v_r_496_ = lean_box(v_res_495_);
return v_r_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg(lean_object* v_s_497_, lean_object* v_h__1_498_, lean_object* v_h__2_499_){
_start:
{
lean_object* v_zero_500_; uint8_t v_isZero_501_; 
v_zero_500_ = lean_unsigned_to_nat(0u);
v_isZero_501_ = lean_nat_dec_eq(v_s_497_, v_zero_500_);
if (v_isZero_501_ == 1)
{
lean_object* v___x_502_; 
lean_dec(v_h__2_499_);
v___x_502_ = lean_apply_3(v_h__1_498_, lean_box(0), lean_box(0), lean_box(0));
return v___x_502_;
}
else
{
lean_object* v_one_503_; lean_object* v_n_504_; lean_object* v___x_505_; 
lean_dec(v_h__1_498_);
v_one_503_ = lean_unsigned_to_nat(1u);
v_n_504_ = lean_nat_sub(v_s_497_, v_one_503_);
v___x_505_ = lean_apply_4(v_h__2_499_, v_n_504_, lean_box(0), lean_box(0), lean_box(0));
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg___boxed(lean_object* v_s_506_, lean_object* v_h__1_507_, lean_object* v_h__2_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg(v_s_506_, v_h__1_507_, v_h__2_508_);
lean_dec(v_s_506_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter(lean_object* v_w_510_, lean_object* v_motive_511_, lean_object* v_s_512_, lean_object* v_hs_513_, lean_object* v_hslt_514_, lean_object* v_h__1_515_, lean_object* v_h__2_516_){
_start:
{
lean_object* v_zero_517_; uint8_t v_isZero_518_; 
v_zero_517_ = lean_unsigned_to_nat(0u);
v_isZero_518_ = lean_nat_dec_eq(v_s_512_, v_zero_517_);
if (v_isZero_518_ == 1)
{
lean_object* v___x_519_; 
lean_dec(v_h__2_516_);
v___x_519_ = lean_apply_3(v_h__1_515_, lean_box(0), lean_box(0), lean_box(0));
return v___x_519_;
}
else
{
lean_object* v_one_520_; lean_object* v_n_521_; lean_object* v___x_522_; 
lean_dec(v_h__1_515_);
v_one_520_ = lean_unsigned_to_nat(1u);
v_n_521_ = lean_nat_sub(v_s_512_, v_one_520_);
v___x_522_ = lean_apply_4(v_h__2_516_, v_n_521_, lean_box(0), lean_box(0), lean_box(0));
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___boxed(lean_object* v_w_523_, lean_object* v_motive_524_, lean_object* v_s_525_, lean_object* v_hs_526_, lean_object* v_hslt_527_, lean_object* v_h__1_528_, lean_object* v_h__2_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter(v_w_523_, v_motive_524_, v_s_525_, v_hs_526_, v_hslt_527_, v_h__1_528_, v_h__2_529_);
lean_dec(v_s_525_);
lean_dec(v_w_523_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg(lean_object* v_s_x27_531_, lean_object* v_h__1_532_, lean_object* v_h__2_533_){
_start:
{
lean_object* v_zero_534_; uint8_t v_isZero_535_; 
v_zero_534_ = lean_unsigned_to_nat(0u);
v_isZero_535_ = lean_nat_dec_eq(v_s_x27_531_, v_zero_534_);
if (v_isZero_535_ == 1)
{
lean_object* v___x_536_; 
lean_dec(v_h__2_533_);
v___x_536_ = lean_apply_4(v_h__1_532_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_536_;
}
else
{
lean_object* v_one_537_; lean_object* v_n_538_; lean_object* v___x_539_; 
lean_dec(v_h__1_532_);
v_one_537_ = lean_unsigned_to_nat(1u);
v_n_538_ = lean_nat_sub(v_s_x27_531_, v_one_537_);
v___x_539_ = lean_apply_5(v_h__2_533_, v_n_538_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg___boxed(lean_object* v_s_x27_540_, lean_object* v_h__1_541_, lean_object* v_h__2_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg(v_s_x27_540_, v_h__1_541_, v_h__2_542_);
lean_dec(v_s_x27_540_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter(lean_object* v_w_544_, lean_object* v_s_545_, lean_object* v_motive_546_, lean_object* v_s_x27_547_, lean_object* v_hs_548_, lean_object* v_hslt_549_, lean_object* v_hs0_550_, lean_object* v_h__1_551_, lean_object* v_h__2_552_){
_start:
{
lean_object* v_zero_553_; uint8_t v_isZero_554_; 
v_zero_553_ = lean_unsigned_to_nat(0u);
v_isZero_554_ = lean_nat_dec_eq(v_s_x27_547_, v_zero_553_);
if (v_isZero_554_ == 1)
{
lean_object* v___x_555_; 
lean_dec(v_h__2_552_);
v___x_555_ = lean_apply_4(v_h__1_551_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_555_;
}
else
{
lean_object* v_one_556_; lean_object* v_n_557_; lean_object* v___x_558_; 
lean_dec(v_h__1_551_);
v_one_556_ = lean_unsigned_to_nat(1u);
v_n_557_ = lean_nat_sub(v_s_x27_547_, v_one_556_);
v___x_558_ = lean_apply_5(v_h__2_552_, v_n_557_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___boxed(lean_object* v_w_559_, lean_object* v_s_560_, lean_object* v_motive_561_, lean_object* v_s_x27_562_, lean_object* v_hs_563_, lean_object* v_hslt_564_, lean_object* v_hs0_565_, lean_object* v_h__1_566_, lean_object* v_h__2_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter(v_w_559_, v_s_560_, v_motive_561_, v_s_x27_562_, v_hs_563_, v_hslt_564_, v_hs0_565_, v_h__1_566_, v_h__2_567_);
lean_dec(v_s_x27_562_);
lean_dec(v_s_560_);
lean_dec(v_w_559_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___redArg(lean_object* v_idx_569_, lean_object* v_len_570_, lean_object* v_x_571_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = lean_unsigned_to_nat(1u);
v___x_573_ = l_BitVec_extractLsb_x27___redArg(v_idx_569_, v___x_572_, v_x_571_);
v___x_574_ = l_BitVec_setWidth(v___x_572_, v_len_570_, v___x_573_);
lean_dec(v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___redArg___boxed(lean_object* v_idx_575_, lean_object* v_len_576_, lean_object* v_x_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_BitVec_extractAndExtendBit___redArg(v_idx_575_, v_len_576_, v_x_577_);
lean_dec(v_x_577_);
lean_dec(v_len_576_);
lean_dec(v_idx_575_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit(lean_object* v_w_579_, lean_object* v_idx_580_, lean_object* v_len_581_, lean_object* v_x_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_BitVec_extractAndExtendBit___redArg(v_idx_580_, v_len_581_, v_x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___boxed(lean_object* v_w_584_, lean_object* v_idx_585_, lean_object* v_len_586_, lean_object* v_x_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_BitVec_extractAndExtendBit(v_w_584_, v_idx_585_, v_len_586_, v_x_587_);
lean_dec(v_x_587_);
lean_dec(v_len_586_);
lean_dec(v_idx_585_);
lean_dec(v_w_584_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___redArg(lean_object* v_w_589_, lean_object* v_k_590_, lean_object* v_len_591_, lean_object* v_x_592_, lean_object* v_acc_593_){
_start:
{
lean_object* v___x_594_; lean_object* v_zero_595_; uint8_t v_isZero_596_; 
v___x_594_ = lean_nat_sub(v_w_589_, v_k_590_);
v_zero_595_ = lean_unsigned_to_nat(0u);
v_isZero_596_ = lean_nat_dec_eq(v___x_594_, v_zero_595_);
lean_dec(v___x_594_);
if (v_isZero_596_ == 1)
{
lean_dec(v_k_590_);
return v_acc_593_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v_acc_x27_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_597_ = lean_nat_mul(v_k_590_, v_len_591_);
v___x_598_ = l_BitVec_extractAndExtendBit___redArg(v_k_590_, v_len_591_, v_x_592_);
v_acc_x27_599_ = l_BitVec_append___redArg(v___x_597_, v___x_598_, v_acc_593_);
lean_dec(v_acc_593_);
lean_dec(v___x_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = lean_nat_add(v_k_590_, v___x_600_);
lean_dec(v_k_590_);
v_k_590_ = v___x_601_;
v_acc_593_ = v_acc_x27_599_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___redArg___boxed(lean_object* v_w_603_, lean_object* v_k_604_, lean_object* v_len_605_, lean_object* v_x_606_, lean_object* v_acc_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_BitVec_extractAndExtendAux___redArg(v_w_603_, v_k_604_, v_len_605_, v_x_606_, v_acc_607_);
lean_dec(v_x_606_);
lean_dec(v_len_605_);
lean_dec(v_w_603_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux(lean_object* v_w_609_, lean_object* v_k_610_, lean_object* v_len_611_, lean_object* v_x_612_, lean_object* v_acc_613_, lean_object* v_hle_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_BitVec_extractAndExtendAux___redArg(v_w_609_, v_k_610_, v_len_611_, v_x_612_, v_acc_613_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___boxed(lean_object* v_w_616_, lean_object* v_k_617_, lean_object* v_len_618_, lean_object* v_x_619_, lean_object* v_acc_620_, lean_object* v_hle_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_BitVec_extractAndExtendAux(v_w_616_, v_k_617_, v_len_618_, v_x_619_, v_acc_620_, v_hle_621_);
lean_dec(v_x_619_);
lean_dec(v_len_618_);
lean_dec(v_w_616_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg(lean_object* v_x_623_, lean_object* v_h__1_624_, lean_object* v_h__2_625_){
_start:
{
lean_object* v_zero_626_; uint8_t v_isZero_627_; 
v_zero_626_ = lean_unsigned_to_nat(0u);
v_isZero_627_ = lean_nat_dec_eq(v_x_623_, v_zero_626_);
if (v_isZero_627_ == 1)
{
lean_object* v___x_628_; 
lean_dec(v_h__2_625_);
v___x_628_ = lean_apply_1(v_h__1_624_, lean_box(0));
return v___x_628_;
}
else
{
lean_object* v_one_629_; lean_object* v_n_630_; lean_object* v___x_631_; 
lean_dec(v_h__1_624_);
v_one_629_ = lean_unsigned_to_nat(1u);
v_n_630_ = lean_nat_sub(v_x_623_, v_one_629_);
v___x_631_ = lean_apply_2(v_h__2_625_, v_n_630_, lean_box(0));
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg___boxed(lean_object* v_x_632_, lean_object* v_h__1_633_, lean_object* v_h__2_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg(v_x_632_, v_h__1_633_, v_h__2_634_);
lean_dec(v_x_632_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter(lean_object* v_motive_636_, lean_object* v_x_637_, lean_object* v_h__1_638_, lean_object* v_h__2_639_){
_start:
{
lean_object* v_zero_640_; uint8_t v_isZero_641_; 
v_zero_640_ = lean_unsigned_to_nat(0u);
v_isZero_641_ = lean_nat_dec_eq(v_x_637_, v_zero_640_);
if (v_isZero_641_ == 1)
{
lean_object* v___x_642_; 
lean_dec(v_h__2_639_);
v___x_642_ = lean_apply_1(v_h__1_638_, lean_box(0));
return v___x_642_;
}
else
{
lean_object* v_one_643_; lean_object* v_n_644_; lean_object* v___x_645_; 
lean_dec(v_h__1_638_);
v_one_643_ = lean_unsigned_to_nat(1u);
v_n_644_ = lean_nat_sub(v_x_637_, v_one_643_);
v___x_645_ = lean_apply_2(v_h__2_639_, v_n_644_, lean_box(0));
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___boxed(lean_object* v_motive_646_, lean_object* v_x_647_, lean_object* v_h__1_648_, lean_object* v_h__2_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter(v_motive_646_, v_x_647_, v_h__1_648_, v_h__2_649_);
lean_dec(v_x_647_);
return v_res_650_;
}
}
static lean_object* _init_l_BitVec_extractAndExtend___closed__0(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = l_BitVec_ofNat(v___x_651_, v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtend(lean_object* v_w_653_, lean_object* v_len_654_, lean_object* v_x_655_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_obj_once(&l_BitVec_extractAndExtend___closed__0, &l_BitVec_extractAndExtend___closed__0_once, _init_l_BitVec_extractAndExtend___closed__0);
v___x_658_ = l_BitVec_extractAndExtendAux___redArg(v_w_653_, v___x_656_, v_len_654_, v_x_655_, v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtend___boxed(lean_object* v_w_659_, lean_object* v_len_660_, lean_object* v_x_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_BitVec_extractAndExtend(v_w_659_, v_len_660_, v_x_661_);
lean_dec(v_x_661_);
lean_dec(v_len_660_);
lean_dec(v_w_659_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___redArg(lean_object* v_len_663_, lean_object* v_w_664_, lean_object* v_iterNum_665_, lean_object* v_oldLayer_666_, lean_object* v_newLayer_667_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_668_ = lean_unsigned_to_nat(2u);
v___x_669_ = lean_nat_mul(v_iterNum_665_, v___x_668_);
v___x_670_ = lean_nat_sub(v_len_663_, v___x_669_);
lean_dec(v___x_669_);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_nat_dec_eq(v___x_670_, v___x_671_);
lean_dec(v___x_670_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v_op1_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v_op2_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v_newLayer_x27_682_; lean_object* v___x_683_; 
v___x_673_ = lean_nat_mul(v___x_668_, v_iterNum_665_);
v___x_674_ = lean_nat_mul(v___x_673_, v_w_664_);
v_op1_675_ = l_BitVec_extractLsb_x27___redArg(v___x_674_, v_w_664_, v_oldLayer_666_);
lean_dec(v___x_674_);
v___x_676_ = lean_unsigned_to_nat(1u);
v___x_677_ = lean_nat_add(v___x_673_, v___x_676_);
lean_dec(v___x_673_);
v___x_678_ = lean_nat_mul(v___x_677_, v_w_664_);
lean_dec(v___x_677_);
v_op2_679_ = l_BitVec_extractLsb_x27___redArg(v___x_678_, v_w_664_, v_oldLayer_666_);
lean_dec(v___x_678_);
v___x_680_ = lean_nat_mul(v_iterNum_665_, v_w_664_);
v___x_681_ = l_BitVec_add(v_w_664_, v_op1_675_, v_op2_679_);
lean_dec(v_op2_679_);
lean_dec(v_op1_675_);
v_newLayer_x27_682_ = l_BitVec_append___redArg(v___x_680_, v___x_681_, v_newLayer_667_);
lean_dec(v_newLayer_667_);
lean_dec(v___x_681_);
lean_dec(v___x_680_);
v___x_683_ = lean_nat_add(v_iterNum_665_, v___x_676_);
lean_dec(v_iterNum_665_);
v_iterNum_665_ = v___x_683_;
v_newLayer_667_ = v_newLayer_x27_682_;
goto _start;
}
else
{
lean_dec(v_iterNum_665_);
return v_newLayer_667_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___redArg___boxed(lean_object* v_len_685_, lean_object* v_w_686_, lean_object* v_iterNum_687_, lean_object* v_oldLayer_688_, lean_object* v_newLayer_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_BitVec_cpopLayer___redArg(v_len_685_, v_w_686_, v_iterNum_687_, v_oldLayer_688_, v_newLayer_689_);
lean_dec(v_oldLayer_688_);
lean_dec(v_w_686_);
lean_dec(v_len_685_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer(lean_object* v_len_691_, lean_object* v_w_692_, lean_object* v_iterNum_693_, lean_object* v_oldLayer_694_, lean_object* v_newLayer_695_, lean_object* v_hold_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_BitVec_cpopLayer___redArg(v_len_691_, v_w_692_, v_iterNum_693_, v_oldLayer_694_, v_newLayer_695_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___boxed(lean_object* v_len_698_, lean_object* v_w_699_, lean_object* v_iterNum_700_, lean_object* v_oldLayer_701_, lean_object* v_newLayer_702_, lean_object* v_hold_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_BitVec_cpopLayer(v_len_698_, v_w_699_, v_iterNum_700_, v_oldLayer_701_, v_newLayer_702_, v_hold_703_);
lean_dec(v_oldLayer_701_);
lean_dec(v_w_699_);
lean_dec(v_len_698_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopTree(lean_object* v_len_705_, lean_object* v_w_706_, lean_object* v_l_707_){
_start:
{
lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_nat_dec_eq(v_len_705_, v___x_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_710_ = lean_unsigned_to_nat(1u);
v___x_711_ = lean_nat_dec_eq(v_len_705_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_712_ = lean_nat_add(v_len_705_, v___x_710_);
v___x_713_ = lean_nat_shiftr(v___x_712_, v___x_710_);
lean_dec(v___x_712_);
v___x_714_ = lean_obj_once(&l_BitVec_extractAndExtend___closed__0, &l_BitVec_extractAndExtend___closed__0_once, _init_l_BitVec_extractAndExtend___closed__0);
v___x_715_ = l_BitVec_cpopLayer___redArg(v_len_705_, v_w_706_, v___x_708_, v_l_707_, v___x_714_);
lean_dec(v_l_707_);
lean_dec(v_len_705_);
v_len_705_ = v___x_713_;
v_l_707_ = v___x_715_;
goto _start;
}
else
{
lean_dec(v_len_705_);
return v_l_707_;
}
}
else
{
lean_object* v___x_717_; 
lean_dec(v_l_707_);
lean_dec(v_len_705_);
v___x_717_ = l_BitVec_ofNat(v_w_706_, v___x_708_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopTree___boxed(lean_object* v_len_718_, lean_object* v_w_719_, lean_object* v_l_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_BitVec_cpopTree(v_len_718_, v_w_719_, v_l_720_);
lean_dec(v_w_719_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopRec(lean_object* v_w_722_, lean_object* v_x_723_){
_start:
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_nat_dec_lt(v___x_724_, v_w_722_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = lean_nat_dec_lt(v___x_726_, v_w_722_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; 
v___x_728_ = l_BitVec_ofNat(v_w_722_, v___x_726_);
lean_dec(v_w_722_);
return v___x_728_;
}
else
{
lean_dec(v_w_722_);
lean_inc(v_x_723_);
return v_x_723_;
}
}
else
{
lean_object* v_extendedBits_729_; lean_object* v___x_730_; 
v_extendedBits_729_ = l_BitVec_extractAndExtend(v_w_722_, v_w_722_, v_x_723_);
lean_inc(v_w_722_);
v___x_730_ = l_BitVec_cpopTree(v_w_722_, v_w_722_, v_extendedBits_729_);
lean_dec(v_w_722_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopRec___boxed(lean_object* v_w_731_, lean_object* v_x_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_BitVec_cpopRec(v_w_731_, v_x_732_);
lean_dec(v_x_732_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(lean_object* v_w_734_, lean_object* v_x_735_, lean_object* v_rem_736_, lean_object* v_acc_737_){
_start:
{
lean_object* v_zero_738_; uint8_t v_isZero_739_; 
v_zero_738_ = lean_unsigned_to_nat(0u);
v_isZero_739_ = lean_nat_dec_eq(v_rem_736_, v_zero_738_);
if (v_isZero_739_ == 1)
{
lean_dec(v_rem_736_);
return v_acc_737_;
}
else
{
lean_object* v_one_740_; lean_object* v_n_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_one_740_ = lean_unsigned_to_nat(1u);
v_n_741_ = lean_nat_sub(v_rem_736_, v_one_740_);
lean_dec(v_rem_736_);
v___x_742_ = lean_nat_mul(v_n_741_, v_w_734_);
v___x_743_ = l_BitVec_extractLsb_x27___redArg(v___x_742_, v_w_734_, v_x_735_);
lean_dec(v___x_742_);
v___x_744_ = l_BitVec_add(v_w_734_, v_acc_737_, v___x_743_);
lean_dec(v___x_743_);
lean_dec(v_acc_737_);
v_rem_736_ = v_n_741_;
v_acc_737_ = v___x_744_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg___boxed(lean_object* v_w_746_, lean_object* v_x_747_, lean_object* v_rem_748_, lean_object* v_acc_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_746_, v_x_747_, v_rem_748_, v_acc_749_);
lean_dec(v_x_747_);
lean_dec(v_w_746_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux(lean_object* v_l_751_, lean_object* v_w_752_, lean_object* v_x_753_, lean_object* v_rem_754_, lean_object* v_acc_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_752_, v_x_753_, v_rem_754_, v_acc_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___boxed(lean_object* v_l_757_, lean_object* v_w_758_, lean_object* v_x_759_, lean_object* v_rem_760_, lean_object* v_acc_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux(v_l_757_, v_w_758_, v_x_759_, v_rem_760_, v_acc_761_);
lean_dec(v_x_759_);
lean_dec(v_w_758_);
lean_dec(v_l_757_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec(lean_object* v_l_763_, lean_object* v_w_764_, lean_object* v_x_765_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = l_BitVec_ofNat(v_w_764_, v___x_766_);
v___x_768_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_764_, v_x_765_, v_l_763_, v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec___boxed(lean_object* v_l_769_, lean_object* v_w_770_, lean_object* v_x_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec(v_l_769_, v_w_770_, v_x_771_);
lean_dec(v_x_771_);
lean_dec(v_w_770_);
return v_res_772_;
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
