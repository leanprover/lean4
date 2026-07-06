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
LEAN_EXPORT lean_object* l_BitVec_shiftLeftRec(lean_object* v_w_u2081_127_, lean_object* v_w_u2082_128_, lean_object* v_x_129_, lean_object* v_y_130_, lean_object* v_n_131_){
_start:
{
lean_object* v___x_132_; lean_object* v_shiftAmt_133_; lean_object* v_zero_134_; uint8_t v_isZero_135_; 
v___x_132_ = l_BitVec_twoPow(v_w_u2082_128_, v_n_131_);
v_shiftAmt_133_ = lean_nat_land(v_y_130_, v___x_132_);
lean_dec(v___x_132_);
v_zero_134_ = lean_unsigned_to_nat(0u);
v_isZero_135_ = lean_nat_dec_eq(v_n_131_, v_zero_134_);
if (v_isZero_135_ == 1)
{
lean_object* v___x_136_; 
v___x_136_ = l_BitVec_shiftLeft(v_w_u2081_127_, v_x_129_, v_shiftAmt_133_);
lean_dec(v_shiftAmt_133_);
return v___x_136_;
}
else
{
lean_object* v_one_137_; lean_object* v_n_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_one_137_ = lean_unsigned_to_nat(1u);
v_n_138_ = lean_nat_sub(v_n_131_, v_one_137_);
v___x_139_ = l_BitVec_shiftLeftRec(v_w_u2081_127_, v_w_u2082_128_, v_x_129_, v_y_130_, v_n_138_);
lean_dec(v_n_138_);
v___x_140_ = l_BitVec_shiftLeft(v_w_u2081_127_, v___x_139_, v_shiftAmt_133_);
lean_dec(v_shiftAmt_133_);
lean_dec(v___x_139_);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_shiftLeftRec___boxed(lean_object* v_w_u2081_141_, lean_object* v_w_u2082_142_, lean_object* v_x_143_, lean_object* v_y_144_, lean_object* v_n_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_BitVec_shiftLeftRec(v_w_u2081_141_, v_w_u2082_142_, v_x_143_, v_y_144_, v_n_145_);
lean_dec(v_n_145_);
lean_dec(v_y_144_);
lean_dec(v_x_143_);
lean_dec(v_w_u2082_142_);
lean_dec(v_w_u2081_141_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_BitVec_DivModState_init(lean_object* v_w_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = l_BitVec_ofNat(v_w_147_, v___x_148_);
lean_inc(v___x_149_);
v___x_150_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_150_, 0, v_w_147_);
lean_ctor_set(v___x_150_, 1, v___x_148_);
lean_ctor_set(v___x_150_, 2, v___x_149_);
lean_ctor_set(v___x_150_, 3, v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_BitVec_divSubtractShift(lean_object* v_w_151_, lean_object* v_args_152_, lean_object* v_qr_153_){
_start:
{
lean_object* v_n_154_; lean_object* v_d_155_; lean_object* v_wn_156_; lean_object* v_wr_157_; lean_object* v_q_158_; lean_object* v_r_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_180_; 
v_n_154_ = lean_ctor_get(v_args_152_, 0);
v_d_155_ = lean_ctor_get(v_args_152_, 1);
v_wn_156_ = lean_ctor_get(v_qr_153_, 0);
v_wr_157_ = lean_ctor_get(v_qr_153_, 1);
v_q_158_ = lean_ctor_get(v_qr_153_, 2);
v_r_159_ = lean_ctor_get(v_qr_153_, 3);
v_isSharedCheck_180_ = !lean_is_exclusive(v_qr_153_);
if (v_isSharedCheck_180_ == 0)
{
v___x_161_ = v_qr_153_;
v_isShared_162_ = v_isSharedCheck_180_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_r_159_);
lean_inc(v_q_158_);
lean_inc(v_wr_157_);
lean_inc(v_wn_156_);
lean_dec(v_qr_153_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_180_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v_wn_164_; lean_object* v_wr_165_; uint8_t v___x_166_; lean_object* v_r_x27_167_; uint8_t v___x_168_; 
v___x_163_ = lean_unsigned_to_nat(1u);
v_wn_164_ = lean_nat_sub(v_wn_156_, v___x_163_);
lean_dec(v_wn_156_);
v_wr_165_ = lean_nat_add(v_wr_157_, v___x_163_);
lean_dec(v_wr_157_);
v___x_166_ = l_Nat_testBit(v_n_154_, v_wn_164_);
v_r_x27_167_ = l_BitVec_shiftConcat(v_w_151_, v_r_159_, v___x_166_);
lean_dec(v_r_159_);
v___x_168_ = lean_nat_dec_lt(v_r_x27_167_, v_d_155_);
if (v___x_168_ == 0)
{
uint8_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_169_ = 1;
v___x_170_ = l_BitVec_shiftConcat(v_w_151_, v_q_158_, v___x_169_);
lean_dec(v_q_158_);
v___x_171_ = l_BitVec_sub(v_w_151_, v_r_x27_167_, v_d_155_);
lean_dec(v_r_x27_167_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 3, v___x_171_);
lean_ctor_set(v___x_161_, 2, v___x_170_);
lean_ctor_set(v___x_161_, 1, v_wr_165_);
lean_ctor_set(v___x_161_, 0, v_wn_164_);
v___x_173_ = v___x_161_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_wn_164_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_wr_165_);
lean_ctor_set(v_reuseFailAlloc_174_, 2, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_174_, 3, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
else
{
uint8_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_175_ = 0;
v___x_176_ = l_BitVec_shiftConcat(v_w_151_, v_q_158_, v___x_175_);
lean_dec(v_q_158_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 3, v_r_x27_167_);
lean_ctor_set(v___x_161_, 2, v___x_176_);
lean_ctor_set(v___x_161_, 1, v_wr_165_);
lean_ctor_set(v___x_161_, 0, v_wn_164_);
v___x_178_ = v___x_161_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_wn_164_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_wr_165_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_179_, 3, v_r_x27_167_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_divSubtractShift___boxed(lean_object* v_w_181_, lean_object* v_args_182_, lean_object* v_qr_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_BitVec_divSubtractShift(v_w_181_, v_args_182_, v_qr_183_);
lean_dec_ref(v_args_182_);
lean_dec(v_w_181_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_BitVec_divRec(lean_object* v_w_185_, lean_object* v_m_186_, lean_object* v_args_187_, lean_object* v_qr_188_){
_start:
{
lean_object* v_zero_189_; uint8_t v_isZero_190_; 
v_zero_189_ = lean_unsigned_to_nat(0u);
v_isZero_190_ = lean_nat_dec_eq(v_m_186_, v_zero_189_);
if (v_isZero_190_ == 1)
{
lean_dec(v_m_186_);
return v_qr_188_;
}
else
{
lean_object* v_one_191_; lean_object* v_n_192_; lean_object* v___x_193_; 
v_one_191_ = lean_unsigned_to_nat(1u);
v_n_192_ = lean_nat_sub(v_m_186_, v_one_191_);
lean_dec(v_m_186_);
v___x_193_ = l_BitVec_divSubtractShift(v_w_185_, v_args_187_, v_qr_188_);
v_m_186_ = v_n_192_;
v_qr_188_ = v___x_193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_divRec___boxed(lean_object* v_w_195_, lean_object* v_m_196_, lean_object* v_args_197_, lean_object* v_qr_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_BitVec_divRec(v_w_195_, v_m_196_, v_args_197_, v_qr_198_);
lean_dec_ref(v_args_197_);
lean_dec(v_w_195_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRightRec(lean_object* v_w_u2081_200_, lean_object* v_w_u2082_201_, lean_object* v_x_202_, lean_object* v_y_203_, lean_object* v_n_204_){
_start:
{
lean_object* v___x_205_; lean_object* v_shiftAmt_206_; lean_object* v_zero_207_; uint8_t v_isZero_208_; 
v___x_205_ = l_BitVec_twoPow(v_w_u2082_201_, v_n_204_);
v_shiftAmt_206_ = lean_nat_land(v_y_203_, v___x_205_);
lean_dec(v___x_205_);
v_zero_207_ = lean_unsigned_to_nat(0u);
v_isZero_208_ = lean_nat_dec_eq(v_n_204_, v_zero_207_);
if (v_isZero_208_ == 1)
{
lean_object* v___x_209_; 
v___x_209_ = l_BitVec_sshiftRight(v_w_u2081_200_, v_x_202_, v_shiftAmt_206_);
lean_dec(v_shiftAmt_206_);
return v___x_209_;
}
else
{
lean_object* v_one_210_; lean_object* v_n_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_one_210_ = lean_unsigned_to_nat(1u);
v_n_211_ = lean_nat_sub(v_n_204_, v_one_210_);
v___x_212_ = l_BitVec_sshiftRightRec(v_w_u2081_200_, v_w_u2082_201_, v_x_202_, v_y_203_, v_n_211_);
lean_dec(v_n_211_);
v___x_213_ = l_BitVec_sshiftRight(v_w_u2081_200_, v___x_212_, v_shiftAmt_206_);
lean_dec(v_shiftAmt_206_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_sshiftRightRec___boxed(lean_object* v_w_u2081_214_, lean_object* v_w_u2082_215_, lean_object* v_x_216_, lean_object* v_y_217_, lean_object* v_n_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_BitVec_sshiftRightRec(v_w_u2081_214_, v_w_u2082_215_, v_x_216_, v_y_217_, v_n_218_);
lean_dec(v_n_218_);
lean_dec(v_y_217_);
lean_dec(v_w_u2082_215_);
lean_dec(v_w_u2081_214_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___redArg(lean_object* v_w_u2082_220_, lean_object* v_x_221_, lean_object* v_y_222_, lean_object* v_n_223_){
_start:
{
lean_object* v___x_224_; lean_object* v_shiftAmt_225_; lean_object* v_zero_226_; uint8_t v_isZero_227_; 
v___x_224_ = l_BitVec_twoPow(v_w_u2082_220_, v_n_223_);
v_shiftAmt_225_ = lean_nat_land(v_y_222_, v___x_224_);
lean_dec(v___x_224_);
v_zero_226_ = lean_unsigned_to_nat(0u);
v_isZero_227_ = lean_nat_dec_eq(v_n_223_, v_zero_226_);
if (v_isZero_227_ == 1)
{
lean_object* v___x_228_; 
v___x_228_ = lean_nat_shiftr(v_x_221_, v_shiftAmt_225_);
lean_dec(v_shiftAmt_225_);
return v___x_228_;
}
else
{
lean_object* v_one_229_; lean_object* v_n_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_one_229_ = lean_unsigned_to_nat(1u);
v_n_230_ = lean_nat_sub(v_n_223_, v_one_229_);
v___x_231_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_220_, v_x_221_, v_y_222_, v_n_230_);
lean_dec(v_n_230_);
v___x_232_ = lean_nat_shiftr(v___x_231_, v_shiftAmt_225_);
lean_dec(v_shiftAmt_225_);
lean_dec(v___x_231_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___redArg___boxed(lean_object* v_w_u2082_233_, lean_object* v_x_234_, lean_object* v_y_235_, lean_object* v_n_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_233_, v_x_234_, v_y_235_, v_n_236_);
lean_dec(v_n_236_);
lean_dec(v_y_235_);
lean_dec(v_x_234_);
lean_dec(v_w_u2082_233_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec(lean_object* v_w_u2081_238_, lean_object* v_w_u2082_239_, lean_object* v_x_240_, lean_object* v_y_241_, lean_object* v_n_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_BitVec_ushiftRightRec___redArg(v_w_u2082_239_, v_x_240_, v_y_241_, v_n_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_BitVec_ushiftRightRec___boxed(lean_object* v_w_u2081_244_, lean_object* v_w_u2082_245_, lean_object* v_x_246_, lean_object* v_y_247_, lean_object* v_n_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_BitVec_ushiftRightRec(v_w_u2081_244_, v_w_u2082_245_, v_x_246_, v_y_247_, v_n_248_);
lean_dec(v_n_248_);
lean_dec(v_y_247_);
lean_dec(v_x_246_);
lean_dec(v_w_u2082_245_);
lean_dec(v_w_u2081_244_);
return v_res_249_;
}
}
LEAN_EXPORT uint8_t l_BitVec_uppcRec___redArg(lean_object* v_w_250_, lean_object* v_x_251_, lean_object* v_s_252_){
_start:
{
lean_object* v_zero_253_; uint8_t v_isZero_254_; 
v_zero_253_ = lean_unsigned_to_nat(0u);
v_isZero_254_ = lean_nat_dec_eq(v_s_252_, v_zero_253_);
if (v_isZero_254_ == 1)
{
uint8_t v___x_255_; 
lean_dec(v_s_252_);
v___x_255_ = lean_nat_dec_lt(v_zero_253_, v_w_250_);
if (v___x_255_ == 0)
{
return v___x_255_;
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_256_ = lean_unsigned_to_nat(1u);
v___x_257_ = lean_nat_sub(v_w_250_, v___x_256_);
v___x_258_ = l_Nat_testBit(v_x_251_, v___x_257_);
lean_dec(v___x_257_);
return v___x_258_;
}
}
else
{
lean_object* v_one_259_; lean_object* v_n_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_one_259_ = lean_unsigned_to_nat(1u);
v_n_260_ = lean_nat_sub(v_s_252_, v_one_259_);
lean_dec(v_s_252_);
v___x_261_ = lean_nat_sub(v_w_250_, v_one_259_);
v___x_262_ = lean_nat_sub(v___x_261_, v_n_260_);
lean_dec(v___x_261_);
v___x_263_ = l_Nat_testBit(v_x_251_, v___x_262_);
lean_dec(v___x_262_);
if (v___x_263_ == 0)
{
v_s_252_ = v_n_260_;
goto _start;
}
else
{
lean_dec(v_n_260_);
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_uppcRec___redArg___boxed(lean_object* v_w_265_, lean_object* v_x_266_, lean_object* v_s_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_BitVec_uppcRec___redArg(v_w_265_, v_x_266_, v_s_267_);
lean_dec(v_x_266_);
lean_dec(v_w_265_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint8_t l_BitVec_uppcRec(lean_object* v_w_270_, lean_object* v_x_271_, lean_object* v_s_272_, lean_object* v_hs_273_){
_start:
{
uint8_t v___x_274_; 
v___x_274_ = l_BitVec_uppcRec___redArg(v_w_270_, v_x_271_, v_s_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_BitVec_uppcRec___boxed(lean_object* v_w_275_, lean_object* v_x_276_, lean_object* v_s_277_, lean_object* v_hs_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_BitVec_uppcRec(v_w_275_, v_x_276_, v_s_277_, v_hs_278_);
lean_dec(v_x_276_);
lean_dec(v_w_275_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT uint8_t l_BitVec_aandRec___redArg(lean_object* v_w_281_, lean_object* v_x_282_, lean_object* v_y_283_, lean_object* v_s_284_){
_start:
{
uint8_t v___x_285_; 
v___x_285_ = l_Nat_testBit(v_y_283_, v_s_284_);
if (v___x_285_ == 0)
{
lean_dec(v_s_284_);
return v___x_285_;
}
else
{
uint8_t v___x_286_; 
v___x_286_ = l_BitVec_uppcRec___redArg(v_w_281_, v_x_282_, v_s_284_);
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_aandRec___redArg___boxed(lean_object* v_w_287_, lean_object* v_x_288_, lean_object* v_y_289_, lean_object* v_s_290_){
_start:
{
uint8_t v_res_291_; lean_object* v_r_292_; 
v_res_291_ = l_BitVec_aandRec___redArg(v_w_287_, v_x_288_, v_y_289_, v_s_290_);
lean_dec(v_y_289_);
lean_dec(v_x_288_);
lean_dec(v_w_287_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
LEAN_EXPORT uint8_t l_BitVec_aandRec(lean_object* v_w_293_, lean_object* v_x_294_, lean_object* v_y_295_, lean_object* v_s_296_, lean_object* v_hs_297_){
_start:
{
uint8_t v___x_298_; 
v___x_298_ = l_BitVec_aandRec___redArg(v_w_293_, v_x_294_, v_y_295_, v_s_296_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_BitVec_aandRec___boxed(lean_object* v_w_299_, lean_object* v_x_300_, lean_object* v_y_301_, lean_object* v_s_302_, lean_object* v_hs_303_){
_start:
{
uint8_t v_res_304_; lean_object* v_r_305_; 
v_res_304_ = l_BitVec_aandRec(v_w_299_, v_x_300_, v_y_301_, v_s_302_, v_hs_303_);
lean_dec(v_y_301_);
lean_dec(v_x_300_);
lean_dec(v_w_299_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT uint8_t l_BitVec_resRec___redArg(lean_object* v_w_306_, lean_object* v_x_307_, lean_object* v_y_308_, lean_object* v_s_309_){
_start:
{
lean_object* v_zero_310_; uint8_t v_isZero_311_; lean_object* v_one_312_; lean_object* v_n_313_; uint8_t v_isZero_314_; 
v_zero_310_ = lean_unsigned_to_nat(0u);
v_isZero_311_ = lean_nat_dec_eq(v_s_309_, v_zero_310_);
v_one_312_ = lean_unsigned_to_nat(1u);
v_n_313_ = lean_nat_sub(v_s_309_, v_one_312_);
v_isZero_314_ = lean_nat_dec_eq(v_n_313_, v_zero_310_);
if (v_isZero_314_ == 1)
{
uint8_t v___x_315_; 
lean_dec(v_n_313_);
lean_dec(v_s_309_);
v___x_315_ = l_BitVec_aandRec___redArg(v_w_306_, v_x_307_, v_y_308_, v_one_312_);
return v___x_315_;
}
else
{
uint8_t v___x_316_; 
v___x_316_ = l_BitVec_resRec___redArg(v_w_306_, v_x_307_, v_y_308_, v_n_313_);
if (v___x_316_ == 0)
{
uint8_t v___x_317_; 
v___x_317_ = l_BitVec_aandRec___redArg(v_w_306_, v_x_307_, v_y_308_, v_s_309_);
return v___x_317_;
}
else
{
lean_dec(v_s_309_);
return v___x_316_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_resRec___redArg___boxed(lean_object* v_w_318_, lean_object* v_x_319_, lean_object* v_y_320_, lean_object* v_s_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_BitVec_resRec___redArg(v_w_318_, v_x_319_, v_y_320_, v_s_321_);
lean_dec(v_y_320_);
lean_dec(v_x_319_);
lean_dec(v_w_318_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT uint8_t l_BitVec_resRec(lean_object* v_w_324_, lean_object* v_x_325_, lean_object* v_y_326_, lean_object* v_s_327_, lean_object* v_hs_328_, lean_object* v_hslt_329_){
_start:
{
uint8_t v___x_330_; 
v___x_330_ = l_BitVec_resRec___redArg(v_w_324_, v_x_325_, v_y_326_, v_s_327_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_BitVec_resRec___boxed(lean_object* v_w_331_, lean_object* v_x_332_, lean_object* v_y_333_, lean_object* v_s_334_, lean_object* v_hs_335_, lean_object* v_hslt_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_BitVec_resRec(v_w_331_, v_x_332_, v_y_333_, v_s_334_, v_hs_335_, v_hslt_336_);
lean_dec(v_y_333_);
lean_dec(v_x_332_);
lean_dec(v_w_331_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___redArg(lean_object* v_idx_339_, lean_object* v_len_340_, lean_object* v_x_341_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = l_BitVec_extractLsb_x27___redArg(v_idx_339_, v___x_342_, v_x_341_);
v___x_344_ = l_BitVec_setWidth(v___x_342_, v_len_340_, v___x_343_);
lean_dec(v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___redArg___boxed(lean_object* v_idx_345_, lean_object* v_len_346_, lean_object* v_x_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_BitVec_extractAndExtendBit___redArg(v_idx_345_, v_len_346_, v_x_347_);
lean_dec(v_x_347_);
lean_dec(v_len_346_);
lean_dec(v_idx_345_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit(lean_object* v_w_349_, lean_object* v_idx_350_, lean_object* v_len_351_, lean_object* v_x_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_BitVec_extractAndExtendBit___redArg(v_idx_350_, v_len_351_, v_x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendBit___boxed(lean_object* v_w_354_, lean_object* v_idx_355_, lean_object* v_len_356_, lean_object* v_x_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_BitVec_extractAndExtendBit(v_w_354_, v_idx_355_, v_len_356_, v_x_357_);
lean_dec(v_x_357_);
lean_dec(v_len_356_);
lean_dec(v_idx_355_);
lean_dec(v_w_354_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___redArg(lean_object* v_w_359_, lean_object* v_k_360_, lean_object* v_len_361_, lean_object* v_x_362_, lean_object* v_acc_363_){
_start:
{
lean_object* v___x_364_; lean_object* v_zero_365_; uint8_t v_isZero_366_; 
v___x_364_ = lean_nat_sub(v_w_359_, v_k_360_);
v_zero_365_ = lean_unsigned_to_nat(0u);
v_isZero_366_ = lean_nat_dec_eq(v___x_364_, v_zero_365_);
lean_dec(v___x_364_);
if (v_isZero_366_ == 1)
{
lean_dec(v_k_360_);
return v_acc_363_;
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v_acc_x27_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_367_ = lean_nat_mul(v_k_360_, v_len_361_);
v___x_368_ = l_BitVec_extractAndExtendBit___redArg(v_k_360_, v_len_361_, v_x_362_);
v_acc_x27_369_ = l_BitVec_append___redArg(v___x_367_, v___x_368_, v_acc_363_);
lean_dec(v_acc_363_);
lean_dec(v___x_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = lean_nat_add(v_k_360_, v___x_370_);
lean_dec(v_k_360_);
v_k_360_ = v___x_371_;
v_acc_363_ = v_acc_x27_369_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___redArg___boxed(lean_object* v_w_373_, lean_object* v_k_374_, lean_object* v_len_375_, lean_object* v_x_376_, lean_object* v_acc_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_BitVec_extractAndExtendAux___redArg(v_w_373_, v_k_374_, v_len_375_, v_x_376_, v_acc_377_);
lean_dec(v_x_376_);
lean_dec(v_len_375_);
lean_dec(v_w_373_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux(lean_object* v_w_379_, lean_object* v_k_380_, lean_object* v_len_381_, lean_object* v_x_382_, lean_object* v_acc_383_, lean_object* v_hle_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_BitVec_extractAndExtendAux___redArg(v_w_379_, v_k_380_, v_len_381_, v_x_382_, v_acc_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtendAux___boxed(lean_object* v_w_386_, lean_object* v_k_387_, lean_object* v_len_388_, lean_object* v_x_389_, lean_object* v_acc_390_, lean_object* v_hle_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_BitVec_extractAndExtendAux(v_w_386_, v_k_387_, v_len_388_, v_x_389_, v_acc_390_, v_hle_391_);
lean_dec(v_x_389_);
lean_dec(v_len_388_);
lean_dec(v_w_386_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg(lean_object* v_x_393_, lean_object* v_h__1_394_, lean_object* v_h__2_395_){
_start:
{
lean_object* v_zero_396_; uint8_t v_isZero_397_; 
v_zero_396_ = lean_unsigned_to_nat(0u);
v_isZero_397_ = lean_nat_dec_eq(v_x_393_, v_zero_396_);
if (v_isZero_397_ == 1)
{
lean_object* v___x_398_; 
lean_dec(v_h__2_395_);
v___x_398_ = lean_apply_1(v_h__1_394_, lean_box(0));
return v___x_398_;
}
else
{
lean_object* v_one_399_; lean_object* v_n_400_; lean_object* v___x_401_; 
lean_dec(v_h__1_394_);
v_one_399_ = lean_unsigned_to_nat(1u);
v_n_400_ = lean_nat_sub(v_x_393_, v_one_399_);
v___x_401_ = lean_apply_2(v_h__2_395_, v_n_400_, lean_box(0));
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg___boxed(lean_object* v_x_402_, lean_object* v_h__1_403_, lean_object* v_h__2_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg(v_x_402_, v_h__1_403_, v_h__2_404_);
lean_dec(v_x_402_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter(lean_object* v_motive_406_, lean_object* v_x_407_, lean_object* v_h__1_408_, lean_object* v_h__2_409_){
_start:
{
lean_object* v_zero_410_; uint8_t v_isZero_411_; 
v_zero_410_ = lean_unsigned_to_nat(0u);
v_isZero_411_ = lean_nat_dec_eq(v_x_407_, v_zero_410_);
if (v_isZero_411_ == 1)
{
lean_object* v___x_412_; 
lean_dec(v_h__2_409_);
v___x_412_ = lean_apply_1(v_h__1_408_, lean_box(0));
return v___x_412_;
}
else
{
lean_object* v_one_413_; lean_object* v_n_414_; lean_object* v___x_415_; 
lean_dec(v_h__1_408_);
v_one_413_ = lean_unsigned_to_nat(1u);
v_n_414_ = lean_nat_sub(v_x_407_, v_one_413_);
v___x_415_ = lean_apply_2(v_h__2_409_, v_n_414_, lean_box(0));
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___boxed(lean_object* v_motive_416_, lean_object* v_x_417_, lean_object* v_h__1_418_, lean_object* v_h__2_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter(v_motive_416_, v_x_417_, v_h__1_418_, v_h__2_419_);
lean_dec(v_x_417_);
return v_res_420_;
}
}
static lean_object* _init_l_BitVec_extractAndExtend___closed__0(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = l_BitVec_ofNat(v___x_421_, v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtend(lean_object* v_w_423_, lean_object* v_len_424_, lean_object* v_x_425_){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_obj_once(&l_BitVec_extractAndExtend___closed__0, &l_BitVec_extractAndExtend___closed__0_once, _init_l_BitVec_extractAndExtend___closed__0);
v___x_428_ = l_BitVec_extractAndExtendAux___redArg(v_w_423_, v___x_426_, v_len_424_, v_x_425_, v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_BitVec_extractAndExtend___boxed(lean_object* v_w_429_, lean_object* v_len_430_, lean_object* v_x_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_BitVec_extractAndExtend(v_w_429_, v_len_430_, v_x_431_);
lean_dec(v_x_431_);
lean_dec(v_len_430_);
lean_dec(v_w_429_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___redArg(lean_object* v_len_433_, lean_object* v_w_434_, lean_object* v_iterNum_435_, lean_object* v_oldLayer_436_, lean_object* v_newLayer_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_438_ = lean_unsigned_to_nat(2u);
v___x_439_ = lean_nat_mul(v_iterNum_435_, v___x_438_);
v___x_440_ = lean_nat_sub(v_len_433_, v___x_439_);
lean_dec(v___x_439_);
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_nat_dec_eq(v___x_440_, v___x_441_);
lean_dec(v___x_440_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_op1_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_op2_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v_newLayer_x27_452_; lean_object* v___x_453_; 
v___x_443_ = lean_nat_mul(v___x_438_, v_iterNum_435_);
v___x_444_ = lean_nat_mul(v___x_443_, v_w_434_);
v_op1_445_ = l_BitVec_extractLsb_x27___redArg(v___x_444_, v_w_434_, v_oldLayer_436_);
lean_dec(v___x_444_);
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_nat_add(v___x_443_, v___x_446_);
lean_dec(v___x_443_);
v___x_448_ = lean_nat_mul(v___x_447_, v_w_434_);
lean_dec(v___x_447_);
v_op2_449_ = l_BitVec_extractLsb_x27___redArg(v___x_448_, v_w_434_, v_oldLayer_436_);
lean_dec(v___x_448_);
v___x_450_ = lean_nat_mul(v_iterNum_435_, v_w_434_);
v___x_451_ = l_BitVec_add(v_w_434_, v_op1_445_, v_op2_449_);
lean_dec(v_op2_449_);
lean_dec(v_op1_445_);
v_newLayer_x27_452_ = l_BitVec_append___redArg(v___x_450_, v___x_451_, v_newLayer_437_);
lean_dec(v_newLayer_437_);
lean_dec(v___x_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_nat_add(v_iterNum_435_, v___x_446_);
lean_dec(v_iterNum_435_);
v_iterNum_435_ = v___x_453_;
v_newLayer_437_ = v_newLayer_x27_452_;
goto _start;
}
else
{
lean_dec(v_iterNum_435_);
return v_newLayer_437_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___redArg___boxed(lean_object* v_len_455_, lean_object* v_w_456_, lean_object* v_iterNum_457_, lean_object* v_oldLayer_458_, lean_object* v_newLayer_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_BitVec_cpopLayer___redArg(v_len_455_, v_w_456_, v_iterNum_457_, v_oldLayer_458_, v_newLayer_459_);
lean_dec(v_oldLayer_458_);
lean_dec(v_w_456_);
lean_dec(v_len_455_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer(lean_object* v_len_461_, lean_object* v_w_462_, lean_object* v_iterNum_463_, lean_object* v_oldLayer_464_, lean_object* v_newLayer_465_, lean_object* v_hold_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_BitVec_cpopLayer___redArg(v_len_461_, v_w_462_, v_iterNum_463_, v_oldLayer_464_, v_newLayer_465_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopLayer___boxed(lean_object* v_len_468_, lean_object* v_w_469_, lean_object* v_iterNum_470_, lean_object* v_oldLayer_471_, lean_object* v_newLayer_472_, lean_object* v_hold_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_BitVec_cpopLayer(v_len_468_, v_w_469_, v_iterNum_470_, v_oldLayer_471_, v_newLayer_472_, v_hold_473_);
lean_dec(v_oldLayer_471_);
lean_dec(v_w_469_);
lean_dec(v_len_468_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopTree(lean_object* v_len_475_, lean_object* v_w_476_, lean_object* v_l_477_){
_start:
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = lean_nat_dec_eq(v_len_475_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_dec_eq(v_len_475_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_482_ = lean_nat_add(v_len_475_, v___x_480_);
v___x_483_ = lean_nat_shiftr(v___x_482_, v___x_480_);
lean_dec(v___x_482_);
v___x_484_ = lean_obj_once(&l_BitVec_extractAndExtend___closed__0, &l_BitVec_extractAndExtend___closed__0_once, _init_l_BitVec_extractAndExtend___closed__0);
v___x_485_ = l_BitVec_cpopLayer___redArg(v_len_475_, v_w_476_, v___x_478_, v_l_477_, v___x_484_);
lean_dec(v_l_477_);
lean_dec(v_len_475_);
v_len_475_ = v___x_483_;
v_l_477_ = v___x_485_;
goto _start;
}
else
{
lean_dec(v_len_475_);
return v_l_477_;
}
}
else
{
lean_object* v___x_487_; 
lean_dec(v_l_477_);
lean_dec(v_len_475_);
v___x_487_ = l_BitVec_ofNat(v_w_476_, v___x_478_);
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopTree___boxed(lean_object* v_len_488_, lean_object* v_w_489_, lean_object* v_l_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_BitVec_cpopTree(v_len_488_, v_w_489_, v_l_490_);
lean_dec(v_w_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopRec(lean_object* v_w_492_, lean_object* v_x_493_){
_start:
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = lean_nat_dec_lt(v___x_494_, v_w_492_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = lean_unsigned_to_nat(0u);
v___x_497_ = lean_nat_dec_lt(v___x_496_, v_w_492_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; 
v___x_498_ = l_BitVec_ofNat(v_w_492_, v___x_496_);
lean_dec(v_w_492_);
return v___x_498_;
}
else
{
lean_dec(v_w_492_);
lean_inc(v_x_493_);
return v_x_493_;
}
}
else
{
lean_object* v_extendedBits_499_; lean_object* v___x_500_; 
v_extendedBits_499_ = l_BitVec_extractAndExtend(v_w_492_, v_w_492_, v_x_493_);
lean_inc(v_w_492_);
v___x_500_ = l_BitVec_cpopTree(v_w_492_, v_w_492_, v_extendedBits_499_);
lean_dec(v_w_492_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l_BitVec_cpopRec___boxed(lean_object* v_w_501_, lean_object* v_x_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_BitVec_cpopRec(v_w_501_, v_x_502_);
lean_dec(v_x_502_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(lean_object* v_w_504_, lean_object* v_x_505_, lean_object* v_rem_506_, lean_object* v_acc_507_){
_start:
{
lean_object* v_zero_508_; uint8_t v_isZero_509_; 
v_zero_508_ = lean_unsigned_to_nat(0u);
v_isZero_509_ = lean_nat_dec_eq(v_rem_506_, v_zero_508_);
if (v_isZero_509_ == 1)
{
lean_dec(v_rem_506_);
return v_acc_507_;
}
else
{
lean_object* v_one_510_; lean_object* v_n_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_one_510_ = lean_unsigned_to_nat(1u);
v_n_511_ = lean_nat_sub(v_rem_506_, v_one_510_);
lean_dec(v_rem_506_);
v___x_512_ = lean_nat_mul(v_n_511_, v_w_504_);
v___x_513_ = l_BitVec_extractLsb_x27___redArg(v___x_512_, v_w_504_, v_x_505_);
lean_dec(v___x_512_);
v___x_514_ = l_BitVec_add(v_w_504_, v_acc_507_, v___x_513_);
lean_dec(v___x_513_);
lean_dec(v_acc_507_);
v_rem_506_ = v_n_511_;
v_acc_507_ = v___x_514_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg___boxed(lean_object* v_w_516_, lean_object* v_x_517_, lean_object* v_rem_518_, lean_object* v_acc_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_516_, v_x_517_, v_rem_518_, v_acc_519_);
lean_dec(v_x_517_);
lean_dec(v_w_516_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux(lean_object* v_l_521_, lean_object* v_w_522_, lean_object* v_x_523_, lean_object* v_rem_524_, lean_object* v_acc_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_522_, v_x_523_, v_rem_524_, v_acc_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___boxed(lean_object* v_l_527_, lean_object* v_w_528_, lean_object* v_x_529_, lean_object* v_rem_530_, lean_object* v_acc_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux(v_l_527_, v_w_528_, v_x_529_, v_rem_530_, v_acc_531_);
lean_dec(v_x_529_);
lean_dec(v_w_528_);
lean_dec(v_l_527_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec(lean_object* v_l_533_, lean_object* v_w_534_, lean_object* v_x_535_){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = l_BitVec_ofNat(v_w_534_, v___x_536_);
v___x_538_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(v_w_534_, v_x_535_, v_l_533_, v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec___boxed(lean_object* v_l_539_, lean_object* v_w_540_, lean_object* v_x_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec(v_l_539_, v_w_540_, v_x_541_);
lean_dec(v_x_541_);
lean_dec(v_w_540_);
return v_res_542_;
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
