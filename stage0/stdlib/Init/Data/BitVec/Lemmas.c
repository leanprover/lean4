// Lean compiler output
// Module: Init.Data.BitVec.Lemmas
// Imports: import all Init.Data.BitVec.Basic import all Init.Data.BitVec.BasicAux public import Init.Data.Fin.Lemmas public import Init.Data.List.BasicAux import Init.Data.List.Lemmas import Init.Data.List.TakeDrop import Init.Data.List.Nat.TakeDrop public import Init.Data.BitVec.Basic import Init.ByCases import Init.Data.BitVec.Bootstrap import Init.Data.Int.Bitwise.Lemmas import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.LemmasAux import Init.Data.Int.Pow import Init.Data.Nat.Div.Lemmas import Init.Data.Nat.MinMax import Init.Data.Nat.Mod import Init.Data.Nat.Simproc import Init.TacticsExtra
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
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_List_take___redArg(lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_flattenList_toNatAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_flattenList_toNatAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_flattenListFast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_flattenListFast___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_ofBoolListBE_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_ofBoolListBE_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_1_; lean_object* v_intZero_2_; 
v_natZero_1_ = lean_unsigned_to_nat(0u);
v_intZero_2_ = lean_nat_to_int(v_natZero_1_);
return v_intZero_2_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg(lean_object* v_x_3_, lean_object* v_h__1_4_, lean_object* v_h__2_5_){
_start:
{
lean_object* v_intZero_6_; uint8_t v_isNeg_7_; 
v_intZero_6_ = lean_obj_once(&l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0, &l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0);
v_isNeg_7_ = lean_int_dec_lt(v_x_3_, v_intZero_6_);
if (v_isNeg_7_ == 0)
{
lean_object* v_a_8_; lean_object* v___x_9_; 
lean_dec(v_h__2_5_);
v_a_8_ = lean_nat_abs(v_x_3_);
v___x_9_ = lean_apply_1(v_h__1_4_, v_a_8_);
return v___x_9_;
}
else
{
lean_object* v_abs_10_; lean_object* v_one_11_; lean_object* v_a_12_; lean_object* v___x_13_; 
lean_dec(v_h__1_4_);
v_abs_10_ = lean_nat_abs(v_x_3_);
v_one_11_ = lean_unsigned_to_nat(1u);
v_a_12_ = lean_nat_sub(v_abs_10_, v_one_11_);
lean_dec(v_abs_10_);
v___x_13_ = lean_apply_1(v_h__2_5_, v_a_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___boxed(lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg(v_x_14_, v_h__1_15_, v_h__2_16_);
lean_dec(v_x_14_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter(lean_object* v_motive_18_, lean_object* v_x_19_, lean_object* v_h__1_20_, lean_object* v_h__2_21_){
_start:
{
lean_object* v_intZero_22_; uint8_t v_isNeg_23_; 
v_intZero_22_ = lean_obj_once(&l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0, &l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0);
v_isNeg_23_ = lean_int_dec_lt(v_x_19_, v_intZero_22_);
if (v_isNeg_23_ == 0)
{
lean_object* v_a_24_; lean_object* v___x_25_; 
lean_dec(v_h__2_21_);
v_a_24_ = lean_nat_abs(v_x_19_);
v___x_25_ = lean_apply_1(v_h__1_20_, v_a_24_);
return v___x_25_;
}
else
{
lean_object* v_abs_26_; lean_object* v_one_27_; lean_object* v_a_28_; lean_object* v___x_29_; 
lean_dec(v_h__1_20_);
v_abs_26_ = lean_nat_abs(v_x_19_);
v_one_27_ = lean_unsigned_to_nat(1u);
v_a_28_ = lean_nat_sub(v_abs_26_, v_one_27_);
lean_dec(v_abs_26_);
v___x_29_ = lean_apply_1(v_h__2_21_, v_a_28_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___boxed(lean_object* v_motive_30_, lean_object* v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter(v_motive_30_, v_x_31_, v_h__1_32_, v_h__2_33_);
lean_dec(v_x_31_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_match__1_splitter___redArg(lean_object* v_xs_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_){
_start:
{
if (lean_obj_tag(v_xs_35_) == 0)
{
lean_object* v___x_38_; lean_object* v___x_39_; 
lean_dec(v_h__2_37_);
v___x_38_ = lean_box(0);
v___x_39_ = lean_apply_1(v_h__1_36_, v___x_38_);
return v___x_39_;
}
else
{
lean_object* v_head_40_; lean_object* v_tail_41_; lean_object* v___x_42_; 
lean_dec(v_h__1_36_);
v_head_40_ = lean_ctor_get(v_xs_35_, 0);
lean_inc(v_head_40_);
v_tail_41_ = lean_ctor_get(v_xs_35_, 1);
lean_inc(v_tail_41_);
lean_dec_ref_known(v_xs_35_, 2);
v___x_42_ = lean_apply_2(v_h__2_37_, v_head_40_, v_tail_41_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_match__1_splitter(lean_object* v_n_43_, lean_object* v_motive_44_, lean_object* v_xs_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_){
_start:
{
if (lean_obj_tag(v_xs_45_) == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_h__2_47_);
v___x_48_ = lean_box(0);
v___x_49_ = lean_apply_1(v_h__1_46_, v___x_48_);
return v___x_49_;
}
else
{
lean_object* v_head_50_; lean_object* v_tail_51_; lean_object* v___x_52_; 
lean_dec(v_h__1_46_);
v_head_50_ = lean_ctor_get(v_xs_45_, 0);
lean_inc(v_head_50_);
v_tail_51_ = lean_ctor_get(v_xs_45_, 1);
lean_inc(v_tail_51_);
lean_dec_ref_known(v_xs_45_, 2);
v___x_52_ = lean_apply_2(v_h__2_47_, v_head_50_, v_tail_51_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_match__1_splitter___boxed(lean_object* v_n_53_, lean_object* v_motive_54_, lean_object* v_xs_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_match__1_splitter(v_n_53_, v_motive_54_, v_xs_55_, v_h__1_56_, v_h__2_57_);
lean_dec(v_n_53_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_BitVec_flattenList_toNatAux(lean_object* v_n_59_, lean_object* v_x_60_){
_start:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v___x_61_; 
v___x_61_ = lean_unsigned_to_nat(0u);
return v___x_61_;
}
else
{
lean_object* v_tail_62_; 
v_tail_62_ = lean_ctor_get(v_x_60_, 1);
if (lean_obj_tag(v_tail_62_) == 0)
{
lean_object* v_head_63_; 
v_head_63_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_head_63_);
lean_dec_ref_known(v_x_60_, 2);
return v_head_63_;
}
else
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v_mid_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_64_ = l_List_lengthTR___redArg(v_x_60_);
v___x_65_ = lean_unsigned_to_nat(1u);
v_mid_66_ = lean_nat_shiftr(v___x_64_, v___x_65_);
lean_dec(v___x_64_);
lean_inc_ref(v_x_60_);
v___x_67_ = l_List_take___redArg(v_mid_66_, v_x_60_);
v___x_68_ = l_BitVec_flattenList_toNatAux(v_n_59_, v___x_67_);
v___x_69_ = l_List_drop___redArg(v_mid_66_, v_x_60_);
lean_dec_ref_known(v_x_60_, 2);
v___x_70_ = l_List_lengthTR___redArg(v___x_69_);
v___x_71_ = lean_nat_mul(v_n_59_, v___x_70_);
lean_dec(v___x_70_);
v___x_72_ = lean_nat_shiftl(v___x_68_, v___x_71_);
lean_dec(v___x_71_);
lean_dec(v___x_68_);
v___x_73_ = l_BitVec_flattenList_toNatAux(v_n_59_, v___x_69_);
v___x_74_ = lean_nat_lor(v___x_72_, v___x_73_);
lean_dec(v___x_73_);
lean_dec(v___x_72_);
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_flattenList_toNatAux___boxed(lean_object* v_n_75_, lean_object* v_x_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_BitVec_flattenList_toNatAux(v_n_75_, v_x_76_);
lean_dec(v_n_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter___redArg(lean_object* v_x_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_, lean_object* v_h__3_81_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v_h__3_81_);
lean_dec(v_h__2_80_);
v___x_82_ = lean_box(0);
v___x_83_ = lean_apply_1(v_h__1_79_, v___x_82_);
return v___x_83_;
}
else
{
lean_object* v_tail_84_; 
lean_dec(v_h__1_79_);
v_tail_84_ = lean_ctor_get(v_x_78_, 1);
if (lean_obj_tag(v_tail_84_) == 0)
{
lean_object* v_head_85_; lean_object* v___x_86_; 
lean_dec(v_h__3_81_);
v_head_85_ = lean_ctor_get(v_x_78_, 0);
lean_inc(v_head_85_);
lean_dec_ref_known(v_x_78_, 2);
v___x_86_ = lean_apply_1(v_h__2_80_, v_head_85_);
return v___x_86_;
}
else
{
lean_object* v_head_87_; lean_object* v_head_88_; lean_object* v_tail_89_; lean_object* v___x_90_; 
lean_inc_ref(v_tail_84_);
lean_dec(v_h__2_80_);
v_head_87_ = lean_ctor_get(v_x_78_, 0);
lean_inc(v_head_87_);
lean_dec_ref_known(v_x_78_, 2);
v_head_88_ = lean_ctor_get(v_tail_84_, 0);
lean_inc(v_head_88_);
v_tail_89_ = lean_ctor_get(v_tail_84_, 1);
lean_inc(v_tail_89_);
lean_dec_ref_known(v_tail_84_, 2);
v___x_90_ = lean_apply_3(v_h__3_81_, v_head_87_, v_head_88_, v_tail_89_);
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter(lean_object* v_n_91_, lean_object* v_motive_92_, lean_object* v_x_93_, lean_object* v_h__1_94_, lean_object* v_h__2_95_, lean_object* v_h__3_96_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; 
lean_dec(v_h__3_96_);
lean_dec(v_h__2_95_);
v___x_97_ = lean_box(0);
v___x_98_ = lean_apply_1(v_h__1_94_, v___x_97_);
return v___x_98_;
}
else
{
lean_object* v_tail_99_; 
lean_dec(v_h__1_94_);
v_tail_99_ = lean_ctor_get(v_x_93_, 1);
if (lean_obj_tag(v_tail_99_) == 0)
{
lean_object* v_head_100_; lean_object* v___x_101_; 
lean_dec(v_h__3_96_);
v_head_100_ = lean_ctor_get(v_x_93_, 0);
lean_inc(v_head_100_);
lean_dec_ref_known(v_x_93_, 2);
v___x_101_ = lean_apply_1(v_h__2_95_, v_head_100_);
return v___x_101_;
}
else
{
lean_object* v_head_102_; lean_object* v_head_103_; lean_object* v_tail_104_; lean_object* v___x_105_; 
lean_inc_ref(v_tail_99_);
lean_dec(v_h__2_95_);
v_head_102_ = lean_ctor_get(v_x_93_, 0);
lean_inc(v_head_102_);
lean_dec_ref_known(v_x_93_, 2);
v_head_103_ = lean_ctor_get(v_tail_99_, 0);
lean_inc(v_head_103_);
v_tail_104_ = lean_ctor_get(v_tail_99_, 1);
lean_inc(v_tail_104_);
lean_dec_ref_known(v_tail_99_, 2);
v___x_105_ = lean_apply_3(v_h__3_96_, v_head_102_, v_head_103_, v_tail_104_);
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter___boxed(lean_object* v_n_106_, lean_object* v_motive_107_, lean_object* v_x_108_, lean_object* v_h__1_109_, lean_object* v_h__2_110_, lean_object* v_h__3_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter(v_n_106_, v_motive_107_, v_x_108_, v_h__1_109_, v_h__2_110_, v_h__3_111_);
lean_dec(v_n_106_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_BitVec_flattenListFast(lean_object* v_n_113_, lean_object* v_xs_114_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_115_ = l_List_lengthTR___redArg(v_xs_114_);
v___x_116_ = lean_nat_mul(v_n_113_, v___x_115_);
lean_dec(v___x_115_);
v___x_117_ = l_BitVec_flattenList_toNatAux(v_n_113_, v_xs_114_);
v___x_118_ = l_BitVec_ofNat(v___x_116_, v___x_117_);
lean_dec(v___x_117_);
lean_dec(v___x_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_BitVec_flattenListFast___boxed(lean_object* v_n_119_, lean_object* v_xs_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_BitVec_flattenListFast(v_n_119_, v_xs_120_);
lean_dec(v_n_119_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg(uint8_t v_x_122_, uint8_t v_x_123_, lean_object* v_h__1_124_, lean_object* v_h__2_125_, lean_object* v_h__3_126_, lean_object* v_h__4_127_){
_start:
{
if (v_x_122_ == 0)
{
lean_dec(v_h__4_127_);
lean_dec(v_h__3_126_);
if (v_x_123_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v_h__2_125_);
v___x_128_ = lean_box(0);
v___x_129_ = lean_apply_1(v_h__1_124_, v___x_128_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec(v_h__1_124_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_apply_1(v_h__2_125_, v___x_130_);
return v___x_131_;
}
}
else
{
lean_dec(v_h__2_125_);
lean_dec(v_h__1_124_);
if (v_x_123_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec(v_h__4_127_);
v___x_132_ = lean_box(0);
v___x_133_ = lean_apply_1(v_h__3_126_, v___x_132_);
return v___x_133_;
}
else
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec(v_h__3_126_);
v___x_134_ = lean_box(0);
v___x_135_ = lean_apply_1(v_h__4_127_, v___x_134_);
return v___x_135_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg___boxed(lean_object* v_x_136_, lean_object* v_x_137_, lean_object* v_h__1_138_, lean_object* v_h__2_139_, lean_object* v_h__3_140_, lean_object* v_h__4_141_){
_start:
{
uint8_t v_x_46__boxed_142_; uint8_t v_x_47__boxed_143_; lean_object* v_res_144_; 
v_x_46__boxed_142_ = lean_unbox(v_x_136_);
v_x_47__boxed_143_ = lean_unbox(v_x_137_);
v_res_144_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg(v_x_46__boxed_142_, v_x_47__boxed_143_, v_h__1_138_, v_h__2_139_, v_h__3_140_, v_h__4_141_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter(lean_object* v_motive_145_, uint8_t v_x_146_, uint8_t v_x_147_, lean_object* v_h__1_148_, lean_object* v_h__2_149_, lean_object* v_h__3_150_, lean_object* v_h__4_151_){
_start:
{
if (v_x_146_ == 0)
{
lean_dec(v_h__4_151_);
lean_dec(v_h__3_150_);
if (v_x_147_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec(v_h__2_149_);
v___x_152_ = lean_box(0);
v___x_153_ = lean_apply_1(v_h__1_148_, v___x_152_);
return v___x_153_;
}
else
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v_h__1_148_);
v___x_154_ = lean_box(0);
v___x_155_ = lean_apply_1(v_h__2_149_, v___x_154_);
return v___x_155_;
}
}
else
{
lean_dec(v_h__2_149_);
lean_dec(v_h__1_148_);
if (v_x_147_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec(v_h__4_151_);
v___x_156_ = lean_box(0);
v___x_157_ = lean_apply_1(v_h__3_150_, v___x_156_);
return v___x_157_;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_dec(v_h__3_150_);
v___x_158_ = lean_box(0);
v___x_159_ = lean_apply_1(v_h__4_151_, v___x_158_);
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___boxed(lean_object* v_motive_160_, lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_h__1_163_, lean_object* v_h__2_164_, lean_object* v_h__3_165_, lean_object* v_h__4_166_){
_start:
{
uint8_t v_x_68__boxed_167_; uint8_t v_x_69__boxed_168_; lean_object* v_res_169_; 
v_x_68__boxed_167_ = lean_unbox(v_x_161_);
v_x_69__boxed_168_ = lean_unbox(v_x_162_);
v_res_169_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter(v_motive_160_, v_x_68__boxed_167_, v_x_69__boxed_168_, v_h__1_163_, v_h__2_164_, v_h__3_165_, v_h__4_166_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_ofBoolListBE_match__1_splitter___redArg(lean_object* v_x_170_, lean_object* v_h__1_171_, lean_object* v_h__2_172_){
_start:
{
if (lean_obj_tag(v_x_170_) == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec(v_h__2_172_);
v___x_173_ = lean_box(0);
v___x_174_ = lean_apply_1(v_h__1_171_, v___x_173_);
return v___x_174_;
}
else
{
lean_object* v_head_175_; lean_object* v_tail_176_; lean_object* v___x_177_; 
lean_dec(v_h__1_171_);
v_head_175_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_head_175_);
v_tail_176_ = lean_ctor_get(v_x_170_, 1);
lean_inc(v_tail_176_);
lean_dec_ref_known(v_x_170_, 2);
v___x_177_ = lean_apply_2(v_h__2_172_, v_head_175_, v_tail_176_);
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_ofBoolListBE_match__1_splitter(lean_object* v_motive_178_, lean_object* v_x_179_, lean_object* v_h__1_180_, lean_object* v_h__2_181_){
_start:
{
if (lean_obj_tag(v_x_179_) == 0)
{
lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec(v_h__2_181_);
v___x_182_ = lean_box(0);
v___x_183_ = lean_apply_1(v_h__1_180_, v___x_182_);
return v___x_183_;
}
else
{
lean_object* v_head_184_; lean_object* v_tail_185_; lean_object* v___x_186_; 
lean_dec(v_h__1_180_);
v_head_184_ = lean_ctor_get(v_x_179_, 0);
lean_inc(v_head_184_);
v_tail_185_ = lean_ctor_get(v_x_179_, 1);
lean_inc(v_tail_185_);
lean_dec_ref_known(v_x_179_, 2);
v___x_186_ = lean_apply_2(v_h__2_181_, v_head_184_, v_tail_185_);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg(lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v_h__1_189_, lean_object* v_h__2_190_){
_start:
{
lean_object* v_zero_191_; uint8_t v_isZero_192_; 
v_zero_191_ = lean_unsigned_to_nat(0u);
v_isZero_192_ = lean_nat_dec_eq(v_x_187_, v_zero_191_);
if (v_isZero_192_ == 1)
{
lean_object* v___x_193_; 
lean_dec(v_h__2_190_);
v___x_193_ = lean_apply_1(v_h__1_189_, v_x_188_);
return v___x_193_;
}
else
{
lean_object* v_one_194_; lean_object* v_n_195_; lean_object* v___x_196_; 
lean_dec(v_h__1_189_);
v_one_194_ = lean_unsigned_to_nat(1u);
v_n_195_ = lean_nat_sub(v_x_187_, v_one_194_);
v___x_196_ = lean_apply_2(v_h__2_190_, v_n_195_, v_x_188_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg___boxed(lean_object* v_x_197_, lean_object* v_x_198_, lean_object* v_h__1_199_, lean_object* v_h__2_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg(v_x_197_, v_x_198_, v_h__1_199_, v_h__2_200_);
lean_dec(v_x_197_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter(lean_object* v_w_202_, lean_object* v_motive_203_, lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_h__1_206_, lean_object* v_h__2_207_){
_start:
{
lean_object* v_zero_208_; uint8_t v_isZero_209_; 
v_zero_208_ = lean_unsigned_to_nat(0u);
v_isZero_209_ = lean_nat_dec_eq(v_x_204_, v_zero_208_);
if (v_isZero_209_ == 1)
{
lean_object* v___x_210_; 
lean_dec(v_h__2_207_);
v___x_210_ = lean_apply_1(v_h__1_206_, v_x_205_);
return v___x_210_;
}
else
{
lean_object* v_one_211_; lean_object* v_n_212_; lean_object* v___x_213_; 
lean_dec(v_h__1_206_);
v_one_211_ = lean_unsigned_to_nat(1u);
v_n_212_ = lean_nat_sub(v_x_204_, v_one_211_);
v___x_213_ = lean_apply_2(v_h__2_207_, v_n_212_, v_x_205_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___boxed(lean_object* v_w_214_, lean_object* v_motive_215_, lean_object* v_x_216_, lean_object* v_x_217_, lean_object* v_h__1_218_, lean_object* v_h__2_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter(v_w_214_, v_motive_215_, v_x_216_, v_x_217_, v_h__1_218_, v_h__2_219_);
lean_dec(v_x_216_);
lean_dec(v_w_214_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg(lean_object* v_x_221_, lean_object* v_x_222_, lean_object* v_h__1_223_, lean_object* v_h__2_224_){
_start:
{
lean_object* v_zero_225_; uint8_t v_isZero_226_; 
v_zero_225_ = lean_unsigned_to_nat(0u);
v_isZero_226_ = lean_nat_dec_eq(v_x_221_, v_zero_225_);
if (v_isZero_226_ == 1)
{
lean_object* v___x_227_; 
lean_dec(v_h__2_224_);
v___x_227_ = lean_apply_1(v_h__1_223_, v_x_222_);
return v___x_227_;
}
else
{
lean_object* v_one_228_; lean_object* v_n_229_; lean_object* v___x_230_; 
lean_dec(v_h__1_223_);
v_one_228_ = lean_unsigned_to_nat(1u);
v_n_229_ = lean_nat_sub(v_x_221_, v_one_228_);
v___x_230_ = lean_apply_2(v_h__2_224_, v_n_229_, v_x_222_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg___boxed(lean_object* v_x_231_, lean_object* v_x_232_, lean_object* v_h__1_233_, lean_object* v_h__2_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg(v_x_231_, v_x_232_, v_h__1_233_, v_h__2_234_);
lean_dec(v_x_231_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter(lean_object* v_motive_236_, lean_object* v_x_237_, lean_object* v_x_238_, lean_object* v_h__1_239_, lean_object* v_h__2_240_){
_start:
{
lean_object* v_zero_241_; uint8_t v_isZero_242_; 
v_zero_241_ = lean_unsigned_to_nat(0u);
v_isZero_242_ = lean_nat_dec_eq(v_x_237_, v_zero_241_);
if (v_isZero_242_ == 1)
{
lean_object* v___x_243_; 
lean_dec(v_h__2_240_);
v___x_243_ = lean_apply_1(v_h__1_239_, v_x_238_);
return v___x_243_;
}
else
{
lean_object* v_one_244_; lean_object* v_n_245_; lean_object* v___x_246_; 
lean_dec(v_h__1_239_);
v_one_244_ = lean_unsigned_to_nat(1u);
v_n_245_ = lean_nat_sub(v_x_237_, v_one_244_);
v___x_246_ = lean_apply_2(v_h__2_240_, v_n_245_, v_x_238_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___boxed(lean_object* v_motive_247_, lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_h__1_250_, lean_object* v_h__2_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter(v_motive_247_, v_x_248_, v_x_249_, v_h__1_250_, v_h__2_251_);
lean_dec(v_x_248_);
return v_res_252_;
}
}
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
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
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_BitVec_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
