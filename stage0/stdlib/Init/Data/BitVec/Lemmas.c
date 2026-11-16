// Lean compiler output
// Module: Init.Data.BitVec.Lemmas
// Imports: import all Init.Data.BitVec.Basic import all Init.Data.BitVec.BasicAux public import Init.Data.Fin.Lemmas public import Init.Data.List.BasicAux import Init.Data.List.Lemmas import Init.Data.List.Impl import Init.Data.List.TakeDrop import Init.Data.List.Nat.TakeDrop public import Init.Data.BitVec.Basic import Init.ByCases import Init.Data.BitVec.Bootstrap import Init.Grind.Norm import Init.Data.Int.Bitwise.Lemmas import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.LemmasAux import Init.Data.Int.Pow import Init.Data.Nat.Bitwise.Lemmas import Init.Data.Nat.Div.Lemmas import Init.Data.Nat.MinMax import Init.Data.Nat.Mod import Init.Data.Nat.Simproc import Init.TacticsExtra public import Init.PropLemmas
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_BitVec_flattenList_toNatAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_BitVec_flattenList_toNatAux___closed__0 = (const lean_object*)&l_BitVec_flattenList_toNatAux___closed__0_value;
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
LEAN_EXPORT lean_object* l_BitVec_flattenList_toNatAux(lean_object* v_n_61_, lean_object* v_x_62_){
_start:
{
if (lean_obj_tag(v_x_62_) == 0)
{
lean_object* v___x_63_; 
v___x_63_ = lean_unsigned_to_nat(0u);
return v___x_63_;
}
else
{
lean_object* v_tail_64_; 
v_tail_64_ = lean_ctor_get(v_x_62_, 1);
if (lean_obj_tag(v_tail_64_) == 0)
{
lean_object* v_head_65_; 
v_head_65_ = lean_ctor_get(v_x_62_, 0);
lean_inc(v_head_65_);
lean_dec_ref_known(v_x_62_, 2);
return v_head_65_;
}
else
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v_mid_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_66_ = l_List_lengthTR___redArg(v_x_62_);
v___x_67_ = lean_unsigned_to_nat(1u);
v_mid_68_ = lean_nat_shiftr(v___x_66_, v___x_67_);
lean_dec(v___x_66_);
v___x_69_ = ((lean_object*)(l_BitVec_flattenList_toNatAux___closed__0));
lean_inc(v_mid_68_);
lean_inc_ref(v_x_62_);
v___x_70_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_x_62_, v_x_62_, v_mid_68_, v___x_69_);
v___x_71_ = l_BitVec_flattenList_toNatAux(v_n_61_, v___x_70_);
v___x_72_ = l_List_drop___redArg(v_mid_68_, v_x_62_);
lean_dec_ref_known(v_x_62_, 2);
v___x_73_ = l_List_lengthTR___redArg(v___x_72_);
v___x_74_ = lean_nat_mul(v_n_61_, v___x_73_);
lean_dec(v___x_73_);
v___x_75_ = lean_nat_shiftl(v___x_71_, v___x_74_);
lean_dec(v___x_74_);
lean_dec(v___x_71_);
v___x_76_ = l_BitVec_flattenList_toNatAux(v_n_61_, v___x_72_);
v___x_77_ = lean_nat_lor(v___x_75_, v___x_76_);
lean_dec(v___x_76_);
lean_dec(v___x_75_);
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_flattenList_toNatAux___boxed(lean_object* v_n_78_, lean_object* v_x_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_BitVec_flattenList_toNatAux(v_n_78_, v_x_79_);
lean_dec(v_n_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter___redArg(lean_object* v_x_81_, lean_object* v_h__1_82_, lean_object* v_h__2_83_, lean_object* v_h__3_84_){
_start:
{
if (lean_obj_tag(v_x_81_) == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec(v_h__3_84_);
lean_dec(v_h__2_83_);
v___x_85_ = lean_box(0);
v___x_86_ = lean_apply_1(v_h__1_82_, v___x_85_);
return v___x_86_;
}
else
{
lean_object* v_tail_87_; 
lean_dec(v_h__1_82_);
v_tail_87_ = lean_ctor_get(v_x_81_, 1);
if (lean_obj_tag(v_tail_87_) == 0)
{
lean_object* v_head_88_; lean_object* v___x_89_; 
lean_dec(v_h__3_84_);
v_head_88_ = lean_ctor_get(v_x_81_, 0);
lean_inc(v_head_88_);
lean_dec_ref_known(v_x_81_, 2);
v___x_89_ = lean_apply_1(v_h__2_83_, v_head_88_);
return v___x_89_;
}
else
{
lean_object* v_head_90_; lean_object* v_head_91_; lean_object* v_tail_92_; lean_object* v___x_93_; 
lean_inc_ref(v_tail_87_);
lean_dec(v_h__2_83_);
v_head_90_ = lean_ctor_get(v_x_81_, 0);
lean_inc(v_head_90_);
lean_dec_ref_known(v_x_81_, 2);
v_head_91_ = lean_ctor_get(v_tail_87_, 0);
lean_inc(v_head_91_);
v_tail_92_ = lean_ctor_get(v_tail_87_, 1);
lean_inc(v_tail_92_);
lean_dec_ref_known(v_tail_87_, 2);
v___x_93_ = lean_apply_3(v_h__3_84_, v_head_90_, v_head_91_, v_tail_92_);
return v___x_93_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter(lean_object* v_n_94_, lean_object* v_motive_95_, lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_, lean_object* v_h__3_99_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v_h__3_99_);
lean_dec(v_h__2_98_);
v___x_100_ = lean_box(0);
v___x_101_ = lean_apply_1(v_h__1_97_, v___x_100_);
return v___x_101_;
}
else
{
lean_object* v_tail_102_; 
lean_dec(v_h__1_97_);
v_tail_102_ = lean_ctor_get(v_x_96_, 1);
if (lean_obj_tag(v_tail_102_) == 0)
{
lean_object* v_head_103_; lean_object* v___x_104_; 
lean_dec(v_h__3_99_);
v_head_103_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_head_103_);
lean_dec_ref_known(v_x_96_, 2);
v___x_104_ = lean_apply_1(v_h__2_98_, v_head_103_);
return v___x_104_;
}
else
{
lean_object* v_head_105_; lean_object* v_head_106_; lean_object* v_tail_107_; lean_object* v___x_108_; 
lean_inc_ref(v_tail_102_);
lean_dec(v_h__2_98_);
v_head_105_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_head_105_);
lean_dec_ref_known(v_x_96_, 2);
v_head_106_ = lean_ctor_get(v_tail_102_, 0);
lean_inc(v_head_106_);
v_tail_107_ = lean_ctor_get(v_tail_102_, 1);
lean_inc(v_tail_107_);
lean_dec_ref_known(v_tail_102_, 2);
v___x_108_ = lean_apply_3(v_h__3_99_, v_head_105_, v_head_106_, v_tail_107_);
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter___boxed(lean_object* v_n_109_, lean_object* v_motive_110_, lean_object* v_x_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_, lean_object* v_h__3_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter(v_n_109_, v_motive_110_, v_x_111_, v_h__1_112_, v_h__2_113_, v_h__3_114_);
lean_dec(v_n_109_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_BitVec_flattenListFast(lean_object* v_n_116_, lean_object* v_xs_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = l_List_lengthTR___redArg(v_xs_117_);
v___x_119_ = lean_nat_mul(v_n_116_, v___x_118_);
lean_dec(v___x_118_);
v___x_120_ = l_BitVec_flattenList_toNatAux(v_n_116_, v_xs_117_);
v___x_121_ = l_BitVec_ofNat(v___x_119_, v___x_120_);
lean_dec(v___x_120_);
lean_dec(v___x_119_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_BitVec_flattenListFast___boxed(lean_object* v_n_122_, lean_object* v_xs_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_BitVec_flattenListFast(v_n_122_, v_xs_123_);
lean_dec(v_n_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg(uint8_t v_x_125_, uint8_t v_x_126_, lean_object* v_h__1_127_, lean_object* v_h__2_128_, lean_object* v_h__3_129_, lean_object* v_h__4_130_){
_start:
{
if (v_x_125_ == 0)
{
lean_dec(v_h__4_130_);
lean_dec(v_h__3_129_);
if (v_x_126_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
lean_dec(v_h__2_128_);
v___x_131_ = lean_box(0);
v___x_132_ = lean_apply_1(v_h__1_127_, v___x_131_);
return v___x_132_;
}
else
{
lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec(v_h__1_127_);
v___x_133_ = lean_box(0);
v___x_134_ = lean_apply_1(v_h__2_128_, v___x_133_);
return v___x_134_;
}
}
else
{
lean_dec(v_h__2_128_);
lean_dec(v_h__1_127_);
if (v_x_126_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec(v_h__4_130_);
v___x_135_ = lean_box(0);
v___x_136_ = lean_apply_1(v_h__3_129_, v___x_135_);
return v___x_136_;
}
else
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec(v_h__3_129_);
v___x_137_ = lean_box(0);
v___x_138_ = lean_apply_1(v_h__4_130_, v___x_137_);
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg___boxed(lean_object* v_x_139_, lean_object* v_x_140_, lean_object* v_h__1_141_, lean_object* v_h__2_142_, lean_object* v_h__3_143_, lean_object* v_h__4_144_){
_start:
{
uint8_t v_x_46__boxed_145_; uint8_t v_x_47__boxed_146_; lean_object* v_res_147_; 
v_x_46__boxed_145_ = lean_unbox(v_x_139_);
v_x_47__boxed_146_ = lean_unbox(v_x_140_);
v_res_147_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg(v_x_46__boxed_145_, v_x_47__boxed_146_, v_h__1_141_, v_h__2_142_, v_h__3_143_, v_h__4_144_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter(lean_object* v_motive_148_, uint8_t v_x_149_, uint8_t v_x_150_, lean_object* v_h__1_151_, lean_object* v_h__2_152_, lean_object* v_h__3_153_, lean_object* v_h__4_154_){
_start:
{
if (v_x_149_ == 0)
{
lean_dec(v_h__4_154_);
lean_dec(v_h__3_153_);
if (v_x_150_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec(v_h__2_152_);
v___x_155_ = lean_box(0);
v___x_156_ = lean_apply_1(v_h__1_151_, v___x_155_);
return v___x_156_;
}
else
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_h__1_151_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_apply_1(v_h__2_152_, v___x_157_);
return v___x_158_;
}
}
else
{
lean_dec(v_h__2_152_);
lean_dec(v_h__1_151_);
if (v_x_150_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
lean_dec(v_h__4_154_);
v___x_159_ = lean_box(0);
v___x_160_ = lean_apply_1(v_h__3_153_, v___x_159_);
return v___x_160_;
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v_h__3_153_);
v___x_161_ = lean_box(0);
v___x_162_ = lean_apply_1(v_h__4_154_, v___x_161_);
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___boxed(lean_object* v_motive_163_, lean_object* v_x_164_, lean_object* v_x_165_, lean_object* v_h__1_166_, lean_object* v_h__2_167_, lean_object* v_h__3_168_, lean_object* v_h__4_169_){
_start:
{
uint8_t v_x_68__boxed_170_; uint8_t v_x_69__boxed_171_; lean_object* v_res_172_; 
v_x_68__boxed_170_ = lean_unbox(v_x_164_);
v_x_69__boxed_171_ = lean_unbox(v_x_165_);
v_res_172_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter(v_motive_163_, v_x_68__boxed_170_, v_x_69__boxed_171_, v_h__1_166_, v_h__2_167_, v_h__3_168_, v_h__4_169_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_ofBoolListBE_match__1_splitter___redArg(lean_object* v_x_173_, lean_object* v_h__1_174_, lean_object* v_h__2_175_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_dec(v_h__2_175_);
v___x_176_ = lean_box(0);
v___x_177_ = lean_apply_1(v_h__1_174_, v___x_176_);
return v___x_177_;
}
else
{
lean_object* v_head_178_; lean_object* v_tail_179_; lean_object* v___x_180_; 
lean_dec(v_h__1_174_);
v_head_178_ = lean_ctor_get(v_x_173_, 0);
lean_inc(v_head_178_);
v_tail_179_ = lean_ctor_get(v_x_173_, 1);
lean_inc(v_tail_179_);
lean_dec_ref_known(v_x_173_, 2);
v___x_180_ = lean_apply_2(v_h__2_175_, v_head_178_, v_tail_179_);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_ofBoolListBE_match__1_splitter(lean_object* v_motive_181_, lean_object* v_x_182_, lean_object* v_h__1_183_, lean_object* v_h__2_184_){
_start:
{
if (lean_obj_tag(v_x_182_) == 0)
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec(v_h__2_184_);
v___x_185_ = lean_box(0);
v___x_186_ = lean_apply_1(v_h__1_183_, v___x_185_);
return v___x_186_;
}
else
{
lean_object* v_head_187_; lean_object* v_tail_188_; lean_object* v___x_189_; 
lean_dec(v_h__1_183_);
v_head_187_ = lean_ctor_get(v_x_182_, 0);
lean_inc(v_head_187_);
v_tail_188_ = lean_ctor_get(v_x_182_, 1);
lean_inc(v_tail_188_);
lean_dec_ref_known(v_x_182_, 2);
v___x_189_ = lean_apply_2(v_h__2_184_, v_head_187_, v_tail_188_);
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg(lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_h__1_192_, lean_object* v_h__2_193_){
_start:
{
lean_object* v_zero_194_; uint8_t v_isZero_195_; 
v_zero_194_ = lean_unsigned_to_nat(0u);
v_isZero_195_ = lean_nat_dec_eq(v_x_190_, v_zero_194_);
if (v_isZero_195_ == 1)
{
lean_object* v___x_196_; 
lean_dec(v_h__2_193_);
v___x_196_ = lean_apply_1(v_h__1_192_, v_x_191_);
return v___x_196_;
}
else
{
lean_object* v_one_197_; lean_object* v_n_198_; lean_object* v___x_199_; 
lean_dec(v_h__1_192_);
v_one_197_ = lean_unsigned_to_nat(1u);
v_n_198_ = lean_nat_sub(v_x_190_, v_one_197_);
v___x_199_ = lean_apply_2(v_h__2_193_, v_n_198_, v_x_191_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg___boxed(lean_object* v_x_200_, lean_object* v_x_201_, lean_object* v_h__1_202_, lean_object* v_h__2_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg(v_x_200_, v_x_201_, v_h__1_202_, v_h__2_203_);
lean_dec(v_x_200_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter(lean_object* v_w_205_, lean_object* v_motive_206_, lean_object* v_x_207_, lean_object* v_x_208_, lean_object* v_h__1_209_, lean_object* v_h__2_210_){
_start:
{
lean_object* v_zero_211_; uint8_t v_isZero_212_; 
v_zero_211_ = lean_unsigned_to_nat(0u);
v_isZero_212_ = lean_nat_dec_eq(v_x_207_, v_zero_211_);
if (v_isZero_212_ == 1)
{
lean_object* v___x_213_; 
lean_dec(v_h__2_210_);
v___x_213_ = lean_apply_1(v_h__1_209_, v_x_208_);
return v___x_213_;
}
else
{
lean_object* v_one_214_; lean_object* v_n_215_; lean_object* v___x_216_; 
lean_dec(v_h__1_209_);
v_one_214_ = lean_unsigned_to_nat(1u);
v_n_215_ = lean_nat_sub(v_x_207_, v_one_214_);
v___x_216_ = lean_apply_2(v_h__2_210_, v_n_215_, v_x_208_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___boxed(lean_object* v_w_217_, lean_object* v_motive_218_, lean_object* v_x_219_, lean_object* v_x_220_, lean_object* v_h__1_221_, lean_object* v_h__2_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter(v_w_217_, v_motive_218_, v_x_219_, v_x_220_, v_h__1_221_, v_h__2_222_);
lean_dec(v_x_219_);
lean_dec(v_w_217_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg(lean_object* v_x_224_, lean_object* v_x_225_, lean_object* v_h__1_226_, lean_object* v_h__2_227_){
_start:
{
lean_object* v_zero_228_; uint8_t v_isZero_229_; 
v_zero_228_ = lean_unsigned_to_nat(0u);
v_isZero_229_ = lean_nat_dec_eq(v_x_224_, v_zero_228_);
if (v_isZero_229_ == 1)
{
lean_object* v___x_230_; 
lean_dec(v_h__2_227_);
v___x_230_ = lean_apply_1(v_h__1_226_, v_x_225_);
return v___x_230_;
}
else
{
lean_object* v_one_231_; lean_object* v_n_232_; lean_object* v___x_233_; 
lean_dec(v_h__1_226_);
v_one_231_ = lean_unsigned_to_nat(1u);
v_n_232_ = lean_nat_sub(v_x_224_, v_one_231_);
v___x_233_ = lean_apply_2(v_h__2_227_, v_n_232_, v_x_225_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg___boxed(lean_object* v_x_234_, lean_object* v_x_235_, lean_object* v_h__1_236_, lean_object* v_h__2_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg(v_x_234_, v_x_235_, v_h__1_236_, v_h__2_237_);
lean_dec(v_x_234_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter(lean_object* v_motive_239_, lean_object* v_x_240_, lean_object* v_x_241_, lean_object* v_h__1_242_, lean_object* v_h__2_243_){
_start:
{
lean_object* v_zero_244_; uint8_t v_isZero_245_; 
v_zero_244_ = lean_unsigned_to_nat(0u);
v_isZero_245_ = lean_nat_dec_eq(v_x_240_, v_zero_244_);
if (v_isZero_245_ == 1)
{
lean_object* v___x_246_; 
lean_dec(v_h__2_243_);
v___x_246_ = lean_apply_1(v_h__1_242_, v_x_241_);
return v___x_246_;
}
else
{
lean_object* v_one_247_; lean_object* v_n_248_; lean_object* v___x_249_; 
lean_dec(v_h__1_242_);
v_one_247_ = lean_unsigned_to_nat(1u);
v_n_248_ = lean_nat_sub(v_x_240_, v_one_247_);
v___x_249_ = lean_apply_2(v_h__2_243_, v_n_248_, v_x_241_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___boxed(lean_object* v_motive_250_, lean_object* v_x_251_, lean_object* v_x_252_, lean_object* v_h__1_253_, lean_object* v_h__2_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter(v_motive_250_, v_x_251_, v_x_252_, v_h__1_253_, v_h__2_254_);
lean_dec(v_x_251_);
return v_res_255_;
}
}
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Norm(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = runtime_initialize_Init_Data_List_Impl(builtin);
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
res = runtime_initialize_Init_Grind_Norm(builtin);
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
res = runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
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
res = runtime_initialize_Init_PropLemmas(builtin);
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
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Grind_Norm(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Bitwise_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
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
res = initialize_Init_Data_List_Impl(builtin);
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
res = initialize_Init_Grind_Norm(builtin);
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
res = initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
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
res = initialize_Init_PropLemmas(builtin);
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
