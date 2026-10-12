// Lean compiler output
// Module: Init.Data.BitVec.Lemmas
// Imports: import all Init.Data.BitVec.Basic import all Init.Data.BitVec.BasicAux public import Init.Data.Fin.Lemmas public import Init.Data.List.BasicAux import Init.Data.List.Lemmas import Init.Data.List.TakeDrop import Init.Data.List.Nat.TakeDrop public import Init.Data.BitVec.Basic import Init.ByCases import Init.Data.BitVec.Bootstrap import Init.Grind.Norm import Init.Data.Int.Bitwise.Lemmas import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.LemmasAux import Init.Data.Int.Pow import Init.Data.Nat.Div.Lemmas import Init.Data.Nat.MinMax import Init.Data.Nat.Mod import Init.Data.Nat.Simproc import Init.TacticsExtra public import Init.PropLemmas
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
static lean_once_cell_t l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_BitVec_flattenList_toNatAux(lean_object* v_n_35_, lean_object* v_x_36_){
_start:
{
if (lean_obj_tag(v_x_36_) == 0)
{
lean_object* v___x_37_; 
v___x_37_ = lean_unsigned_to_nat(0u);
return v___x_37_;
}
else
{
lean_object* v_tail_38_; 
v_tail_38_ = lean_ctor_get(v_x_36_, 1);
if (lean_obj_tag(v_tail_38_) == 0)
{
lean_object* v_head_39_; 
v_head_39_ = lean_ctor_get(v_x_36_, 0);
lean_inc(v_head_39_);
lean_dec_ref_known(v_x_36_, 2);
return v_head_39_;
}
else
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v_mid_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_40_ = l_List_lengthTR___redArg(v_x_36_);
v___x_41_ = lean_unsigned_to_nat(1u);
v_mid_42_ = lean_nat_shiftr(v___x_40_, v___x_41_);
lean_dec(v___x_40_);
lean_inc_ref(v_x_36_);
v___x_43_ = l_List_take___redArg(v_mid_42_, v_x_36_);
v___x_44_ = l_BitVec_flattenList_toNatAux(v_n_35_, v___x_43_);
v___x_45_ = l_List_drop___redArg(v_mid_42_, v_x_36_);
lean_dec_ref_known(v_x_36_, 2);
v___x_46_ = l_List_lengthTR___redArg(v___x_45_);
v___x_47_ = lean_nat_mul(v_n_35_, v___x_46_);
lean_dec(v___x_46_);
v___x_48_ = lean_nat_shiftl(v___x_44_, v___x_47_);
lean_dec(v___x_47_);
lean_dec(v___x_44_);
v___x_49_ = l_BitVec_flattenList_toNatAux(v_n_35_, v___x_45_);
v___x_50_ = lean_nat_lor(v___x_48_, v___x_49_);
lean_dec(v___x_49_);
lean_dec(v___x_48_);
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l_BitVec_flattenList_toNatAux___boxed(lean_object* v_n_51_, lean_object* v_x_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_BitVec_flattenList_toNatAux(v_n_51_, v_x_52_);
lean_dec(v_n_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter___redArg(lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_, lean_object* v_h__3_57_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; 
lean_dec(v_h__3_57_);
lean_dec(v_h__2_56_);
v___x_58_ = lean_box(0);
v___x_59_ = lean_apply_1(v_h__1_55_, v___x_58_);
return v___x_59_;
}
else
{
lean_object* v_tail_60_; 
lean_dec(v_h__1_55_);
v_tail_60_ = lean_ctor_get(v_x_54_, 1);
if (lean_obj_tag(v_tail_60_) == 0)
{
lean_object* v_head_61_; lean_object* v___x_62_; 
lean_dec(v_h__3_57_);
v_head_61_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_head_61_);
lean_dec_ref_known(v_x_54_, 2);
v___x_62_ = lean_apply_1(v_h__2_56_, v_head_61_);
return v___x_62_;
}
else
{
lean_object* v_head_63_; lean_object* v_head_64_; lean_object* v_tail_65_; lean_object* v___x_66_; 
lean_inc_ref(v_tail_60_);
lean_dec(v_h__2_56_);
v_head_63_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_head_63_);
lean_dec_ref_known(v_x_54_, 2);
v_head_64_ = lean_ctor_get(v_tail_60_, 0);
lean_inc(v_head_64_);
v_tail_65_ = lean_ctor_get(v_tail_60_, 1);
lean_inc(v_tail_65_);
lean_dec_ref_known(v_tail_60_, 2);
v___x_66_ = lean_apply_3(v_h__3_57_, v_head_63_, v_head_64_, v_tail_65_);
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter(lean_object* v_n_67_, lean_object* v_motive_68_, lean_object* v_x_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_, lean_object* v_h__3_72_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec(v_h__3_72_);
lean_dec(v_h__2_71_);
v___x_73_ = lean_box(0);
v___x_74_ = lean_apply_1(v_h__1_70_, v___x_73_);
return v___x_74_;
}
else
{
lean_object* v_tail_75_; 
lean_dec(v_h__1_70_);
v_tail_75_ = lean_ctor_get(v_x_69_, 1);
if (lean_obj_tag(v_tail_75_) == 0)
{
lean_object* v_head_76_; lean_object* v___x_77_; 
lean_dec(v_h__3_72_);
v_head_76_ = lean_ctor_get(v_x_69_, 0);
lean_inc(v_head_76_);
lean_dec_ref_known(v_x_69_, 2);
v___x_77_ = lean_apply_1(v_h__2_71_, v_head_76_);
return v___x_77_;
}
else
{
lean_object* v_head_78_; lean_object* v_head_79_; lean_object* v_tail_80_; lean_object* v___x_81_; 
lean_inc_ref(v_tail_75_);
lean_dec(v_h__2_71_);
v_head_78_ = lean_ctor_get(v_x_69_, 0);
lean_inc(v_head_78_);
lean_dec_ref_known(v_x_69_, 2);
v_head_79_ = lean_ctor_get(v_tail_75_, 0);
lean_inc(v_head_79_);
v_tail_80_ = lean_ctor_get(v_tail_75_, 1);
lean_inc(v_tail_80_);
lean_dec_ref_known(v_tail_75_, 2);
v___x_81_ = lean_apply_3(v_h__3_72_, v_head_78_, v_head_79_, v_tail_80_);
return v___x_81_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter___boxed(lean_object* v_n_82_, lean_object* v_motive_83_, lean_object* v_x_84_, lean_object* v_h__1_85_, lean_object* v_h__2_86_, lean_object* v_h__3_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_flattenList_toNatAux_match__1_splitter(v_n_82_, v_motive_83_, v_x_84_, v_h__1_85_, v_h__2_86_, v_h__3_87_);
lean_dec(v_n_82_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_BitVec_flattenListFast(lean_object* v_n_89_, lean_object* v_xs_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = l_List_lengthTR___redArg(v_xs_90_);
v___x_92_ = lean_nat_mul(v_n_89_, v___x_91_);
lean_dec(v___x_91_);
v___x_93_ = l_BitVec_flattenList_toNatAux(v_n_89_, v_xs_90_);
v___x_94_ = l_BitVec_ofNat(v___x_92_, v___x_93_);
lean_dec(v___x_93_);
lean_dec(v___x_92_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_BitVec_flattenListFast___boxed(lean_object* v_n_95_, lean_object* v_xs_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_BitVec_flattenListFast(v_n_95_, v_xs_96_);
lean_dec(v_n_95_);
return v_res_97_;
}
}
lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg(uint8_t v_x_98_, uint8_t v_x_99_, lean_object* v_h__1_100_, lean_object* v_h__2_101_, lean_object* v_h__3_102_, lean_object* v_h__4_103_){
_start:
{
if (v_x_98_ == 0)
{
lean_dec(v_h__4_103_);
lean_dec(v_h__3_102_);
if (v_x_99_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v_h__2_101_);
v___x_104_ = lean_box(0);
v___x_105_ = lean_apply_1(v_h__1_100_, v___x_104_);
return v___x_105_;
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; 
lean_dec(v_h__1_100_);
v___x_106_ = lean_box(0);
v___x_107_ = lean_apply_1(v_h__2_101_, v___x_106_);
return v___x_107_;
}
}
else
{
lean_dec(v_h__2_101_);
lean_dec(v_h__1_100_);
if (v_x_99_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec(v_h__4_103_);
v___x_108_ = lean_box(0);
v___x_109_ = lean_apply_1(v_h__3_102_, v___x_108_);
return v___x_109_;
}
else
{
lean_object* v___x_110_; lean_object* v___x_111_; 
lean_dec(v_h__3_102_);
v___x_110_ = lean_box(0);
v___x_111_ = lean_apply_1(v_h__4_103_, v___x_110_);
return v___x_111_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_98_ = stack[0].m_num;
uint8_t v_x_99_ = stack[1].m_num;
lean_object* v_h__1_100_ = stack[2].m_obj;
lean_object* v_h__2_101_ = stack[3].m_obj;
lean_object* v_h__3_102_ = stack[4].m_obj;
lean_object* v_h__4_103_ = stack[5].m_obj;
lean_object* v_res_112_;
v_res_112_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg(v_x_98_, v_x_99_, v_h__1_100_, v_h__2_101_, v_h__3_102_, v_h__4_103_);
stack->m_obj
 = v_res_112_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg___boxed(lean_object* v_x_113_, lean_object* v_x_114_, lean_object* v_h__1_115_, lean_object* v_h__2_116_, lean_object* v_h__3_117_, lean_object* v_h__4_118_){
_start:
{
uint8_t v_x_46__boxed_119_; uint8_t v_x_47__boxed_120_; lean_object* v_res_121_; 
v_x_46__boxed_119_ = lean_unbox(v_x_113_);
v_x_47__boxed_120_ = lean_unbox(v_x_114_);
v_res_121_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg(v_x_46__boxed_119_, v_x_47__boxed_120_, v_h__1_115_, v_h__2_116_, v_h__3_117_, v_h__4_118_);
return v_res_121_;
}
}
lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter(lean_object* v_motive_122_, uint8_t v_x_123_, uint8_t v_x_124_, lean_object* v_h__1_125_, lean_object* v_h__2_126_, lean_object* v_h__3_127_, lean_object* v_h__4_128_){
_start:
{
if (v_x_123_ == 0)
{
lean_dec(v_h__4_128_);
lean_dec(v_h__3_127_);
if (v_x_124_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec(v_h__2_126_);
v___x_129_ = lean_box(0);
v___x_130_ = lean_apply_1(v_h__1_125_, v___x_129_);
return v___x_130_;
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; 
lean_dec(v_h__1_125_);
v___x_131_ = lean_box(0);
v___x_132_ = lean_apply_1(v_h__2_126_, v___x_131_);
return v___x_132_;
}
}
else
{
lean_dec(v_h__2_126_);
lean_dec(v_h__1_125_);
if (v_x_124_ == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec(v_h__4_128_);
v___x_133_ = lean_box(0);
v___x_134_ = lean_apply_1(v_h__3_127_, v___x_133_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec(v_h__3_127_);
v___x_135_ = lean_box(0);
v___x_136_ = lean_apply_1(v_h__4_128_, v___x_135_);
return v___x_136_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_123_ = stack[1].m_num;
uint8_t v_x_124_ = stack[2].m_num;
lean_object* v_h__1_125_ = stack[3].m_obj;
lean_object* v_h__2_126_ = stack[4].m_obj;
lean_object* v_h__3_127_ = stack[5].m_obj;
lean_object* v_h__4_128_ = stack[6].m_obj;
lean_object* v_res_137_;
v_res_137_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter(lean_box(0), v_x_123_, v_x_124_, v_h__1_125_, v_h__2_126_, v_h__3_127_, v_h__4_128_);
stack->m_obj
 = v_res_137_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___boxed(lean_object* v_motive_138_, lean_object* v_x_139_, lean_object* v_x_140_, lean_object* v_h__1_141_, lean_object* v_h__2_142_, lean_object* v_h__3_143_, lean_object* v_h__4_144_){
_start:
{
uint8_t v_x_80__boxed_145_; uint8_t v_x_81__boxed_146_; lean_object* v_res_147_; 
v_x_80__boxed_145_ = lean_unbox(v_x_139_);
v_x_81__boxed_146_ = lean_unbox(v_x_140_);
v_res_147_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter(v_motive_138_, v_x_80__boxed_145_, v_x_81__boxed_146_, v_h__1_141_, v_h__2_142_, v_h__3_143_, v_h__4_144_);
return v_res_147_;
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
lean_object* runtime_initialize_Init_Grind_Norm(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
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
