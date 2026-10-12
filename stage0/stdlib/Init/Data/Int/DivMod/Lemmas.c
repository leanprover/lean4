// Lean compiler output
// Module: Init.Data.Int.DivMod.Lemmas
// Imports: import Init.TacticsExtra public import Init.Data.Int.DivMod.Basic public import Init.Data.Nat.Div.Basic public import Init.NotationExtra import Init.ByCases import Init.Data.Bool import Init.Data.Nat.Div.Lemmas import Init.Data.Nat.Lemmas import Init.Omega import Init.RCases
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t l_Int_decidableDvd___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_decidableDvd___closed__0;
LEAN_EXPORT uint8_t l_Int_decidableDvd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_decidableDvd___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Int_decidableDvd___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
uint8_t l_Int_decidableDvd(lean_object* v_a_3_, lean_object* v_b_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_5_ = lean_int_emod(v_b_4_, v_a_3_);
v___x_6_ = lean_obj_once(&l_Int_decidableDvd___closed__0, &l_Int_decidableDvd___closed__0_once, _init_l_Int_decidableDvd___closed__0);
v___x_7_ = lean_int_dec_eq(v___x_5_, v___x_6_);
lean_dec(v___x_5_);
return v___x_7_;
}
}
LEAN_EXPORT void l_Int_decidableDvd_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3_ = stack[0].m_obj;
lean_object* v_b_4_ = stack[1].m_obj;
uint8_t v_res_8_;
v_res_8_ = l_Int_decidableDvd(v_a_3_, v_b_4_);
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l_Int_decidableDvd___boxed(lean_object* v_a_9_, lean_object* v_b_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Int_decidableDvd(v_a_9_, v_b_10_);
lean_dec(v_b_10_);
lean_dec(v_a_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
static lean_object* _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_13_; lean_object* v_intZero_14_; 
v_natZero_13_ = lean_unsigned_to_nat(0u);
v_intZero_14_ = lean_nat_to_int(v_natZero_13_);
return v_intZero_14_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg(lean_object* v_x_15_, lean_object* v_x_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_, lean_object* v_h__3_19_, lean_object* v_h__4_20_, lean_object* v_h__5_21_, lean_object* v_h__6_22_){
_start:
{
lean_object* v_natZero_23_; lean_object* v_intZero_24_; uint8_t v_isNeg_25_; 
v_natZero_23_ = lean_unsigned_to_nat(0u);
v_intZero_24_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0);
v_isNeg_25_ = lean_int_dec_lt(v_x_15_, v_intZero_24_);
if (v_isNeg_25_ == 0)
{
lean_object* v_a_26_; uint8_t v_isZero_27_; 
lean_dec(v_h__6_22_);
lean_dec(v_h__5_21_);
lean_dec(v_h__4_20_);
v_a_26_ = lean_nat_abs(v_x_15_);
v_isZero_27_ = lean_nat_dec_eq(v_a_26_, v_natZero_23_);
if (v_isZero_27_ == 1)
{
lean_object* v___x_28_; 
lean_dec(v_a_26_);
lean_dec(v_h__3_19_);
lean_dec(v_h__2_18_);
v___x_28_ = lean_apply_1(v_h__1_17_, v_x_16_);
return v___x_28_;
}
else
{
uint8_t v_isNeg_29_; 
lean_dec(v_h__1_17_);
v_isNeg_29_ = lean_int_dec_lt(v_x_16_, v_intZero_24_);
if (v_isNeg_29_ == 0)
{
lean_object* v_a_30_; lean_object* v___x_31_; 
lean_dec(v_h__3_19_);
v_a_30_ = lean_nat_abs(v_x_16_);
lean_dec(v_x_16_);
v___x_31_ = lean_apply_3(v_h__2_18_, v_a_26_, v_a_30_, lean_box(0));
return v___x_31_;
}
else
{
lean_object* v_one_32_; lean_object* v_n_33_; lean_object* v_abs_34_; lean_object* v_a_35_; lean_object* v___x_36_; 
lean_dec(v_h__2_18_);
v_one_32_ = lean_unsigned_to_nat(1u);
v_n_33_ = lean_nat_sub(v_a_26_, v_one_32_);
lean_dec(v_a_26_);
v_abs_34_ = lean_nat_abs(v_x_16_);
lean_dec(v_x_16_);
v_a_35_ = lean_nat_sub(v_abs_34_, v_one_32_);
lean_dec(v_abs_34_);
v___x_36_ = lean_apply_2(v_h__3_19_, v_n_33_, v_a_35_);
return v___x_36_;
}
}
}
else
{
lean_object* v_abs_37_; lean_object* v_one_38_; lean_object* v_a_39_; uint8_t v_isNeg_40_; 
lean_dec(v_h__3_19_);
lean_dec(v_h__2_18_);
lean_dec(v_h__1_17_);
v_abs_37_ = lean_nat_abs(v_x_15_);
v_one_38_ = lean_unsigned_to_nat(1u);
v_a_39_ = lean_nat_sub(v_abs_37_, v_one_38_);
lean_dec(v_abs_37_);
v_isNeg_40_ = lean_int_dec_lt(v_x_16_, v_intZero_24_);
if (v_isNeg_40_ == 0)
{
lean_object* v_a_41_; uint8_t v_isZero_42_; 
lean_dec(v_h__6_22_);
v_a_41_ = lean_nat_abs(v_x_16_);
lean_dec(v_x_16_);
v_isZero_42_ = lean_nat_dec_eq(v_a_41_, v_natZero_23_);
if (v_isZero_42_ == 1)
{
lean_object* v___x_43_; 
lean_dec(v_a_41_);
lean_dec(v_h__5_21_);
v___x_43_ = lean_apply_1(v_h__4_20_, v_a_39_);
return v___x_43_;
}
else
{
lean_object* v_n_44_; lean_object* v___x_45_; 
lean_dec(v_h__4_20_);
v_n_44_ = lean_nat_sub(v_a_41_, v_one_38_);
lean_dec(v_a_41_);
v___x_45_ = lean_apply_2(v_h__5_21_, v_a_39_, v_n_44_);
return v___x_45_;
}
}
else
{
lean_object* v_abs_46_; lean_object* v_a_47_; lean_object* v___x_48_; 
lean_dec(v_h__5_21_);
lean_dec(v_h__4_20_);
v_abs_46_ = lean_nat_abs(v_x_16_);
lean_dec(v_x_16_);
v_a_47_ = lean_nat_sub(v_abs_46_, v_one_38_);
lean_dec(v_abs_46_);
v___x_48_ = lean_apply_2(v_h__6_22_, v_a_39_, v_a_47_);
return v___x_48_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___boxed(lean_object* v_x_49_, lean_object* v_x_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_, lean_object* v_h__3_53_, lean_object* v_h__4_54_, lean_object* v_h__5_55_, lean_object* v_h__6_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg(v_x_49_, v_x_50_, v_h__1_51_, v_h__2_52_, v_h__3_53_, v_h__4_54_, v_h__5_55_, v_h__6_56_);
lean_dec(v_x_49_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter(lean_object* v_motive_58_, lean_object* v_x_59_, lean_object* v_x_60_, lean_object* v_h__1_61_, lean_object* v_h__2_62_, lean_object* v_h__3_63_, lean_object* v_h__4_64_, lean_object* v_h__5_65_, lean_object* v_h__6_66_){
_start:
{
lean_object* v_natZero_67_; lean_object* v_intZero_68_; uint8_t v_isNeg_69_; 
v_natZero_67_ = lean_unsigned_to_nat(0u);
v_intZero_68_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0);
v_isNeg_69_ = lean_int_dec_lt(v_x_59_, v_intZero_68_);
if (v_isNeg_69_ == 0)
{
lean_object* v_a_70_; uint8_t v_isZero_71_; 
lean_dec(v_h__6_66_);
lean_dec(v_h__5_65_);
lean_dec(v_h__4_64_);
v_a_70_ = lean_nat_abs(v_x_59_);
v_isZero_71_ = lean_nat_dec_eq(v_a_70_, v_natZero_67_);
if (v_isZero_71_ == 1)
{
lean_object* v___x_72_; 
lean_dec(v_a_70_);
lean_dec(v_h__3_63_);
lean_dec(v_h__2_62_);
v___x_72_ = lean_apply_1(v_h__1_61_, v_x_60_);
return v___x_72_;
}
else
{
uint8_t v_isNeg_73_; 
lean_dec(v_h__1_61_);
v_isNeg_73_ = lean_int_dec_lt(v_x_60_, v_intZero_68_);
if (v_isNeg_73_ == 0)
{
lean_object* v_a_74_; lean_object* v___x_75_; 
lean_dec(v_h__3_63_);
v_a_74_ = lean_nat_abs(v_x_60_);
lean_dec(v_x_60_);
v___x_75_ = lean_apply_3(v_h__2_62_, v_a_70_, v_a_74_, lean_box(0));
return v___x_75_;
}
else
{
lean_object* v_one_76_; lean_object* v_n_77_; lean_object* v_abs_78_; lean_object* v_a_79_; lean_object* v___x_80_; 
lean_dec(v_h__2_62_);
v_one_76_ = lean_unsigned_to_nat(1u);
v_n_77_ = lean_nat_sub(v_a_70_, v_one_76_);
lean_dec(v_a_70_);
v_abs_78_ = lean_nat_abs(v_x_60_);
lean_dec(v_x_60_);
v_a_79_ = lean_nat_sub(v_abs_78_, v_one_76_);
lean_dec(v_abs_78_);
v___x_80_ = lean_apply_2(v_h__3_63_, v_n_77_, v_a_79_);
return v___x_80_;
}
}
}
else
{
lean_object* v_abs_81_; lean_object* v_one_82_; lean_object* v_a_83_; uint8_t v_isNeg_84_; 
lean_dec(v_h__3_63_);
lean_dec(v_h__2_62_);
lean_dec(v_h__1_61_);
v_abs_81_ = lean_nat_abs(v_x_59_);
v_one_82_ = lean_unsigned_to_nat(1u);
v_a_83_ = lean_nat_sub(v_abs_81_, v_one_82_);
lean_dec(v_abs_81_);
v_isNeg_84_ = lean_int_dec_lt(v_x_60_, v_intZero_68_);
if (v_isNeg_84_ == 0)
{
lean_object* v_a_85_; uint8_t v_isZero_86_; 
lean_dec(v_h__6_66_);
v_a_85_ = lean_nat_abs(v_x_60_);
lean_dec(v_x_60_);
v_isZero_86_ = lean_nat_dec_eq(v_a_85_, v_natZero_67_);
if (v_isZero_86_ == 1)
{
lean_object* v___x_87_; 
lean_dec(v_a_85_);
lean_dec(v_h__5_65_);
v___x_87_ = lean_apply_1(v_h__4_64_, v_a_83_);
return v___x_87_;
}
else
{
lean_object* v_n_88_; lean_object* v___x_89_; 
lean_dec(v_h__4_64_);
v_n_88_ = lean_nat_sub(v_a_85_, v_one_82_);
lean_dec(v_a_85_);
v___x_89_ = lean_apply_2(v_h__5_65_, v_a_83_, v_n_88_);
return v___x_89_;
}
}
else
{
lean_object* v_abs_90_; lean_object* v_a_91_; lean_object* v___x_92_; 
lean_dec(v_h__5_65_);
lean_dec(v_h__4_64_);
v_abs_90_ = lean_nat_abs(v_x_60_);
lean_dec(v_x_60_);
v_a_91_ = lean_nat_sub(v_abs_90_, v_one_82_);
lean_dec(v_abs_90_);
v___x_92_ = lean_apply_2(v_h__6_66_, v_a_83_, v_a_91_);
return v___x_92_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___boxed(lean_object* v_motive_93_, lean_object* v_x_94_, lean_object* v_x_95_, lean_object* v_h__1_96_, lean_object* v_h__2_97_, lean_object* v_h__3_98_, lean_object* v_h__4_99_, lean_object* v_h__5_100_, lean_object* v_h__6_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter(v_motive_93_, v_x_94_, v_x_95_, v_h__1_96_, v_h__2_97_, v_h__3_98_, v_h__4_99_, v_h__5_100_, v_h__6_101_);
lean_dec(v_x_94_);
return v_res_102_;
}
}
static lean_object* _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_103_; lean_object* v_intZero_104_; 
v_natZero_103_ = lean_unsigned_to_nat(0u);
v_intZero_104_ = lean_nat_to_int(v_natZero_103_);
return v_intZero_104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg(lean_object* v_x_105_, lean_object* v_x_106_, lean_object* v_h__1_107_, lean_object* v_h__2_108_, lean_object* v_h__3_109_, lean_object* v_h__4_110_, lean_object* v_h__5_111_){
_start:
{
lean_object* v_natZero_112_; lean_object* v_intZero_113_; uint8_t v_isNeg_114_; 
v_natZero_112_ = lean_unsigned_to_nat(0u);
v_intZero_113_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0);
v_isNeg_114_ = lean_int_dec_lt(v_x_105_, v_intZero_113_);
if (v_isNeg_114_ == 0)
{
lean_object* v_a_115_; uint8_t v_isZero_116_; 
lean_dec(v_h__5_111_);
lean_dec(v_h__4_110_);
v_a_115_ = lean_nat_abs(v_x_105_);
v_isZero_116_ = lean_nat_dec_eq(v_a_115_, v_natZero_112_);
if (v_isZero_116_ == 1)
{
lean_object* v___x_117_; 
lean_dec(v_a_115_);
lean_dec(v_h__3_109_);
lean_dec(v_h__2_108_);
v___x_117_ = lean_apply_1(v_h__1_107_, v_x_106_);
return v___x_117_;
}
else
{
uint8_t v_isNeg_118_; 
lean_dec(v_h__1_107_);
v_isNeg_118_ = lean_int_dec_lt(v_x_106_, v_intZero_113_);
if (v_isNeg_118_ == 0)
{
lean_object* v_a_119_; lean_object* v___x_120_; 
lean_dec(v_h__3_109_);
v_a_119_ = lean_nat_abs(v_x_106_);
lean_dec(v_x_106_);
v___x_120_ = lean_apply_3(v_h__2_108_, v_a_115_, v_a_119_, lean_box(0));
return v___x_120_;
}
else
{
lean_object* v_one_121_; lean_object* v_n_122_; lean_object* v_abs_123_; lean_object* v_a_124_; lean_object* v___x_125_; 
lean_dec(v_h__2_108_);
v_one_121_ = lean_unsigned_to_nat(1u);
v_n_122_ = lean_nat_sub(v_a_115_, v_one_121_);
lean_dec(v_a_115_);
v_abs_123_ = lean_nat_abs(v_x_106_);
lean_dec(v_x_106_);
v_a_124_ = lean_nat_sub(v_abs_123_, v_one_121_);
lean_dec(v_abs_123_);
v___x_125_ = lean_apply_2(v_h__3_109_, v_n_122_, v_a_124_);
return v___x_125_;
}
}
}
else
{
lean_object* v_abs_126_; lean_object* v_one_127_; lean_object* v_a_128_; uint8_t v_isNeg_129_; 
lean_dec(v_h__3_109_);
lean_dec(v_h__2_108_);
lean_dec(v_h__1_107_);
v_abs_126_ = lean_nat_abs(v_x_105_);
v_one_127_ = lean_unsigned_to_nat(1u);
v_a_128_ = lean_nat_sub(v_abs_126_, v_one_127_);
lean_dec(v_abs_126_);
v_isNeg_129_ = lean_int_dec_lt(v_x_106_, v_intZero_113_);
if (v_isNeg_129_ == 0)
{
lean_object* v_a_130_; lean_object* v___x_131_; 
lean_dec(v_h__5_111_);
v_a_130_ = lean_nat_abs(v_x_106_);
lean_dec(v_x_106_);
v___x_131_ = lean_apply_2(v_h__4_110_, v_a_128_, v_a_130_);
return v___x_131_;
}
else
{
lean_object* v_abs_132_; lean_object* v_a_133_; lean_object* v___x_134_; 
lean_dec(v_h__4_110_);
v_abs_132_ = lean_nat_abs(v_x_106_);
lean_dec(v_x_106_);
v_a_133_ = lean_nat_sub(v_abs_132_, v_one_127_);
lean_dec(v_abs_132_);
v___x_134_ = lean_apply_2(v_h__5_111_, v_a_128_, v_a_133_);
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___boxed(lean_object* v_x_135_, lean_object* v_x_136_, lean_object* v_h__1_137_, lean_object* v_h__2_138_, lean_object* v_h__3_139_, lean_object* v_h__4_140_, lean_object* v_h__5_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg(v_x_135_, v_x_136_, v_h__1_137_, v_h__2_138_, v_h__3_139_, v_h__4_140_, v_h__5_141_);
lean_dec(v_x_135_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter(lean_object* v_motive_143_, lean_object* v_x_144_, lean_object* v_x_145_, lean_object* v_h__1_146_, lean_object* v_h__2_147_, lean_object* v_h__3_148_, lean_object* v_h__4_149_, lean_object* v_h__5_150_){
_start:
{
lean_object* v_natZero_151_; lean_object* v_intZero_152_; uint8_t v_isNeg_153_; 
v_natZero_151_ = lean_unsigned_to_nat(0u);
v_intZero_152_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0);
v_isNeg_153_ = lean_int_dec_lt(v_x_144_, v_intZero_152_);
if (v_isNeg_153_ == 0)
{
lean_object* v_a_154_; uint8_t v_isZero_155_; 
lean_dec(v_h__5_150_);
lean_dec(v_h__4_149_);
v_a_154_ = lean_nat_abs(v_x_144_);
v_isZero_155_ = lean_nat_dec_eq(v_a_154_, v_natZero_151_);
if (v_isZero_155_ == 1)
{
lean_object* v___x_156_; 
lean_dec(v_a_154_);
lean_dec(v_h__3_148_);
lean_dec(v_h__2_147_);
v___x_156_ = lean_apply_1(v_h__1_146_, v_x_145_);
return v___x_156_;
}
else
{
uint8_t v_isNeg_157_; 
lean_dec(v_h__1_146_);
v_isNeg_157_ = lean_int_dec_lt(v_x_145_, v_intZero_152_);
if (v_isNeg_157_ == 0)
{
lean_object* v_a_158_; lean_object* v___x_159_; 
lean_dec(v_h__3_148_);
v_a_158_ = lean_nat_abs(v_x_145_);
lean_dec(v_x_145_);
v___x_159_ = lean_apply_3(v_h__2_147_, v_a_154_, v_a_158_, lean_box(0));
return v___x_159_;
}
else
{
lean_object* v_one_160_; lean_object* v_n_161_; lean_object* v_abs_162_; lean_object* v_a_163_; lean_object* v___x_164_; 
lean_dec(v_h__2_147_);
v_one_160_ = lean_unsigned_to_nat(1u);
v_n_161_ = lean_nat_sub(v_a_154_, v_one_160_);
lean_dec(v_a_154_);
v_abs_162_ = lean_nat_abs(v_x_145_);
lean_dec(v_x_145_);
v_a_163_ = lean_nat_sub(v_abs_162_, v_one_160_);
lean_dec(v_abs_162_);
v___x_164_ = lean_apply_2(v_h__3_148_, v_n_161_, v_a_163_);
return v___x_164_;
}
}
}
else
{
lean_object* v_abs_165_; lean_object* v_one_166_; lean_object* v_a_167_; uint8_t v_isNeg_168_; 
lean_dec(v_h__3_148_);
lean_dec(v_h__2_147_);
lean_dec(v_h__1_146_);
v_abs_165_ = lean_nat_abs(v_x_144_);
v_one_166_ = lean_unsigned_to_nat(1u);
v_a_167_ = lean_nat_sub(v_abs_165_, v_one_166_);
lean_dec(v_abs_165_);
v_isNeg_168_ = lean_int_dec_lt(v_x_145_, v_intZero_152_);
if (v_isNeg_168_ == 0)
{
lean_object* v_a_169_; lean_object* v___x_170_; 
lean_dec(v_h__5_150_);
v_a_169_ = lean_nat_abs(v_x_145_);
lean_dec(v_x_145_);
v___x_170_ = lean_apply_2(v_h__4_149_, v_a_167_, v_a_169_);
return v___x_170_;
}
else
{
lean_object* v_abs_171_; lean_object* v_a_172_; lean_object* v___x_173_; 
lean_dec(v_h__4_149_);
v_abs_171_ = lean_nat_abs(v_x_145_);
lean_dec(v_x_145_);
v_a_172_ = lean_nat_sub(v_abs_171_, v_one_166_);
lean_dec(v_abs_171_);
v___x_173_ = lean_apply_2(v_h__5_150_, v_a_167_, v_a_172_);
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___boxed(lean_object* v_motive_174_, lean_object* v_x_175_, lean_object* v_x_176_, lean_object* v_h__1_177_, lean_object* v_h__2_178_, lean_object* v_h__3_179_, lean_object* v_h__4_180_, lean_object* v_h__5_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter(v_motive_174_, v_x_175_, v_x_176_, v_h__1_177_, v_h__2_178_, v_h__3_179_, v_h__4_180_, v_h__5_181_);
lean_dec(v_x_175_);
return v_res_182_;
}
}
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Int_DivMod_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
