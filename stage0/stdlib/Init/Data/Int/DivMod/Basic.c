// Lean compiler output
// Module: Init.Data.Int.DivMod.Basic
// Imports: public import Init.Data.Int.Basic import Init.Data.Nat.Div.Basic
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_int_neg_succ_of_nat(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Int_subNatNat(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_ediv___boxed(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_emod___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_instDiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_ediv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instDiv___closed__0 = (const lean_object*)&l_Int_instDiv___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_instDiv = (const lean_object*)&l_Int_instDiv___closed__0_value;
static const lean_closure_object l_Int_instMod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_emod___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_instMod___closed__0 = (const lean_object*)&l_Int_instMod___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_instMod = (const lean_object*)&l_Int_instMod___closed__0_value;
lean_object* lean_int_div_exact(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_divExact___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_tdiv___boxed(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_tmod___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Int_fdiv___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_fdiv___closed__0;
LEAN_EXPORT lean_object* l_Int_fdiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_fdiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_fmod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_fmod___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_bmod_spec__0(lean_object*);
static lean_once_cell_t l_Int_bmod___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_bmod___closed__0;
static lean_once_cell_t l_Int_bmod___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_bmod___closed__1;
LEAN_EXPORT lean_object* l_Int_bmod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_bmod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_bdiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_bdiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_ediv___boxed(lean_object* v_a_00___x40___internal___hyg_3_, lean_object* v_a_00___x40___internal___hyg_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lean_int_ediv(v_a_00___x40___internal___hyg_3_, v_a_00___x40___internal___hyg_4_);
lean_dec(v_a_00___x40___internal___hyg_4_);
lean_dec(v_a_00___x40___internal___hyg_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Int_emod___boxed(lean_object* v_a_00___x40___internal___hyg_8_, lean_object* v_a_00___x40___internal___hyg_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lean_int_emod(v_a_00___x40___internal___hyg_8_, v_a_00___x40___internal___hyg_9_);
lean_dec(v_a_00___x40___internal___hyg_9_);
lean_dec(v_a_00___x40___internal___hyg_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Int_divExact___boxed(lean_object* v_x_18_, lean_object* v_y_19_, lean_object* v_h_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lean_int_div_exact(v_x_18_, v_y_19_);
lean_dec(v_y_19_);
lean_dec(v_x_18_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Int_tdiv___boxed(lean_object* v_a_00___x40___internal___hyg_24_, lean_object* v_a_00___x40___internal___hyg_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lean_int_div(v_a_00___x40___internal___hyg_24_, v_a_00___x40___internal___hyg_25_);
lean_dec(v_a_00___x40___internal___hyg_25_);
lean_dec(v_a_00___x40___internal___hyg_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Int_tmod___boxed(lean_object* v_a_00___x40___internal___hyg_29_, lean_object* v_a_00___x40___internal___hyg_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lean_int_mod(v_a_00___x40___internal___hyg_29_, v_a_00___x40___internal___hyg_30_);
lean_dec(v_a_00___x40___internal___hyg_30_);
lean_dec(v_a_00___x40___internal___hyg_29_);
return v_res_31_;
}
}
static lean_object* _init_l_Int_fdiv___closed__0(void){
_start:
{
lean_object* v_natZero_32_; lean_object* v_intZero_33_; 
v_natZero_32_ = lean_unsigned_to_nat(0u);
v_intZero_33_ = lean_nat_to_int(v_natZero_32_);
return v_intZero_33_;
}
}
LEAN_EXPORT lean_object* l_Int_fdiv(lean_object* v_x_34_, lean_object* v_x_35_){
_start:
{
lean_object* v_m_37_; lean_object* v_n_38_; lean_object* v_natZero_43_; lean_object* v_intZero_44_; uint8_t v_isNeg_45_; 
v_natZero_43_ = lean_unsigned_to_nat(0u);
v_intZero_44_ = lean_obj_once(&l_Int_fdiv___closed__0, &l_Int_fdiv___closed__0_once, _init_l_Int_fdiv___closed__0);
v_isNeg_45_ = lean_int_dec_lt(v_x_34_, v_intZero_44_);
if (v_isNeg_45_ == 0)
{
lean_object* v_a_46_; uint8_t v_isZero_47_; 
v_a_46_ = lean_nat_abs(v_x_34_);
v_isZero_47_ = lean_nat_dec_eq(v_a_46_, v_natZero_43_);
if (v_isZero_47_ == 1)
{
lean_dec(v_a_46_);
return v_intZero_44_;
}
else
{
uint8_t v_isNeg_48_; 
v_isNeg_48_ = lean_int_dec_lt(v_x_35_, v_intZero_44_);
if (v_isNeg_48_ == 0)
{
lean_object* v_a_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_a_49_ = lean_nat_abs(v_x_35_);
v___x_50_ = lean_nat_div(v_a_46_, v_a_49_);
lean_dec(v_a_49_);
lean_dec(v_a_46_);
v___x_51_ = lean_nat_to_int(v___x_50_);
return v___x_51_;
}
else
{
lean_object* v_one_52_; lean_object* v_n_53_; lean_object* v_abs_54_; lean_object* v_a_55_; 
v_one_52_ = lean_unsigned_to_nat(1u);
v_n_53_ = lean_nat_sub(v_a_46_, v_one_52_);
lean_dec(v_a_46_);
v_abs_54_ = lean_nat_abs(v_x_35_);
v_a_55_ = lean_nat_sub(v_abs_54_, v_one_52_);
lean_dec(v_abs_54_);
v_m_37_ = v_n_53_;
v_n_38_ = v_a_55_;
goto v___jp_36_;
}
}
}
else
{
lean_object* v_abs_56_; lean_object* v_one_57_; lean_object* v_a_58_; uint8_t v_isNeg_59_; 
v_abs_56_ = lean_nat_abs(v_x_34_);
v_one_57_ = lean_unsigned_to_nat(1u);
v_a_58_ = lean_nat_sub(v_abs_56_, v_one_57_);
lean_dec(v_abs_56_);
v_isNeg_59_ = lean_int_dec_lt(v_x_35_, v_intZero_44_);
if (v_isNeg_59_ == 0)
{
lean_object* v_a_60_; uint8_t v_isZero_61_; 
v_a_60_ = lean_nat_abs(v_x_35_);
v_isZero_61_ = lean_nat_dec_eq(v_a_60_, v_natZero_43_);
if (v_isZero_61_ == 1)
{
lean_dec(v_a_60_);
lean_dec(v_a_58_);
return v_intZero_44_;
}
else
{
lean_object* v_n_62_; 
v_n_62_ = lean_nat_sub(v_a_60_, v_one_57_);
lean_dec(v_a_60_);
v_m_37_ = v_a_58_;
v_n_38_ = v_n_62_;
goto v___jp_36_;
}
}
else
{
lean_object* v_abs_63_; lean_object* v_a_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_abs_63_ = lean_nat_abs(v_x_35_);
v_a_64_ = lean_nat_sub(v_abs_63_, v_one_57_);
lean_dec(v_abs_63_);
v___x_65_ = lean_nat_add(v_a_58_, v_one_57_);
lean_dec(v_a_58_);
v___x_66_ = lean_nat_add(v_a_64_, v_one_57_);
lean_dec(v_a_64_);
v___x_67_ = lean_nat_div(v___x_65_, v___x_66_);
lean_dec(v___x_66_);
lean_dec(v___x_65_);
v___x_68_ = lean_nat_to_int(v___x_67_);
return v___x_68_;
}
}
v___jp_36_:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_39_ = lean_unsigned_to_nat(1u);
v___x_40_ = lean_nat_add(v_n_38_, v___x_39_);
lean_dec(v_n_38_);
v___x_41_ = lean_nat_div(v_m_37_, v___x_40_);
lean_dec(v___x_40_);
lean_dec(v_m_37_);
v___x_42_ = lean_int_neg_succ_of_nat(v___x_41_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_Int_fdiv___boxed(lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Int_fdiv(v_x_69_, v_x_70_);
lean_dec(v_x_70_);
lean_dec(v_x_69_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Int_fmod(lean_object* v_x_72_, lean_object* v_x_73_){
_start:
{
lean_object* v_natZero_74_; lean_object* v_intZero_75_; uint8_t v_isNeg_76_; 
v_natZero_74_ = lean_unsigned_to_nat(0u);
v_intZero_75_ = lean_obj_once(&l_Int_fdiv___closed__0, &l_Int_fdiv___closed__0_once, _init_l_Int_fdiv___closed__0);
v_isNeg_76_ = lean_int_dec_lt(v_x_72_, v_intZero_75_);
if (v_isNeg_76_ == 0)
{
lean_object* v_a_77_; uint8_t v_isZero_78_; 
v_a_77_ = lean_nat_abs(v_x_72_);
v_isZero_78_ = lean_nat_dec_eq(v_a_77_, v_natZero_74_);
if (v_isZero_78_ == 1)
{
lean_dec(v_a_77_);
return v_intZero_75_;
}
else
{
uint8_t v_isNeg_79_; 
v_isNeg_79_ = lean_int_dec_lt(v_x_73_, v_intZero_75_);
if (v_isNeg_79_ == 0)
{
lean_object* v_a_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_a_80_ = lean_nat_abs(v_x_73_);
v___x_81_ = lean_nat_mod(v_a_77_, v_a_80_);
lean_dec(v_a_80_);
lean_dec(v_a_77_);
v___x_82_ = lean_nat_to_int(v___x_81_);
return v___x_82_;
}
else
{
lean_object* v_one_83_; lean_object* v_n_84_; lean_object* v_abs_85_; lean_object* v_a_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v_one_83_ = lean_unsigned_to_nat(1u);
v_n_84_ = lean_nat_sub(v_a_77_, v_one_83_);
lean_dec(v_a_77_);
v_abs_85_ = lean_nat_abs(v_x_73_);
v_a_86_ = lean_nat_sub(v_abs_85_, v_one_83_);
lean_dec(v_abs_85_);
v___x_87_ = lean_nat_add(v_a_86_, v_one_83_);
v___x_88_ = lean_nat_mod(v_n_84_, v___x_87_);
lean_dec(v___x_87_);
lean_dec(v_n_84_);
v___x_89_ = l_Int_subNatNat(v___x_88_, v_a_86_);
lean_dec(v_a_86_);
lean_dec(v___x_88_);
return v___x_89_;
}
}
}
else
{
lean_object* v_abs_90_; lean_object* v_one_91_; lean_object* v_a_92_; uint8_t v_isNeg_93_; 
v_abs_90_ = lean_nat_abs(v_x_72_);
v_one_91_ = lean_unsigned_to_nat(1u);
v_a_92_ = lean_nat_sub(v_abs_90_, v_one_91_);
lean_dec(v_abs_90_);
v_isNeg_93_ = lean_int_dec_lt(v_x_73_, v_intZero_75_);
if (v_isNeg_93_ == 0)
{
lean_object* v_a_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v_a_94_ = lean_nat_abs(v_x_73_);
v___x_95_ = lean_nat_mod(v_a_92_, v_a_94_);
lean_dec(v_a_92_);
v___x_96_ = lean_nat_add(v___x_95_, v_one_91_);
lean_dec(v___x_95_);
v___x_97_ = l_Int_subNatNat(v_a_94_, v___x_96_);
lean_dec(v___x_96_);
lean_dec(v_a_94_);
return v___x_97_;
}
else
{
lean_object* v_abs_98_; lean_object* v_a_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_abs_98_ = lean_nat_abs(v_x_73_);
v_a_99_ = lean_nat_sub(v_abs_98_, v_one_91_);
lean_dec(v_abs_98_);
v___x_100_ = lean_nat_add(v_a_92_, v_one_91_);
lean_dec(v_a_92_);
v___x_101_ = lean_nat_add(v_a_99_, v_one_91_);
lean_dec(v_a_99_);
v___x_102_ = lean_nat_mod(v___x_100_, v___x_101_);
lean_dec(v___x_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_nat_to_int(v___x_102_);
v___x_104_ = lean_int_neg(v___x_103_);
lean_dec(v___x_103_);
return v___x_104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_fmod___boxed(lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Int_fmod(v_x_105_, v_x_106_);
lean_dec(v_x_106_);
lean_dec(v_x_105_);
return v_res_107_;
}
}
static lean_object* _init_l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_108_; lean_object* v_intZero_109_; 
v_natZero_108_ = lean_unsigned_to_nat(0u);
v_intZero_109_ = lean_nat_to_int(v_natZero_108_);
return v_intZero_109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg(lean_object* v_x_110_, lean_object* v_x_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_, lean_object* v_h__3_114_, lean_object* v_h__4_115_, lean_object* v_h__5_116_, lean_object* v_h__6_117_){
_start:
{
lean_object* v_natZero_118_; lean_object* v_intZero_119_; uint8_t v_isNeg_120_; 
v_natZero_118_ = lean_unsigned_to_nat(0u);
v_intZero_119_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0);
v_isNeg_120_ = lean_int_dec_lt(v_x_110_, v_intZero_119_);
if (v_isNeg_120_ == 0)
{
lean_object* v_a_121_; uint8_t v_isZero_122_; 
lean_dec(v_h__6_117_);
lean_dec(v_h__5_116_);
lean_dec(v_h__4_115_);
v_a_121_ = lean_nat_abs(v_x_110_);
v_isZero_122_ = lean_nat_dec_eq(v_a_121_, v_natZero_118_);
if (v_isZero_122_ == 1)
{
lean_object* v___x_123_; 
lean_dec(v_a_121_);
lean_dec(v_h__3_114_);
lean_dec(v_h__2_113_);
v___x_123_ = lean_apply_1(v_h__1_112_, v_x_111_);
return v___x_123_;
}
else
{
uint8_t v_isNeg_124_; 
lean_dec(v_h__1_112_);
v_isNeg_124_ = lean_int_dec_lt(v_x_111_, v_intZero_119_);
if (v_isNeg_124_ == 0)
{
lean_object* v_a_125_; lean_object* v___x_126_; 
lean_dec(v_h__3_114_);
v_a_125_ = lean_nat_abs(v_x_111_);
lean_dec(v_x_111_);
v___x_126_ = lean_apply_3(v_h__2_113_, v_a_121_, v_a_125_, lean_box(0));
return v___x_126_;
}
else
{
lean_object* v_one_127_; lean_object* v_n_128_; lean_object* v_abs_129_; lean_object* v_a_130_; lean_object* v___x_131_; 
lean_dec(v_h__2_113_);
v_one_127_ = lean_unsigned_to_nat(1u);
v_n_128_ = lean_nat_sub(v_a_121_, v_one_127_);
lean_dec(v_a_121_);
v_abs_129_ = lean_nat_abs(v_x_111_);
lean_dec(v_x_111_);
v_a_130_ = lean_nat_sub(v_abs_129_, v_one_127_);
lean_dec(v_abs_129_);
v___x_131_ = lean_apply_2(v_h__3_114_, v_n_128_, v_a_130_);
return v___x_131_;
}
}
}
else
{
lean_object* v_abs_132_; lean_object* v_one_133_; lean_object* v_a_134_; uint8_t v_isNeg_135_; 
lean_dec(v_h__3_114_);
lean_dec(v_h__2_113_);
lean_dec(v_h__1_112_);
v_abs_132_ = lean_nat_abs(v_x_110_);
v_one_133_ = lean_unsigned_to_nat(1u);
v_a_134_ = lean_nat_sub(v_abs_132_, v_one_133_);
lean_dec(v_abs_132_);
v_isNeg_135_ = lean_int_dec_lt(v_x_111_, v_intZero_119_);
if (v_isNeg_135_ == 0)
{
lean_object* v_a_136_; uint8_t v_isZero_137_; 
lean_dec(v_h__6_117_);
v_a_136_ = lean_nat_abs(v_x_111_);
lean_dec(v_x_111_);
v_isZero_137_ = lean_nat_dec_eq(v_a_136_, v_natZero_118_);
if (v_isZero_137_ == 1)
{
lean_object* v___x_138_; 
lean_dec(v_a_136_);
lean_dec(v_h__5_116_);
v___x_138_ = lean_apply_1(v_h__4_115_, v_a_134_);
return v___x_138_;
}
else
{
lean_object* v_n_139_; lean_object* v___x_140_; 
lean_dec(v_h__4_115_);
v_n_139_ = lean_nat_sub(v_a_136_, v_one_133_);
lean_dec(v_a_136_);
v___x_140_ = lean_apply_2(v_h__5_116_, v_a_134_, v_n_139_);
return v___x_140_;
}
}
else
{
lean_object* v_abs_141_; lean_object* v_a_142_; lean_object* v___x_143_; 
lean_dec(v_h__5_116_);
lean_dec(v_h__4_115_);
v_abs_141_ = lean_nat_abs(v_x_111_);
lean_dec(v_x_111_);
v_a_142_ = lean_nat_sub(v_abs_141_, v_one_133_);
lean_dec(v_abs_141_);
v___x_143_ = lean_apply_2(v_h__6_117_, v_a_134_, v_a_142_);
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___boxed(lean_object* v_x_144_, lean_object* v_x_145_, lean_object* v_h__1_146_, lean_object* v_h__2_147_, lean_object* v_h__3_148_, lean_object* v_h__4_149_, lean_object* v_h__5_150_, lean_object* v_h__6_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg(v_x_144_, v_x_145_, v_h__1_146_, v_h__2_147_, v_h__3_148_, v_h__4_149_, v_h__5_150_, v_h__6_151_);
lean_dec(v_x_144_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter(lean_object* v_motive_153_, lean_object* v_x_154_, lean_object* v_x_155_, lean_object* v_h__1_156_, lean_object* v_h__2_157_, lean_object* v_h__3_158_, lean_object* v_h__4_159_, lean_object* v_h__5_160_, lean_object* v_h__6_161_){
_start:
{
lean_object* v_natZero_162_; lean_object* v_intZero_163_; uint8_t v_isNeg_164_; 
v_natZero_162_ = lean_unsigned_to_nat(0u);
v_intZero_163_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0);
v_isNeg_164_ = lean_int_dec_lt(v_x_154_, v_intZero_163_);
if (v_isNeg_164_ == 0)
{
lean_object* v_a_165_; uint8_t v_isZero_166_; 
lean_dec(v_h__6_161_);
lean_dec(v_h__5_160_);
lean_dec(v_h__4_159_);
v_a_165_ = lean_nat_abs(v_x_154_);
v_isZero_166_ = lean_nat_dec_eq(v_a_165_, v_natZero_162_);
if (v_isZero_166_ == 1)
{
lean_object* v___x_167_; 
lean_dec(v_a_165_);
lean_dec(v_h__3_158_);
lean_dec(v_h__2_157_);
v___x_167_ = lean_apply_1(v_h__1_156_, v_x_155_);
return v___x_167_;
}
else
{
uint8_t v_isNeg_168_; 
lean_dec(v_h__1_156_);
v_isNeg_168_ = lean_int_dec_lt(v_x_155_, v_intZero_163_);
if (v_isNeg_168_ == 0)
{
lean_object* v_a_169_; lean_object* v___x_170_; 
lean_dec(v_h__3_158_);
v_a_169_ = lean_nat_abs(v_x_155_);
lean_dec(v_x_155_);
v___x_170_ = lean_apply_3(v_h__2_157_, v_a_165_, v_a_169_, lean_box(0));
return v___x_170_;
}
else
{
lean_object* v_one_171_; lean_object* v_n_172_; lean_object* v_abs_173_; lean_object* v_a_174_; lean_object* v___x_175_; 
lean_dec(v_h__2_157_);
v_one_171_ = lean_unsigned_to_nat(1u);
v_n_172_ = lean_nat_sub(v_a_165_, v_one_171_);
lean_dec(v_a_165_);
v_abs_173_ = lean_nat_abs(v_x_155_);
lean_dec(v_x_155_);
v_a_174_ = lean_nat_sub(v_abs_173_, v_one_171_);
lean_dec(v_abs_173_);
v___x_175_ = lean_apply_2(v_h__3_158_, v_n_172_, v_a_174_);
return v___x_175_;
}
}
}
else
{
lean_object* v_abs_176_; lean_object* v_one_177_; lean_object* v_a_178_; uint8_t v_isNeg_179_; 
lean_dec(v_h__3_158_);
lean_dec(v_h__2_157_);
lean_dec(v_h__1_156_);
v_abs_176_ = lean_nat_abs(v_x_154_);
v_one_177_ = lean_unsigned_to_nat(1u);
v_a_178_ = lean_nat_sub(v_abs_176_, v_one_177_);
lean_dec(v_abs_176_);
v_isNeg_179_ = lean_int_dec_lt(v_x_155_, v_intZero_163_);
if (v_isNeg_179_ == 0)
{
lean_object* v_a_180_; uint8_t v_isZero_181_; 
lean_dec(v_h__6_161_);
v_a_180_ = lean_nat_abs(v_x_155_);
lean_dec(v_x_155_);
v_isZero_181_ = lean_nat_dec_eq(v_a_180_, v_natZero_162_);
if (v_isZero_181_ == 1)
{
lean_object* v___x_182_; 
lean_dec(v_a_180_);
lean_dec(v_h__5_160_);
v___x_182_ = lean_apply_1(v_h__4_159_, v_a_178_);
return v___x_182_;
}
else
{
lean_object* v_n_183_; lean_object* v___x_184_; 
lean_dec(v_h__4_159_);
v_n_183_ = lean_nat_sub(v_a_180_, v_one_177_);
lean_dec(v_a_180_);
v___x_184_ = lean_apply_2(v_h__5_160_, v_a_178_, v_n_183_);
return v___x_184_;
}
}
else
{
lean_object* v_abs_185_; lean_object* v_a_186_; lean_object* v___x_187_; 
lean_dec(v_h__5_160_);
lean_dec(v_h__4_159_);
v_abs_185_ = lean_nat_abs(v_x_155_);
lean_dec(v_x_155_);
v_a_186_ = lean_nat_sub(v_abs_185_, v_one_177_);
lean_dec(v_abs_185_);
v___x_187_ = lean_apply_2(v_h__6_161_, v_a_178_, v_a_186_);
return v___x_187_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___boxed(lean_object* v_motive_188_, lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_h__1_191_, lean_object* v_h__2_192_, lean_object* v_h__3_193_, lean_object* v_h__4_194_, lean_object* v_h__5_195_, lean_object* v_h__6_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter(v_motive_188_, v_x_189_, v_x_190_, v_h__1_191_, v_h__2_192_, v_h__3_193_, v_h__4_194_, v_h__5_195_, v_h__6_196_);
lean_dec(v_x_189_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_bmod_spec__0(lean_object* v_a_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_nat_to_int(v_a_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Int_bmod___closed__0(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_unsigned_to_nat(1u);
v___x_201_ = lean_nat_to_int(v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l_Int_bmod___closed__1(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_unsigned_to_nat(2u);
v___x_203_ = lean_nat_to_int(v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Int_bmod(lean_object* v_x_204_, lean_object* v_m_205_){
_start:
{
lean_object* v___x_206_; lean_object* v_r_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_206_ = lean_nat_to_int(v_m_205_);
v_r_207_ = lean_int_emod(v_x_204_, v___x_206_);
v___x_208_ = lean_obj_once(&l_Int_bmod___closed__0, &l_Int_bmod___closed__0_once, _init_l_Int_bmod___closed__0);
v___x_209_ = lean_int_add(v___x_206_, v___x_208_);
v___x_210_ = lean_obj_once(&l_Int_bmod___closed__1, &l_Int_bmod___closed__1_once, _init_l_Int_bmod___closed__1);
v___x_211_ = lean_int_ediv(v___x_209_, v___x_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_int_dec_lt(v_r_207_, v___x_211_);
lean_dec(v___x_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
v___x_213_ = lean_int_sub(v_r_207_, v___x_206_);
lean_dec(v___x_206_);
lean_dec(v_r_207_);
return v___x_213_;
}
else
{
lean_dec(v___x_206_);
return v_r_207_;
}
}
}
LEAN_EXPORT lean_object* l_Int_bmod___boxed(lean_object* v_x_214_, lean_object* v_m_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Int_bmod(v_x_214_, v_m_215_);
lean_dec(v_x_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Int_bdiv(lean_object* v_x_217_, lean_object* v_m_218_){
_start:
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_nat_dec_eq(v_m_218_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; lean_object* v_q_222_; lean_object* v_r_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_221_ = lean_nat_to_int(v_m_218_);
v_q_222_ = lean_int_ediv(v_x_217_, v___x_221_);
v_r_223_ = lean_int_emod(v_x_217_, v___x_221_);
v___x_224_ = lean_obj_once(&l_Int_bmod___closed__0, &l_Int_bmod___closed__0_once, _init_l_Int_bmod___closed__0);
v___x_225_ = lean_int_add(v___x_221_, v___x_224_);
lean_dec(v___x_221_);
v___x_226_ = lean_obj_once(&l_Int_bmod___closed__1, &l_Int_bmod___closed__1_once, _init_l_Int_bmod___closed__1);
v___x_227_ = lean_int_ediv(v___x_225_, v___x_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_int_dec_lt(v_r_223_, v___x_227_);
lean_dec(v___x_227_);
lean_dec(v_r_223_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; 
v___x_229_ = lean_int_add(v_q_222_, v___x_224_);
lean_dec(v_q_222_);
return v___x_229_;
}
else
{
return v_q_222_;
}
}
else
{
lean_object* v___x_230_; 
lean_dec(v_m_218_);
v___x_230_ = lean_obj_once(&l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l_Int_bdiv___boxed(lean_object* v_x_231_, lean_object* v_m_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Int_bdiv(v_x_231_, v_m_232_);
lean_dec(v_x_231_);
return v_res_233_;
}
}
lean_object* runtime_initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Int_DivMod_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
