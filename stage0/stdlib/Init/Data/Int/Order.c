// Lean compiler output
// Module: Init.Data.Int.Order
// Imports: import Init.Data.Order.Lemmas public import Init.Data.Order.Classes public import Init.NotationExtra import Init.ByCases import Init.Data.Int.Lemmas
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_instTransLe;
LEAN_EXPORT lean_object* l_Int_instTransLtLe;
LEAN_EXPORT lean_object* l_Int_instTransLeLt;
LEAN_EXPORT lean_object* l_Int_instTransLt;
static lean_once_cell_t l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Int_instTransLe(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
static lean_object* _init_l_Int_instTransLtLe(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
static lean_object* _init_l_Int_instTransLeLt(void){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
static lean_object* _init_l_Int_instTransLt(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
static lean_object* _init_l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_5_; lean_object* v_intZero_6_; 
v_natZero_5_ = lean_unsigned_to_nat(0u);
v_intZero_6_ = lean_nat_to_int(v_natZero_5_);
return v_intZero_6_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg(lean_object* v_m_7_, lean_object* v_n_8_, lean_object* v_h__1_9_, lean_object* v_h__2_10_, lean_object* v_h__3_11_, lean_object* v_h__4_12_){
_start:
{
lean_object* v_intZero_13_; uint8_t v_isNeg_14_; 
v_intZero_13_ = lean_obj_once(&l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___closed__0);
v_isNeg_14_ = lean_int_dec_lt(v_m_7_, v_intZero_13_);
if (v_isNeg_14_ == 0)
{
lean_object* v_a_15_; uint8_t v_isNeg_16_; 
lean_dec(v_h__4_12_);
lean_dec(v_h__3_11_);
v_a_15_ = lean_nat_abs(v_m_7_);
v_isNeg_16_ = lean_int_dec_lt(v_n_8_, v_intZero_13_);
if (v_isNeg_16_ == 0)
{
lean_object* v_a_17_; lean_object* v___x_18_; 
lean_dec(v_h__2_10_);
v_a_17_ = lean_nat_abs(v_n_8_);
v___x_18_ = lean_apply_2(v_h__1_9_, v_a_15_, v_a_17_);
return v___x_18_;
}
else
{
lean_object* v_abs_19_; lean_object* v_one_20_; lean_object* v_a_21_; lean_object* v___x_22_; 
lean_dec(v_h__1_9_);
v_abs_19_ = lean_nat_abs(v_n_8_);
v_one_20_ = lean_unsigned_to_nat(1u);
v_a_21_ = lean_nat_sub(v_abs_19_, v_one_20_);
lean_dec(v_abs_19_);
v___x_22_ = lean_apply_2(v_h__2_10_, v_a_15_, v_a_21_);
return v___x_22_;
}
}
else
{
lean_object* v_abs_23_; lean_object* v_one_24_; lean_object* v_a_25_; uint8_t v_isNeg_26_; 
lean_dec(v_h__2_10_);
lean_dec(v_h__1_9_);
v_abs_23_ = lean_nat_abs(v_m_7_);
v_one_24_ = lean_unsigned_to_nat(1u);
v_a_25_ = lean_nat_sub(v_abs_23_, v_one_24_);
lean_dec(v_abs_23_);
v_isNeg_26_ = lean_int_dec_lt(v_n_8_, v_intZero_13_);
if (v_isNeg_26_ == 0)
{
lean_object* v_a_27_; lean_object* v___x_28_; 
lean_dec(v_h__4_12_);
v_a_27_ = lean_nat_abs(v_n_8_);
v___x_28_ = lean_apply_2(v_h__3_11_, v_a_25_, v_a_27_);
return v___x_28_;
}
else
{
lean_object* v_abs_29_; lean_object* v_a_30_; lean_object* v___x_31_; 
lean_dec(v_h__3_11_);
v_abs_29_ = lean_nat_abs(v_n_8_);
v_a_30_ = lean_nat_sub(v_abs_29_, v_one_24_);
lean_dec(v_abs_29_);
v___x_31_ = lean_apply_2(v_h__4_12_, v_a_25_, v_a_30_);
return v___x_31_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___boxed(lean_object* v_m_32_, lean_object* v_n_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_, lean_object* v_h__3_36_, lean_object* v_h__4_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg(v_m_32_, v_n_33_, v_h__1_34_, v_h__2_35_, v_h__3_36_, v_h__4_37_);
lean_dec(v_n_33_);
lean_dec(v_m_32_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter(lean_object* v_motive_39_, lean_object* v_m_40_, lean_object* v_n_41_, lean_object* v_h__1_42_, lean_object* v_h__2_43_, lean_object* v_h__3_44_, lean_object* v_h__4_45_){
_start:
{
lean_object* v_intZero_46_; uint8_t v_isNeg_47_; 
v_intZero_46_ = lean_obj_once(&l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___closed__0);
v_isNeg_47_ = lean_int_dec_lt(v_m_40_, v_intZero_46_);
if (v_isNeg_47_ == 0)
{
lean_object* v_a_48_; uint8_t v_isNeg_49_; 
lean_dec(v_h__4_45_);
lean_dec(v_h__3_44_);
v_a_48_ = lean_nat_abs(v_m_40_);
v_isNeg_49_ = lean_int_dec_lt(v_n_41_, v_intZero_46_);
if (v_isNeg_49_ == 0)
{
lean_object* v_a_50_; lean_object* v___x_51_; 
lean_dec(v_h__2_43_);
v_a_50_ = lean_nat_abs(v_n_41_);
v___x_51_ = lean_apply_2(v_h__1_42_, v_a_48_, v_a_50_);
return v___x_51_;
}
else
{
lean_object* v_abs_52_; lean_object* v_one_53_; lean_object* v_a_54_; lean_object* v___x_55_; 
lean_dec(v_h__1_42_);
v_abs_52_ = lean_nat_abs(v_n_41_);
v_one_53_ = lean_unsigned_to_nat(1u);
v_a_54_ = lean_nat_sub(v_abs_52_, v_one_53_);
lean_dec(v_abs_52_);
v___x_55_ = lean_apply_2(v_h__2_43_, v_a_48_, v_a_54_);
return v___x_55_;
}
}
else
{
lean_object* v_abs_56_; lean_object* v_one_57_; lean_object* v_a_58_; uint8_t v_isNeg_59_; 
lean_dec(v_h__2_43_);
lean_dec(v_h__1_42_);
v_abs_56_ = lean_nat_abs(v_m_40_);
v_one_57_ = lean_unsigned_to_nat(1u);
v_a_58_ = lean_nat_sub(v_abs_56_, v_one_57_);
lean_dec(v_abs_56_);
v_isNeg_59_ = lean_int_dec_lt(v_n_41_, v_intZero_46_);
if (v_isNeg_59_ == 0)
{
lean_object* v_a_60_; lean_object* v___x_61_; 
lean_dec(v_h__4_45_);
v_a_60_ = lean_nat_abs(v_n_41_);
v___x_61_ = lean_apply_2(v_h__3_44_, v_a_58_, v_a_60_);
return v___x_61_;
}
else
{
lean_object* v_abs_62_; lean_object* v_a_63_; lean_object* v___x_64_; 
lean_dec(v_h__3_44_);
v_abs_62_ = lean_nat_abs(v_n_41_);
v_a_63_ = lean_nat_sub(v_abs_62_, v_one_57_);
lean_dec(v_abs_62_);
v___x_64_ = lean_apply_2(v_h__4_45_, v_a_58_, v_a_63_);
return v___x_64_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___boxed(lean_object* v_motive_65_, lean_object* v_m_66_, lean_object* v_n_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_, lean_object* v_h__3_70_, lean_object* v_h__4_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter(v_motive_65_, v_m_66_, v_n_67_, v_h__1_68_, v_h__2_69_, v_h__3_70_, v_h__4_71_);
lean_dec(v_n_67_);
lean_dec(v_m_66_);
return v_res_72_;
}
}
static lean_object* _init_l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_73_; lean_object* v_intZero_74_; 
v_natZero_73_ = lean_unsigned_to_nat(0u);
v_intZero_74_ = lean_nat_to_int(v_natZero_73_);
return v_intZero_74_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg(lean_object* v_n_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_){
_start:
{
lean_object* v_intZero_78_; uint8_t v_isNeg_79_; 
v_intZero_78_ = lean_obj_once(&l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0);
v_isNeg_79_ = lean_int_dec_lt(v_n_75_, v_intZero_78_);
if (v_isNeg_79_ == 0)
{
lean_object* v_a_80_; lean_object* v___x_81_; 
lean_dec(v_h__2_77_);
v_a_80_ = lean_nat_abs(v_n_75_);
v___x_81_ = lean_apply_1(v_h__1_76_, v_a_80_);
return v___x_81_;
}
else
{
lean_object* v_abs_82_; lean_object* v_one_83_; lean_object* v_a_84_; lean_object* v___x_85_; 
lean_dec(v_h__1_76_);
v_abs_82_ = lean_nat_abs(v_n_75_);
v_one_83_ = lean_unsigned_to_nat(1u);
v_a_84_ = lean_nat_sub(v_abs_82_, v_one_83_);
lean_dec(v_abs_82_);
v___x_85_ = lean_apply_1(v_h__2_77_, v_a_84_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___boxed(lean_object* v_n_86_, lean_object* v_h__1_87_, lean_object* v_h__2_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg(v_n_86_, v_h__1_87_, v_h__2_88_);
lean_dec(v_n_86_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter(lean_object* v_motive_90_, lean_object* v_n_91_, lean_object* v_h__1_92_, lean_object* v_h__2_93_){
_start:
{
lean_object* v_intZero_94_; uint8_t v_isNeg_95_; 
v_intZero_94_ = lean_obj_once(&l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0);
v_isNeg_95_ = lean_int_dec_lt(v_n_91_, v_intZero_94_);
if (v_isNeg_95_ == 0)
{
lean_object* v_a_96_; lean_object* v___x_97_; 
lean_dec(v_h__2_93_);
v_a_96_ = lean_nat_abs(v_n_91_);
v___x_97_ = lean_apply_1(v_h__1_92_, v_a_96_);
return v___x_97_;
}
else
{
lean_object* v_abs_98_; lean_object* v_one_99_; lean_object* v_a_100_; lean_object* v___x_101_; 
lean_dec(v_h__1_92_);
v_abs_98_ = lean_nat_abs(v_n_91_);
v_one_99_ = lean_unsigned_to_nat(1u);
v_a_100_ = lean_nat_sub(v_abs_98_, v_one_99_);
lean_dec(v_abs_98_);
v___x_101_ = lean_apply_1(v_h__2_93_, v_a_100_);
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___boxed(lean_object* v_motive_102_, lean_object* v_n_103_, lean_object* v_h__1_104_, lean_object* v_h__2_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter(v_motive_102_, v_n_103_, v_h__1_104_, v_h__2_105_);
lean_dec(v_n_103_);
return v_res_106_;
}
}
static lean_object* _init_l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_107_; lean_object* v_intZero_108_; 
v_natZero_107_ = lean_unsigned_to_nat(0u);
v_intZero_108_ = lean_nat_to_int(v_natZero_107_);
return v_intZero_108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg(lean_object* v_x_109_, lean_object* v_h__1_110_, lean_object* v_h__2_111_){
_start:
{
lean_object* v_intZero_112_; uint8_t v_isNeg_113_; 
v_intZero_112_ = lean_obj_once(&l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0);
v_isNeg_113_ = lean_int_dec_lt(v_x_109_, v_intZero_112_);
if (v_isNeg_113_ == 0)
{
lean_object* v_a_114_; lean_object* v___x_115_; 
lean_dec(v_h__2_111_);
v_a_114_ = lean_nat_abs(v_x_109_);
v___x_115_ = lean_apply_1(v_h__1_110_, v_a_114_);
return v___x_115_;
}
else
{
lean_object* v_abs_116_; lean_object* v_one_117_; lean_object* v_a_118_; lean_object* v___x_119_; 
lean_dec(v_h__1_110_);
v_abs_116_ = lean_nat_abs(v_x_109_);
v_one_117_ = lean_unsigned_to_nat(1u);
v_a_118_ = lean_nat_sub(v_abs_116_, v_one_117_);
lean_dec(v_abs_116_);
v___x_119_ = lean_apply_1(v_h__2_111_, v_a_118_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___boxed(lean_object* v_x_120_, lean_object* v_h__1_121_, lean_object* v_h__2_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg(v_x_120_, v_h__1_121_, v_h__2_122_);
lean_dec(v_x_120_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter(lean_object* v_motive_124_, lean_object* v_x_125_, lean_object* v_h__1_126_, lean_object* v_h__2_127_){
_start:
{
lean_object* v_intZero_128_; uint8_t v_isNeg_129_; 
v_intZero_128_ = lean_obj_once(&l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0);
v_isNeg_129_ = lean_int_dec_lt(v_x_125_, v_intZero_128_);
if (v_isNeg_129_ == 0)
{
lean_object* v_a_130_; lean_object* v___x_131_; 
lean_dec(v_h__2_127_);
v_a_130_ = lean_nat_abs(v_x_125_);
v___x_131_ = lean_apply_1(v_h__1_126_, v_a_130_);
return v___x_131_;
}
else
{
lean_object* v_abs_132_; lean_object* v_one_133_; lean_object* v_a_134_; lean_object* v___x_135_; 
lean_dec(v_h__1_126_);
v_abs_132_ = lean_nat_abs(v_x_125_);
v_one_133_ = lean_unsigned_to_nat(1u);
v_a_134_ = lean_nat_sub(v_abs_132_, v_one_133_);
lean_dec(v_abs_132_);
v___x_135_ = lean_apply_1(v_h__2_127_, v_a_134_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___boxed(lean_object* v_motive_136_, lean_object* v_x_137_, lean_object* v_h__1_138_, lean_object* v_h__2_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter(v_motive_136_, v_x_137_, v_h__1_138_, v_h__2_139_);
lean_dec(v_x_137_);
return v_res_140_;
}
}
static lean_object* _init_l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_141_; lean_object* v_intZero_142_; 
v_natZero_141_ = lean_unsigned_to_nat(0u);
v_intZero_142_ = lean_nat_to_int(v_natZero_141_);
return v_intZero_142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg(lean_object* v_x_143_, lean_object* v_h__1_144_, lean_object* v_h__2_145_, lean_object* v_h__3_146_){
_start:
{
lean_object* v_natZero_147_; lean_object* v_intZero_148_; uint8_t v_isNeg_149_; 
v_natZero_147_ = lean_unsigned_to_nat(0u);
v_intZero_148_ = lean_obj_once(&l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0);
v_isNeg_149_ = lean_int_dec_lt(v_x_143_, v_intZero_148_);
if (v_isNeg_149_ == 0)
{
lean_object* v_a_150_; uint8_t v_isZero_151_; 
lean_dec(v_h__3_146_);
v_a_150_ = lean_nat_abs(v_x_143_);
v_isZero_151_ = lean_nat_dec_eq(v_a_150_, v_natZero_147_);
if (v_isZero_151_ == 1)
{
lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec(v_a_150_);
lean_dec(v_h__1_144_);
v___x_152_ = lean_box(0);
v___x_153_ = lean_apply_1(v_h__2_145_, v___x_152_);
return v___x_153_;
}
else
{
lean_object* v_one_154_; lean_object* v_n_155_; lean_object* v___x_156_; 
lean_dec(v_h__2_145_);
v_one_154_ = lean_unsigned_to_nat(1u);
v_n_155_ = lean_nat_sub(v_a_150_, v_one_154_);
lean_dec(v_a_150_);
v___x_156_ = lean_apply_1(v_h__1_144_, v_n_155_);
return v___x_156_;
}
}
else
{
lean_object* v_abs_157_; lean_object* v_one_158_; lean_object* v_a_159_; lean_object* v___x_160_; 
lean_dec(v_h__2_145_);
lean_dec(v_h__1_144_);
v_abs_157_ = lean_nat_abs(v_x_143_);
v_one_158_ = lean_unsigned_to_nat(1u);
v_a_159_ = lean_nat_sub(v_abs_157_, v_one_158_);
lean_dec(v_abs_157_);
v___x_160_ = lean_apply_1(v_h__3_146_, v_a_159_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___boxed(lean_object* v_x_161_, lean_object* v_h__1_162_, lean_object* v_h__2_163_, lean_object* v_h__3_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg(v_x_161_, v_h__1_162_, v_h__2_163_, v_h__3_164_);
lean_dec(v_x_161_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter(lean_object* v_motive_166_, lean_object* v_x_167_, lean_object* v_h__1_168_, lean_object* v_h__2_169_, lean_object* v_h__3_170_){
_start:
{
lean_object* v_natZero_171_; lean_object* v_intZero_172_; uint8_t v_isNeg_173_; 
v_natZero_171_ = lean_unsigned_to_nat(0u);
v_intZero_172_ = lean_obj_once(&l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0);
v_isNeg_173_ = lean_int_dec_lt(v_x_167_, v_intZero_172_);
if (v_isNeg_173_ == 0)
{
lean_object* v_a_174_; uint8_t v_isZero_175_; 
lean_dec(v_h__3_170_);
v_a_174_ = lean_nat_abs(v_x_167_);
v_isZero_175_ = lean_nat_dec_eq(v_a_174_, v_natZero_171_);
if (v_isZero_175_ == 1)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_dec(v_a_174_);
lean_dec(v_h__1_168_);
v___x_176_ = lean_box(0);
v___x_177_ = lean_apply_1(v_h__2_169_, v___x_176_);
return v___x_177_;
}
else
{
lean_object* v_one_178_; lean_object* v_n_179_; lean_object* v___x_180_; 
lean_dec(v_h__2_169_);
v_one_178_ = lean_unsigned_to_nat(1u);
v_n_179_ = lean_nat_sub(v_a_174_, v_one_178_);
lean_dec(v_a_174_);
v___x_180_ = lean_apply_1(v_h__1_168_, v_n_179_);
return v___x_180_;
}
}
else
{
lean_object* v_abs_181_; lean_object* v_one_182_; lean_object* v_a_183_; lean_object* v___x_184_; 
lean_dec(v_h__2_169_);
lean_dec(v_h__1_168_);
v_abs_181_ = lean_nat_abs(v_x_167_);
v_one_182_ = lean_unsigned_to_nat(1u);
v_a_183_ = lean_nat_sub(v_abs_181_, v_one_182_);
lean_dec(v_abs_181_);
v___x_184_ = lean_apply_1(v_h__3_170_, v_a_183_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___boxed(lean_object* v_motive_185_, lean_object* v_x_186_, lean_object* v_h__1_187_, lean_object* v_h__2_188_, lean_object* v_h__3_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter(v_motive_185_, v_x_186_, v_h__1_187_, v_h__2_188_, v_h__3_189_);
lean_dec(v_x_186_);
return v_res_190_;
}
}
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Int_Order(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_instTransLe = _init_l_Int_instTransLe();
l_Int_instTransLtLe = _init_l_Int_instTransLtLe();
l_Int_instTransLeLt = _init_l_Int_instTransLeLt();
l_Int_instTransLt = _init_l_Int_instTransLt();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Int_Order(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_Order(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Int_Order(builtin);
}
#ifdef __cplusplus
}
#endif
