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
lean_object* v___x_46_; 
v___x_46_ = l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg(v_m_40_, v_n_41_, v_h__1_42_, v_h__2_43_, v_h__3_44_, v_h__4_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___boxed(lean_object* v_motive_47_, lean_object* v_m_48_, lean_object* v_n_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_, lean_object* v_h__3_52_, lean_object* v_h__4_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter(v_motive_47_, v_m_48_, v_n_49_, v_h__1_50_, v_h__2_51_, v_h__3_52_, v_h__4_53_);
lean_dec(v_n_49_);
lean_dec(v_m_48_);
return v_res_54_;
}
}
static lean_object* _init_l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_55_; lean_object* v_intZero_56_; 
v_natZero_55_ = lean_unsigned_to_nat(0u);
v_intZero_56_ = lean_nat_to_int(v_natZero_55_);
return v_intZero_56_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg(lean_object* v_n_57_, lean_object* v_h__1_58_, lean_object* v_h__2_59_){
_start:
{
lean_object* v_intZero_60_; uint8_t v_isNeg_61_; 
v_intZero_60_ = lean_obj_once(&l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0);
v_isNeg_61_ = lean_int_dec_lt(v_n_57_, v_intZero_60_);
if (v_isNeg_61_ == 0)
{
lean_object* v_a_62_; lean_object* v___x_63_; 
lean_dec(v_h__2_59_);
v_a_62_ = lean_nat_abs(v_n_57_);
v___x_63_ = lean_apply_1(v_h__1_58_, v_a_62_);
return v___x_63_;
}
else
{
lean_object* v_abs_64_; lean_object* v_one_65_; lean_object* v_a_66_; lean_object* v___x_67_; 
lean_dec(v_h__1_58_);
v_abs_64_ = lean_nat_abs(v_n_57_);
v_one_65_ = lean_unsigned_to_nat(1u);
v_a_66_ = lean_nat_sub(v_abs_64_, v_one_65_);
lean_dec(v_abs_64_);
v___x_67_ = lean_apply_1(v_h__2_59_, v_a_66_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___boxed(lean_object* v_n_68_, lean_object* v_h__1_69_, lean_object* v_h__2_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg(v_n_68_, v_h__1_69_, v_h__2_70_);
lean_dec(v_n_68_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter(lean_object* v_motive_72_, lean_object* v_n_73_, lean_object* v_h__1_74_, lean_object* v_h__2_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg(v_n_73_, v_h__1_74_, v_h__2_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___boxed(lean_object* v_motive_77_, lean_object* v_n_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter(v_motive_77_, v_n_78_, v_h__1_79_, v_h__2_80_);
lean_dec(v_n_78_);
return v_res_81_;
}
}
static lean_object* _init_l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_82_; lean_object* v_intZero_83_; 
v_natZero_82_ = lean_unsigned_to_nat(0u);
v_intZero_83_ = lean_nat_to_int(v_natZero_82_);
return v_intZero_83_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg(lean_object* v_x_84_, lean_object* v_h__1_85_, lean_object* v_h__2_86_){
_start:
{
lean_object* v_intZero_87_; uint8_t v_isNeg_88_; 
v_intZero_87_ = lean_obj_once(&l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0);
v_isNeg_88_ = lean_int_dec_lt(v_x_84_, v_intZero_87_);
if (v_isNeg_88_ == 0)
{
lean_object* v_a_89_; lean_object* v___x_90_; 
lean_dec(v_h__2_86_);
v_a_89_ = lean_nat_abs(v_x_84_);
v___x_90_ = lean_apply_1(v_h__1_85_, v_a_89_);
return v___x_90_;
}
else
{
lean_object* v_abs_91_; lean_object* v_one_92_; lean_object* v_a_93_; lean_object* v___x_94_; 
lean_dec(v_h__1_85_);
v_abs_91_ = lean_nat_abs(v_x_84_);
v_one_92_ = lean_unsigned_to_nat(1u);
v_a_93_ = lean_nat_sub(v_abs_91_, v_one_92_);
lean_dec(v_abs_91_);
v___x_94_ = lean_apply_1(v_h__2_86_, v_a_93_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___boxed(lean_object* v_x_95_, lean_object* v_h__1_96_, lean_object* v_h__2_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg(v_x_95_, v_h__1_96_, v_h__2_97_);
lean_dec(v_x_95_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter(lean_object* v_motive_99_, lean_object* v_x_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg(v_x_100_, v_h__1_101_, v_h__2_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___boxed(lean_object* v_motive_104_, lean_object* v_x_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter(v_motive_104_, v_x_105_, v_h__1_106_, v_h__2_107_);
lean_dec(v_x_105_);
return v_res_108_;
}
}
static lean_object* _init_l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_109_; lean_object* v_intZero_110_; 
v_natZero_109_ = lean_unsigned_to_nat(0u);
v_intZero_110_ = lean_nat_to_int(v_natZero_109_);
return v_intZero_110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg(lean_object* v_x_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_, lean_object* v_h__3_114_){
_start:
{
lean_object* v_natZero_115_; lean_object* v_intZero_116_; uint8_t v_isNeg_117_; 
v_natZero_115_ = lean_unsigned_to_nat(0u);
v_intZero_116_ = lean_obj_once(&l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0);
v_isNeg_117_ = lean_int_dec_lt(v_x_111_, v_intZero_116_);
if (v_isNeg_117_ == 0)
{
lean_object* v_a_118_; uint8_t v_isZero_119_; 
lean_dec(v_h__3_114_);
v_a_118_ = lean_nat_abs(v_x_111_);
v_isZero_119_ = lean_nat_dec_eq(v_a_118_, v_natZero_115_);
if (v_isZero_119_ == 1)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v_a_118_);
lean_dec(v_h__1_112_);
v___x_120_ = lean_box(0);
v___x_121_ = lean_apply_1(v_h__2_113_, v___x_120_);
return v___x_121_;
}
else
{
lean_object* v_one_122_; lean_object* v_n_123_; lean_object* v___x_124_; 
lean_dec(v_h__2_113_);
v_one_122_ = lean_unsigned_to_nat(1u);
v_n_123_ = lean_nat_sub(v_a_118_, v_one_122_);
lean_dec(v_a_118_);
v___x_124_ = lean_apply_1(v_h__1_112_, v_n_123_);
return v___x_124_;
}
}
else
{
lean_object* v_abs_125_; lean_object* v_one_126_; lean_object* v_a_127_; lean_object* v___x_128_; 
lean_dec(v_h__2_113_);
lean_dec(v_h__1_112_);
v_abs_125_ = lean_nat_abs(v_x_111_);
v_one_126_ = lean_unsigned_to_nat(1u);
v_a_127_ = lean_nat_sub(v_abs_125_, v_one_126_);
lean_dec(v_abs_125_);
v___x_128_ = lean_apply_1(v_h__3_114_, v_a_127_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___boxed(lean_object* v_x_129_, lean_object* v_h__1_130_, lean_object* v_h__2_131_, lean_object* v_h__3_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg(v_x_129_, v_h__1_130_, v_h__2_131_, v_h__3_132_);
lean_dec(v_x_129_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter(lean_object* v_motive_134_, lean_object* v_x_135_, lean_object* v_h__1_136_, lean_object* v_h__2_137_, lean_object* v_h__3_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg(v_x_135_, v_h__1_136_, v_h__2_137_, v_h__3_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___boxed(lean_object* v_motive_140_, lean_object* v_x_141_, lean_object* v_h__1_142_, lean_object* v_h__2_143_, lean_object* v_h__3_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter(v_motive_140_, v_x_141_, v_h__1_142_, v_h__2_143_, v_h__3_144_);
lean_dec(v_x_141_);
return v_res_145_;
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
