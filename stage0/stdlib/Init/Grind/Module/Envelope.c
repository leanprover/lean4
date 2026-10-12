// Lean compiler output
// Module: Init.Grind.Module.Envelope
// Imports: public import Init.Grind.Ordered.Module import all Init.Data.AC import Init.Omega import Init.RCases
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
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_mk___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_mk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_nsmul___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_nsmul(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_sub___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_sub(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_add___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_add(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_neg___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_neg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_neg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zero___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zero(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_ofNatModule___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_ofNatModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_toQ___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_toQ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd___redArg();
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd___redArg();
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_mk___redArg(lean_object* v_p_1_){
_start:
{
lean_inc_ref(v_p_1_);
return v_p_1_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_mk___redArg___boxed(lean_object* v_p_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_Lean_Grind_IntModule_OfNatModule_Q_mk___redArg(v_p_2_);
lean_dec_ref(v_p_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_mk(lean_object* v_00_u03b1_4_, lean_object* v_inst_5_, lean_object* v_p_6_){
_start:
{
lean_inc_ref(v_p_6_);
return v_p_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_mk___boxed(lean_object* v_00_u03b1_7_, lean_object* v_inst_8_, lean_object* v_p_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Grind_IntModule_OfNatModule_Q_mk(v_00_u03b1_7_, v_inst_8_, v_p_9_);
lean_dec_ref(v_p_9_);
lean_dec_ref(v_inst_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082___redArg(lean_object* v_q_u2081_11_, lean_object* v_q_u2082_12_, lean_object* v_f_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_apply_2(v_f_13_, v_q_u2081_11_, v_q_u2082_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082(lean_object* v_00_u03b1_15_, lean_object* v_inst_16_, lean_object* v_00_u03b2_17_, lean_object* v_q_u2081_18_, lean_object* v_q_u2082_19_, lean_object* v_f_20_, lean_object* v_h_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_apply_2(v_f_20_, v_q_u2081_18_, v_q_u2082_19_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082___boxed(lean_object* v_00_u03b1_23_, lean_object* v_inst_24_, lean_object* v_00_u03b2_25_, lean_object* v_q_u2081_26_, lean_object* v_q_u2082_27_, lean_object* v_f_28_, lean_object* v_h_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082(v_00_u03b1_23_, v_inst_24_, v_00_u03b2_25_, v_q_u2081_26_, v_q_u2082_27_, v_f_28_, v_h_29_);
lean_dec_ref(v_inst_24_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_nsmul___redArg(lean_object* v_inst_31_, lean_object* v_n_32_, lean_object* v_q_33_){
_start:
{
lean_object* v_nsmul_34_; lean_object* v_fst_35_; lean_object* v_snd_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_45_; 
v_nsmul_34_ = lean_ctor_get(v_inst_31_, 1);
lean_inc(v_nsmul_34_);
lean_dec_ref(v_inst_31_);
v_fst_35_ = lean_ctor_get(v_q_33_, 0);
v_snd_36_ = lean_ctor_get(v_q_33_, 1);
v_isSharedCheck_45_ = !lean_is_exclusive(v_q_33_);
if (v_isSharedCheck_45_ == 0)
{
v___x_38_ = v_q_33_;
v_isShared_39_ = v_isSharedCheck_45_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_snd_36_);
lean_inc(v_fst_35_);
lean_dec(v_q_33_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_45_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_43_; 
lean_inc(v_nsmul_34_);
lean_inc(v_n_32_);
v___x_40_ = lean_apply_2(v_nsmul_34_, v_n_32_, v_fst_35_);
v___x_41_ = lean_apply_2(v_nsmul_34_, v_n_32_, v_snd_36_);
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 1, v___x_41_);
lean_ctor_set(v___x_38_, 0, v___x_40_);
v___x_43_ = v___x_38_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_40_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v___x_41_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_nsmul(lean_object* v_00_u03b1_46_, lean_object* v_inst_47_, lean_object* v_n_48_, lean_object* v_q_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Grind_IntModule_OfNatModule_nsmul___redArg(v_inst_47_, v_n_48_, v_q_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_unsigned_to_nat(0u);
v___x_52_ = lean_nat_to_int(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg(lean_object* v_inst_53_, lean_object* v_n_54_, lean_object* v_q_55_){
_start:
{
lean_object* v_nsmul_56_; lean_object* v_fst_57_; lean_object* v_snd_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_76_; 
v_nsmul_56_ = lean_ctor_get(v_inst_53_, 1);
lean_inc(v_nsmul_56_);
lean_dec_ref(v_inst_53_);
v_fst_57_ = lean_ctor_get(v_q_55_, 0);
v_snd_58_ = lean_ctor_get(v_q_55_, 1);
v_isSharedCheck_76_ = !lean_is_exclusive(v_q_55_);
if (v_isSharedCheck_76_ == 0)
{
v___x_60_ = v_q_55_;
v_isShared_61_ = v_isSharedCheck_76_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_snd_58_);
lean_inc(v_fst_57_);
lean_dec(v_q_55_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_76_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = lean_obj_once(&l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0, &l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0_once, _init_l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0);
v___x_63_ = lean_int_dec_lt(v_n_54_, v___x_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_68_; 
v___x_64_ = lean_nat_abs(v_n_54_);
lean_inc(v_nsmul_56_);
lean_inc(v___x_64_);
v___x_65_ = lean_apply_2(v_nsmul_56_, v___x_64_, v_fst_57_);
v___x_66_ = lean_apply_2(v_nsmul_56_, v___x_64_, v_snd_58_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 1, v___x_66_);
lean_ctor_set(v___x_60_, 0, v___x_65_);
v___x_68_ = v___x_60_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_65_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v___x_66_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_70_ = lean_nat_abs(v_n_54_);
lean_inc(v_nsmul_56_);
lean_inc(v___x_70_);
v___x_71_ = lean_apply_2(v_nsmul_56_, v___x_70_, v_snd_58_);
v___x_72_ = lean_apply_2(v_nsmul_56_, v___x_70_, v_fst_57_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 1, v___x_72_);
lean_ctor_set(v___x_60_, 0, v___x_71_);
v___x_74_ = v___x_60_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_71_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___boxed(lean_object* v_inst_77_, lean_object* v_n_78_, lean_object* v_q_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg(v_inst_77_, v_n_78_, v_q_79_);
lean_dec(v_n_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul(lean_object* v_00_u03b1_81_, lean_object* v_inst_82_, lean_object* v_n_83_, lean_object* v_q_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg(v_inst_82_, v_n_83_, v_q_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul___boxed(lean_object* v_00_u03b1_86_, lean_object* v_inst_87_, lean_object* v_n_88_, lean_object* v_q_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Grind_IntModule_OfNatModule_zsmul(v_00_u03b1_86_, v_inst_87_, v_n_88_, v_q_89_);
lean_dec(v_n_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_sub___redArg(lean_object* v_inst_91_, lean_object* v_q_u2081_92_, lean_object* v_q_u2082_93_){
_start:
{
lean_object* v_toAddCommMonoid_94_; lean_object* v_toAdd_95_; lean_object* v_fst_96_; lean_object* v_snd_97_; lean_object* v_fst_98_; lean_object* v_snd_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_108_; 
v_toAddCommMonoid_94_ = lean_ctor_get(v_inst_91_, 0);
lean_inc_ref(v_toAddCommMonoid_94_);
lean_dec_ref(v_inst_91_);
v_toAdd_95_ = lean_ctor_get(v_toAddCommMonoid_94_, 1);
lean_inc(v_toAdd_95_);
lean_dec_ref(v_toAddCommMonoid_94_);
v_fst_96_ = lean_ctor_get(v_q_u2081_92_, 0);
lean_inc(v_fst_96_);
v_snd_97_ = lean_ctor_get(v_q_u2081_92_, 1);
lean_inc(v_snd_97_);
lean_dec(v_q_u2081_92_);
v_fst_98_ = lean_ctor_get(v_q_u2082_93_, 0);
v_snd_99_ = lean_ctor_get(v_q_u2082_93_, 1);
v_isSharedCheck_108_ = !lean_is_exclusive(v_q_u2082_93_);
if (v_isSharedCheck_108_ == 0)
{
v___x_101_ = v_q_u2082_93_;
v_isShared_102_ = v_isSharedCheck_108_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_snd_99_);
lean_inc(v_fst_98_);
lean_dec(v_q_u2082_93_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_108_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
lean_inc(v_toAdd_95_);
v___x_103_ = lean_apply_2(v_toAdd_95_, v_fst_96_, v_snd_99_);
v___x_104_ = lean_apply_2(v_toAdd_95_, v_fst_98_, v_snd_97_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v___x_104_);
lean_ctor_set(v___x_101_, 0, v___x_103_);
v___x_106_ = v___x_101_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_sub(lean_object* v_00_u03b1_109_, lean_object* v_inst_110_, lean_object* v_q_u2081_111_, lean_object* v_q_u2082_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Grind_IntModule_OfNatModule_sub___redArg(v_inst_110_, v_q_u2081_111_, v_q_u2082_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_add___redArg(lean_object* v_inst_114_, lean_object* v_q_u2081_115_, lean_object* v_q_u2082_116_){
_start:
{
lean_object* v_toAddCommMonoid_117_; lean_object* v_toAdd_118_; lean_object* v_fst_119_; lean_object* v_snd_120_; lean_object* v_fst_121_; lean_object* v_snd_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_131_; 
v_toAddCommMonoid_117_ = lean_ctor_get(v_inst_114_, 0);
lean_inc_ref(v_toAddCommMonoid_117_);
lean_dec_ref(v_inst_114_);
v_toAdd_118_ = lean_ctor_get(v_toAddCommMonoid_117_, 1);
lean_inc(v_toAdd_118_);
lean_dec_ref(v_toAddCommMonoid_117_);
v_fst_119_ = lean_ctor_get(v_q_u2081_115_, 0);
lean_inc(v_fst_119_);
v_snd_120_ = lean_ctor_get(v_q_u2081_115_, 1);
lean_inc(v_snd_120_);
lean_dec(v_q_u2081_115_);
v_fst_121_ = lean_ctor_get(v_q_u2082_116_, 0);
v_snd_122_ = lean_ctor_get(v_q_u2082_116_, 1);
v_isSharedCheck_131_ = !lean_is_exclusive(v_q_u2082_116_);
if (v_isSharedCheck_131_ == 0)
{
v___x_124_ = v_q_u2082_116_;
v_isShared_125_ = v_isSharedCheck_131_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_snd_122_);
lean_inc(v_fst_121_);
lean_dec(v_q_u2082_116_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_131_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_129_; 
lean_inc(v_toAdd_118_);
v___x_126_ = lean_apply_2(v_toAdd_118_, v_fst_119_, v_fst_121_);
v___x_127_ = lean_apply_2(v_toAdd_118_, v_snd_120_, v_snd_122_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v___x_127_);
lean_ctor_set(v___x_124_, 0, v___x_126_);
v___x_129_ = v___x_124_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_add(lean_object* v_00_u03b1_132_, lean_object* v_inst_133_, lean_object* v_q_u2081_134_, lean_object* v_q_u2082_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Grind_IntModule_OfNatModule_add___redArg(v_inst_133_, v_q_u2081_134_, v_q_u2082_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_neg___redArg(lean_object* v_q_137_){
_start:
{
lean_object* v_fst_138_; lean_object* v_snd_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
v_fst_138_ = lean_ctor_get(v_q_137_, 0);
v_snd_139_ = lean_ctor_get(v_q_137_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_q_137_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v_q_137_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_snd_139_);
lean_inc(v_fst_138_);
lean_dec(v_q_137_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 1, v_fst_138_);
lean_ctor_set(v___x_141_, 0, v_snd_139_);
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_snd_139_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_fst_138_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_neg(lean_object* v_00_u03b1_147_, lean_object* v_inst_148_, lean_object* v_q_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Grind_IntModule_OfNatModule_neg___redArg(v_q_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_neg___boxed(lean_object* v_00_u03b1_151_, lean_object* v_inst_152_, lean_object* v_q_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Grind_IntModule_OfNatModule_neg(v_00_u03b1_151_, v_inst_152_, v_q_153_);
lean_dec_ref(v_inst_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zero___redArg(lean_object* v_inst_155_){
_start:
{
lean_object* v_toAddCommMonoid_156_; lean_object* v_toZero_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
v_toAddCommMonoid_156_ = lean_ctor_get(v_inst_155_, 0);
lean_inc_ref(v_toAddCommMonoid_156_);
lean_dec_ref(v_inst_155_);
v_toZero_157_ = lean_ctor_get(v_toAddCommMonoid_156_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v_toAddCommMonoid_156_);
if (v_isSharedCheck_164_ == 0)
{
lean_object* v_unused_165_; 
v_unused_165_ = lean_ctor_get(v_toAddCommMonoid_156_, 1);
lean_dec(v_unused_165_);
v___x_159_ = v_toAddCommMonoid_156_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_toZero_157_);
lean_dec(v_toAddCommMonoid_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
lean_inc(v_toZero_157_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v_toZero_157_);
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_toZero_157_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_toZero_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zero(lean_object* v_00_u03b1_166_, lean_object* v_inst_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_Grind_IntModule_OfNatModule_zero___redArg(v_inst_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_ofNatModule___redArg(lean_object* v_inst_169_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
lean_inc_ref_n(v_inst_169_, 5);
v___x_170_ = l_Lean_Grind_IntModule_OfNatModule_zero___redArg(v_inst_169_);
v___x_171_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_add), 4, 2);
lean_closure_set(v___x_171_, 0, lean_box(0));
lean_closure_set(v___x_171_, 1, v_inst_169_);
v___x_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_neg___boxed), 3, 2);
lean_closure_set(v___x_173_, 0, lean_box(0));
lean_closure_set(v___x_173_, 1, v_inst_169_);
v___x_174_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_sub), 4, 2);
lean_closure_set(v___x_174_, 0, lean_box(0));
lean_closure_set(v___x_174_, 1, v_inst_169_);
v___x_175_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_175_, 0, v___x_172_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
lean_ctor_set(v___x_175_, 2, v___x_174_);
v___x_176_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_nsmul), 4, 2);
lean_closure_set(v___x_176_, 0, lean_box(0));
lean_closure_set(v___x_176_, 1, v_inst_169_);
v___x_177_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_zsmul___boxed), 4, 2);
lean_closure_set(v___x_177_, 0, lean_box(0));
lean_closure_set(v___x_177_, 1, v_inst_169_);
v___x_178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_178_, 0, v___x_175_);
lean_ctor_set(v___x_178_, 1, v___x_176_);
lean_ctor_set(v___x_178_, 2, v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_ofNatModule(lean_object* v_00_u03b1_179_, lean_object* v_inst_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_Grind_IntModule_OfNatModule_ofNatModule___redArg(v_inst_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_toQ___redArg(lean_object* v_inst_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_toAddCommMonoid_184_; lean_object* v_toZero_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
v_toAddCommMonoid_184_ = lean_ctor_get(v_inst_182_, 0);
lean_inc_ref(v_toAddCommMonoid_184_);
lean_dec_ref(v_inst_182_);
v_toZero_185_ = lean_ctor_get(v_toAddCommMonoid_184_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v_toAddCommMonoid_184_);
if (v_isSharedCheck_192_ == 0)
{
lean_object* v_unused_193_; 
v_unused_193_ = lean_ctor_get(v_toAddCommMonoid_184_, 1);
lean_dec(v_unused_193_);
v___x_187_ = v_toAddCommMonoid_184_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_toZero_185_);
lean_dec(v_toAddCommMonoid_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 1, v_toZero_185_);
lean_ctor_set(v___x_187_, 0, v_a_183_);
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_183_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_toZero_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_toQ(lean_object* v_00_u03b1_194_, lean_object* v_inst_195_, lean_object* v_a_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Grind_IntModule_OfNatModule_toQ___redArg(v_inst_195_, v_a_196_);
return v___x_197_;
}
}
lean_object* l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd___redArg(){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_box(0);
return v___x_199_;
}
}
LEAN_EXPORT void l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_200_;
v_res_200_ = l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd___redArg();
stack->m_obj
 = v_res_200_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd___redArg___boxed(lean_object* v___dummy_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd___redArg();
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd(lean_object* v_00_u03b1_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_inst_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lean_box(0);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd___boxed(lean_object* v_00_u03b1_209_, lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_inst_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd(v_00_u03b1_209_, v_inst_210_, v_inst_211_, v_inst_212_, v_inst_213_);
lean_dec_ref(v_inst_210_);
return v_res_214_;
}
}
lean_object* l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd___redArg(){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_box(0);
return v___x_216_;
}
}
LEAN_EXPORT void l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_217_;
v_res_217_ = l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd___redArg();
stack->m_obj
 = v_res_217_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd___redArg___boxed(lean_object* v___dummy_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd___redArg();
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd(lean_object* v_00_u03b1_220_, lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_inst_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = lean_box(0);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd___boxed(lean_object* v_00_u03b1_226_, lean_object* v_inst_227_, lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_inst_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd(v_00_u03b1_226_, v_inst_227_, v_inst_228_, v_inst_229_, v_inst_230_);
lean_dec_ref(v_inst_227_);
return v_res_231_;
}
}
lean_object* runtime_initialize_Init_Grind_Ordered_Module(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_AC(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Module_Envelope(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Ordered_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_AC(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Module_Envelope(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ordered_Module(uint8_t builtin);
lean_object* initialize_Init_Data_AC(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Module_Envelope(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ordered_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Module_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Module_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Module_Envelope(builtin);
}
#ifdef __cplusplus
}
#endif
