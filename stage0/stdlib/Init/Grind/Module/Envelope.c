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
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_Envelope_0__Lean_Grind_IntModule_OfNatModule_r_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_Envelope_0__Lean_Grind_IntModule_OfNatModule_r_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_Envelope_0__Lean_Grind_IntModule_OfNatModule_r_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_){
_start:
{
lean_object* v_fst_4_; lean_object* v_snd_5_; lean_object* v_fst_6_; lean_object* v_snd_7_; lean_object* v___x_8_; 
v_fst_4_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_fst_4_);
v_snd_5_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_snd_5_);
lean_dec_ref(v_x_1_);
v_fst_6_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_fst_6_);
v_snd_7_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_snd_7_);
lean_dec_ref(v_x_2_);
v___x_8_ = lean_apply_4(v_h__1_3_, v_fst_4_, v_snd_5_, v_fst_6_, v_snd_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_Envelope_0__Lean_Grind_IntModule_OfNatModule_r_match__1_splitter(lean_object* v_00_u03b1_9_, lean_object* v_motive_10_, lean_object* v_x_11_, lean_object* v_x_12_, lean_object* v_h__1_13_){
_start:
{
lean_object* v_fst_14_; lean_object* v_snd_15_; lean_object* v_fst_16_; lean_object* v_snd_17_; lean_object* v___x_18_; 
v_fst_14_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_fst_14_);
v_snd_15_ = lean_ctor_get(v_x_11_, 1);
lean_inc(v_snd_15_);
lean_dec_ref(v_x_11_);
v_fst_16_ = lean_ctor_get(v_x_12_, 0);
lean_inc(v_fst_16_);
v_snd_17_ = lean_ctor_get(v_x_12_, 1);
lean_inc(v_snd_17_);
lean_dec_ref(v_x_12_);
v___x_18_ = lean_apply_4(v_h__1_13_, v_fst_14_, v_snd_15_, v_fst_16_, v_snd_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_mk___redArg(lean_object* v_p_19_){
_start:
{
lean_inc_ref(v_p_19_);
return v_p_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_mk___redArg___boxed(lean_object* v_p_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Grind_IntModule_OfNatModule_Q_mk___redArg(v_p_20_);
lean_dec_ref(v_p_20_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_mk(lean_object* v_00_u03b1_22_, lean_object* v_inst_23_, lean_object* v_p_24_){
_start:
{
lean_inc_ref(v_p_24_);
return v_p_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_mk___boxed(lean_object* v_00_u03b1_25_, lean_object* v_inst_26_, lean_object* v_p_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Grind_IntModule_OfNatModule_Q_mk(v_00_u03b1_25_, v_inst_26_, v_p_27_);
lean_dec_ref(v_p_27_);
lean_dec_ref(v_inst_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082___redArg(lean_object* v_q_u2081_29_, lean_object* v_q_u2082_30_, lean_object* v_f_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_apply_2(v_f_31_, v_q_u2081_29_, v_q_u2082_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082(lean_object* v_00_u03b1_33_, lean_object* v_inst_34_, lean_object* v_00_u03b2_35_, lean_object* v_q_u2081_36_, lean_object* v_q_u2082_37_, lean_object* v_f_38_, lean_object* v_h_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_apply_2(v_f_38_, v_q_u2081_36_, v_q_u2082_37_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082___boxed(lean_object* v_00_u03b1_41_, lean_object* v_inst_42_, lean_object* v_00_u03b2_43_, lean_object* v_q_u2081_44_, lean_object* v_q_u2082_45_, lean_object* v_f_46_, lean_object* v_h_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082(v_00_u03b1_41_, v_inst_42_, v_00_u03b2_43_, v_q_u2081_44_, v_q_u2082_45_, v_f_46_, v_h_47_);
lean_dec_ref(v_inst_42_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_nsmul___redArg(lean_object* v_inst_49_, lean_object* v_n_50_, lean_object* v_q_51_){
_start:
{
lean_object* v_nsmul_52_; lean_object* v_fst_53_; lean_object* v_snd_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_63_; 
v_nsmul_52_ = lean_ctor_get(v_inst_49_, 1);
lean_inc(v_nsmul_52_);
lean_dec_ref(v_inst_49_);
v_fst_53_ = lean_ctor_get(v_q_51_, 0);
v_snd_54_ = lean_ctor_get(v_q_51_, 1);
v_isSharedCheck_63_ = !lean_is_exclusive(v_q_51_);
if (v_isSharedCheck_63_ == 0)
{
v___x_56_ = v_q_51_;
v_isShared_57_ = v_isSharedCheck_63_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_snd_54_);
lean_inc(v_fst_53_);
lean_dec(v_q_51_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_63_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_61_; 
lean_inc(v_nsmul_52_);
lean_inc(v_n_50_);
v___x_58_ = lean_apply_2(v_nsmul_52_, v_n_50_, v_fst_53_);
v___x_59_ = lean_apply_2(v_nsmul_52_, v_n_50_, v_snd_54_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 1, v___x_59_);
lean_ctor_set(v___x_56_, 0, v___x_58_);
v___x_61_ = v___x_56_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v___x_59_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_nsmul(lean_object* v_00_u03b1_64_, lean_object* v_inst_65_, lean_object* v_n_66_, lean_object* v_q_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Grind_IntModule_OfNatModule_nsmul___redArg(v_inst_65_, v_n_66_, v_q_67_);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_nat_to_int(v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg(lean_object* v_inst_71_, lean_object* v_n_72_, lean_object* v_q_73_){
_start:
{
lean_object* v_nsmul_74_; lean_object* v_fst_75_; lean_object* v_snd_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_94_; 
v_nsmul_74_ = lean_ctor_get(v_inst_71_, 1);
lean_inc(v_nsmul_74_);
lean_dec_ref(v_inst_71_);
v_fst_75_ = lean_ctor_get(v_q_73_, 0);
v_snd_76_ = lean_ctor_get(v_q_73_, 1);
v_isSharedCheck_94_ = !lean_is_exclusive(v_q_73_);
if (v_isSharedCheck_94_ == 0)
{
v___x_78_ = v_q_73_;
v_isShared_79_ = v_isSharedCheck_94_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_snd_76_);
lean_inc(v_fst_75_);
lean_dec(v_q_73_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_94_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_80_ = lean_obj_once(&l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0, &l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0_once, _init_l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0);
v___x_81_ = lean_int_dec_lt(v_n_72_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_82_ = lean_nat_abs(v_n_72_);
lean_inc(v_nsmul_74_);
lean_inc(v___x_82_);
v___x_83_ = lean_apply_2(v_nsmul_74_, v___x_82_, v_fst_75_);
v___x_84_ = lean_apply_2(v_nsmul_74_, v___x_82_, v_snd_76_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v___x_84_);
lean_ctor_set(v___x_78_, 0, v___x_83_);
v___x_86_ = v___x_78_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_83_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v___x_84_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
else
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_92_; 
v___x_88_ = lean_nat_abs(v_n_72_);
lean_inc(v_nsmul_74_);
lean_inc(v___x_88_);
v___x_89_ = lean_apply_2(v_nsmul_74_, v___x_88_, v_snd_76_);
v___x_90_ = lean_apply_2(v_nsmul_74_, v___x_88_, v_fst_75_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v___x_90_);
lean_ctor_set(v___x_78_, 0, v___x_89_);
v___x_92_ = v___x_78_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_89_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v___x_90_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___boxed(lean_object* v_inst_95_, lean_object* v_n_96_, lean_object* v_q_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg(v_inst_95_, v_n_96_, v_q_97_);
lean_dec(v_n_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul(lean_object* v_00_u03b1_99_, lean_object* v_inst_100_, lean_object* v_n_101_, lean_object* v_q_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg(v_inst_100_, v_n_101_, v_q_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul___boxed(lean_object* v_00_u03b1_104_, lean_object* v_inst_105_, lean_object* v_n_106_, lean_object* v_q_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Grind_IntModule_OfNatModule_zsmul(v_00_u03b1_104_, v_inst_105_, v_n_106_, v_q_107_);
lean_dec(v_n_106_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_sub___redArg(lean_object* v_inst_109_, lean_object* v_q_u2081_110_, lean_object* v_q_u2082_111_){
_start:
{
lean_object* v_toAddCommMonoid_112_; lean_object* v_toAdd_113_; lean_object* v_fst_114_; lean_object* v_snd_115_; lean_object* v_fst_116_; lean_object* v_snd_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_126_; 
v_toAddCommMonoid_112_ = lean_ctor_get(v_inst_109_, 0);
lean_inc_ref(v_toAddCommMonoid_112_);
lean_dec_ref(v_inst_109_);
v_toAdd_113_ = lean_ctor_get(v_toAddCommMonoid_112_, 1);
lean_inc(v_toAdd_113_);
lean_dec_ref(v_toAddCommMonoid_112_);
v_fst_114_ = lean_ctor_get(v_q_u2081_110_, 0);
lean_inc(v_fst_114_);
v_snd_115_ = lean_ctor_get(v_q_u2081_110_, 1);
lean_inc(v_snd_115_);
lean_dec(v_q_u2081_110_);
v_fst_116_ = lean_ctor_get(v_q_u2082_111_, 0);
v_snd_117_ = lean_ctor_get(v_q_u2082_111_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v_q_u2082_111_);
if (v_isSharedCheck_126_ == 0)
{
v___x_119_ = v_q_u2082_111_;
v_isShared_120_ = v_isSharedCheck_126_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_snd_117_);
lean_inc(v_fst_116_);
lean_dec(v_q_u2082_111_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_126_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
lean_inc(v_toAdd_113_);
v___x_121_ = lean_apply_2(v_toAdd_113_, v_fst_114_, v_snd_117_);
v___x_122_ = lean_apply_2(v_toAdd_113_, v_fst_116_, v_snd_115_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 1, v___x_122_);
lean_ctor_set(v___x_119_, 0, v___x_121_);
v___x_124_ = v___x_119_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_sub(lean_object* v_00_u03b1_127_, lean_object* v_inst_128_, lean_object* v_q_u2081_129_, lean_object* v_q_u2082_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_Grind_IntModule_OfNatModule_sub___redArg(v_inst_128_, v_q_u2081_129_, v_q_u2082_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_add___redArg(lean_object* v_inst_132_, lean_object* v_q_u2081_133_, lean_object* v_q_u2082_134_){
_start:
{
lean_object* v_toAddCommMonoid_135_; lean_object* v_toAdd_136_; lean_object* v_fst_137_; lean_object* v_snd_138_; lean_object* v_fst_139_; lean_object* v_snd_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_149_; 
v_toAddCommMonoid_135_ = lean_ctor_get(v_inst_132_, 0);
lean_inc_ref(v_toAddCommMonoid_135_);
lean_dec_ref(v_inst_132_);
v_toAdd_136_ = lean_ctor_get(v_toAddCommMonoid_135_, 1);
lean_inc(v_toAdd_136_);
lean_dec_ref(v_toAddCommMonoid_135_);
v_fst_137_ = lean_ctor_get(v_q_u2081_133_, 0);
lean_inc(v_fst_137_);
v_snd_138_ = lean_ctor_get(v_q_u2081_133_, 1);
lean_inc(v_snd_138_);
lean_dec(v_q_u2081_133_);
v_fst_139_ = lean_ctor_get(v_q_u2082_134_, 0);
v_snd_140_ = lean_ctor_get(v_q_u2082_134_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_q_u2082_134_);
if (v_isSharedCheck_149_ == 0)
{
v___x_142_ = v_q_u2082_134_;
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_snd_140_);
lean_inc(v_fst_139_);
lean_dec(v_q_u2082_134_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
lean_inc(v_toAdd_136_);
v___x_144_ = lean_apply_2(v_toAdd_136_, v_fst_137_, v_fst_139_);
v___x_145_ = lean_apply_2(v_toAdd_136_, v_snd_138_, v_snd_140_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 1, v___x_145_);
lean_ctor_set(v___x_142_, 0, v___x_144_);
v___x_147_ = v___x_142_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_add(lean_object* v_00_u03b1_150_, lean_object* v_inst_151_, lean_object* v_q_u2081_152_, lean_object* v_q_u2082_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Grind_IntModule_OfNatModule_add___redArg(v_inst_151_, v_q_u2081_152_, v_q_u2082_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_neg___redArg(lean_object* v_q_155_){
_start:
{
lean_object* v_fst_156_; lean_object* v_snd_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
v_fst_156_ = lean_ctor_get(v_q_155_, 0);
v_snd_157_ = lean_ctor_get(v_q_155_, 1);
v_isSharedCheck_164_ = !lean_is_exclusive(v_q_155_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v_q_155_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_snd_157_);
lean_inc(v_fst_156_);
lean_dec(v_q_155_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v_fst_156_);
lean_ctor_set(v___x_159_, 0, v_snd_157_);
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_snd_157_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_fst_156_);
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
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_neg(lean_object* v_00_u03b1_165_, lean_object* v_inst_166_, lean_object* v_q_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_Grind_IntModule_OfNatModule_neg___redArg(v_q_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_neg___boxed(lean_object* v_00_u03b1_169_, lean_object* v_inst_170_, lean_object* v_q_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_Grind_IntModule_OfNatModule_neg(v_00_u03b1_169_, v_inst_170_, v_q_171_);
lean_dec_ref(v_inst_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zero___redArg(lean_object* v_inst_173_){
_start:
{
lean_object* v_toAddCommMonoid_174_; lean_object* v_toZero_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
v_toAddCommMonoid_174_ = lean_ctor_get(v_inst_173_, 0);
lean_inc_ref(v_toAddCommMonoid_174_);
lean_dec_ref(v_inst_173_);
v_toZero_175_ = lean_ctor_get(v_toAddCommMonoid_174_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v_toAddCommMonoid_174_);
if (v_isSharedCheck_182_ == 0)
{
lean_object* v_unused_183_; 
v_unused_183_ = lean_ctor_get(v_toAddCommMonoid_174_, 1);
lean_dec(v_unused_183_);
v___x_177_ = v_toAddCommMonoid_174_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_toZero_175_);
lean_dec(v_toAddCommMonoid_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
lean_inc(v_toZero_175_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v_toZero_175_);
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_toZero_175_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_toZero_175_);
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
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zero(lean_object* v_00_u03b1_184_, lean_object* v_inst_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Grind_IntModule_OfNatModule_zero___redArg(v_inst_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_ofNatModule___redArg(lean_object* v_inst_187_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
lean_inc_ref_n(v_inst_187_, 5);
v___x_188_ = l_Lean_Grind_IntModule_OfNatModule_zero___redArg(v_inst_187_);
v___x_189_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_add), 4, 2);
lean_closure_set(v___x_189_, 0, lean_box(0));
lean_closure_set(v___x_189_, 1, v_inst_187_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_188_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_neg___boxed), 3, 2);
lean_closure_set(v___x_191_, 0, lean_box(0));
lean_closure_set(v___x_191_, 1, v_inst_187_);
v___x_192_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_sub), 4, 2);
lean_closure_set(v___x_192_, 0, lean_box(0));
lean_closure_set(v___x_192_, 1, v_inst_187_);
v___x_193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_193_, 0, v___x_190_);
lean_ctor_set(v___x_193_, 1, v___x_191_);
lean_ctor_set(v___x_193_, 2, v___x_192_);
v___x_194_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_nsmul), 4, 2);
lean_closure_set(v___x_194_, 0, lean_box(0));
lean_closure_set(v___x_194_, 1, v_inst_187_);
v___x_195_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_zsmul___boxed), 4, 2);
lean_closure_set(v___x_195_, 0, lean_box(0));
lean_closure_set(v___x_195_, 1, v_inst_187_);
v___x_196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_196_, 0, v___x_193_);
lean_ctor_set(v___x_196_, 1, v___x_194_);
lean_ctor_set(v___x_196_, 2, v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_ofNatModule(lean_object* v_00_u03b1_197_, lean_object* v_inst_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Grind_IntModule_OfNatModule_ofNatModule___redArg(v_inst_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_toQ___redArg(lean_object* v_inst_200_, lean_object* v_a_201_){
_start:
{
lean_object* v_toAddCommMonoid_202_; lean_object* v_toZero_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
v_toAddCommMonoid_202_ = lean_ctor_get(v_inst_200_, 0);
lean_inc_ref(v_toAddCommMonoid_202_);
lean_dec_ref(v_inst_200_);
v_toZero_203_ = lean_ctor_get(v_toAddCommMonoid_202_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v_toAddCommMonoid_202_);
if (v_isSharedCheck_210_ == 0)
{
lean_object* v_unused_211_; 
v_unused_211_ = lean_ctor_get(v_toAddCommMonoid_202_, 1);
lean_dec(v_unused_211_);
v___x_205_ = v_toAddCommMonoid_202_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_toZero_203_);
lean_dec(v_toAddCommMonoid_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v_toZero_203_);
lean_ctor_set(v___x_205_, 0, v_a_201_);
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_201_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_toZero_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_toQ(lean_object* v_00_u03b1_212_, lean_object* v_inst_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_Grind_IntModule_OfNatModule_toQ___redArg(v_inst_213_, v_a_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd(lean_object* v_00_u03b1_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_inst_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_box(0);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd___boxed(lean_object* v_00_u03b1_222_, lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_inst_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd(v_00_u03b1_222_, v_inst_223_, v_inst_224_, v_inst_225_, v_inst_226_);
lean_dec_ref(v_inst_223_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd(lean_object* v_00_u03b1_228_, lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v_inst_231_, lean_object* v_inst_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_box(0);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd___boxed(lean_object* v_00_u03b1_234_, lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_inst_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd(v_00_u03b1_234_, v_inst_235_, v_inst_236_, v_inst_237_, v_inst_238_);
lean_dec_ref(v_inst_235_);
return v_res_239_;
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
