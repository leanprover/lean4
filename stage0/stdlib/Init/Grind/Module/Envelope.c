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
lean_object* v_fst_74_; lean_object* v_snd_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_95_; 
v_fst_74_ = lean_ctor_get(v_q_73_, 0);
v_snd_75_ = lean_ctor_get(v_q_73_, 1);
v_isSharedCheck_95_ = !lean_is_exclusive(v_q_73_);
if (v_isSharedCheck_95_ == 0)
{
v___x_77_ = v_q_73_;
v_isShared_78_ = v_isSharedCheck_95_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_snd_75_);
lean_inc(v_fst_74_);
lean_dec(v_q_73_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_95_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_obj_once(&l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0, &l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0_once, _init_l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0);
v___x_80_ = lean_int_dec_lt(v_n_72_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v_nsmul_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v_nsmul_81_ = lean_ctor_get(v_inst_71_, 1);
lean_inc(v_nsmul_81_);
lean_dec_ref(v_inst_71_);
v___x_82_ = lean_nat_abs(v_n_72_);
lean_inc(v_nsmul_81_);
lean_inc(v___x_82_);
v___x_83_ = lean_apply_2(v_nsmul_81_, v___x_82_, v_fst_74_);
v___x_84_ = lean_apply_2(v_nsmul_81_, v___x_82_, v_snd_75_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 1, v___x_84_);
lean_ctor_set(v___x_77_, 0, v___x_83_);
v___x_86_ = v___x_77_;
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
lean_object* v_nsmul_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v_nsmul_88_ = lean_ctor_get(v_inst_71_, 1);
lean_inc(v_nsmul_88_);
lean_dec_ref(v_inst_71_);
v___x_89_ = lean_nat_abs(v_n_72_);
lean_inc(v_nsmul_88_);
lean_inc(v___x_89_);
v___x_90_ = lean_apply_2(v_nsmul_88_, v___x_89_, v_snd_75_);
v___x_91_ = lean_apply_2(v_nsmul_88_, v___x_89_, v_fst_74_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 1, v___x_91_);
lean_ctor_set(v___x_77_, 0, v___x_90_);
v___x_93_ = v___x_77_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_90_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___boxed(lean_object* v_inst_96_, lean_object* v_n_97_, lean_object* v_q_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg(v_inst_96_, v_n_97_, v_q_98_);
lean_dec(v_n_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul(lean_object* v_00_u03b1_100_, lean_object* v_inst_101_, lean_object* v_n_102_, lean_object* v_q_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg(v_inst_101_, v_n_102_, v_q_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul___boxed(lean_object* v_00_u03b1_105_, lean_object* v_inst_106_, lean_object* v_n_107_, lean_object* v_q_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_Grind_IntModule_OfNatModule_zsmul(v_00_u03b1_105_, v_inst_106_, v_n_107_, v_q_108_);
lean_dec(v_n_107_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_sub___redArg(lean_object* v_inst_110_, lean_object* v_q_u2081_111_, lean_object* v_q_u2082_112_){
_start:
{
lean_object* v_toAddCommMonoid_113_; lean_object* v_toAdd_114_; lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v_fst_117_; lean_object* v_snd_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_127_; 
v_toAddCommMonoid_113_ = lean_ctor_get(v_inst_110_, 0);
lean_inc_ref(v_toAddCommMonoid_113_);
lean_dec_ref(v_inst_110_);
v_toAdd_114_ = lean_ctor_get(v_toAddCommMonoid_113_, 1);
lean_inc(v_toAdd_114_);
lean_dec_ref(v_toAddCommMonoid_113_);
v_fst_115_ = lean_ctor_get(v_q_u2081_111_, 0);
lean_inc(v_fst_115_);
v_snd_116_ = lean_ctor_get(v_q_u2081_111_, 1);
lean_inc(v_snd_116_);
lean_dec(v_q_u2081_111_);
v_fst_117_ = lean_ctor_get(v_q_u2082_112_, 0);
v_snd_118_ = lean_ctor_get(v_q_u2082_112_, 1);
v_isSharedCheck_127_ = !lean_is_exclusive(v_q_u2082_112_);
if (v_isSharedCheck_127_ == 0)
{
v___x_120_ = v_q_u2082_112_;
v_isShared_121_ = v_isSharedCheck_127_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_snd_118_);
lean_inc(v_fst_117_);
lean_dec(v_q_u2082_112_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_127_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_125_; 
lean_inc(v_toAdd_114_);
v___x_122_ = lean_apply_2(v_toAdd_114_, v_fst_115_, v_snd_118_);
v___x_123_ = lean_apply_2(v_toAdd_114_, v_fst_117_, v_snd_116_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v___x_123_);
lean_ctor_set(v___x_120_, 0, v___x_122_);
v___x_125_ = v___x_120_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v___x_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_sub(lean_object* v_00_u03b1_128_, lean_object* v_inst_129_, lean_object* v_q_u2081_130_, lean_object* v_q_u2082_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_Grind_IntModule_OfNatModule_sub___redArg(v_inst_129_, v_q_u2081_130_, v_q_u2082_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_add___redArg(lean_object* v_inst_133_, lean_object* v_q_u2081_134_, lean_object* v_q_u2082_135_){
_start:
{
lean_object* v_toAddCommMonoid_136_; lean_object* v_toAdd_137_; lean_object* v_fst_138_; lean_object* v_snd_139_; lean_object* v_fst_140_; lean_object* v_snd_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_150_; 
v_toAddCommMonoid_136_ = lean_ctor_get(v_inst_133_, 0);
lean_inc_ref(v_toAddCommMonoid_136_);
lean_dec_ref(v_inst_133_);
v_toAdd_137_ = lean_ctor_get(v_toAddCommMonoid_136_, 1);
lean_inc(v_toAdd_137_);
lean_dec_ref(v_toAddCommMonoid_136_);
v_fst_138_ = lean_ctor_get(v_q_u2081_134_, 0);
lean_inc(v_fst_138_);
v_snd_139_ = lean_ctor_get(v_q_u2081_134_, 1);
lean_inc(v_snd_139_);
lean_dec(v_q_u2081_134_);
v_fst_140_ = lean_ctor_get(v_q_u2082_135_, 0);
v_snd_141_ = lean_ctor_get(v_q_u2082_135_, 1);
v_isSharedCheck_150_ = !lean_is_exclusive(v_q_u2082_135_);
if (v_isSharedCheck_150_ == 0)
{
v___x_143_ = v_q_u2082_135_;
v_isShared_144_ = v_isSharedCheck_150_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_snd_141_);
lean_inc(v_fst_140_);
lean_dec(v_q_u2082_135_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_150_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_148_; 
lean_inc(v_toAdd_137_);
v___x_145_ = lean_apply_2(v_toAdd_137_, v_fst_138_, v_fst_140_);
v___x_146_ = lean_apply_2(v_toAdd_137_, v_snd_139_, v_snd_141_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 1, v___x_146_);
lean_ctor_set(v___x_143_, 0, v___x_145_);
v___x_148_ = v___x_143_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_145_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v___x_146_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_add(lean_object* v_00_u03b1_151_, lean_object* v_inst_152_, lean_object* v_q_u2081_153_, lean_object* v_q_u2082_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Grind_IntModule_OfNatModule_add___redArg(v_inst_152_, v_q_u2081_153_, v_q_u2082_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_neg___redArg(lean_object* v_q_156_){
_start:
{
lean_object* v_fst_157_; lean_object* v_snd_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
v_fst_157_ = lean_ctor_get(v_q_156_, 0);
v_snd_158_ = lean_ctor_get(v_q_156_, 1);
v_isSharedCheck_165_ = !lean_is_exclusive(v_q_156_);
if (v_isSharedCheck_165_ == 0)
{
v___x_160_ = v_q_156_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_snd_158_);
lean_inc(v_fst_157_);
lean_dec(v_q_156_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v_fst_157_);
lean_ctor_set(v___x_160_, 0, v_snd_158_);
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_snd_158_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_fst_157_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_neg(lean_object* v_00_u03b1_166_, lean_object* v_inst_167_, lean_object* v_q_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Grind_IntModule_OfNatModule_neg___redArg(v_q_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_neg___boxed(lean_object* v_00_u03b1_170_, lean_object* v_inst_171_, lean_object* v_q_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Grind_IntModule_OfNatModule_neg(v_00_u03b1_170_, v_inst_171_, v_q_172_);
lean_dec_ref(v_inst_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zero___redArg(lean_object* v_inst_174_){
_start:
{
lean_object* v_toAddCommMonoid_175_; lean_object* v_toZero_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
v_toAddCommMonoid_175_ = lean_ctor_get(v_inst_174_, 0);
lean_inc_ref(v_toAddCommMonoid_175_);
lean_dec_ref(v_inst_174_);
v_toZero_176_ = lean_ctor_get(v_toAddCommMonoid_175_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v_toAddCommMonoid_175_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v_toAddCommMonoid_175_, 1);
lean_dec(v_unused_184_);
v___x_178_ = v_toAddCommMonoid_175_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_toZero_176_);
lean_dec(v_toAddCommMonoid_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
lean_inc(v_toZero_176_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v_toZero_176_);
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_toZero_176_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_toZero_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zero(lean_object* v_00_u03b1_185_, lean_object* v_inst_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Grind_IntModule_OfNatModule_zero___redArg(v_inst_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_ofNatModule___redArg(lean_object* v_inst_188_){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
lean_inc_ref(v_inst_188_);
v___x_189_ = l_Lean_Grind_IntModule_OfNatModule_zero___redArg(v_inst_188_);
lean_inc_ref(v_inst_188_);
v___x_190_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_add), 4, 2);
lean_closure_set(v___x_190_, 0, lean_box(0));
lean_closure_set(v___x_190_, 1, v_inst_188_);
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_189_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
lean_inc_ref(v_inst_188_);
v___x_192_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_neg___boxed), 3, 2);
lean_closure_set(v___x_192_, 0, lean_box(0));
lean_closure_set(v___x_192_, 1, v_inst_188_);
lean_inc_ref(v_inst_188_);
v___x_193_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_sub), 4, 2);
lean_closure_set(v___x_193_, 0, lean_box(0));
lean_closure_set(v___x_193_, 1, v_inst_188_);
v___x_194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_194_, 0, v___x_191_);
lean_ctor_set(v___x_194_, 1, v___x_192_);
lean_ctor_set(v___x_194_, 2, v___x_193_);
lean_inc_ref(v_inst_188_);
v___x_195_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_nsmul), 4, 2);
lean_closure_set(v___x_195_, 0, lean_box(0));
lean_closure_set(v___x_195_, 1, v_inst_188_);
v___x_196_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_zsmul___boxed), 4, 2);
lean_closure_set(v___x_196_, 0, lean_box(0));
lean_closure_set(v___x_196_, 1, v_inst_188_);
v___x_197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_197_, 0, v___x_194_);
lean_ctor_set(v___x_197_, 1, v___x_195_);
lean_ctor_set(v___x_197_, 2, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_ofNatModule(lean_object* v_00_u03b1_198_, lean_object* v_inst_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Grind_IntModule_OfNatModule_ofNatModule___redArg(v_inst_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_toQ___redArg(lean_object* v_inst_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_toAddCommMonoid_203_; lean_object* v_toZero_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
v_toAddCommMonoid_203_ = lean_ctor_get(v_inst_201_, 0);
lean_inc_ref(v_toAddCommMonoid_203_);
lean_dec_ref(v_inst_201_);
v_toZero_204_ = lean_ctor_get(v_toAddCommMonoid_203_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v_toAddCommMonoid_203_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v_toAddCommMonoid_203_, 1);
lean_dec(v_unused_212_);
v___x_206_ = v_toAddCommMonoid_203_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_toZero_204_);
lean_dec(v_toAddCommMonoid_203_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 1, v_toZero_204_);
lean_ctor_set(v___x_206_, 0, v_a_202_);
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_202_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_toZero_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_toQ(lean_object* v_00_u03b1_213_, lean_object* v_inst_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Grind_IntModule_OfNatModule_toQ___redArg(v_inst_214_, v_a_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd(lean_object* v_00_u03b1_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_inst_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_box(0);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd___boxed(lean_object* v_00_u03b1_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_inst_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd(v_00_u03b1_223_, v_inst_224_, v_inst_225_, v_inst_226_, v_inst_227_);
lean_dec_ref(v_inst_224_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd(lean_object* v_00_u03b1_229_, lean_object* v_inst_230_, lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_inst_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_box(0);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd___boxed(lean_object* v_00_u03b1_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_inst_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd(v_00_u03b1_235_, v_inst_236_, v_inst_237_, v_inst_238_, v_inst_239_);
lean_dec_ref(v_inst_236_);
return v_res_240_;
}
}
lean_object* runtime_initialize_Init_Grind_Ordered_Module(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_AC(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Module_Envelope(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
