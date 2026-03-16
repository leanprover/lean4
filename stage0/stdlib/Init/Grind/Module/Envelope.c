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
lean_object* v___x_14_; 
v___x_14_ = l___private_Init_Grind_Module_Envelope_0__Lean_Grind_IntModule_OfNatModule_r_match__1_splitter___redArg(v_x_11_, v_x_12_, v_h__1_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_mk___redArg(lean_object* v_p_15_){
_start:
{
lean_inc_ref(v_p_15_);
return v_p_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_mk___redArg___boxed(lean_object* v_p_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_Grind_IntModule_OfNatModule_Q_mk___redArg(v_p_16_);
lean_dec_ref(v_p_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_mk(lean_object* v_00_u03b1_18_, lean_object* v_inst_19_, lean_object* v_p_20_){
_start:
{
lean_inc_ref(v_p_20_);
return v_p_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_mk___boxed(lean_object* v_00_u03b1_21_, lean_object* v_inst_22_, lean_object* v_p_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Grind_IntModule_OfNatModule_Q_mk(v_00_u03b1_21_, v_inst_22_, v_p_23_);
lean_dec_ref(v_p_23_);
lean_dec_ref(v_inst_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082___redArg(lean_object* v_q_u2081_25_, lean_object* v_q_u2082_26_, lean_object* v_f_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_apply_2(v_f_27_, v_q_u2081_25_, v_q_u2082_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082(lean_object* v_00_u03b1_29_, lean_object* v_inst_30_, lean_object* v_00_u03b2_31_, lean_object* v_q_u2081_32_, lean_object* v_q_u2082_33_, lean_object* v_f_34_, lean_object* v_h_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_apply_2(v_f_34_, v_q_u2081_32_, v_q_u2082_33_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082___boxed(lean_object* v_00_u03b1_37_, lean_object* v_inst_38_, lean_object* v_00_u03b2_39_, lean_object* v_q_u2081_40_, lean_object* v_q_u2082_41_, lean_object* v_f_42_, lean_object* v_h_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082(v_00_u03b1_37_, v_inst_38_, v_00_u03b2_39_, v_q_u2081_40_, v_q_u2082_41_, v_f_42_, v_h_43_);
lean_dec_ref(v_inst_38_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_nsmul___redArg(lean_object* v_inst_45_, lean_object* v_n_46_, lean_object* v_q_47_){
_start:
{
lean_object* v_nsmul_48_; lean_object* v_fst_49_; lean_object* v_snd_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_59_; 
v_nsmul_48_ = lean_ctor_get(v_inst_45_, 1);
lean_inc(v_nsmul_48_);
lean_dec_ref(v_inst_45_);
v_fst_49_ = lean_ctor_get(v_q_47_, 0);
v_snd_50_ = lean_ctor_get(v_q_47_, 1);
v_isSharedCheck_59_ = !lean_is_exclusive(v_q_47_);
if (v_isSharedCheck_59_ == 0)
{
v___x_52_ = v_q_47_;
v_isShared_53_ = v_isSharedCheck_59_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_snd_50_);
lean_inc(v_fst_49_);
lean_dec(v_q_47_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_59_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_57_; 
lean_inc(v_nsmul_48_);
lean_inc(v_n_46_);
v___x_54_ = lean_apply_2(v_nsmul_48_, v_n_46_, v_fst_49_);
v___x_55_ = lean_apply_2(v_nsmul_48_, v_n_46_, v_snd_50_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 1, v___x_55_);
lean_ctor_set(v___x_52_, 0, v___x_54_);
v___x_57_ = v___x_52_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_54_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v___x_55_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_nsmul(lean_object* v_00_u03b1_60_, lean_object* v_inst_61_, lean_object* v_n_62_, lean_object* v_q_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Grind_IntModule_OfNatModule_nsmul___redArg(v_inst_61_, v_n_62_, v_q_63_);
return v___x_64_;
}
}
static lean_object* _init_l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = lean_nat_to_int(v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg(lean_object* v_inst_67_, lean_object* v_n_68_, lean_object* v_q_69_){
_start:
{
lean_object* v_fst_70_; lean_object* v_snd_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_91_; 
v_fst_70_ = lean_ctor_get(v_q_69_, 0);
v_snd_71_ = lean_ctor_get(v_q_69_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v_q_69_);
if (v_isSharedCheck_91_ == 0)
{
v___x_73_ = v_q_69_;
v_isShared_74_ = v_isSharedCheck_91_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_snd_71_);
lean_inc(v_fst_70_);
lean_dec(v_q_69_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_91_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = lean_obj_once(&l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0, &l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0_once, _init_l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0);
v___x_76_ = lean_int_dec_lt(v_n_68_, v___x_75_);
if (v___x_76_ == 0)
{
lean_object* v_nsmul_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_82_; 
v_nsmul_77_ = lean_ctor_get(v_inst_67_, 1);
lean_inc(v_nsmul_77_);
lean_dec_ref(v_inst_67_);
v___x_78_ = lean_nat_abs(v_n_68_);
lean_inc(v_nsmul_77_);
lean_inc(v___x_78_);
v___x_79_ = lean_apply_2(v_nsmul_77_, v___x_78_, v_fst_70_);
v___x_80_ = lean_apply_2(v_nsmul_77_, v___x_78_, v_snd_71_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v___x_80_);
lean_ctor_set(v___x_73_, 0, v___x_79_);
v___x_82_ = v___x_73_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
else
{
lean_object* v_nsmul_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_89_; 
v_nsmul_84_ = lean_ctor_get(v_inst_67_, 1);
lean_inc(v_nsmul_84_);
lean_dec_ref(v_inst_67_);
v___x_85_ = lean_nat_abs(v_n_68_);
lean_inc(v_nsmul_84_);
lean_inc(v___x_85_);
v___x_86_ = lean_apply_2(v_nsmul_84_, v___x_85_, v_snd_71_);
v___x_87_ = lean_apply_2(v_nsmul_84_, v___x_85_, v_fst_70_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v___x_87_);
lean_ctor_set(v___x_73_, 0, v___x_86_);
v___x_89_ = v___x_73_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_86_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___boxed(lean_object* v_inst_92_, lean_object* v_n_93_, lean_object* v_q_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg(v_inst_92_, v_n_93_, v_q_94_);
lean_dec(v_n_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul(lean_object* v_00_u03b1_96_, lean_object* v_inst_97_, lean_object* v_n_98_, lean_object* v_q_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg(v_inst_97_, v_n_98_, v_q_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zsmul___boxed(lean_object* v_00_u03b1_101_, lean_object* v_inst_102_, lean_object* v_n_103_, lean_object* v_q_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Grind_IntModule_OfNatModule_zsmul(v_00_u03b1_101_, v_inst_102_, v_n_103_, v_q_104_);
lean_dec(v_n_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_sub___redArg(lean_object* v_inst_106_, lean_object* v_q_u2081_107_, lean_object* v_q_u2082_108_){
_start:
{
lean_object* v_toAddCommMonoid_109_; lean_object* v_toAdd_110_; lean_object* v_fst_111_; lean_object* v_snd_112_; lean_object* v_fst_113_; lean_object* v_snd_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_123_; 
v_toAddCommMonoid_109_ = lean_ctor_get(v_inst_106_, 0);
lean_inc_ref(v_toAddCommMonoid_109_);
lean_dec_ref(v_inst_106_);
v_toAdd_110_ = lean_ctor_get(v_toAddCommMonoid_109_, 1);
lean_inc(v_toAdd_110_);
lean_dec_ref(v_toAddCommMonoid_109_);
v_fst_111_ = lean_ctor_get(v_q_u2081_107_, 0);
lean_inc(v_fst_111_);
v_snd_112_ = lean_ctor_get(v_q_u2081_107_, 1);
lean_inc(v_snd_112_);
lean_dec(v_q_u2081_107_);
v_fst_113_ = lean_ctor_get(v_q_u2082_108_, 0);
v_snd_114_ = lean_ctor_get(v_q_u2082_108_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v_q_u2082_108_);
if (v_isSharedCheck_123_ == 0)
{
v___x_116_ = v_q_u2082_108_;
v_isShared_117_ = v_isSharedCheck_123_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_snd_114_);
lean_inc(v_fst_113_);
lean_dec(v_q_u2082_108_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_123_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_121_; 
lean_inc(v_toAdd_110_);
v___x_118_ = lean_apply_2(v_toAdd_110_, v_fst_111_, v_snd_114_);
v___x_119_ = lean_apply_2(v_toAdd_110_, v_fst_113_, v_snd_112_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 1, v___x_119_);
lean_ctor_set(v___x_116_, 0, v___x_118_);
v___x_121_ = v___x_116_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_118_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_sub(lean_object* v_00_u03b1_124_, lean_object* v_inst_125_, lean_object* v_q_u2081_126_, lean_object* v_q_u2082_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_Grind_IntModule_OfNatModule_sub___redArg(v_inst_125_, v_q_u2081_126_, v_q_u2082_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_add___redArg(lean_object* v_inst_129_, lean_object* v_q_u2081_130_, lean_object* v_q_u2082_131_){
_start:
{
lean_object* v_toAddCommMonoid_132_; lean_object* v_toAdd_133_; lean_object* v_fst_134_; lean_object* v_snd_135_; lean_object* v_fst_136_; lean_object* v_snd_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_146_; 
v_toAddCommMonoid_132_ = lean_ctor_get(v_inst_129_, 0);
lean_inc_ref(v_toAddCommMonoid_132_);
lean_dec_ref(v_inst_129_);
v_toAdd_133_ = lean_ctor_get(v_toAddCommMonoid_132_, 1);
lean_inc(v_toAdd_133_);
lean_dec_ref(v_toAddCommMonoid_132_);
v_fst_134_ = lean_ctor_get(v_q_u2081_130_, 0);
lean_inc(v_fst_134_);
v_snd_135_ = lean_ctor_get(v_q_u2081_130_, 1);
lean_inc(v_snd_135_);
lean_dec(v_q_u2081_130_);
v_fst_136_ = lean_ctor_get(v_q_u2082_131_, 0);
v_snd_137_ = lean_ctor_get(v_q_u2082_131_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_q_u2082_131_);
if (v_isSharedCheck_146_ == 0)
{
v___x_139_ = v_q_u2082_131_;
v_isShared_140_ = v_isSharedCheck_146_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_snd_137_);
lean_inc(v_fst_136_);
lean_dec(v_q_u2082_131_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_146_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
lean_inc(v_toAdd_133_);
v___x_141_ = lean_apply_2(v_toAdd_133_, v_fst_134_, v_fst_136_);
v___x_142_ = lean_apply_2(v_toAdd_133_, v_snd_135_, v_snd_137_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v___x_142_);
lean_ctor_set(v___x_139_, 0, v___x_141_);
v___x_144_ = v___x_139_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v___x_142_);
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
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_add(lean_object* v_00_u03b1_147_, lean_object* v_inst_148_, lean_object* v_q_u2081_149_, lean_object* v_q_u2082_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Grind_IntModule_OfNatModule_add___redArg(v_inst_148_, v_q_u2081_149_, v_q_u2082_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_neg___redArg(lean_object* v_q_152_){
_start:
{
lean_object* v_fst_153_; lean_object* v_snd_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v_fst_153_ = lean_ctor_get(v_q_152_, 0);
v_snd_154_ = lean_ctor_get(v_q_152_, 1);
v_isSharedCheck_161_ = !lean_is_exclusive(v_q_152_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v_q_152_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_snd_154_);
lean_inc(v_fst_153_);
lean_dec(v_q_152_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v_fst_153_);
lean_ctor_set(v___x_156_, 0, v_snd_154_);
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_snd_154_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_fst_153_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_neg(lean_object* v_00_u03b1_162_, lean_object* v_inst_163_, lean_object* v_q_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Grind_IntModule_OfNatModule_neg___redArg(v_q_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_neg___boxed(lean_object* v_00_u03b1_166_, lean_object* v_inst_167_, lean_object* v_q_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Grind_IntModule_OfNatModule_neg(v_00_u03b1_166_, v_inst_167_, v_q_168_);
lean_dec_ref(v_inst_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zero___redArg(lean_object* v_inst_170_){
_start:
{
lean_object* v_toAddCommMonoid_171_; lean_object* v_toZero_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
v_toAddCommMonoid_171_ = lean_ctor_get(v_inst_170_, 0);
lean_inc_ref(v_toAddCommMonoid_171_);
lean_dec_ref(v_inst_170_);
v_toZero_172_ = lean_ctor_get(v_toAddCommMonoid_171_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v_toAddCommMonoid_171_);
if (v_isSharedCheck_179_ == 0)
{
lean_object* v_unused_180_; 
v_unused_180_ = lean_ctor_get(v_toAddCommMonoid_171_, 1);
lean_dec(v_unused_180_);
v___x_174_ = v_toAddCommMonoid_171_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_toZero_172_);
lean_dec(v_toAddCommMonoid_171_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
lean_inc(v_toZero_172_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v_toZero_172_);
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_toZero_172_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_toZero_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_zero(lean_object* v_00_u03b1_181_, lean_object* v_inst_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Grind_IntModule_OfNatModule_zero___redArg(v_inst_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_ofNatModule___redArg(lean_object* v_inst_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
lean_inc_ref(v_inst_184_);
v___x_185_ = l_Lean_Grind_IntModule_OfNatModule_zero___redArg(v_inst_184_);
lean_inc_ref(v_inst_184_);
v___x_186_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_add), 4, 2);
lean_closure_set(v___x_186_, 0, lean_box(0));
lean_closure_set(v___x_186_, 1, v_inst_184_);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_185_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
lean_inc_ref(v_inst_184_);
v___x_188_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_neg___boxed), 3, 2);
lean_closure_set(v___x_188_, 0, lean_box(0));
lean_closure_set(v___x_188_, 1, v_inst_184_);
lean_inc_ref(v_inst_184_);
v___x_189_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_sub), 4, 2);
lean_closure_set(v___x_189_, 0, lean_box(0));
lean_closure_set(v___x_189_, 1, v_inst_184_);
v___x_190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_190_, 0, v___x_187_);
lean_ctor_set(v___x_190_, 1, v___x_188_);
lean_ctor_set(v___x_190_, 2, v___x_189_);
lean_inc_ref(v_inst_184_);
v___x_191_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_nsmul), 4, 2);
lean_closure_set(v___x_191_, 0, lean_box(0));
lean_closure_set(v___x_191_, 1, v_inst_184_);
v___x_192_ = lean_alloc_closure((void*)(l_Lean_Grind_IntModule_OfNatModule_zsmul___boxed), 4, 2);
lean_closure_set(v___x_192_, 0, lean_box(0));
lean_closure_set(v___x_192_, 1, v_inst_184_);
v___x_193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_193_, 0, v___x_190_);
lean_ctor_set(v___x_193_, 1, v___x_191_);
lean_ctor_set(v___x_193_, 2, v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_ofNatModule(lean_object* v_00_u03b1_194_, lean_object* v_inst_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Grind_IntModule_OfNatModule_ofNatModule___redArg(v_inst_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_toQ___redArg(lean_object* v_inst_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_toAddCommMonoid_199_; lean_object* v_toZero_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
v_toAddCommMonoid_199_ = lean_ctor_get(v_inst_197_, 0);
lean_inc_ref(v_toAddCommMonoid_199_);
lean_dec_ref(v_inst_197_);
v_toZero_200_ = lean_ctor_get(v_toAddCommMonoid_199_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v_toAddCommMonoid_199_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; 
v_unused_208_ = lean_ctor_get(v_toAddCommMonoid_199_, 1);
lean_dec(v_unused_208_);
v___x_202_ = v_toAddCommMonoid_199_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_toZero_200_);
lean_dec(v_toAddCommMonoid_199_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 1, v_toZero_200_);
lean_ctor_set(v___x_202_, 0, v_a_198_);
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_198_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_toZero_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_toQ(lean_object* v_00_u03b1_209_, lean_object* v_inst_210_, lean_object* v_a_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Grind_IntModule_OfNatModule_toQ___redArg(v_inst_210_, v_a_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd(lean_object* v_00_u03b1_213_, lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_inst_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_box(0);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd___boxed(lean_object* v_00_u03b1_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_inst_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd(v_00_u03b1_219_, v_inst_220_, v_inst_221_, v_inst_222_, v_inst_223_);
lean_dec_ref(v_inst_220_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd(lean_object* v_00_u03b1_225_, lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_inst_228_, lean_object* v_inst_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = lean_box(0);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd___boxed(lean_object* v_00_u03b1_231_, lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_inst_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd(v_00_u03b1_231_, v_inst_232_, v_inst_233_, v_inst_234_, v_inst_235_);
lean_dec_ref(v_inst_232_);
return v_res_236_;
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
