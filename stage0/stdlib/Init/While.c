// Lean compiler output
// Module: Init.While
// Imports: public import Init.Core public import Init.Classical
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
LEAN_EXPORT lean_object* l_repeatM_body___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_repeatM_body___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_repeatM_body(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_impl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_impl___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_impl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_toCtorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_repeatM_body___redArg___lam__0(lean_object* v_recur_1_, lean_object* v_toPure_2_, lean_object* v_____do__lift_3_){
_start:
{
if (lean_obj_tag(v_____do__lift_3_) == 0)
{
lean_object* v_val_4_; lean_object* v___x_5_; 
lean_dec(v_toPure_2_);
v_val_4_ = lean_ctor_get(v_____do__lift_3_, 0);
lean_inc(v_val_4_);
lean_dec_ref_known(v_____do__lift_3_, 1);
v___x_5_ = lean_apply_1(v_recur_1_, v_val_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_recur_1_);
v_val_6_ = lean_ctor_get(v_____do__lift_3_, 0);
lean_inc(v_val_6_);
lean_dec_ref_known(v_____do__lift_3_, 1);
v___x_7_ = lean_apply_2(v_toPure_2_, lean_box(0), v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l_repeatM_body___redArg(lean_object* v_inst_8_, lean_object* v_f_9_, lean_object* v_recur_10_, lean_object* v_a_11_){
_start:
{
lean_object* v_toApplicative_12_; lean_object* v_toBind_13_; lean_object* v_toPure_14_; lean_object* v___x_15_; lean_object* v___f_16_; lean_object* v___x_17_; 
v_toApplicative_12_ = lean_ctor_get(v_inst_8_, 0);
lean_inc_ref(v_toApplicative_12_);
v_toBind_13_ = lean_ctor_get(v_inst_8_, 1);
lean_inc(v_toBind_13_);
lean_dec_ref(v_inst_8_);
v_toPure_14_ = lean_ctor_get(v_toApplicative_12_, 1);
lean_inc(v_toPure_14_);
lean_dec_ref(v_toApplicative_12_);
v___x_15_ = lean_apply_1(v_f_9_, v_a_11_);
v___f_16_ = lean_alloc_closure((void*)(l_repeatM_body___redArg___lam__0), 3, 2);
lean_closure_set(v___f_16_, 0, v_recur_10_);
lean_closure_set(v___f_16_, 1, v_toPure_14_);
v___x_17_ = lean_apply_4(v_toBind_13_, lean_box(0), lean_box(0), v___x_15_, v___f_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_repeatM_body(lean_object* v_00_u03b1_18_, lean_object* v_m_19_, lean_object* v_inst_20_, lean_object* v_00_u03b2_21_, lean_object* v_f_22_, lean_object* v_recur_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_toApplicative_25_; lean_object* v_toBind_26_; lean_object* v_toPure_27_; lean_object* v___x_28_; lean_object* v___f_29_; lean_object* v___x_30_; 
v_toApplicative_25_ = lean_ctor_get(v_inst_20_, 0);
lean_inc_ref(v_toApplicative_25_);
v_toBind_26_ = lean_ctor_get(v_inst_20_, 1);
lean_inc(v_toBind_26_);
lean_dec_ref(v_inst_20_);
v_toPure_27_ = lean_ctor_get(v_toApplicative_25_, 1);
lean_inc(v_toPure_27_);
lean_dec_ref(v_toApplicative_25_);
v___x_28_ = lean_apply_1(v_f_22_, v_a_24_);
v___f_29_ = lean_alloc_closure((void*)(l_repeatM_body___redArg___lam__0), 3, 2);
lean_closure_set(v___f_29_, 0, v_recur_23_);
lean_closure_set(v___f_29_, 1, v_toPure_27_);
v___x_30_ = lean_apply_4(v_toBind_26_, lean_box(0), lean_box(0), v___x_28_, v___f_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_impl___redArg(lean_object* v_inst_31_, lean_object* v_f_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_toApplicative_34_; lean_object* v_toBind_35_; lean_object* v_toPure_36_; lean_object* v___x_37_; lean_object* v___f_38_; lean_object* v___x_39_; 
v_toApplicative_34_ = lean_ctor_get(v_inst_31_, 0);
v_toBind_35_ = lean_ctor_get(v_inst_31_, 1);
lean_inc(v_toBind_35_);
v_toPure_36_ = lean_ctor_get(v_toApplicative_34_, 1);
lean_inc(v_toPure_36_);
lean_inc(v_f_32_);
v___x_37_ = lean_apply_1(v_f_32_, v_a_33_);
v___f_38_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_impl___redArg___lam__0), 4, 3);
lean_closure_set(v___f_38_, 0, v_inst_31_);
lean_closure_set(v___f_38_, 1, v_f_32_);
lean_closure_set(v___f_38_, 2, v_toPure_36_);
v___x_39_ = lean_apply_4(v_toBind_35_, lean_box(0), lean_box(0), v___x_37_, v___f_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_impl___redArg___lam__0(lean_object* v_inst_40_, lean_object* v_f_41_, lean_object* v_toPure_42_, lean_object* v_____do__lift_43_){
_start:
{
if (lean_obj_tag(v_____do__lift_43_) == 0)
{
lean_object* v_val_44_; lean_object* v___x_45_; 
lean_dec(v_toPure_42_);
v_val_44_ = lean_ctor_get(v_____do__lift_43_, 0);
lean_inc(v_val_44_);
lean_dec_ref_known(v_____do__lift_43_, 1);
v___x_45_ = l___private_Init_While_0__repeatM_impl___redArg(v_inst_40_, v_f_41_, v_val_44_);
return v___x_45_;
}
else
{
lean_object* v_val_46_; lean_object* v___x_47_; 
lean_dec(v_f_41_);
lean_dec_ref(v_inst_40_);
v_val_46_ = lean_ctor_get(v_____do__lift_43_, 0);
lean_inc(v_val_46_);
lean_dec_ref_known(v_____do__lift_43_, 1);
v___x_47_ = lean_apply_2(v_toPure_42_, lean_box(0), v_val_46_);
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_impl(lean_object* v_00_u03b1_48_, lean_object* v_m_49_, lean_object* v_inst_50_, lean_object* v_00_u03b2_51_, lean_object* v_inst_52_, lean_object* v_f_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l___private_Init_While_0__repeatM_impl___redArg(v_inst_50_, v_f_53_, v_a_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___redArg(lean_object* v_inst_56_, lean_object* v_f_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_toApplicative_59_; lean_object* v_toBind_60_; lean_object* v_toPure_61_; lean_object* v___x_62_; lean_object* v___f_63_; lean_object* v___x_64_; 
v_toApplicative_59_ = lean_ctor_get(v_inst_56_, 0);
v_toBind_60_ = lean_ctor_get(v_inst_56_, 1);
lean_inc(v_toBind_60_);
v_toPure_61_ = lean_ctor_get(v_toApplicative_59_, 1);
lean_inc(v_toPure_61_);
lean_inc(v_f_57_);
v___x_62_ = lean_apply_1(v_f_57_, v_a_58_);
v___f_63_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___redArg___lam__0), 4, 3);
lean_closure_set(v___f_63_, 0, v_inst_56_);
lean_closure_set(v___f_63_, 1, v_f_57_);
lean_closure_set(v___f_63_, 2, v_toPure_61_);
v___x_64_ = lean_apply_4(v_toBind_60_, lean_box(0), lean_box(0), v___x_62_, v___f_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___redArg___lam__0(lean_object* v_inst_65_, lean_object* v_f_66_, lean_object* v_toPure_67_, lean_object* v_____do__lift_68_){
_start:
{
if (lean_obj_tag(v_____do__lift_68_) == 0)
{
lean_object* v_val_69_; lean_object* v___x_70_; 
lean_dec(v_toPure_67_);
v_val_69_ = lean_ctor_get(v_____do__lift_68_, 0);
lean_inc(v_val_69_);
lean_dec_ref_known(v_____do__lift_68_, 1);
v___x_70_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_65_, v_f_66_, v_val_69_);
return v___x_70_;
}
else
{
lean_object* v_val_71_; lean_object* v___x_72_; 
lean_dec(v_f_66_);
lean_dec_ref(v_inst_65_);
v_val_71_ = lean_ctor_get(v_____do__lift_68_, 0);
lean_inc(v_val_71_);
lean_dec_ref_known(v_____do__lift_68_, 1);
v___x_72_ = lean_apply_2(v_toPure_67_, lean_box(0), v_val_71_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased(lean_object* v_00_u03b1_73_, lean_object* v_m_74_, lean_object* v_inst_75_, lean_object* v_00_u03b2_76_, lean_object* v_inst_77_, lean_object* v_f_78_, lean_object* v_a_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_75_, v_f_78_, v_a_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_toCtorIdx(lean_object* v_x_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_unsigned_to_nat(0u);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg___lam__0(lean_object* v_toPure_83_, lean_object* v_____do__lift_84_){
_start:
{
if (lean_obj_tag(v_____do__lift_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_93_; 
v_a_85_ = lean_ctor_get(v_____do__lift_84_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v_____do__lift_84_);
if (v_isSharedCheck_93_ == 0)
{
v___x_87_ = v_____do__lift_84_;
v_isShared_88_ = v_isSharedCheck_93_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v_____do__lift_84_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_93_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 1);
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_a_85_);
v___x_90_ = v_reuseFailAlloc_92_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_91_; 
v___x_91_ = lean_apply_2(v_toPure_83_, lean_box(0), v___x_90_);
return v___x_91_;
}
}
}
else
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_102_; 
v_a_94_ = lean_ctor_get(v_____do__lift_84_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v_____do__lift_84_);
if (v_isSharedCheck_102_ == 0)
{
v___x_96_ = v_____do__lift_84_;
v_isShared_97_ = v_isSharedCheck_102_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v_____do__lift_84_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_102_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set_tag(v___x_96_, 0);
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_101_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_100_; 
v___x_100_ = lean_apply_2(v_toPure_83_, lean_box(0), v___x_99_);
return v___x_100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg___lam__1(lean_object* v_f_103_, lean_object* v_toBind_104_, lean_object* v___f_105_, lean_object* v_b_106_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = lean_box(0);
v___x_108_ = lean_apply_2(v_f_103_, v___x_107_, v_b_106_);
v___x_109_ = lean_apply_4(v_toBind_104_, lean_box(0), lean_box(0), v___x_108_, v___f_105_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg(lean_object* v_inst_110_, lean_object* v_init_111_, lean_object* v_f_112_){
_start:
{
lean_object* v_toApplicative_113_; lean_object* v_toBind_114_; lean_object* v_toPure_115_; lean_object* v___f_116_; lean_object* v___f_117_; lean_object* v___x_118_; 
v_toApplicative_113_ = lean_ctor_get(v_inst_110_, 0);
v_toBind_114_ = lean_ctor_get(v_inst_110_, 1);
v_toPure_115_ = lean_ctor_get(v_toApplicative_113_, 1);
lean_inc(v_toPure_115_);
v___f_116_ = lean_alloc_closure((void*)(l_Lean_Loop_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_116_, 0, v_toPure_115_);
lean_inc(v_toBind_114_);
v___f_117_ = lean_alloc_closure((void*)(l_Lean_Loop_forIn___redArg___lam__1), 4, 3);
lean_closure_set(v___f_117_, 0, v_f_112_);
lean_closure_set(v___f_117_, 1, v_toBind_114_);
lean_closure_set(v___f_117_, 2, v___f_116_);
v___x_118_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_110_, v___f_117_, v_init_111_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn(lean_object* v_00_u03b2_119_, lean_object* v_m_120_, lean_object* v_inst_121_, lean_object* v_x_122_, lean_object* v_init_123_, lean_object* v_f_124_){
_start:
{
lean_object* v_toApplicative_125_; lean_object* v_toBind_126_; lean_object* v_toPure_127_; lean_object* v___f_128_; lean_object* v___f_129_; lean_object* v___x_130_; 
v_toApplicative_125_ = lean_ctor_get(v_inst_121_, 0);
v_toBind_126_ = lean_ctor_get(v_inst_121_, 1);
v_toPure_127_ = lean_ctor_get(v_toApplicative_125_, 1);
lean_inc(v_toPure_127_);
v___f_128_ = lean_alloc_closure((void*)(l_Lean_Loop_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_128_, 0, v_toPure_127_);
lean_inc(v_toBind_126_);
v___f_129_ = lean_alloc_closure((void*)(l_Lean_Loop_forIn___redArg___lam__1), 4, 3);
lean_closure_set(v___f_129_, 0, v_f_124_);
lean_closure_set(v___f_129_, 1, v_toBind_126_);
lean_closure_set(v___f_129_, 2, v___f_128_);
v___x_130_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_121_, v___f_129_, v_init_123_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg___lam__1(lean_object* v___y_131_, lean_object* v_toBind_132_, lean_object* v___f_133_, lean_object* v_b_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = lean_box(0);
v___x_136_ = lean_apply_2(v___y_131_, v___x_135_, v_b_134_);
v___x_137_ = lean_apply_4(v_toBind_132_, lean_box(0), lean_box(0), v___x_136_, v___f_133_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg___lam__0(lean_object* v_inst_138_, lean_object* v_00_u03b2_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_toApplicative_143_; lean_object* v_toBind_144_; lean_object* v_toPure_145_; lean_object* v___f_146_; lean_object* v___f_147_; lean_object* v___x_148_; 
v_toApplicative_143_ = lean_ctor_get(v_inst_138_, 0);
v_toBind_144_ = lean_ctor_get(v_inst_138_, 1);
v_toPure_145_ = lean_ctor_get(v_toApplicative_143_, 1);
lean_inc(v_toPure_145_);
v___f_146_ = lean_alloc_closure((void*)(l_Lean_Loop_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_146_, 0, v_toPure_145_);
lean_inc(v_toBind_144_);
v___f_147_ = lean_alloc_closure((void*)(l_Lean_instForInLoopUnitOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_147_, 0, v___y_142_);
lean_closure_set(v___f_147_, 1, v_toBind_144_);
lean_closure_set(v___f_147_, 2, v___f_146_);
v___x_148_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_138_, v___f_147_, v___y_141_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg(lean_object* v_inst_149_){
_start:
{
lean_object* v___f_150_; 
v___f_150_ = lean_alloc_closure((void*)(l_Lean_instForInLoopUnitOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_150_, 0, v_inst_149_);
return v___f_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad(lean_object* v_m_151_, lean_object* v_inst_152_){
_start:
{
lean_object* v___f_153_; 
v___f_153_ = lean_alloc_closure((void*)(l_Lean_instForInLoopUnitOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_153_, 0, v_inst_152_);
return v___f_153_;
}
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_While(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_While(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Core(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_While(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_While(builtin);
}
#ifdef __cplusplus
}
#endif
