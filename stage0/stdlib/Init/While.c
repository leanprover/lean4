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
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg___lam__0(lean_object* v_toPure_81_, lean_object* v_____do__lift_82_){
_start:
{
if (lean_obj_tag(v_____do__lift_82_) == 0)
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_91_; 
v_a_83_ = lean_ctor_get(v_____do__lift_82_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v_____do__lift_82_);
if (v_isSharedCheck_91_ == 0)
{
v___x_85_ = v_____do__lift_82_;
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v_____do__lift_82_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set_tag(v___x_85_, 1);
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_a_83_);
v___x_88_ = v_reuseFailAlloc_90_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_89_; 
v___x_89_ = lean_apply_2(v_toPure_81_, lean_box(0), v___x_88_);
return v___x_89_;
}
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_100_; 
v_a_92_ = lean_ctor_get(v_____do__lift_82_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v_____do__lift_82_);
if (v_isSharedCheck_100_ == 0)
{
v___x_94_ = v_____do__lift_82_;
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v_____do__lift_82_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
lean_ctor_set_tag(v___x_94_, 0);
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_99_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; 
v___x_98_ = lean_apply_2(v_toPure_81_, lean_box(0), v___x_97_);
return v___x_98_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg___lam__1(lean_object* v_f_101_, lean_object* v_toBind_102_, lean_object* v___f_103_, lean_object* v_b_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_box(0);
v___x_106_ = lean_apply_2(v_f_101_, v___x_105_, v_b_104_);
v___x_107_ = lean_apply_4(v_toBind_102_, lean_box(0), lean_box(0), v___x_106_, v___f_103_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg(lean_object* v_inst_108_, lean_object* v_init_109_, lean_object* v_f_110_){
_start:
{
lean_object* v_toApplicative_111_; lean_object* v_toBind_112_; lean_object* v_toPure_113_; lean_object* v___f_114_; lean_object* v___f_115_; lean_object* v___x_116_; 
v_toApplicative_111_ = lean_ctor_get(v_inst_108_, 0);
v_toBind_112_ = lean_ctor_get(v_inst_108_, 1);
v_toPure_113_ = lean_ctor_get(v_toApplicative_111_, 1);
lean_inc(v_toPure_113_);
v___f_114_ = lean_alloc_closure((void*)(l_Lean_Loop_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_114_, 0, v_toPure_113_);
lean_inc(v_toBind_112_);
v___f_115_ = lean_alloc_closure((void*)(l_Lean_Loop_forIn___redArg___lam__1), 4, 3);
lean_closure_set(v___f_115_, 0, v_f_110_);
lean_closure_set(v___f_115_, 1, v_toBind_112_);
lean_closure_set(v___f_115_, 2, v___f_114_);
v___x_116_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_108_, v___f_115_, v_init_109_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn(lean_object* v_00_u03b2_117_, lean_object* v_m_118_, lean_object* v_inst_119_, lean_object* v_x_120_, lean_object* v_init_121_, lean_object* v_f_122_){
_start:
{
lean_object* v_toApplicative_123_; lean_object* v_toBind_124_; lean_object* v_toPure_125_; lean_object* v___f_126_; lean_object* v___f_127_; lean_object* v___x_128_; 
v_toApplicative_123_ = lean_ctor_get(v_inst_119_, 0);
v_toBind_124_ = lean_ctor_get(v_inst_119_, 1);
v_toPure_125_ = lean_ctor_get(v_toApplicative_123_, 1);
lean_inc(v_toPure_125_);
v___f_126_ = lean_alloc_closure((void*)(l_Lean_Loop_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_126_, 0, v_toPure_125_);
lean_inc(v_toBind_124_);
v___f_127_ = lean_alloc_closure((void*)(l_Lean_Loop_forIn___redArg___lam__1), 4, 3);
lean_closure_set(v___f_127_, 0, v_f_122_);
lean_closure_set(v___f_127_, 1, v_toBind_124_);
lean_closure_set(v___f_127_, 2, v___f_126_);
v___x_128_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_119_, v___f_127_, v_init_121_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg___lam__1(lean_object* v___y_129_, lean_object* v_toBind_130_, lean_object* v___f_131_, lean_object* v_b_132_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = lean_box(0);
v___x_134_ = lean_apply_2(v___y_129_, v___x_133_, v_b_132_);
v___x_135_ = lean_apply_4(v_toBind_130_, lean_box(0), lean_box(0), v___x_134_, v___f_131_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg___lam__0(lean_object* v_inst_136_, lean_object* v_00_u03b2_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_toApplicative_141_; lean_object* v_toBind_142_; lean_object* v_toPure_143_; lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___x_146_; 
v_toApplicative_141_ = lean_ctor_get(v_inst_136_, 0);
v_toBind_142_ = lean_ctor_get(v_inst_136_, 1);
v_toPure_143_ = lean_ctor_get(v_toApplicative_141_, 1);
lean_inc(v_toPure_143_);
v___f_144_ = lean_alloc_closure((void*)(l_Lean_Loop_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_144_, 0, v_toPure_143_);
lean_inc(v_toBind_142_);
v___f_145_ = lean_alloc_closure((void*)(l_Lean_instForInLoopUnitOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_145_, 0, v___y_140_);
lean_closure_set(v___f_145_, 1, v_toBind_142_);
lean_closure_set(v___f_145_, 2, v___f_144_);
v___x_146_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_136_, v___f_145_, v___y_139_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg(lean_object* v_inst_147_){
_start:
{
lean_object* v___f_148_; 
v___f_148_ = lean_alloc_closure((void*)(l_Lean_instForInLoopUnitOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_148_, 0, v_inst_147_);
return v___f_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad(lean_object* v_m_149_, lean_object* v_inst_150_){
_start:
{
lean_object* v___f_151_; 
v___f_151_ = lean_alloc_closure((void*)(l_Lean_instForInLoopUnitOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_151_, 0, v_inst_150_);
return v___f_151_;
}
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_While(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
