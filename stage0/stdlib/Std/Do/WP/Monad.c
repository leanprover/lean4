// Lean compiler output
// Module: Std.Do.WP.Monad
// Imports: public import Std.Do.WP.Basic import all Std.Do.WP.Basic
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
lean_object* l_Std_Do_Id_instWP___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_Except_instWP(lean_object*);
lean_object* l_Std_Do_StateT_instWP___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_ReaderT_instWP___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_ExceptT_instWP___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_EStateM_instWP(lean_object*, lean_object*);
lean_object* l_Std_Do_OptionT_instWP___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Do_Option_instWP;
static const lean_closure_object l_Std_Do_Id_instWPMonad___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Do_Id_instWP___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Do_Id_instWPMonad___closed__0 = (const lean_object*)&l_Std_Do_Id_instWPMonad___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Do_Id_instWPMonad = (const lean_object*)&l_Std_Do_Id_instWPMonad___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Do_StateT_instWPMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StateT_instWPMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StateT_instWPMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ReaderT_instWPMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ReaderT_instWPMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ReaderT_instWPMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushExcept_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__ExceptT_run__bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__ExceptT_run__bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptT_instWPMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptT_instWPMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptT_instWPMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushOption_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Option_elim_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Option_elim_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_OptionT_instWPMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_OptionT_instWPMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_OptionT_instWPMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__EStateM_run__bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__EStateM_run__bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Std_Do_EStateM_instWP_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Std_Do_EStateM_instWP_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Do_EStateM_instWPMonad___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do_EStateM_instWPMonad___closed__0;
LEAN_EXPORT lean_object* l_Std_Do_EStateM_instWPMonad(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Do_Except_instWPMonad___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do_Except_instWPMonad___closed__0;
LEAN_EXPORT lean_object* l_Std_Do_Except_instWPMonad(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_Option_instWPMonad;
static const lean_closure_object l_Std_Do_State_instWPMonad___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Do_StateT_instWP___redArg___lam__1, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Do_Id_instWPMonad___closed__0_value)} };
static const lean_object* l_Std_Do_State_instWPMonad___closed__0 = (const lean_object*)&l_Std_Do_State_instWPMonad___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Do_State_instWPMonad(lean_object*);
static const lean_closure_object l_Std_Do_Reader_instWPMonad___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Do_ReaderT_instWP___redArg___lam__2, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Do_Id_instWPMonad___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Do_Reader_instWPMonad___closed__0 = (const lean_object*)&l_Std_Do_Reader_instWPMonad___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Do_Reader_instWPMonad(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_StateT_instWPMonad___redArg(lean_object* v_inst_3_){
_start:
{
lean_object* v___f_4_; 
v___f_4_ = lean_alloc_closure((void*)(l_Std_Do_StateT_instWP___redArg___lam__1), 4, 1);
lean_closure_set(v___f_4_, 0, v_inst_3_);
return v___f_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StateT_instWPMonad(lean_object* v_m_5_, lean_object* v_ps_6_, lean_object* v_00_u03c3_7_, lean_object* v_inst_8_, lean_object* v_inst_9_){
_start:
{
lean_object* v___f_10_; 
v___f_10_ = lean_alloc_closure((void*)(l_Std_Do_StateT_instWP___redArg___lam__1), 4, 1);
lean_closure_set(v___f_10_, 0, v_inst_9_);
return v___f_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_StateT_instWPMonad___boxed(lean_object* v_m_11_, lean_object* v_ps_12_, lean_object* v_00_u03c3_13_, lean_object* v_inst_14_, lean_object* v_inst_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Std_Do_StateT_instWPMonad(v_m_11_, v_ps_12_, v_00_u03c3_13_, v_inst_14_, v_inst_15_);
lean_dec_ref(v_inst_14_);
lean_dec(v_ps_12_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ReaderT_instWPMonad___redArg(lean_object* v_ps_17_, lean_object* v_inst_18_){
_start:
{
lean_object* v___f_19_; 
v___f_19_ = lean_alloc_closure((void*)(l_Std_Do_ReaderT_instWP___redArg___lam__2), 5, 2);
lean_closure_set(v___f_19_, 0, v_inst_18_);
lean_closure_set(v___f_19_, 1, v_ps_17_);
return v___f_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ReaderT_instWPMonad(lean_object* v_m_20_, lean_object* v_ps_21_, lean_object* v_00_u03c1_22_, lean_object* v_inst_23_, lean_object* v_inst_24_){
_start:
{
lean_object* v___f_25_; 
v___f_25_ = lean_alloc_closure((void*)(l_Std_Do_ReaderT_instWP___redArg___lam__2), 5, 2);
lean_closure_set(v___f_25_, 0, v_inst_24_);
lean_closure_set(v___f_25_, 1, v_ps_21_);
return v___f_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ReaderT_instWPMonad___boxed(lean_object* v_m_26_, lean_object* v_ps_27_, lean_object* v_00_u03c1_28_, lean_object* v_inst_29_, lean_object* v_inst_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Std_Do_ReaderT_instWPMonad(v_m_26_, v_ps_27_, v_00_u03c1_28_, v_inst_29_, v_inst_30_);
lean_dec_ref(v_inst_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(lean_object* v_x_32_, lean_object* v_h__1_33_, lean_object* v_h__2_34_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
lean_object* v_a_35_; lean_object* v___x_36_; 
lean_dec(v_h__1_33_);
v_a_35_ = lean_ctor_get(v_x_32_, 0);
lean_inc(v_a_35_);
lean_dec_ref(v_x_32_);
v___x_36_ = lean_apply_1(v_h__2_34_, v_a_35_);
return v___x_36_;
}
else
{
lean_object* v_a_37_; lean_object* v___x_38_; 
lean_dec(v_h__2_34_);
v_a_37_ = lean_ctor_get(v_x_32_, 0);
lean_inc(v_a_37_);
lean_dec_ref(v_x_32_);
v___x_38_ = lean_apply_1(v_h__1_33_, v_a_37_);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushExcept_match__1_splitter(lean_object* v_00_u03b1_39_, lean_object* v_00_u03b5_40_, lean_object* v_motive_41_, lean_object* v_x_42_, lean_object* v_h__1_43_, lean_object* v_h__2_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(v_x_42_, v_h__1_43_, v_h__2_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__ExceptT_run__bind_match__1_splitter___redArg(lean_object* v_x_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
lean_object* v_a_49_; lean_object* v___x_50_; 
lean_dec(v_h__1_47_);
v_a_49_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_a_49_);
lean_dec_ref(v_x_46_);
v___x_50_ = lean_apply_1(v_h__2_48_, v_a_49_);
return v___x_50_;
}
else
{
lean_object* v_a_51_; lean_object* v___x_52_; 
lean_dec(v_h__2_48_);
v_a_51_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_a_51_);
lean_dec_ref(v_x_46_);
v___x_52_ = lean_apply_1(v_h__1_47_, v_a_51_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__ExceptT_run__bind_match__1_splitter(lean_object* v_00_u03b5_53_, lean_object* v_00_u03b1_54_, lean_object* v_motive_55_, lean_object* v_x_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l___private_Std_Do_WP_Monad_0__ExceptT_run__bind_match__1_splitter___redArg(v_x_56_, v_h__1_57_, v_h__2_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptT_instWPMonad___redArg(lean_object* v_inst_60_){
_start:
{
lean_object* v___f_61_; 
v___f_61_ = lean_alloc_closure((void*)(l_Std_Do_ExceptT_instWP___redArg___lam__0), 4, 1);
lean_closure_set(v___f_61_, 0, v_inst_60_);
return v___f_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptT_instWPMonad(lean_object* v_m_62_, lean_object* v_ps_63_, lean_object* v_00_u03b5_64_, lean_object* v_inst_65_, lean_object* v_inst_66_){
_start:
{
lean_object* v___f_67_; 
v___f_67_ = lean_alloc_closure((void*)(l_Std_Do_ExceptT_instWP___redArg___lam__0), 4, 1);
lean_closure_set(v___f_67_, 0, v_inst_66_);
return v___f_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptT_instWPMonad___boxed(lean_object* v_m_68_, lean_object* v_ps_69_, lean_object* v_00_u03b5_70_, lean_object* v_inst_71_, lean_object* v_inst_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Std_Do_ExceptT_instWPMonad(v_m_68_, v_ps_69_, v_00_u03b5_70_, v_inst_71_, v_inst_72_);
lean_dec_ref(v_inst_71_);
lean_dec(v_ps_69_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(lean_object* v_x_74_, lean_object* v_h__1_75_, lean_object* v_h__2_76_){
_start:
{
if (lean_obj_tag(v_x_74_) == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec(v_h__1_75_);
v___x_77_ = lean_box(0);
v___x_78_ = lean_apply_1(v_h__2_76_, v___x_77_);
return v___x_78_;
}
else
{
lean_object* v_val_79_; lean_object* v___x_80_; 
lean_dec(v_h__2_76_);
v_val_79_ = lean_ctor_get(v_x_74_, 0);
lean_inc(v_val_79_);
lean_dec_ref(v_x_74_);
v___x_80_ = lean_apply_1(v_h__1_75_, v_val_79_);
return v___x_80_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushOption_match__1_splitter(lean_object* v_00_u03b1_81_, lean_object* v_motive_82_, lean_object* v_x_83_, lean_object* v_h__1_84_, lean_object* v_h__2_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(v_x_83_, v_h__1_84_, v_h__2_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Option_elim_match__1_splitter___redArg(lean_object* v_x_87_, lean_object* v_x_88_, lean_object* v_x_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v___x_92_; 
lean_dec(v_h__1_90_);
v___x_92_ = lean_apply_2(v_h__2_91_, v_x_88_, v_x_89_);
return v___x_92_;
}
else
{
lean_object* v_val_93_; lean_object* v___x_94_; 
lean_dec(v_h__2_91_);
v_val_93_ = lean_ctor_get(v_x_87_, 0);
lean_inc(v_val_93_);
lean_dec_ref(v_x_87_);
v___x_94_ = lean_apply_3(v_h__1_90_, v_val_93_, v_x_88_, v_x_89_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Option_elim_match__1_splitter(lean_object* v_00_u03b1_95_, lean_object* v_00_u03b2_96_, lean_object* v_motive_97_, lean_object* v_x_98_, lean_object* v_x_99_, lean_object* v_x_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l___private_Std_Do_WP_Monad_0__Option_elim_match__1_splitter___redArg(v_x_98_, v_x_99_, v_x_100_, v_h__1_101_, v_h__2_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_OptionT_instWPMonad___redArg(lean_object* v_inst_104_){
_start:
{
lean_object* v___f_105_; 
v___f_105_ = lean_alloc_closure((void*)(l_Std_Do_OptionT_instWP___redArg___lam__0), 4, 1);
lean_closure_set(v___f_105_, 0, v_inst_104_);
return v___f_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_OptionT_instWPMonad(lean_object* v_m_106_, lean_object* v_ps_107_, lean_object* v_inst_108_, lean_object* v_inst_109_){
_start:
{
lean_object* v___f_110_; 
v___f_110_ = lean_alloc_closure((void*)(l_Std_Do_OptionT_instWP___redArg___lam__0), 4, 1);
lean_closure_set(v___f_110_, 0, v_inst_109_);
return v___f_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_OptionT_instWPMonad___boxed(lean_object* v_m_111_, lean_object* v_ps_112_, lean_object* v_inst_113_, lean_object* v_inst_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Std_Do_OptionT_instWPMonad(v_m_111_, v_ps_112_, v_inst_113_, v_inst_114_);
lean_dec_ref(v_inst_113_);
lean_dec(v_ps_112_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__EStateM_run__bind_match__1_splitter___redArg(lean_object* v_x_116_, lean_object* v_h__1_117_, lean_object* v_h__2_118_){
_start:
{
if (lean_obj_tag(v_x_116_) == 0)
{
lean_object* v_a_119_; lean_object* v_a_120_; lean_object* v___x_121_; 
lean_dec(v_h__2_118_);
v_a_119_ = lean_ctor_get(v_x_116_, 0);
lean_inc(v_a_119_);
v_a_120_ = lean_ctor_get(v_x_116_, 1);
lean_inc(v_a_120_);
lean_dec_ref(v_x_116_);
v___x_121_ = lean_apply_2(v_h__1_117_, v_a_119_, v_a_120_);
return v___x_121_;
}
else
{
lean_object* v_a_122_; lean_object* v_a_123_; lean_object* v___x_124_; 
lean_dec(v_h__1_117_);
v_a_122_ = lean_ctor_get(v_x_116_, 0);
lean_inc(v_a_122_);
v_a_123_ = lean_ctor_get(v_x_116_, 1);
lean_inc(v_a_123_);
lean_dec_ref(v_x_116_);
v___x_124_ = lean_apply_2(v_h__2_118_, v_a_122_, v_a_123_);
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__EStateM_run__bind_match__1_splitter(lean_object* v_00_u03b5_125_, lean_object* v_00_u03c3_126_, lean_object* v_00_u03b1_127_, lean_object* v_motive_128_, lean_object* v_x_129_, lean_object* v_h__1_130_, lean_object* v_h__2_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l___private_Std_Do_WP_Monad_0__EStateM_run__bind_match__1_splitter___redArg(v_x_129_, v_h__1_130_, v_h__2_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Std_Do_EStateM_instWP_match__1_splitter___redArg(lean_object* v_x_133_, lean_object* v_h__1_134_, lean_object* v_h__2_135_){
_start:
{
if (lean_obj_tag(v_x_133_) == 0)
{
lean_object* v_a_136_; lean_object* v_a_137_; lean_object* v___x_138_; 
lean_dec(v_h__2_135_);
v_a_136_ = lean_ctor_get(v_x_133_, 0);
lean_inc(v_a_136_);
v_a_137_ = lean_ctor_get(v_x_133_, 1);
lean_inc(v_a_137_);
lean_dec_ref(v_x_133_);
v___x_138_ = lean_apply_2(v_h__1_134_, v_a_136_, v_a_137_);
return v___x_138_;
}
else
{
lean_object* v_a_139_; lean_object* v_a_140_; lean_object* v___x_141_; 
lean_dec(v_h__1_134_);
v_a_139_ = lean_ctor_get(v_x_133_, 0);
lean_inc(v_a_139_);
v_a_140_ = lean_ctor_get(v_x_133_, 1);
lean_inc(v_a_140_);
lean_dec_ref(v_x_133_);
v___x_141_ = lean_apply_2(v_h__2_135_, v_a_139_, v_a_140_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Std_Do_EStateM_instWP_match__1_splitter(lean_object* v_00_u03b5_142_, lean_object* v_00_u03c3_143_, lean_object* v_00_u03b1_144_, lean_object* v_motive_145_, lean_object* v_x_146_, lean_object* v_h__1_147_, lean_object* v_h__2_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l___private_Std_Do_WP_Monad_0__Std_Do_EStateM_instWP_match__1_splitter___redArg(v_x_146_, v_h__1_147_, v_h__2_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Std_Do_EStateM_instWPMonad___closed__0(void){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Std_Do_EStateM_instWP(lean_box(0), lean_box(0));
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_EStateM_instWPMonad(lean_object* v_00_u03b5_151_, lean_object* v_00_u03c3_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = lean_obj_once(&l_Std_Do_EStateM_instWPMonad___closed__0, &l_Std_Do_EStateM_instWPMonad___closed__0_once, _init_l_Std_Do_EStateM_instWPMonad___closed__0);
return v___x_153_;
}
}
static lean_object* _init_l_Std_Do_Except_instWPMonad___closed__0(void){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Std_Do_Except_instWP(lean_box(0));
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Except_instWPMonad(lean_object* v_00_u03b5_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = lean_obj_once(&l_Std_Do_Except_instWPMonad___closed__0, &l_Std_Do_Except_instWPMonad___closed__0_once, _init_l_Std_Do_Except_instWPMonad___closed__0);
return v___x_156_;
}
}
static lean_object* _init_l_Std_Do_Option_instWPMonad(void){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Std_Do_Option_instWP;
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_State_instWPMonad(lean_object* v_00_u03c3_160_){
_start:
{
lean_object* v___f_161_; 
v___f_161_ = ((lean_object*)(l_Std_Do_State_instWPMonad___closed__0));
return v___f_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Reader_instWPMonad(lean_object* v_00_u03c1_165_){
_start:
{
lean_object* v___f_166_; 
v___f_166_ = ((lean_object*)(l_Std_Do_Reader_instWPMonad___closed__0));
return v___f_166_;
}
}
lean_object* runtime_initialize_Std_Do_WP_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Do_WP_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Do_WP_Monad(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Do_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Do_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Do_Option_instWPMonad = _init_l_Std_Do_Option_instWPMonad();
lean_mark_persistent(l_Std_Do_Option_instWPMonad);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Do_WP_Monad(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Do_WP_Basic(uint8_t builtin);
lean_object* initialize_Std_Do_WP_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Do_WP_Monad(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Do_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Do_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Do_WP_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Do_WP_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Do_WP_Monad(builtin);
}
#ifdef __cplusplus
}
#endif
