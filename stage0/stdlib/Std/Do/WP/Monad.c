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
lean_object* l_Std_Do_Except_instWP___aux__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_StateT_instWP___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_Reader_instWP(lean_object*);
lean_object* l_Std_Do_ExceptT_instWP___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_ReaderT_instWP___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_EStateM_instWP(lean_object*, lean_object*);
lean_object* l_Std_Do_OptionT_instWP___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_Option_instWP___aux__1(lean_object*, lean_object*);
lean_object* l_Std_Do_State_instWP___lam__1(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Std_Do_Except_instWPMonad___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Do_Except_instWP___aux__1, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Do_Except_instWPMonad___closed__0 = (const lean_object*)&l_Std_Do_Except_instWPMonad___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Do_Except_instWPMonad(lean_object*);
static const lean_closure_object l_Std_Do_Option_instWPMonad___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Do_Option_instWP___aux__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Do_Option_instWPMonad___closed__0 = (const lean_object*)&l_Std_Do_Option_instWPMonad___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Do_Option_instWPMonad = (const lean_object*)&l_Std_Do_Option_instWPMonad___closed__0_value;
static const lean_closure_object l_Std_Do_State_instWPMonad___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Do_State_instWP___lam__1, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Do_State_instWPMonad___closed__0 = (const lean_object*)&l_Std_Do_State_instWPMonad___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Do_State_instWPMonad(lean_object*);
static lean_once_cell_t l_Std_Do_Reader_instWPMonad___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do_Reader_instWPMonad___closed__0;
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
if (lean_obj_tag(v_x_42_) == 0)
{
lean_object* v_a_45_; lean_object* v___x_46_; 
lean_dec(v_h__1_43_);
v_a_45_ = lean_ctor_get(v_x_42_, 0);
lean_inc(v_a_45_);
lean_dec_ref(v_x_42_);
v___x_46_ = lean_apply_1(v_h__2_44_, v_a_45_);
return v___x_46_;
}
else
{
lean_object* v_a_47_; lean_object* v___x_48_; 
lean_dec(v_h__2_44_);
v_a_47_ = lean_ctor_get(v_x_42_, 0);
lean_inc(v_a_47_);
lean_dec_ref(v_x_42_);
v___x_48_ = lean_apply_1(v_h__1_43_, v_a_47_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__ExceptT_run__bind_match__1_splitter___redArg(lean_object* v_x_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_53_; 
lean_dec(v_h__1_50_);
v_a_52_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_a_52_);
lean_dec_ref(v_x_49_);
v___x_53_ = lean_apply_1(v_h__2_51_, v_a_52_);
return v___x_53_;
}
else
{
lean_object* v_a_54_; lean_object* v___x_55_; 
lean_dec(v_h__2_51_);
v_a_54_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_a_54_);
lean_dec_ref(v_x_49_);
v___x_55_ = lean_apply_1(v_h__1_50_, v_a_54_);
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__ExceptT_run__bind_match__1_splitter(lean_object* v_00_u03b5_56_, lean_object* v_00_u03b1_57_, lean_object* v_motive_58_, lean_object* v_x_59_, lean_object* v_h__1_60_, lean_object* v_h__2_61_){
_start:
{
if (lean_obj_tag(v_x_59_) == 0)
{
lean_object* v_a_62_; lean_object* v___x_63_; 
lean_dec(v_h__1_60_);
v_a_62_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_a_62_);
lean_dec_ref(v_x_59_);
v___x_63_ = lean_apply_1(v_h__2_61_, v_a_62_);
return v___x_63_;
}
else
{
lean_object* v_a_64_; lean_object* v___x_65_; 
lean_dec(v_h__2_61_);
v_a_64_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_a_64_);
lean_dec_ref(v_x_59_);
v___x_65_ = lean_apply_1(v_h__1_60_, v_a_64_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptT_instWPMonad___redArg(lean_object* v_inst_66_){
_start:
{
lean_object* v___f_67_; 
v___f_67_ = lean_alloc_closure((void*)(l_Std_Do_ExceptT_instWP___redArg___lam__0), 4, 1);
lean_closure_set(v___f_67_, 0, v_inst_66_);
return v___f_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptT_instWPMonad(lean_object* v_m_68_, lean_object* v_ps_69_, lean_object* v_00_u03b5_70_, lean_object* v_inst_71_, lean_object* v_inst_72_){
_start:
{
lean_object* v___f_73_; 
v___f_73_ = lean_alloc_closure((void*)(l_Std_Do_ExceptT_instWP___redArg___lam__0), 4, 1);
lean_closure_set(v___f_73_, 0, v_inst_72_);
return v___f_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptT_instWPMonad___boxed(lean_object* v_m_74_, lean_object* v_ps_75_, lean_object* v_00_u03b5_76_, lean_object* v_inst_77_, lean_object* v_inst_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Std_Do_ExceptT_instWPMonad(v_m_74_, v_ps_75_, v_00_u03b5_76_, v_inst_77_, v_inst_78_);
lean_dec_ref(v_inst_77_);
lean_dec(v_ps_75_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(lean_object* v_x_80_, lean_object* v_h__1_81_, lean_object* v_h__2_82_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec(v_h__1_81_);
v___x_83_ = lean_box(0);
v___x_84_ = lean_apply_1(v_h__2_82_, v___x_83_);
return v___x_84_;
}
else
{
lean_object* v_val_85_; lean_object* v___x_86_; 
lean_dec(v_h__2_82_);
v_val_85_ = lean_ctor_get(v_x_80_, 0);
lean_inc(v_val_85_);
lean_dec_ref(v_x_80_);
v___x_86_ = lean_apply_1(v_h__1_81_, v_val_85_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushOption_match__1_splitter(lean_object* v_00_u03b1_87_, lean_object* v_motive_88_, lean_object* v_x_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_){
_start:
{
if (lean_obj_tag(v_x_89_) == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; 
lean_dec(v_h__1_90_);
v___x_92_ = lean_box(0);
v___x_93_ = lean_apply_1(v_h__2_91_, v___x_92_);
return v___x_93_;
}
else
{
lean_object* v_val_94_; lean_object* v___x_95_; 
lean_dec(v_h__2_91_);
v_val_94_ = lean_ctor_get(v_x_89_, 0);
lean_inc(v_val_94_);
lean_dec_ref(v_x_89_);
v___x_95_ = lean_apply_1(v_h__1_90_, v_val_94_);
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Option_elim_match__1_splitter___redArg(lean_object* v_x_96_, lean_object* v_x_97_, lean_object* v_x_98_, lean_object* v_h__1_99_, lean_object* v_h__2_100_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
lean_object* v___x_101_; 
lean_dec(v_h__1_99_);
v___x_101_ = lean_apply_2(v_h__2_100_, v_x_97_, v_x_98_);
return v___x_101_;
}
else
{
lean_object* v_val_102_; lean_object* v___x_103_; 
lean_dec(v_h__2_100_);
v_val_102_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_val_102_);
lean_dec_ref(v_x_96_);
v___x_103_ = lean_apply_3(v_h__1_99_, v_val_102_, v_x_97_, v_x_98_);
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Option_elim_match__1_splitter(lean_object* v_00_u03b1_104_, lean_object* v_00_u03b2_105_, lean_object* v_motive_106_, lean_object* v_x_107_, lean_object* v_x_108_, lean_object* v_x_109_, lean_object* v_h__1_110_, lean_object* v_h__2_111_){
_start:
{
if (lean_obj_tag(v_x_107_) == 0)
{
lean_object* v___x_112_; 
lean_dec(v_h__1_110_);
v___x_112_ = lean_apply_2(v_h__2_111_, v_x_108_, v_x_109_);
return v___x_112_;
}
else
{
lean_object* v_val_113_; lean_object* v___x_114_; 
lean_dec(v_h__2_111_);
v_val_113_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_val_113_);
lean_dec_ref(v_x_107_);
v___x_114_ = lean_apply_3(v_h__1_110_, v_val_113_, v_x_108_, v_x_109_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_OptionT_instWPMonad___redArg(lean_object* v_inst_115_){
_start:
{
lean_object* v___f_116_; 
v___f_116_ = lean_alloc_closure((void*)(l_Std_Do_OptionT_instWP___redArg___lam__0), 4, 1);
lean_closure_set(v___f_116_, 0, v_inst_115_);
return v___f_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_OptionT_instWPMonad(lean_object* v_m_117_, lean_object* v_ps_118_, lean_object* v_inst_119_, lean_object* v_inst_120_){
_start:
{
lean_object* v___f_121_; 
v___f_121_ = lean_alloc_closure((void*)(l_Std_Do_OptionT_instWP___redArg___lam__0), 4, 1);
lean_closure_set(v___f_121_, 0, v_inst_120_);
return v___f_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_OptionT_instWPMonad___boxed(lean_object* v_m_122_, lean_object* v_ps_123_, lean_object* v_inst_124_, lean_object* v_inst_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Std_Do_OptionT_instWPMonad(v_m_122_, v_ps_123_, v_inst_124_, v_inst_125_);
lean_dec_ref(v_inst_124_);
lean_dec(v_ps_123_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__EStateM_run__bind_match__1_splitter___redArg(lean_object* v_x_127_, lean_object* v_h__1_128_, lean_object* v_h__2_129_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v_a_130_; lean_object* v_a_131_; lean_object* v___x_132_; 
lean_dec(v_h__2_129_);
v_a_130_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_a_130_);
v_a_131_ = lean_ctor_get(v_x_127_, 1);
lean_inc(v_a_131_);
lean_dec_ref(v_x_127_);
v___x_132_ = lean_apply_2(v_h__1_128_, v_a_130_, v_a_131_);
return v___x_132_;
}
else
{
lean_object* v_a_133_; lean_object* v_a_134_; lean_object* v___x_135_; 
lean_dec(v_h__1_128_);
v_a_133_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_a_133_);
v_a_134_ = lean_ctor_get(v_x_127_, 1);
lean_inc(v_a_134_);
lean_dec_ref(v_x_127_);
v___x_135_ = lean_apply_2(v_h__2_129_, v_a_133_, v_a_134_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__EStateM_run__bind_match__1_splitter(lean_object* v_00_u03b5_136_, lean_object* v_00_u03c3_137_, lean_object* v_00_u03b1_138_, lean_object* v_motive_139_, lean_object* v_x_140_, lean_object* v_h__1_141_, lean_object* v_h__2_142_){
_start:
{
if (lean_obj_tag(v_x_140_) == 0)
{
lean_object* v_a_143_; lean_object* v_a_144_; lean_object* v___x_145_; 
lean_dec(v_h__2_142_);
v_a_143_ = lean_ctor_get(v_x_140_, 0);
lean_inc(v_a_143_);
v_a_144_ = lean_ctor_get(v_x_140_, 1);
lean_inc(v_a_144_);
lean_dec_ref(v_x_140_);
v___x_145_ = lean_apply_2(v_h__1_141_, v_a_143_, v_a_144_);
return v___x_145_;
}
else
{
lean_object* v_a_146_; lean_object* v_a_147_; lean_object* v___x_148_; 
lean_dec(v_h__1_141_);
v_a_146_ = lean_ctor_get(v_x_140_, 0);
lean_inc(v_a_146_);
v_a_147_ = lean_ctor_get(v_x_140_, 1);
lean_inc(v_a_147_);
lean_dec_ref(v_x_140_);
v___x_148_ = lean_apply_2(v_h__2_142_, v_a_146_, v_a_147_);
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Std_Do_EStateM_instWP_match__1_splitter___redArg(lean_object* v_x_149_, lean_object* v_h__1_150_, lean_object* v_h__2_151_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
lean_object* v_a_152_; lean_object* v_a_153_; lean_object* v___x_154_; 
lean_dec(v_h__2_151_);
v_a_152_ = lean_ctor_get(v_x_149_, 0);
lean_inc(v_a_152_);
v_a_153_ = lean_ctor_get(v_x_149_, 1);
lean_inc(v_a_153_);
lean_dec_ref(v_x_149_);
v___x_154_ = lean_apply_2(v_h__1_150_, v_a_152_, v_a_153_);
return v___x_154_;
}
else
{
lean_object* v_a_155_; lean_object* v_a_156_; lean_object* v___x_157_; 
lean_dec(v_h__1_150_);
v_a_155_ = lean_ctor_get(v_x_149_, 0);
lean_inc(v_a_155_);
v_a_156_ = lean_ctor_get(v_x_149_, 1);
lean_inc(v_a_156_);
lean_dec_ref(v_x_149_);
v___x_157_ = lean_apply_2(v_h__2_151_, v_a_155_, v_a_156_);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_Monad_0__Std_Do_EStateM_instWP_match__1_splitter(lean_object* v_00_u03b5_158_, lean_object* v_00_u03c3_159_, lean_object* v_00_u03b1_160_, lean_object* v_motive_161_, lean_object* v_x_162_, lean_object* v_h__1_163_, lean_object* v_h__2_164_){
_start:
{
if (lean_obj_tag(v_x_162_) == 0)
{
lean_object* v_a_165_; lean_object* v_a_166_; lean_object* v___x_167_; 
lean_dec(v_h__2_164_);
v_a_165_ = lean_ctor_get(v_x_162_, 0);
lean_inc(v_a_165_);
v_a_166_ = lean_ctor_get(v_x_162_, 1);
lean_inc(v_a_166_);
lean_dec_ref(v_x_162_);
v___x_167_ = lean_apply_2(v_h__1_163_, v_a_165_, v_a_166_);
return v___x_167_;
}
else
{
lean_object* v_a_168_; lean_object* v_a_169_; lean_object* v___x_170_; 
lean_dec(v_h__1_163_);
v_a_168_ = lean_ctor_get(v_x_162_, 0);
lean_inc(v_a_168_);
v_a_169_ = lean_ctor_get(v_x_162_, 1);
lean_inc(v_a_169_);
lean_dec_ref(v_x_162_);
v___x_170_ = lean_apply_2(v_h__2_164_, v_a_168_, v_a_169_);
return v___x_170_;
}
}
}
static lean_object* _init_l_Std_Do_EStateM_instWPMonad___closed__0(void){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Std_Do_EStateM_instWP(lean_box(0), lean_box(0));
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_EStateM_instWPMonad(lean_object* v_00_u03b5_172_, lean_object* v_00_u03c3_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_obj_once(&l_Std_Do_EStateM_instWPMonad___closed__0, &l_Std_Do_EStateM_instWPMonad___closed__0_once, _init_l_Std_Do_EStateM_instWPMonad___closed__0);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Except_instWPMonad(lean_object* v_00_u03b5_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = ((lean_object*)(l_Std_Do_Except_instWPMonad___closed__0));
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_State_instWPMonad(lean_object* v_00_u03c3_181_){
_start:
{
lean_object* v___f_182_; 
v___f_182_ = ((lean_object*)(l_Std_Do_State_instWPMonad___closed__0));
return v___f_182_;
}
}
static lean_object* _init_l_Std_Do_Reader_instWPMonad___closed__0(void){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Std_Do_Reader_instWP(lean_box(0));
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_Reader_instWPMonad(lean_object* v_00_u03c1_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&l_Std_Do_Reader_instWPMonad___closed__0, &l_Std_Do_Reader_instWPMonad___closed__0_once, _init_l_Std_Do_Reader_instWPMonad___closed__0);
return v___x_185_;
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
