// Lean compiler output
// Module: Lean.Elab.Task
// Imports: public import Lean.Elab.Tactic.Basic
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_CancelToken_new();
lean_object* l_Lean_Core_wrapAsync___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_IO_CancelToken_set___boxed(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Core_CoreM_asTask___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_CoreM_asTask___redArg___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Core_CoreM_asTask___redArg___closed__0 = (const lean_object*)&l_Lean_Core_CoreM_asTask___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_MetaM_asTask___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_MetaM_asTask___redArg___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_MetaM_asTask___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_MetaM_asTask___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Term_TermElabM_asTask___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_TermElabM_asTask___redArg___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_TermElabM_asTask___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_TermElabM_asTask___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_TacticM_asTask___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__1___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_TacticM_asTask___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__0(lean_object* v_t_1_, lean_object* v_x_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___x_6_; 
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_6_ = lean_apply_3(v_t_1_, v___y_3_, v___y_4_, lean_box(0));
if (lean_obj_tag(v___x_6_) == 0)
{
lean_object* v_a_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_16_; 
v_a_7_ = lean_ctor_get(v___x_6_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v___x_6_);
if (v_isSharedCheck_16_ == 0)
{
v___x_9_ = v___x_6_;
v_isShared_10_ = v_isSharedCheck_16_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_a_7_);
lean_dec(v___x_6_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_16_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_14_; 
v___x_11_ = lean_st_ref_get(v___y_4_);
v___x_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_12_, 0, v_a_7_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
if (v_isShared_10_ == 0)
{
lean_ctor_set(v___x_9_, 0, v___x_12_);
v___x_14_ = v___x_9_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v___x_12_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
else
{
lean_object* v_a_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_24_; 
v_a_17_ = lean_ctor_get(v___x_6_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_6_);
if (v_isSharedCheck_24_ == 0)
{
v___x_19_ = v___x_6_;
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_a_17_);
lean_dec(v___x_6_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_22_; 
if (v_isShared_20_ == 0)
{
v___x_22_ = v___x_19_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_a_17_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__0___boxed(lean_object* v_t_25_, lean_object* v_x_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Core_CoreM_asTask___redArg___lam__0(v_t_25_, v_x_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__1(lean_object* v_a_31_, lean_object* v___x_32_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_apply_2(v_a_31_, v___x_32_, lean_box(0));
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_42_; 
v_a_35_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_42_ == 0)
{
v___x_37_ = v___x_34_;
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_34_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_40_; 
if (v_isShared_38_ == 0)
{
lean_ctor_set_tag(v___x_37_, 1);
v___x_40_ = v___x_37_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_a_35_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
else
{
lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_50_; 
v_a_43_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_50_ == 0)
{
v___x_45_ = v___x_34_;
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_a_43_);
lean_dec(v___x_34_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_48_; 
if (v_isShared_46_ == 0)
{
lean_ctor_set_tag(v___x_45_, 0);
v___x_48_ = v___x_45_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_a_43_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__1___boxed(lean_object* v_a_51_, lean_object* v___x_52_, lean_object* v___y_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Core_CoreM_asTask___redArg___lam__1(v_a_51_, v___x_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__2(lean_object* v_result_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
if (lean_obj_tag(v_result_55_) == 0)
{
lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_66_; 
v_a_59_ = lean_ctor_get(v_result_55_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v_result_55_);
if (v_isSharedCheck_66_ == 0)
{
v___x_61_ = v_result_55_;
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v_result_55_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_66_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_64_; 
if (v_isShared_62_ == 0)
{
lean_ctor_set_tag(v___x_61_, 1);
v___x_64_ = v___x_61_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_a_59_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
else
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_77_; 
v_a_67_ = lean_ctor_get(v_result_55_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v_result_55_);
if (v_isSharedCheck_77_ == 0)
{
v___x_69_ = v_result_55_;
v_isShared_70_ = v_isSharedCheck_77_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v_result_55_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_77_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v_fst_71_; lean_object* v_snd_72_; lean_object* v___x_73_; lean_object* v___x_75_; 
v_fst_71_ = lean_ctor_get(v_a_67_, 0);
lean_inc(v_fst_71_);
v_snd_72_ = lean_ctor_get(v_a_67_, 1);
lean_inc(v_snd_72_);
lean_dec(v_a_67_);
v___x_73_ = lean_st_ref_set(v___y_57_, v_snd_72_);
if (v_isShared_70_ == 0)
{
lean_ctor_set_tag(v___x_69_, 0);
lean_ctor_set(v___x_69_, 0, v_fst_71_);
v___x_75_ = v___x_69_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_fst_71_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__2___boxed(lean_object* v_result_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Core_CoreM_asTask___redArg___lam__2(v_result_78_, v___y_79_, v___y_80_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg(lean_object* v_t_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v___x_88_; lean_object* v___f_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_88_ = l_IO_CancelToken_new();
v___f_89_ = lean_alloc_closure((void*)(l_Lean_Core_CoreM_asTask___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_89_, 0, v_t_84_);
lean_inc(v___x_88_);
v___x_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_88_);
v___x_91_ = l_Lean_Core_wrapAsync___redArg(v___f_89_, v___x_90_, v_a_85_, v_a_86_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_108_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_108_ == 0)
{
v___x_94_ = v___x_91_;
v_isShared_95_ = v_isSharedCheck_108_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_91_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_108_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v___f_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___f_100_; lean_object* v___x_101_; uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_96_ = lean_box(0);
v___f_97_ = lean_alloc_closure((void*)(l_Lean_Core_CoreM_asTask___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_97_, 0, v_a_92_);
lean_closure_set(v___f_97_, 1, v___x_96_);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_io_as_task(v___f_97_, v___x_98_);
v___f_100_ = ((lean_object*)(l_Lean_Core_CoreM_asTask___redArg___closed__0));
v___x_101_ = lean_alloc_closure((void*)(l_IO_CancelToken_set___boxed), 2, 1);
lean_closure_set(v___x_101_, 0, v___x_88_);
v___x_102_ = 1;
v___x_103_ = lean_task_map(v___f_100_, v___x_99_, v___x_98_, v___x_102_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_101_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_104_);
v___x_106_ = v___x_94_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
else
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
lean_dec(v___x_88_);
v_a_109_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v___x_91_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_91_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___boxed(lean_object* v_t_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Core_CoreM_asTask___redArg(v_t_117_, v_a_118_, v_a_119_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask(lean_object* v_00_u03b1_122_, lean_object* v_t_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Core_CoreM_asTask___redArg(v_t_123_, v_a_124_, v_a_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___boxed(lean_object* v_00_u03b1_128_, lean_object* v_t_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Core_CoreM_asTask(v_00_u03b1_128_, v_t_129_, v_a_130_, v_a_131_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask_x27___redArg(lean_object* v_t_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Core_CoreM_asTask___redArg(v_t_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_147_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_147_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_147_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_147_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v_snd_143_; lean_object* v___x_145_; 
v_snd_143_ = lean_ctor_get(v_a_139_, 1);
lean_inc(v_snd_143_);
lean_dec(v_a_139_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v_snd_143_);
v___x_145_ = v___x_141_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_snd_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
v_a_148_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_138_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_138_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask_x27___redArg___boxed(lean_object* v_t_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_Core_CoreM_asTask_x27___redArg(v_t_156_, v_a_157_, v_a_158_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask_x27(lean_object* v_00_u03b1_161_, lean_object* v_t_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_Core_CoreM_asTask_x27___redArg(v_t_162_, v_a_163_, v_a_164_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask_x27___boxed(lean_object* v_00_u03b1_167_, lean_object* v_t_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_Core_CoreM_asTask_x27(v_00_u03b1_167_, v_t_168_, v_a_169_, v_a_170_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask___redArg___lam__0(lean_object* v_val_173_, lean_object* v_t_174_, lean_object* v_a_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_st_mk_ref(v_val_173_);
lean_inc(v___x_179_);
lean_inc_ref(v_a_175_);
v___x_180_ = lean_apply_5(v_t_174_, v_a_175_, v___x_179_, v___y_176_, v___y_177_, lean_box(0));
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_190_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_190_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_190_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_190_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_185_ = lean_st_ref_get(v___x_179_);
lean_dec(v___x_179_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v_a_181_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_186_);
v___x_188_ = v___x_183_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
else
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
lean_dec(v___x_179_);
v_a_191_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_180_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_180_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask___redArg___lam__0___boxed(lean_object* v_val_199_, lean_object* v_t_200_, lean_object* v_a_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Meta_MetaM_asTask___redArg___lam__0(v_val_199_, v_t_200_, v_a_201_, v___y_202_, v___y_203_);
lean_dec_ref(v_a_201_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask___redArg___lam__1(lean_object* v_c_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; 
lean_inc(v___y_210_);
lean_inc_ref(v___y_209_);
v___x_212_ = lean_apply_3(v_c_206_, v___y_209_, v___y_210_, lean_box(0));
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_223_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_223_ == 0)
{
v___x_215_ = v___x_212_;
v_isShared_216_ = v_isSharedCheck_223_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_212_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_223_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_fst_217_; lean_object* v_snd_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v_fst_217_ = lean_ctor_get(v_a_213_, 0);
lean_inc(v_fst_217_);
v_snd_218_ = lean_ctor_get(v_a_213_, 1);
lean_inc(v_snd_218_);
lean_dec(v_a_213_);
v___x_219_ = lean_st_ref_set(v___y_208_, v_snd_218_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v_fst_217_);
v___x_221_ = v___x_215_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_fst_217_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
v_a_224_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_212_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_212_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask___redArg___lam__1___boxed(lean_object* v_c_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Meta_MetaM_asTask___redArg___lam__1(v_c_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask___redArg(lean_object* v_t_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v___x_246_; lean_object* v___f_247_; lean_object* v___x_248_; 
v___x_246_ = lean_st_ref_get(v_a_242_);
lean_inc_ref(v_a_241_);
v___f_247_ = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_asTask___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_247_, 0, v___x_246_);
lean_closure_set(v___f_247_, 1, v_t_240_);
lean_closure_set(v___f_247_, 2, v_a_241_);
v___x_248_ = l_Lean_Core_CoreM_asTask___redArg(v___f_247_, v_a_243_, v_a_244_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_269_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_269_ == 0)
{
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_269_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_269_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v_fst_253_; lean_object* v_snd_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_268_; 
v_fst_253_ = lean_ctor_get(v_a_249_, 0);
v_snd_254_ = lean_ctor_get(v_a_249_, 1);
v_isSharedCheck_268_ = !lean_is_exclusive(v_a_249_);
if (v_isSharedCheck_268_ == 0)
{
v___x_256_ = v_a_249_;
v_isShared_257_ = v_isSharedCheck_268_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_snd_254_);
lean_inc(v_fst_253_);
lean_dec(v_a_249_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_268_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___f_258_; lean_object* v___x_259_; uint8_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v___f_258_ = ((lean_object*)(l_Lean_Meta_MetaM_asTask___redArg___closed__0));
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = 1;
v___x_261_ = lean_task_map(v___f_258_, v_snd_254_, v___x_259_, v___x_260_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 1, v___x_261_);
v___x_263_ = v___x_256_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_fst_253_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v___x_261_);
v___x_263_ = v_reuseFailAlloc_267_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_265_; 
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v___x_263_);
v___x_265_ = v___x_251_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
v_a_270_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_248_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_248_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask___redArg___boxed(lean_object* v_t_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Meta_MetaM_asTask___redArg(v_t_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask(lean_object* v_00_u03b1_285_, lean_object* v_t_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Lean_Meta_MetaM_asTask___redArg(v_t_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask___boxed(lean_object* v_00_u03b1_293_, lean_object* v_t_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Meta_MetaM_asTask(v_00_u03b1_293_, v_t_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask_x27___redArg(lean_object* v_t_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_Meta_MetaM_asTask___redArg(v_t_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_316_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_316_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_316_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_316_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v_snd_312_; lean_object* v___x_314_; 
v_snd_312_ = lean_ctor_get(v_a_308_, 1);
lean_inc(v_snd_312_);
lean_dec(v_a_308_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v_snd_312_);
v___x_314_ = v___x_310_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_snd_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
v_a_317_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_307_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_307_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask_x27___redArg___boxed(lean_object* v_t_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_Meta_MetaM_asTask_x27___redArg(v_t_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask_x27(lean_object* v_00_u03b1_332_, lean_object* v_t_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Meta_MetaM_asTask_x27___redArg(v_t_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask_x27___boxed(lean_object* v_00_u03b1_340_, lean_object* v_t_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Meta_MetaM_asTask_x27(v_00_u03b1_340_, v_t_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask___redArg___lam__0(lean_object* v_c_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; 
lean_inc(v___y_354_);
lean_inc_ref(v___y_353_);
lean_inc(v___y_352_);
lean_inc_ref(v___y_351_);
v___x_356_ = lean_apply_5(v_c_348_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, lean_box(0));
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_367_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_367_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_367_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_367_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_fst_361_; lean_object* v_snd_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v_fst_361_ = lean_ctor_get(v_a_357_, 0);
lean_inc(v_fst_361_);
v_snd_362_ = lean_ctor_get(v_a_357_, 1);
lean_inc(v_snd_362_);
lean_dec(v_a_357_);
v___x_363_ = lean_st_ref_set(v___y_350_, v_snd_362_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v_fst_361_);
v___x_365_ = v___x_359_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_fst_361_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
v_a_368_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_356_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_356_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask___redArg___lam__0___boxed(lean_object* v_c_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Elab_Term_TermElabM_asTask___redArg___lam__0(v_c_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask___redArg(lean_object* v_t_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_394_ = lean_st_ref_get(v_a_388_);
lean_inc_ref(v_a_387_);
v___x_395_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_TermElabM_run___boxed), 9, 4);
lean_closure_set(v___x_395_, 0, lean_box(0));
lean_closure_set(v___x_395_, 1, v_t_386_);
lean_closure_set(v___x_395_, 2, v_a_387_);
lean_closure_set(v___x_395_, 3, v___x_394_);
v___x_396_ = l_Lean_Meta_MetaM_asTask___redArg(v___x_395_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_417_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_417_ == 0)
{
v___x_399_ = v___x_396_;
v_isShared_400_ = v_isSharedCheck_417_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_417_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v_fst_401_; lean_object* v_snd_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_416_; 
v_fst_401_ = lean_ctor_get(v_a_397_, 0);
v_snd_402_ = lean_ctor_get(v_a_397_, 1);
v_isSharedCheck_416_ = !lean_is_exclusive(v_a_397_);
if (v_isSharedCheck_416_ == 0)
{
v___x_404_ = v_a_397_;
v_isShared_405_ = v_isSharedCheck_416_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_snd_402_);
lean_inc(v_fst_401_);
lean_dec(v_a_397_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_416_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___f_406_; lean_object* v___x_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_411_; 
v___f_406_ = ((lean_object*)(l_Lean_Elab_Term_TermElabM_asTask___redArg___closed__0));
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = 1;
v___x_409_ = lean_task_map(v___f_406_, v_snd_402_, v___x_407_, v___x_408_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v___x_409_);
v___x_411_ = v___x_404_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_fst_401_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v___x_409_);
v___x_411_ = v_reuseFailAlloc_415_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v___x_413_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_411_);
v___x_413_ = v___x_399_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
v_a_418_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_396_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_396_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask___redArg___boxed(lean_object* v_t_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Elab_Term_TermElabM_asTask___redArg(v_t_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask(lean_object* v_00_u03b1_435_, lean_object* v_t_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Elab_Term_TermElabM_asTask___redArg(v_t_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask___boxed(lean_object* v_00_u03b1_445_, lean_object* v_t_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Elab_Term_TermElabM_asTask(v_00_u03b1_445_, v_t_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask_x27___redArg(lean_object* v_t_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_Elab_Term_TermElabM_asTask___redArg(v_t_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_472_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_472_ == 0)
{
v___x_466_ = v___x_463_;
v_isShared_467_ = v_isSharedCheck_472_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_463_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_472_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v_snd_468_; lean_object* v___x_470_; 
v_snd_468_ = lean_ctor_get(v_a_464_, 1);
lean_inc(v_snd_468_);
lean_dec(v_a_464_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v_snd_468_);
v___x_470_ = v___x_466_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_snd_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
v_a_473_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_463_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_463_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask_x27___redArg___boxed(lean_object* v_t_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Elab_Term_TermElabM_asTask_x27___redArg(v_t_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask_x27(lean_object* v_00_u03b1_490_, lean_object* v_t_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Elab_Term_TermElabM_asTask_x27___redArg(v_t_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask_x27___boxed(lean_object* v_00_u03b1_500_, lean_object* v_t_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Elab_Term_TermElabM_asTask_x27(v_00_u03b1_500_, v_t_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__0(lean_object* v_val_510_, lean_object* v_t_511_, lean_object* v_a_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_st_mk_ref(v_val_510_);
lean_inc(v___x_520_);
lean_inc_ref(v_a_512_);
v___x_521_ = lean_apply_9(v_t_511_, v_a_512_, v___x_520_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, lean_box(0));
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_531_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_531_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_531_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_531_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_526_ = lean_st_ref_get(v___x_520_);
lean_dec(v___x_520_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v_a_522_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_527_);
v___x_529_ = v___x_524_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec(v___x_520_);
v_a_532_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_521_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_521_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__0___boxed(lean_object* v_val_540_, lean_object* v_t_541_, lean_object* v_a_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__0(v_val_540_, v_t_541_, v_a_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec_ref(v_a_542_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__1(lean_object* v_c_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v___x_561_; 
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
lean_inc(v___y_557_);
lean_inc_ref(v___y_556_);
lean_inc(v___y_555_);
lean_inc_ref(v___y_554_);
v___x_561_ = lean_apply_7(v_c_551_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, lean_box(0));
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_572_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_572_ == 0)
{
v___x_564_ = v___x_561_;
v_isShared_565_ = v_isSharedCheck_572_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_561_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_572_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v_fst_566_; lean_object* v_snd_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v_fst_566_ = lean_ctor_get(v_a_562_, 0);
lean_inc(v_fst_566_);
v_snd_567_ = lean_ctor_get(v_a_562_, 1);
lean_inc(v_snd_567_);
lean_dec(v_a_562_);
v___x_568_ = lean_st_ref_set(v___y_553_, v_snd_567_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v_fst_566_);
v___x_570_ = v___x_564_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_fst_566_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
v_a_573_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_561_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_561_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__1___boxed(lean_object* v_c_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__1(v_c_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg(lean_object* v_t_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v___x_603_; lean_object* v___f_604_; lean_object* v___x_605_; 
v___x_603_ = lean_st_ref_get(v_a_595_);
lean_inc_ref(v_a_594_);
v___f_604_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_604_, 0, v___x_603_);
lean_closure_set(v___f_604_, 1, v_t_593_);
lean_closure_set(v___f_604_, 2, v_a_594_);
v___x_605_ = l_Lean_Elab_Term_TermElabM_asTask___redArg(v___f_604_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_626_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_626_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_626_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_626_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v_fst_610_; lean_object* v_snd_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_625_; 
v_fst_610_ = lean_ctor_get(v_a_606_, 0);
v_snd_611_ = lean_ctor_get(v_a_606_, 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v_a_606_);
if (v_isSharedCheck_625_ == 0)
{
v___x_613_ = v_a_606_;
v_isShared_614_ = v_isSharedCheck_625_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_snd_611_);
lean_inc(v_fst_610_);
lean_dec(v_a_606_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_625_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___f_615_; lean_object* v___x_616_; uint8_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___f_615_ = ((lean_object*)(l_Lean_Elab_Tactic_TacticM_asTask___redArg___closed__0));
v___x_616_ = lean_unsigned_to_nat(8u);
v___x_617_ = 0;
v___x_618_ = lean_task_map(v___f_615_, v_snd_611_, v___x_616_, v___x_617_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v___x_618_);
v___x_620_ = v___x_613_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_fst_610_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v___x_618_);
v___x_620_ = v_reuseFailAlloc_624_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_622_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_620_);
v___x_622_ = v___x_608_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
v_a_627_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_605_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_605_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg___boxed(lean_object* v_t_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg(v_t_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask(lean_object* v_00_u03b1_646_, lean_object* v_t_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg(v_t_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___boxed(lean_object* v_00_u03b1_658_, lean_object* v_t_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_Elab_Tactic_TacticM_asTask(v_00_u03b1_658_, v_t_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg(lean_object* v_t_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg(v_t_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_689_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_689_ == 0)
{
v___x_683_ = v___x_680_;
v_isShared_684_ = v_isSharedCheck_689_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_680_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_689_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v_snd_685_; lean_object* v___x_687_; 
v_snd_685_ = lean_ctor_get(v_a_681_, 1);
lean_inc(v_snd_685_);
lean_dec(v_a_681_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v_snd_685_);
v___x_687_ = v___x_683_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_snd_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_690_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_680_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_680_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg___boxed(lean_object* v_t_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg(v_t_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask_x27(lean_object* v_00_u03b1_709_, lean_object* v_t_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg(v_t_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask_x27___boxed(lean_object* v_00_u03b1_721_, lean_object* v_t_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Elab_Tactic_TacticM_asTask_x27(v_00_u03b1_721_, v_t_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec_ref(v_a_727_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
return v_res_732_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Task(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Task(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Task(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Task(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Task(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Task(builtin);
}
#ifdef __cplusplus
}
#endif
