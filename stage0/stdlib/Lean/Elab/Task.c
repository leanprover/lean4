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
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_CancelToken_new();
lean_object* l_Lean_Core_wrapAsync___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_IO_CancelToken_set___boxed(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_IO_CancelToken_onSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Core_CoreM_asTask___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_CoreM_asTask___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l_Lean_Meta_MetaM_asTask___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_MetaM_asTask___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l_Lean_Elab_Tactic_TacticM_asTask___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_TacticM_asTask___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__0(lean_object* v_result_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
if (lean_obj_tag(v_result_1_) == 0)
{
lean_object* v_a_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_12_; 
v_a_5_ = lean_ctor_get(v_result_1_, 0);
v_isSharedCheck_12_ = !lean_is_exclusive(v_result_1_);
if (v_isSharedCheck_12_ == 0)
{
v___x_7_ = v_result_1_;
v_isShared_8_ = v_isSharedCheck_12_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_a_5_);
lean_dec(v_result_1_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_12_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_10_; 
if (v_isShared_8_ == 0)
{
lean_ctor_set_tag(v___x_7_, 1);
v___x_10_ = v___x_7_;
goto v_reusejp_9_;
}
else
{
lean_object* v_reuseFailAlloc_11_; 
v_reuseFailAlloc_11_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_11_, 0, v_a_5_);
v___x_10_ = v_reuseFailAlloc_11_;
goto v_reusejp_9_;
}
v_reusejp_9_:
{
return v___x_10_;
}
}
}
else
{
lean_object* v_a_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_a_13_ = lean_ctor_get(v_result_1_, 0);
v_isSharedCheck_23_ = !lean_is_exclusive(v_result_1_);
if (v_isSharedCheck_23_ == 0)
{
v___x_15_ = v_result_1_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_a_13_);
lean_dec(v_result_1_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v_fst_17_; lean_object* v_snd_18_; lean_object* v___x_19_; lean_object* v___x_21_; 
v_fst_17_ = lean_ctor_get(v_a_13_, 0);
lean_inc(v_fst_17_);
v_snd_18_ = lean_ctor_get(v_a_13_, 1);
lean_inc(v_snd_18_);
lean_dec(v_a_13_);
v___x_19_ = lean_st_ref_swap(v___y_3_, v_snd_18_);
lean_dec(v___x_19_);
if (v_isShared_16_ == 0)
{
lean_ctor_set_tag(v___x_15_, 0);
lean_ctor_set(v___x_15_, 0, v_fst_17_);
v___x_21_ = v___x_15_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_fst_17_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_asTask___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_result_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v_res_24_;
v_res_24_ = l_Lean_Core_CoreM_asTask___redArg___lam__0(v_result_1_, v___y_2_, v___y_3_);
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__0___boxed(lean_object* v_result_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Core_CoreM_asTask___redArg___lam__0(v_result_25_, v___y_26_, v___y_27_);
lean_dec(v___y_27_);
lean_dec_ref(v___y_26_);
return v_res_29_;
}
}
lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__1(lean_object* v_t_30_, lean_object* v_x_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v___x_35_; 
lean_inc(v___y_33_);
lean_inc_ref(v___y_32_);
v___x_35_ = lean_apply_3(v_t_30_, v___y_32_, v___y_33_, lean_box(0));
if (lean_obj_tag(v___x_35_) == 0)
{
lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_45_; 
v_a_36_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_45_ == 0)
{
v___x_38_ = v___x_35_;
v_isShared_39_ = v_isSharedCheck_45_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_dec(v___x_35_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_45_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_43_; 
v___x_40_ = lean_st_ref_get(v___y_33_);
v___x_41_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_41_, 0, v_a_36_);
lean_ctor_set(v___x_41_, 1, v___x_40_);
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 0, v___x_41_);
v___x_43_ = v___x_38_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_41_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
else
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_53_; 
v_a_46_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_53_ == 0)
{
v___x_48_ = v___x_35_;
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_35_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_51_; 
if (v_isShared_49_ == 0)
{
v___x_51_ = v___x_48_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_a_46_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
return v___x_51_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_asTask___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_30_ = stack[0].m_obj;
lean_object* v_x_31_ = stack[1].m_obj;
lean_object* v___y_32_ = stack[2].m_obj;
lean_object* v___y_33_ = stack[3].m_obj;
lean_object* v_res_54_;
v_res_54_ = l_Lean_Core_CoreM_asTask___redArg___lam__1(v_t_30_, v_x_31_, v___y_32_, v___y_33_);
stack->m_obj
 = v_res_54_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__1___boxed(lean_object* v_t_55_, lean_object* v_x_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Core_CoreM_asTask___redArg___lam__1(v_t_55_, v_x_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
return v_res_60_;
}
}
lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__2(lean_object* v_a_61_, lean_object* v___x_62_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_apply_2(v_a_61_, v___x_62_, lean_box(0));
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_72_; 
v_a_65_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_72_ == 0)
{
v___x_67_ = v___x_64_;
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v___x_64_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_70_; 
if (v_isShared_68_ == 0)
{
lean_ctor_set_tag(v___x_67_, 1);
v___x_70_ = v___x_67_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_a_65_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
else
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
v_a_73_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v___x_64_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_64_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
lean_ctor_set_tag(v___x_75_, 0);
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_asTask___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_61_ = stack[0].m_obj;
lean_object* v___x_62_ = stack[1].m_obj;
lean_object* v_res_81_;
v_res_81_ = l_Lean_Core_CoreM_asTask___redArg___lam__2(v_a_61_, v___x_62_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___lam__2___boxed(lean_object* v_a_82_, lean_object* v___x_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Core_CoreM_asTask___redArg___lam__2(v_a_82_, v___x_83_);
return v_res_85_;
}
}
lean_object* l_Lean_Core_CoreM_asTask___redArg(lean_object* v_t_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___f_91_; lean_object* v___f_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___f_91_ = ((lean_object*)(l_Lean_Core_CoreM_asTask___redArg___closed__0));
v___f_92_ = lean_alloc_closure((void*)(l_Lean_Core_CoreM_asTask___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_92_, 0, v_t_87_);
v___x_93_ = l_IO_CancelToken_new();
lean_inc_ref(v___x_93_);
v___x_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
v___x_95_ = l_Lean_Core_wrapAsync___redArg(v___f_92_, v___x_94_, v_a_88_, v_a_89_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_117_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_117_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_117_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_117_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___f_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v_toCold_112_; lean_object* v_cancelTk_x3f_113_; 
v___x_100_ = lean_box(0);
v___f_101_ = lean_alloc_closure((void*)(l_Lean_Core_CoreM_asTask___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_101_, 0, v_a_96_);
lean_closure_set(v___f_101_, 1, v___x_100_);
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_io_as_task(v___f_101_, v___x_102_);
v_toCold_112_ = lean_ctor_get(v_a_88_, 0);
v_cancelTk_x3f_113_ = lean_ctor_get(v_toCold_112_, 10);
if (lean_obj_tag(v_cancelTk_x3f_113_) == 1)
{
lean_object* v_val_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_val_114_ = lean_ctor_get(v_cancelTk_x3f_113_, 0);
lean_inc_ref(v___x_93_);
v___x_115_ = lean_alloc_closure((void*)(l_IO_CancelToken_set___boxed), 2, 1);
lean_closure_set(v___x_115_, 0, v___x_93_);
v___x_116_ = l_IO_CancelToken_onSet(v_val_114_, v___x_115_);
goto v___jp_104_;
}
else
{
goto v___jp_104_;
}
v___jp_104_:
{
lean_object* v___x_105_; uint8_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_105_ = lean_alloc_closure((void*)(l_IO_CancelToken_set___boxed), 2, 1);
lean_closure_set(v___x_105_, 0, v___x_93_);
v___x_106_ = 1;
v___x_107_ = lean_task_map(v___f_91_, v___x_103_, v___x_102_, v___x_106_);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_105_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_108_);
v___x_110_ = v___x_98_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
lean_dec_ref(v___x_93_);
v_a_118_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_95_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_95_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_asTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_87_ = stack[0].m_obj;
lean_object* v_a_88_ = stack[1].m_obj;
lean_object* v_a_89_ = stack[2].m_obj;
lean_object* v_res_126_;
v_res_126_ = l_Lean_Core_CoreM_asTask___redArg(v_t_87_, v_a_88_, v_a_89_);
stack->m_obj
 = v_res_126_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___redArg___boxed(lean_object* v_t_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Core_CoreM_asTask___redArg(v_t_127_, v_a_128_, v_a_129_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
return v_res_131_;
}
}
lean_object* l_Lean_Core_CoreM_asTask(lean_object* v_00_u03b1_132_, lean_object* v_t_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_Core_CoreM_asTask___redArg(v_t_133_, v_a_134_, v_a_135_);
return v___x_137_;
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_asTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_133_ = stack[1].m_obj;
lean_object* v_a_134_ = stack[2].m_obj;
lean_object* v_a_135_ = stack[3].m_obj;
lean_object* v_res_138_;
v_res_138_ = l_Lean_Core_CoreM_asTask(lean_box(0), v_t_133_, v_a_134_, v_a_135_);
stack->m_obj
 = v_res_138_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask___boxed(lean_object* v_00_u03b1_139_, lean_object* v_t_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Core_CoreM_asTask(v_00_u03b1_139_, v_t_140_, v_a_141_, v_a_142_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
return v_res_144_;
}
}
lean_object* l_Lean_Core_CoreM_asTask_x27___redArg(lean_object* v_t_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_Core_CoreM_asTask___redArg(v_t_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_158_; 
v_a_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_158_ == 0)
{
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v_snd_154_; lean_object* v___x_156_; 
v_snd_154_ = lean_ctor_get(v_a_150_, 1);
lean_inc(v_snd_154_);
lean_dec(v_a_150_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v_snd_154_);
v___x_156_ = v___x_152_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_snd_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
v_a_159_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_149_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_149_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_asTask_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_145_ = stack[0].m_obj;
lean_object* v_a_146_ = stack[1].m_obj;
lean_object* v_a_147_ = stack[2].m_obj;
lean_object* v_res_167_;
v_res_167_ = l_Lean_Core_CoreM_asTask_x27___redArg(v_t_145_, v_a_146_, v_a_147_);
stack->m_obj
 = v_res_167_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask_x27___redArg___boxed(lean_object* v_t_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_Core_CoreM_asTask_x27___redArg(v_t_168_, v_a_169_, v_a_170_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
return v_res_172_;
}
}
lean_object* l_Lean_Core_CoreM_asTask_x27(lean_object* v_00_u03b1_173_, lean_object* v_t_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Core_CoreM_asTask_x27___redArg(v_t_174_, v_a_175_, v_a_176_);
return v___x_178_;
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_asTask_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_174_ = stack[1].m_obj;
lean_object* v_a_175_ = stack[2].m_obj;
lean_object* v_a_176_ = stack[3].m_obj;
lean_object* v_res_179_;
v_res_179_ = l_Lean_Core_CoreM_asTask_x27(lean_box(0), v_t_174_, v_a_175_, v_a_176_);
stack->m_obj
 = v_res_179_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_asTask_x27___boxed(lean_object* v_00_u03b1_180_, lean_object* v_t_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Core_CoreM_asTask_x27(v_00_u03b1_180_, v_t_181_, v_a_182_, v_a_183_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
return v_res_185_;
}
}
lean_object* l_Lean_Meta_MetaM_asTask___redArg___lam__0(lean_object* v_c_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_192_; 
lean_inc(v___y_190_);
lean_inc_ref(v___y_189_);
v___x_192_ = lean_apply_3(v_c_186_, v___y_189_, v___y_190_, lean_box(0));
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_203_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_203_ == 0)
{
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_203_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_203_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v_fst_197_; lean_object* v_snd_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
v_fst_197_ = lean_ctor_get(v_a_193_, 0);
lean_inc(v_fst_197_);
v_snd_198_ = lean_ctor_get(v_a_193_, 1);
lean_inc(v_snd_198_);
lean_dec(v_a_193_);
v___x_199_ = lean_st_ref_swap(v___y_188_, v_snd_198_);
lean_dec(v___x_199_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v_fst_197_);
v___x_201_ = v___x_195_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_fst_197_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
v_a_204_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_192_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_192_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
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
}
LEAN_EXPORT void l_Lean_Meta_MetaM_asTask___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_186_ = stack[0].m_obj;
lean_object* v___y_187_ = stack[1].m_obj;
lean_object* v___y_188_ = stack[2].m_obj;
lean_object* v___y_189_ = stack[3].m_obj;
lean_object* v___y_190_ = stack[4].m_obj;
lean_object* v_res_212_;
v_res_212_ = l_Lean_Meta_MetaM_asTask___redArg___lam__0(v_c_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
stack->m_obj
 = v_res_212_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask___redArg___lam__0___boxed(lean_object* v_c_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Meta_MetaM_asTask___redArg___lam__0(v_c_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
return v_res_219_;
}
}
lean_object* l_Lean_Meta_MetaM_asTask___redArg___lam__1(lean_object* v_val_220_, lean_object* v_t_221_, lean_object* v_a_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_st_mk_ref(v_val_220_);
lean_inc(v___x_226_);
lean_inc_ref(v_a_222_);
v___x_227_ = lean_apply_5(v_t_221_, v_a_222_, v___x_226_, v___y_223_, v___y_224_, lean_box(0));
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_237_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_237_ == 0)
{
v___x_230_ = v___x_227_;
v_isShared_231_ = v_isSharedCheck_237_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_237_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_232_ = lean_st_ref_get(v___x_226_);
lean_dec(v___x_226_);
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v_a_228_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_233_);
v___x_235_ = v___x_230_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_dec(v___x_226_);
v_a_238_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_227_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_227_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MetaM_asTask___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_220_ = stack[0].m_obj;
lean_object* v_t_221_ = stack[1].m_obj;
lean_object* v_a_222_ = stack[2].m_obj;
lean_object* v___y_223_ = stack[3].m_obj;
lean_object* v___y_224_ = stack[4].m_obj;
lean_object* v_res_246_;
v_res_246_ = l_Lean_Meta_MetaM_asTask___redArg___lam__1(v_val_220_, v_t_221_, v_a_222_, v___y_223_, v___y_224_);
stack->m_obj
 = v_res_246_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask___redArg___lam__1___boxed(lean_object* v_val_247_, lean_object* v_t_248_, lean_object* v_a_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Meta_MetaM_asTask___redArg___lam__1(v_val_247_, v_t_248_, v_a_249_, v___y_250_, v___y_251_);
lean_dec_ref(v_a_249_);
return v_res_253_;
}
}
lean_object* l_Lean_Meta_MetaM_asTask___redArg(lean_object* v_t_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___f_261_; lean_object* v___x_262_; lean_object* v___f_263_; lean_object* v___x_264_; 
v___f_261_ = ((lean_object*)(l_Lean_Meta_MetaM_asTask___redArg___closed__0));
v___x_262_ = lean_st_ref_get(v_a_257_);
lean_inc_ref(v_a_256_);
v___f_263_ = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_asTask___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_263_, 0, v___x_262_);
lean_closure_set(v___f_263_, 1, v_t_255_);
lean_closure_set(v___f_263_, 2, v_a_256_);
v___x_264_ = l_Lean_Core_CoreM_asTask___redArg(v___f_263_, v_a_258_, v_a_259_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_284_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_284_ == 0)
{
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_284_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_284_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v_fst_269_; lean_object* v_snd_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_283_; 
v_fst_269_ = lean_ctor_get(v_a_265_, 0);
v_snd_270_ = lean_ctor_get(v_a_265_, 1);
v_isSharedCheck_283_ = !lean_is_exclusive(v_a_265_);
if (v_isSharedCheck_283_ == 0)
{
v___x_272_ = v_a_265_;
v_isShared_273_ = v_isSharedCheck_283_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_snd_270_);
lean_inc(v_fst_269_);
lean_dec(v_a_265_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_283_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = 1;
v___x_276_ = lean_task_map(v___f_261_, v_snd_270_, v___x_274_, v___x_275_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 1, v___x_276_);
v___x_278_ = v___x_272_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_fst_269_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___x_276_);
v___x_278_ = v_reuseFailAlloc_282_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_280_; 
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_278_);
v___x_280_ = v___x_267_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
v_a_285_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_264_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_264_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MetaM_asTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_255_ = stack[0].m_obj;
lean_object* v_a_256_ = stack[1].m_obj;
lean_object* v_a_257_ = stack[2].m_obj;
lean_object* v_a_258_ = stack[3].m_obj;
lean_object* v_a_259_ = stack[4].m_obj;
lean_object* v_res_293_;
v_res_293_ = l_Lean_Meta_MetaM_asTask___redArg(v_t_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
stack->m_obj
 = v_res_293_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask___redArg___boxed(lean_object* v_t_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Meta_MetaM_asTask___redArg(v_t_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
return v_res_300_;
}
}
lean_object* l_Lean_Meta_MetaM_asTask(lean_object* v_00_u03b1_301_, lean_object* v_t_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_Meta_MetaM_asTask___redArg(v_t_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
return v___x_308_;
}
}
LEAN_EXPORT void l_Lean_Meta_MetaM_asTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_302_ = stack[1].m_obj;
lean_object* v_a_303_ = stack[2].m_obj;
lean_object* v_a_304_ = stack[3].m_obj;
lean_object* v_a_305_ = stack[4].m_obj;
lean_object* v_a_306_ = stack[5].m_obj;
lean_object* v_res_309_;
v_res_309_ = l_Lean_Meta_MetaM_asTask(lean_box(0), v_t_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
stack->m_obj
 = v_res_309_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask___boxed(lean_object* v_00_u03b1_310_, lean_object* v_t_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Meta_MetaM_asTask(v_00_u03b1_310_, v_t_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
return v_res_317_;
}
}
lean_object* l_Lean_Meta_MetaM_asTask_x27___redArg(lean_object* v_t_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Meta_MetaM_asTask___redArg(v_t_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_333_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_333_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_333_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_333_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v_snd_329_; lean_object* v___x_331_; 
v_snd_329_ = lean_ctor_get(v_a_325_, 1);
lean_inc(v_snd_329_);
lean_dec(v_a_325_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v_snd_329_);
v___x_331_ = v___x_327_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_snd_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
v_a_334_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_324_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_324_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MetaM_asTask_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_318_ = stack[0].m_obj;
lean_object* v_a_319_ = stack[1].m_obj;
lean_object* v_a_320_ = stack[2].m_obj;
lean_object* v_a_321_ = stack[3].m_obj;
lean_object* v_a_322_ = stack[4].m_obj;
lean_object* v_res_342_;
v_res_342_ = l_Lean_Meta_MetaM_asTask_x27___redArg(v_t_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
stack->m_obj
 = v_res_342_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask_x27___redArg___boxed(lean_object* v_t_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Meta_MetaM_asTask_x27___redArg(v_t_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
return v_res_349_;
}
}
lean_object* l_Lean_Meta_MetaM_asTask_x27(lean_object* v_00_u03b1_350_, lean_object* v_t_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Meta_MetaM_asTask_x27___redArg(v_t_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
return v___x_357_;
}
}
LEAN_EXPORT void l_Lean_Meta_MetaM_asTask_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_351_ = stack[1].m_obj;
lean_object* v_a_352_ = stack[2].m_obj;
lean_object* v_a_353_ = stack[3].m_obj;
lean_object* v_a_354_ = stack[4].m_obj;
lean_object* v_a_355_ = stack[5].m_obj;
lean_object* v_res_358_;
v_res_358_ = l_Lean_Meta_MetaM_asTask_x27(lean_box(0), v_t_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
stack->m_obj
 = v_res_358_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_asTask_x27___boxed(lean_object* v_00_u03b1_359_, lean_object* v_t_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Meta_MetaM_asTask_x27(v_00_u03b1_359_, v_t_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
return v_res_366_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_asTask___redArg___lam__0(lean_object* v_c_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; 
lean_inc(v___y_373_);
lean_inc_ref(v___y_372_);
lean_inc(v___y_371_);
lean_inc_ref(v___y_370_);
v___x_375_ = lean_apply_5(v_c_367_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, lean_box(0));
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_386_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_386_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_386_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_386_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v_fst_380_; lean_object* v_snd_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
v_fst_380_ = lean_ctor_get(v_a_376_, 0);
lean_inc(v_fst_380_);
v_snd_381_ = lean_ctor_get(v_a_376_, 1);
lean_inc(v_snd_381_);
lean_dec(v_a_376_);
v___x_382_ = lean_st_ref_swap(v___y_369_, v_snd_381_);
lean_dec(v___x_382_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v_fst_380_);
v___x_384_ = v___x_378_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_fst_380_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
v_a_387_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_375_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_375_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_asTask___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_367_ = stack[0].m_obj;
lean_object* v___y_368_ = stack[1].m_obj;
lean_object* v___y_369_ = stack[2].m_obj;
lean_object* v___y_370_ = stack[3].m_obj;
lean_object* v___y_371_ = stack[4].m_obj;
lean_object* v___y_372_ = stack[5].m_obj;
lean_object* v___y_373_ = stack[6].m_obj;
lean_object* v_res_395_;
v_res_395_ = l_Lean_Elab_Term_TermElabM_asTask___redArg___lam__0(v_c_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
stack->m_obj
 = v_res_395_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask___redArg___lam__0___boxed(lean_object* v_c_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Elab_Term_TermElabM_asTask___redArg___lam__0(v_c_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
return v_res_404_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_asTask___redArg(lean_object* v_t_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v___f_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___f_414_ = ((lean_object*)(l_Lean_Elab_Term_TermElabM_asTask___redArg___closed__0));
v___x_415_ = lean_st_ref_get(v_a_408_);
lean_inc_ref(v_a_407_);
v___x_416_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_TermElabM_run___boxed), 9, 4);
lean_closure_set(v___x_416_, 0, lean_box(0));
lean_closure_set(v___x_416_, 1, v_t_406_);
lean_closure_set(v___x_416_, 2, v_a_407_);
lean_closure_set(v___x_416_, 3, v___x_415_);
v___x_417_ = l_Lean_Meta_MetaM_asTask___redArg(v___x_416_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_437_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_437_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_437_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_437_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v_fst_422_; lean_object* v_snd_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_436_; 
v_fst_422_ = lean_ctor_get(v_a_418_, 0);
v_snd_423_ = lean_ctor_get(v_a_418_, 1);
v_isSharedCheck_436_ = !lean_is_exclusive(v_a_418_);
if (v_isSharedCheck_436_ == 0)
{
v___x_425_ = v_a_418_;
v_isShared_426_ = v_isSharedCheck_436_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_snd_423_);
lean_inc(v_fst_422_);
lean_dec(v_a_418_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_436_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; uint8_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = 1;
v___x_429_ = lean_task_map(v___f_414_, v_snd_423_, v___x_427_, v___x_428_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 1, v___x_429_);
v___x_431_ = v___x_425_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_fst_422_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___x_429_);
v___x_431_ = v_reuseFailAlloc_435_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_433_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_431_);
v___x_433_ = v___x_420_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
v_a_438_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_417_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_417_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_asTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_406_ = stack[0].m_obj;
lean_object* v_a_407_ = stack[1].m_obj;
lean_object* v_a_408_ = stack[2].m_obj;
lean_object* v_a_409_ = stack[3].m_obj;
lean_object* v_a_410_ = stack[4].m_obj;
lean_object* v_a_411_ = stack[5].m_obj;
lean_object* v_a_412_ = stack[6].m_obj;
lean_object* v_res_446_;
v_res_446_ = l_Lean_Elab_Term_TermElabM_asTask___redArg(v_t_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
stack->m_obj
 = v_res_446_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask___redArg___boxed(lean_object* v_t_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Elab_Term_TermElabM_asTask___redArg(v_t_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
return v_res_455_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_asTask(lean_object* v_00_u03b1_456_, lean_object* v_t_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Elab_Term_TermElabM_asTask___redArg(v_t_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
return v___x_465_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_asTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_457_ = stack[1].m_obj;
lean_object* v_a_458_ = stack[2].m_obj;
lean_object* v_a_459_ = stack[3].m_obj;
lean_object* v_a_460_ = stack[4].m_obj;
lean_object* v_a_461_ = stack[5].m_obj;
lean_object* v_a_462_ = stack[6].m_obj;
lean_object* v_a_463_ = stack[7].m_obj;
lean_object* v_res_466_;
v_res_466_ = l_Lean_Elab_Term_TermElabM_asTask(lean_box(0), v_t_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
stack->m_obj
 = v_res_466_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask___boxed(lean_object* v_00_u03b1_467_, lean_object* v_t_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Elab_Term_TermElabM_asTask(v_00_u03b1_467_, v_t_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
return v_res_476_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_asTask_x27___redArg(lean_object* v_t_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_Elab_Term_TermElabM_asTask___redArg(v_t_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_494_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_494_ == 0)
{
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_494_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_494_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v_snd_490_; lean_object* v___x_492_; 
v_snd_490_ = lean_ctor_get(v_a_486_, 1);
lean_inc(v_snd_490_);
lean_dec(v_a_486_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v_snd_490_);
v___x_492_ = v___x_488_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_snd_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
v_a_495_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_485_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_485_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_asTask_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_477_ = stack[0].m_obj;
lean_object* v_a_478_ = stack[1].m_obj;
lean_object* v_a_479_ = stack[2].m_obj;
lean_object* v_a_480_ = stack[3].m_obj;
lean_object* v_a_481_ = stack[4].m_obj;
lean_object* v_a_482_ = stack[5].m_obj;
lean_object* v_a_483_ = stack[6].m_obj;
lean_object* v_res_503_;
v_res_503_ = l_Lean_Elab_Term_TermElabM_asTask_x27___redArg(v_t_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
stack->m_obj
 = v_res_503_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask_x27___redArg___boxed(lean_object* v_t_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_Elab_Term_TermElabM_asTask_x27___redArg(v_t_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_507_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
return v_res_512_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_asTask_x27(lean_object* v_00_u03b1_513_, lean_object* v_t_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_Elab_Term_TermElabM_asTask_x27___redArg(v_t_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
return v___x_522_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_asTask_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_514_ = stack[1].m_obj;
lean_object* v_a_515_ = stack[2].m_obj;
lean_object* v_a_516_ = stack[3].m_obj;
lean_object* v_a_517_ = stack[4].m_obj;
lean_object* v_a_518_ = stack[5].m_obj;
lean_object* v_a_519_ = stack[6].m_obj;
lean_object* v_a_520_ = stack[7].m_obj;
lean_object* v_res_523_;
v_res_523_ = l_Lean_Elab_Term_TermElabM_asTask_x27(lean_box(0), v_t_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
stack->m_obj
 = v_res_523_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_asTask_x27___boxed(lean_object* v_00_u03b1_524_, lean_object* v_t_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_Elab_Term_TermElabM_asTask_x27(v_00_u03b1_524_, v_t_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
lean_dec(v_a_531_);
lean_dec_ref(v_a_530_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_528_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
return v_res_533_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__0(lean_object* v_c_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___x_544_; 
lean_inc(v___y_542_);
lean_inc_ref(v___y_541_);
lean_inc(v___y_540_);
lean_inc_ref(v___y_539_);
lean_inc(v___y_538_);
lean_inc_ref(v___y_537_);
v___x_544_ = lean_apply_7(v_c_534_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, lean_box(0));
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_555_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_555_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_555_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_555_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v_fst_549_; lean_object* v_snd_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v_fst_549_ = lean_ctor_get(v_a_545_, 0);
lean_inc(v_fst_549_);
v_snd_550_ = lean_ctor_get(v_a_545_, 1);
lean_inc(v_snd_550_);
lean_dec(v_a_545_);
v___x_551_ = lean_st_ref_swap(v___y_536_, v_snd_550_);
lean_dec(v___x_551_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v_fst_549_);
v___x_553_ = v___x_547_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_fst_549_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_a_556_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_544_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_544_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_534_ = stack[0].m_obj;
lean_object* v___y_535_ = stack[1].m_obj;
lean_object* v___y_536_ = stack[2].m_obj;
lean_object* v___y_537_ = stack[3].m_obj;
lean_object* v___y_538_ = stack[4].m_obj;
lean_object* v___y_539_ = stack[5].m_obj;
lean_object* v___y_540_ = stack[6].m_obj;
lean_object* v___y_541_ = stack[7].m_obj;
lean_object* v___y_542_ = stack[8].m_obj;
lean_object* v_res_564_;
v_res_564_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__0(v_c_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
stack->m_obj
 = v_res_564_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__0___boxed(lean_object* v_c_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__0(v_c_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
return v_res_575_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__1(lean_object* v_val_576_, lean_object* v_t_577_, lean_object* v_a_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_st_mk_ref(v_val_576_);
lean_inc(v___x_586_);
lean_inc_ref(v_a_578_);
v___x_587_ = lean_apply_9(v_t_577_, v_a_578_, v___x_586_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, lean_box(0));
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_597_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_597_ == 0)
{
v___x_590_ = v___x_587_;
v_isShared_591_ = v_isSharedCheck_597_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_597_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_592_ = lean_st_ref_get(v___x_586_);
lean_dec(v___x_586_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v_a_588_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_593_);
v___x_595_ = v___x_590_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec(v___x_586_);
v_a_598_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_587_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_587_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_576_ = stack[0].m_obj;
lean_object* v_t_577_ = stack[1].m_obj;
lean_object* v_a_578_ = stack[2].m_obj;
lean_object* v___y_579_ = stack[3].m_obj;
lean_object* v___y_580_ = stack[4].m_obj;
lean_object* v___y_581_ = stack[5].m_obj;
lean_object* v___y_582_ = stack[6].m_obj;
lean_object* v___y_583_ = stack[7].m_obj;
lean_object* v___y_584_ = stack[8].m_obj;
lean_object* v_res_606_;
v_res_606_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__1(v_val_576_, v_t_577_, v_a_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
stack->m_obj
 = v_res_606_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__1___boxed(lean_object* v_val_607_, lean_object* v_t_608_, lean_object* v_a_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__1(v_val_607_, v_t_608_, v_a_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec_ref(v_a_609_);
return v_res_617_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg(lean_object* v_t_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v___f_629_; lean_object* v___x_630_; lean_object* v___f_631_; lean_object* v___x_632_; 
v___f_629_ = ((lean_object*)(l_Lean_Elab_Tactic_TacticM_asTask___redArg___closed__0));
v___x_630_ = lean_st_ref_get(v_a_621_);
lean_inc_ref(v_a_620_);
v___f_631_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_TacticM_asTask___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_631_, 0, v___x_630_);
lean_closure_set(v___f_631_, 1, v_t_619_);
lean_closure_set(v___f_631_, 2, v_a_620_);
v___x_632_ = l_Lean_Elab_Term_TermElabM_asTask___redArg(v___f_631_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_652_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_652_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_652_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_652_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_fst_637_; lean_object* v_snd_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_651_; 
v_fst_637_ = lean_ctor_get(v_a_633_, 0);
v_snd_638_ = lean_ctor_get(v_a_633_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_a_633_);
if (v_isSharedCheck_651_ == 0)
{
v___x_640_ = v_a_633_;
v_isShared_641_ = v_isSharedCheck_651_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_snd_638_);
lean_inc(v_fst_637_);
lean_dec(v_a_633_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_651_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_642_ = lean_unsigned_to_nat(8u);
v___x_643_ = 0;
v___x_644_ = lean_task_map(v___f_629_, v_snd_638_, v___x_642_, v___x_643_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v___x_644_);
v___x_646_ = v___x_640_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_fst_637_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___x_644_);
v___x_646_ = v_reuseFailAlloc_650_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_648_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_646_);
v___x_648_ = v___x_635_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
v_a_653_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_632_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_632_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_asTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_619_ = stack[0].m_obj;
lean_object* v_a_620_ = stack[1].m_obj;
lean_object* v_a_621_ = stack[2].m_obj;
lean_object* v_a_622_ = stack[3].m_obj;
lean_object* v_a_623_ = stack[4].m_obj;
lean_object* v_a_624_ = stack[5].m_obj;
lean_object* v_a_625_ = stack[6].m_obj;
lean_object* v_a_626_ = stack[7].m_obj;
lean_object* v_a_627_ = stack[8].m_obj;
lean_object* v_res_661_;
v_res_661_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg(v_t_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
stack->m_obj
 = v_res_661_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg___boxed(lean_object* v_t_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg(v_t_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
return v_res_672_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_asTask(lean_object* v_00_u03b1_673_, lean_object* v_t_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg(v_t_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
return v___x_684_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_asTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_674_ = stack[1].m_obj;
lean_object* v_a_675_ = stack[2].m_obj;
lean_object* v_a_676_ = stack[3].m_obj;
lean_object* v_a_677_ = stack[4].m_obj;
lean_object* v_a_678_ = stack[5].m_obj;
lean_object* v_a_679_ = stack[6].m_obj;
lean_object* v_a_680_ = stack[7].m_obj;
lean_object* v_a_681_ = stack[8].m_obj;
lean_object* v_a_682_ = stack[9].m_obj;
lean_object* v_res_685_;
v_res_685_ = l_Lean_Elab_Tactic_TacticM_asTask(lean_box(0), v_t_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
stack->m_obj
 = v_res_685_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask___boxed(lean_object* v_00_u03b1_686_, lean_object* v_t_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Elab_Tactic_TacticM_asTask(v_00_u03b1_686_, v_t_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
lean_dec(v_a_691_);
lean_dec_ref(v_a_690_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
return v_res_697_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg(lean_object* v_t_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg(v_t_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_717_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_717_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v_snd_713_; lean_object* v___x_715_; 
v_snd_713_ = lean_ctor_get(v_a_709_, 1);
lean_inc(v_snd_713_);
lean_dec(v_a_709_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v_snd_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_snd_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
v_a_718_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_708_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_708_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_698_ = stack[0].m_obj;
lean_object* v_a_699_ = stack[1].m_obj;
lean_object* v_a_700_ = stack[2].m_obj;
lean_object* v_a_701_ = stack[3].m_obj;
lean_object* v_a_702_ = stack[4].m_obj;
lean_object* v_a_703_ = stack[5].m_obj;
lean_object* v_a_704_ = stack[6].m_obj;
lean_object* v_a_705_ = stack[7].m_obj;
lean_object* v_a_706_ = stack[8].m_obj;
lean_object* v_res_726_;
v_res_726_ = l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg(v_t_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
stack->m_obj
 = v_res_726_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg___boxed(lean_object* v_t_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg(v_t_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
return v_res_737_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_asTask_x27(lean_object* v_00_u03b1_738_, lean_object* v_t_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg(v_t_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
return v___x_749_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_asTask_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_739_ = stack[1].m_obj;
lean_object* v_a_740_ = stack[2].m_obj;
lean_object* v_a_741_ = stack[3].m_obj;
lean_object* v_a_742_ = stack[4].m_obj;
lean_object* v_a_743_ = stack[5].m_obj;
lean_object* v_a_744_ = stack[6].m_obj;
lean_object* v_a_745_ = stack[7].m_obj;
lean_object* v_a_746_ = stack[8].m_obj;
lean_object* v_a_747_ = stack[9].m_obj;
lean_object* v_res_750_;
v_res_750_ = l_Lean_Elab_Tactic_TacticM_asTask_x27(lean_box(0), v_t_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
stack->m_obj
 = v_res_750_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_asTask_x27___boxed(lean_object* v_00_u03b1_751_, lean_object* v_t_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_Elab_Tactic_TacticM_asTask_x27(v_00_u03b1_751_, v_t_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
return v_res_762_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Task(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
