// Lean compiler output
// Module: Lean.Meta.Tactic.Repeat
// Imports: public import Lean.Meta.Basic import Init.Data.Nat.Linear import Init.Omega
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
lean_object* l_Array_appendList(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isAssigned___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_observing_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Bool_not___boxed(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Functor_mapRev___redArg(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_appendList, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__List_map__unattach_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__List_map__unattach_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_repeat_x27Core___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Bool_not___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_repeat_x27Core___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__2(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_repeat_x27Core___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_repeat_x27Core___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_repeat_x27Core___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_repeat_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_repeat_x27___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_repeat_x27___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_repeat_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`repeat1'` made no progress"};
static const lean_object* l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__0___boxed(lean_object* v_a_2_, lean_object* v_head_3_, lean_object* v_inst_4_, lean_object* v_inst_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_f_8_, lean_object* v_n_9_, lean_object* v_a_10_, lean_object* v_tail_11_, lean_object* v_a_12_, lean_object* v___x_13_, lean_object* v_____do__lift_14_){
_start:
{
uint8_t v_a_279__boxed_15_; uint8_t v___x_282__boxed_16_; lean_object* v_res_17_; 
v_a_279__boxed_15_ = lean_unbox(v_a_10_);
v___x_282__boxed_16_ = lean_unbox(v___x_13_);
v_res_17_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__0(v_a_2_, v_head_3_, v_inst_4_, v_inst_5_, v_inst_6_, v_inst_7_, v_f_8_, v_n_9_, v_a_279__boxed_15_, v_tail_11_, v_a_12_, v___x_282__boxed_16_, v_____do__lift_14_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1(lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_head_20_, lean_object* v_tail_21_, lean_object* v_a_22_, uint8_t v_a_23_, lean_object* v_toPure_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_f_29_, lean_object* v_toBind_30_, uint8_t v_____do__lift_31_){
_start:
{
if (v_____do__lift_31_ == 0)
{
lean_object* v_zero_32_; uint8_t v_isZero_33_; 
v_zero_32_ = lean_unsigned_to_nat(0u);
v_isZero_33_ = lean_nat_dec_eq(v_a_18_, v_zero_32_);
if (v_isZero_33_ == 1)
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec(v_toBind_30_);
lean_dec(v_f_29_);
lean_dec_ref(v_inst_28_);
lean_dec_ref(v_inst_27_);
lean_dec_ref(v_inst_26_);
lean_dec_ref(v_inst_25_);
lean_dec(v_a_18_);
v___x_34_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1___closed__0));
v___x_35_ = lean_array_push(v_a_19_, v_head_20_);
v___x_36_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_35_, v_tail_21_);
v___x_37_ = l_List_foldl___redArg(v___x_34_, v___x_36_, v_a_22_);
v___x_38_ = lean_box(v_a_23_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v___x_37_);
v___x_40_ = lean_apply_2(v_toPure_24_, lean_box(0), v___x_39_);
return v___x_40_;
}
else
{
lean_object* v_one_41_; lean_object* v_n_42_; uint8_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___f_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_toPure_24_);
v_one_41_ = lean_unsigned_to_nat(1u);
v_n_42_ = lean_nat_sub(v_a_18_, v_one_41_);
lean_dec(v_a_18_);
v___x_43_ = 1;
v___x_44_ = lean_box(v_a_23_);
v___x_45_ = lean_box(v___x_43_);
lean_inc(v_f_29_);
lean_inc_ref(v_inst_27_);
lean_inc_ref(v_inst_26_);
lean_inc_ref(v_inst_25_);
lean_inc(v_head_20_);
v___f_46_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__0___boxed), 13, 12);
lean_closure_set(v___f_46_, 0, v_a_19_);
lean_closure_set(v___f_46_, 1, v_head_20_);
lean_closure_set(v___f_46_, 2, v_inst_25_);
lean_closure_set(v___f_46_, 3, v_inst_26_);
lean_closure_set(v___f_46_, 4, v_inst_27_);
lean_closure_set(v___f_46_, 5, v_inst_28_);
lean_closure_set(v___f_46_, 6, v_f_29_);
lean_closure_set(v___f_46_, 7, v_n_42_);
lean_closure_set(v___f_46_, 8, v___x_44_);
lean_closure_set(v___f_46_, 9, v_tail_21_);
lean_closure_set(v___f_46_, 10, v_a_22_);
lean_closure_set(v___f_46_, 11, v___x_45_);
v___x_47_ = lean_apply_1(v_f_29_, v_head_20_);
v___x_48_ = l_Lean_observing_x3f___redArg(v_inst_25_, v_inst_27_, v_inst_26_, v___x_47_);
v___x_49_ = lean_apply_4(v_toBind_30_, lean_box(0), lean_box(0), v___x_48_, v___f_46_);
return v___x_49_;
}
}
else
{
lean_object* v___x_50_; 
lean_dec(v_toBind_30_);
lean_dec(v_toPure_24_);
lean_dec(v_head_20_);
v___x_50_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(v_inst_25_, v_inst_26_, v_inst_27_, v_inst_28_, v_f_29_, v_a_18_, v_a_23_, v_tail_21_, v_a_22_, v_a_19_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1___boxed(lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_head_53_, lean_object* v_tail_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_toPure_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_f_62_, lean_object* v_toBind_63_, lean_object* v_____do__lift_64_){
_start:
{
uint8_t v_a_314__boxed_65_; uint8_t v_____do__lift_319__boxed_66_; lean_object* v_res_67_; 
v_a_314__boxed_65_ = lean_unbox(v_a_56_);
v_____do__lift_319__boxed_66_ = lean_unbox(v_____do__lift_64_);
v_res_67_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1(v_a_51_, v_a_52_, v_head_53_, v_tail_54_, v_a_55_, v_a_314__boxed_65_, v_toPure_57_, v_inst_58_, v_inst_59_, v_inst_60_, v_inst_61_, v_f_62_, v_toBind_63_, v_____do__lift_319__boxed_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_f_72_, lean_object* v_a_73_, uint8_t v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
if (lean_obj_tag(v_a_75_) == 0)
{
if (lean_obj_tag(v_a_76_) == 0)
{
lean_object* v_toApplicative_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_88_; 
v_toApplicative_78_ = lean_ctor_get(v_inst_68_, 0);
lean_inc_ref(v_toApplicative_78_);
lean_dec(v_a_73_);
lean_dec(v_f_72_);
lean_dec_ref(v_inst_71_);
lean_dec_ref(v_inst_70_);
lean_dec_ref(v_inst_69_);
v_isSharedCheck_88_ = !lean_is_exclusive(v_inst_68_);
if (v_isSharedCheck_88_ == 0)
{
lean_object* v_unused_89_; lean_object* v_unused_90_; 
v_unused_89_ = lean_ctor_get(v_inst_68_, 1);
lean_dec(v_unused_89_);
v_unused_90_ = lean_ctor_get(v_inst_68_, 0);
lean_dec(v_unused_90_);
v___x_80_ = v_inst_68_;
v_isShared_81_ = v_isSharedCheck_88_;
goto v_resetjp_79_;
}
else
{
lean_dec(v_inst_68_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_88_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v_toPure_82_; lean_object* v___x_83_; lean_object* v___x_85_; 
v_toPure_82_ = lean_ctor_get(v_toApplicative_78_, 1);
lean_inc(v_toPure_82_);
lean_dec_ref(v_toApplicative_78_);
v___x_83_ = lean_box(v_a_74_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 1, v_a_77_);
lean_ctor_set(v___x_80_, 0, v___x_83_);
v___x_85_ = v___x_80_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_83_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v_a_77_);
v___x_85_ = v_reuseFailAlloc_87_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_86_; 
v___x_86_ = lean_apply_2(v_toPure_82_, lean_box(0), v___x_85_);
return v___x_86_;
}
}
}
else
{
lean_object* v_head_91_; lean_object* v_tail_92_; 
v_head_91_ = lean_ctor_get(v_a_76_, 0);
lean_inc(v_head_91_);
v_tail_92_ = lean_ctor_get(v_a_76_, 1);
lean_inc(v_tail_92_);
lean_dec_ref(v_a_76_);
v_a_75_ = v_head_91_;
v_a_76_ = v_tail_92_;
goto _start;
}
}
else
{
lean_object* v_toApplicative_94_; lean_object* v_toBind_95_; lean_object* v_toPure_96_; lean_object* v_head_97_; lean_object* v_tail_98_; lean_object* v___x_99_; lean_object* v___f_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v_toApplicative_94_ = lean_ctor_get(v_inst_68_, 0);
v_toBind_95_ = lean_ctor_get(v_inst_68_, 1);
lean_inc(v_toBind_95_);
v_toPure_96_ = lean_ctor_get(v_toApplicative_94_, 1);
v_head_97_ = lean_ctor_get(v_a_75_, 0);
lean_inc(v_head_97_);
v_tail_98_ = lean_ctor_get(v_a_75_, 1);
lean_inc(v_tail_98_);
lean_dec_ref(v_a_75_);
v___x_99_ = lean_box(v_a_74_);
lean_inc(v_toBind_95_);
lean_inc_ref(v_inst_71_);
lean_inc_ref(v_inst_68_);
lean_inc(v_toPure_96_);
lean_inc(v_head_97_);
v___f_100_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1___boxed), 14, 13);
lean_closure_set(v___f_100_, 0, v_a_73_);
lean_closure_set(v___f_100_, 1, v_a_77_);
lean_closure_set(v___f_100_, 2, v_head_97_);
lean_closure_set(v___f_100_, 3, v_tail_98_);
lean_closure_set(v___f_100_, 4, v_a_76_);
lean_closure_set(v___f_100_, 5, v___x_99_);
lean_closure_set(v___f_100_, 6, v_toPure_96_);
lean_closure_set(v___f_100_, 7, v_inst_68_);
lean_closure_set(v___f_100_, 8, v_inst_69_);
lean_closure_set(v___f_100_, 9, v_inst_70_);
lean_closure_set(v___f_100_, 10, v_inst_71_);
lean_closure_set(v___f_100_, 11, v_f_72_);
lean_closure_set(v___f_100_, 12, v_toBind_95_);
v___x_101_ = l_Lean_MVarId_isAssigned___redArg(v_inst_68_, v_inst_71_, v_head_97_);
v___x_102_ = lean_apply_4(v_toBind_95_, lean_box(0), lean_box(0), v___x_101_, v___f_100_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__0(lean_object* v_a_103_, lean_object* v_head_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_f_109_, lean_object* v_n_110_, uint8_t v_a_111_, lean_object* v_tail_112_, lean_object* v_a_113_, uint8_t v___x_114_, lean_object* v_____do__lift_115_){
_start:
{
if (lean_obj_tag(v_____do__lift_115_) == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_array_push(v_a_103_, v_head_104_);
v___x_117_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(v_inst_105_, v_inst_106_, v_inst_107_, v_inst_108_, v_f_109_, v_n_110_, v_a_111_, v_tail_112_, v_a_113_, v___x_116_);
return v___x_117_;
}
else
{
lean_object* v_val_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
lean_dec(v_head_104_);
v_val_118_ = lean_ctor_get(v_____do__lift_115_, 0);
lean_inc(v_val_118_);
lean_dec_ref(v_____do__lift_115_);
v___x_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_119_, 0, v_tail_112_);
lean_ctor_set(v___x_119_, 1, v_a_113_);
v___x_120_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(v_inst_105_, v_inst_106_, v_inst_107_, v_inst_108_, v_f_109_, v_n_110_, v___x_114_, v_val_118_, v___x_119_, v_a_103_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___boxed(lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_f_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
uint8_t v_a_294__boxed_131_; lean_object* v_res_132_; 
v_a_294__boxed_131_ = lean_unbox(v_a_127_);
v_res_132_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(v_inst_121_, v_inst_122_, v_inst_123_, v_inst_124_, v_f_125_, v_a_126_, v_a_294__boxed_131_, v_a_128_, v_a_129_, v_a_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go(lean_object* v_m_133_, lean_object* v_00_u03b5_134_, lean_object* v_s_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_f_140_, lean_object* v_a_141_, uint8_t v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(v_inst_136_, v_inst_137_, v_inst_138_, v_inst_139_, v_f_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___boxed(lean_object* v_m_147_, lean_object* v_00_u03b5_148_, lean_object* v_s_149_, lean_object* v_inst_150_, lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_f_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
uint8_t v_a_457__boxed_160_; lean_object* v_res_161_; 
v_a_457__boxed_160_ = lean_unbox(v_a_156_);
v_res_161_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go(v_m_147_, v_00_u03b5_148_, v_s_149_, v_inst_150_, v_inst_151_, v_inst_152_, v_inst_153_, v_f_154_, v_a_155_, v_a_457__boxed_160_, v_a_157_, v_a_158_, v_a_159_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___redArg(lean_object* v_x_162_, uint8_t v_x_163_, lean_object* v_x_164_, lean_object* v_x_165_, lean_object* v_x_166_, lean_object* v_h__1_167_, lean_object* v_h__2_168_, lean_object* v_h__3_169_){
_start:
{
if (lean_obj_tag(v_x_164_) == 0)
{
lean_dec(v_h__3_169_);
if (lean_obj_tag(v_x_165_) == 0)
{
lean_object* v___x_170_; lean_object* v___x_171_; 
lean_dec(v_h__2_168_);
v___x_170_ = lean_box(v_x_163_);
v___x_171_ = lean_apply_3(v_h__1_167_, v_x_162_, v___x_170_, v_x_166_);
return v___x_171_;
}
else
{
lean_object* v_head_172_; lean_object* v_tail_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec(v_h__1_167_);
v_head_172_ = lean_ctor_get(v_x_165_, 0);
lean_inc(v_head_172_);
v_tail_173_ = lean_ctor_get(v_x_165_, 1);
lean_inc(v_tail_173_);
lean_dec_ref(v_x_165_);
v___x_174_ = lean_box(v_x_163_);
v___x_175_ = lean_apply_5(v_h__2_168_, v_x_162_, v___x_174_, v_head_172_, v_tail_173_, v_x_166_);
return v___x_175_;
}
}
else
{
lean_object* v_head_176_; lean_object* v_tail_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v_h__2_168_);
lean_dec(v_h__1_167_);
v_head_176_ = lean_ctor_get(v_x_164_, 0);
lean_inc(v_head_176_);
v_tail_177_ = lean_ctor_get(v_x_164_, 1);
lean_inc(v_tail_177_);
lean_dec_ref(v_x_164_);
v___x_178_ = lean_box(v_x_163_);
v___x_179_ = lean_apply_6(v_h__3_169_, v_x_162_, v___x_178_, v_head_176_, v_tail_177_, v_x_165_, v_x_166_);
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___redArg___boxed(lean_object* v_x_180_, lean_object* v_x_181_, lean_object* v_x_182_, lean_object* v_x_183_, lean_object* v_x_184_, lean_object* v_h__1_185_, lean_object* v_h__2_186_, lean_object* v_h__3_187_){
_start:
{
uint8_t v_x_43__boxed_188_; lean_object* v_res_189_; 
v_x_43__boxed_188_ = lean_unbox(v_x_181_);
v_res_189_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___redArg(v_x_180_, v_x_43__boxed_188_, v_x_182_, v_x_183_, v_x_184_, v_h__1_185_, v_h__2_186_, v_h__3_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter(lean_object* v_motive_190_, lean_object* v_x_191_, uint8_t v_x_192_, lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_h__1_196_, lean_object* v_h__2_197_, lean_object* v_h__3_198_){
_start:
{
if (lean_obj_tag(v_x_193_) == 0)
{
lean_dec(v_h__3_198_);
if (lean_obj_tag(v_x_194_) == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec(v_h__2_197_);
v___x_199_ = lean_box(v_x_192_);
v___x_200_ = lean_apply_3(v_h__1_196_, v_x_191_, v___x_199_, v_x_195_);
return v___x_200_;
}
else
{
lean_object* v_head_201_; lean_object* v_tail_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec(v_h__1_196_);
v_head_201_ = lean_ctor_get(v_x_194_, 0);
lean_inc(v_head_201_);
v_tail_202_ = lean_ctor_get(v_x_194_, 1);
lean_inc(v_tail_202_);
lean_dec_ref(v_x_194_);
v___x_203_ = lean_box(v_x_192_);
v___x_204_ = lean_apply_5(v_h__2_197_, v_x_191_, v___x_203_, v_head_201_, v_tail_202_, v_x_195_);
return v___x_204_;
}
}
else
{
lean_object* v_head_205_; lean_object* v_tail_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec(v_h__2_197_);
lean_dec(v_h__1_196_);
v_head_205_ = lean_ctor_get(v_x_193_, 0);
lean_inc(v_head_205_);
v_tail_206_ = lean_ctor_get(v_x_193_, 1);
lean_inc(v_tail_206_);
lean_dec_ref(v_x_193_);
v___x_207_ = lean_box(v_x_192_);
v___x_208_ = lean_apply_6(v_h__3_198_, v_x_191_, v___x_207_, v_head_205_, v_tail_206_, v_x_194_, v_x_195_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___boxed(lean_object* v_motive_209_, lean_object* v_x_210_, lean_object* v_x_211_, lean_object* v_x_212_, lean_object* v_x_213_, lean_object* v_x_214_, lean_object* v_h__1_215_, lean_object* v_h__2_216_, lean_object* v_h__3_217_){
_start:
{
uint8_t v_x_78__boxed_218_; lean_object* v_res_219_; 
v_x_78__boxed_218_ = lean_unbox(v_x_211_);
v_res_219_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter(v_motive_209_, v_x_210_, v_x_78__boxed_218_, v_x_212_, v_x_213_, v_x_214_, v_h__1_215_, v_h__2_216_, v_h__3_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___redArg(lean_object* v_n_220_, lean_object* v_h__1_221_, lean_object* v_h__2_222_){
_start:
{
lean_object* v_zero_223_; uint8_t v_isZero_224_; 
v_zero_223_ = lean_unsigned_to_nat(0u);
v_isZero_224_ = lean_nat_dec_eq(v_n_220_, v_zero_223_);
if (v_isZero_224_ == 1)
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec(v_h__2_222_);
v___x_225_ = lean_box(0);
v___x_226_ = lean_apply_1(v_h__1_221_, v___x_225_);
return v___x_226_;
}
else
{
lean_object* v_one_227_; lean_object* v_n_228_; lean_object* v___x_229_; 
lean_dec(v_h__1_221_);
v_one_227_ = lean_unsigned_to_nat(1u);
v_n_228_ = lean_nat_sub(v_n_220_, v_one_227_);
v___x_229_ = lean_apply_1(v_h__2_222_, v_n_228_);
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___redArg___boxed(lean_object* v_n_230_, lean_object* v_h__1_231_, lean_object* v_h__2_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___redArg(v_n_230_, v_h__1_231_, v_h__2_232_);
lean_dec(v_n_230_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter(lean_object* v_motive_234_, lean_object* v_n_235_, lean_object* v_h__1_236_, lean_object* v_h__2_237_){
_start:
{
lean_object* v_zero_238_; uint8_t v_isZero_239_; 
v_zero_238_ = lean_unsigned_to_nat(0u);
v_isZero_239_ = lean_nat_dec_eq(v_n_235_, v_zero_238_);
if (v_isZero_239_ == 1)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec(v_h__2_237_);
v___x_240_ = lean_box(0);
v___x_241_ = lean_apply_1(v_h__1_236_, v___x_240_);
return v___x_241_;
}
else
{
lean_object* v_one_242_; lean_object* v_n_243_; lean_object* v___x_244_; 
lean_dec(v_h__1_236_);
v_one_242_ = lean_unsigned_to_nat(1u);
v_n_243_ = lean_nat_sub(v_n_235_, v_one_242_);
v___x_244_ = lean_apply_1(v_h__2_237_, v_n_243_);
return v___x_244_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___boxed(lean_object* v_motive_245_, lean_object* v_n_246_, lean_object* v_h__1_247_, lean_object* v_h__2_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter(v_motive_245_, v_n_246_, v_h__1_247_, v_h__2_248_);
lean_dec(v_n_246_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__List_map__unattach_match__1_splitter___redArg(lean_object* v_x_250_, lean_object* v_h__1_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lean_apply_2(v_h__1_251_, v_x_250_, lean_box(0));
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__List_map__unattach_match__1_splitter(lean_object* v_00_u03b1_253_, lean_object* v_P_254_, lean_object* v_motive_255_, lean_object* v_x_256_, lean_object* v_h__1_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lean_apply_2(v_h__1_257_, v_x_256_, lean_box(0));
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__1_splitter___redArg(lean_object* v_____do__lift_259_, lean_object* v_h__1_260_, lean_object* v_h__2_261_){
_start:
{
if (lean_obj_tag(v_____do__lift_259_) == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec(v_h__1_260_);
v___x_262_ = lean_box(0);
v___x_263_ = lean_apply_1(v_h__2_261_, v___x_262_);
return v___x_263_;
}
else
{
lean_object* v_val_264_; lean_object* v___x_265_; 
lean_dec(v_h__2_261_);
v_val_264_ = lean_ctor_get(v_____do__lift_259_, 0);
lean_inc(v_val_264_);
lean_dec_ref(v_____do__lift_259_);
v___x_265_ = lean_apply_1(v_h__1_260_, v_val_264_);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__1_splitter(lean_object* v_motive_266_, lean_object* v_____do__lift_267_, lean_object* v_h__1_268_, lean_object* v_h__2_269_){
_start:
{
if (lean_obj_tag(v_____do__lift_267_) == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec(v_h__1_268_);
v___x_270_ = lean_box(0);
v___x_271_ = lean_apply_1(v_h__2_269_, v___x_270_);
return v___x_271_;
}
else
{
lean_object* v_val_272_; lean_object* v___x_273_; 
lean_dec(v_h__2_269_);
v_val_272_ = lean_ctor_get(v_____do__lift_267_, 0);
lean_inc(v_val_272_);
lean_dec_ref(v_____do__lift_267_);
v___x_273_ = lean_apply_1(v_h__1_268_, v_val_272_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__0(lean_object* v_toPure_274_, lean_object* v_acc_275_, lean_object* v_a_276_, uint8_t v_____do__lift_277_){
_start:
{
if (v_____do__lift_277_ == 0)
{
lean_object* v___x_278_; 
lean_dec(v_a_276_);
v___x_278_ = lean_apply_2(v_toPure_274_, lean_box(0), v_acc_275_);
return v___x_278_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_array_push(v_acc_275_, v_a_276_);
v___x_280_ = lean_apply_2(v_toPure_274_, lean_box(0), v___x_279_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__0___boxed(lean_object* v_toPure_281_, lean_object* v_acc_282_, lean_object* v_a_283_, lean_object* v_____do__lift_284_){
_start:
{
uint8_t v_____do__lift_200__boxed_285_; lean_object* v_res_286_; 
v_____do__lift_200__boxed_285_ = lean_unbox(v_____do__lift_284_);
v_res_286_ = l_Lean_Meta_repeat_x27Core___redArg___lam__0(v_toPure_281_, v_acc_282_, v_a_283_, v_____do__lift_200__boxed_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__1(lean_object* v_toFunctor_288_, lean_object* v_toPure_289_, lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_toBind_292_, lean_object* v_acc_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_map_295_; lean_object* v___f_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_map_295_ = lean_ctor_get(v_toFunctor_288_, 0);
lean_inc(v_map_295_);
lean_dec_ref(v_toFunctor_288_);
lean_inc(v_a_294_);
v___f_296_ = lean_alloc_closure((void*)(l_Lean_Meta_repeat_x27Core___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_296_, 0, v_toPure_289_);
lean_closure_set(v___f_296_, 1, v_acc_293_);
lean_closure_set(v___f_296_, 2, v_a_294_);
v___x_297_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___redArg___lam__1___closed__0));
v___x_298_ = l_Lean_MVarId_isAssigned___redArg(v_inst_290_, v_inst_291_, v_a_294_);
v___x_299_ = lean_apply_4(v_map_295_, lean_box(0), lean_box(0), v___x_297_, v___x_298_);
v___x_300_ = lean_apply_4(v_toBind_292_, lean_box(0), lean_box(0), v___x_299_, v___f_296_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__2(uint8_t v_fst_301_, lean_object* v_toPure_302_, lean_object* v_____do__lift_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_304_ = lean_array_to_list(v_____do__lift_303_);
v___x_305_ = lean_box(v_fst_301_);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_304_);
v___x_307_ = lean_apply_2(v_toPure_302_, lean_box(0), v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__2___boxed(lean_object* v_fst_308_, lean_object* v_toPure_309_, lean_object* v_____do__lift_310_){
_start:
{
uint8_t v_fst_226__boxed_311_; lean_object* v_res_312_; 
v_fst_226__boxed_311_ = lean_unbox(v_fst_308_);
v_res_312_ = l_Lean_Meta_repeat_x27Core___redArg___lam__2(v_fst_226__boxed_311_, v_toPure_309_, v_____do__lift_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__3(lean_object* v_toPure_313_, lean_object* v___x_314_, lean_object* v___x_315_, lean_object* v_toBind_316_, lean_object* v_inst_317_, lean_object* v___f_318_, lean_object* v_____x_319_){
_start:
{
lean_object* v_fst_320_; lean_object* v_snd_321_; lean_object* v___f_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_fst_320_ = lean_ctor_get(v_____x_319_, 0);
lean_inc(v_fst_320_);
v_snd_321_ = lean_ctor_get(v_____x_319_, 1);
lean_inc(v_snd_321_);
lean_dec_ref(v_____x_319_);
lean_inc(v_toPure_313_);
v___f_322_ = lean_alloc_closure((void*)(l_Lean_Meta_repeat_x27Core___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_322_, 0, v_fst_320_);
lean_closure_set(v___f_322_, 1, v_toPure_313_);
v___x_323_ = lean_array_get_size(v_snd_321_);
v___x_324_ = lean_nat_dec_lt(v___x_314_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec(v_snd_321_);
lean_dec(v___f_318_);
lean_dec_ref(v_inst_317_);
v___x_325_ = lean_apply_2(v_toPure_313_, lean_box(0), v___x_315_);
v___x_326_ = lean_apply_4(v_toBind_316_, lean_box(0), lean_box(0), v___x_325_, v___f_322_);
return v___x_326_;
}
else
{
uint8_t v___x_327_; 
v___x_327_ = lean_nat_dec_le(v___x_323_, v___x_323_);
if (v___x_327_ == 0)
{
if (v___x_324_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec(v_snd_321_);
lean_dec(v___f_318_);
lean_dec_ref(v_inst_317_);
v___x_328_ = lean_apply_2(v_toPure_313_, lean_box(0), v___x_315_);
v___x_329_ = lean_apply_4(v_toBind_316_, lean_box(0), lean_box(0), v___x_328_, v___f_322_);
return v___x_329_;
}
else
{
size_t v___x_330_; size_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec(v_toPure_313_);
v___x_330_ = ((size_t)0ULL);
v___x_331_ = lean_usize_of_nat(v___x_323_);
v___x_332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_317_, v___f_318_, v_snd_321_, v___x_330_, v___x_331_, v___x_315_);
v___x_333_ = lean_apply_4(v_toBind_316_, lean_box(0), lean_box(0), v___x_332_, v___f_322_);
return v___x_333_;
}
}
else
{
size_t v___x_334_; size_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec(v_toPure_313_);
v___x_334_ = ((size_t)0ULL);
v___x_335_ = lean_usize_of_nat(v___x_323_);
v___x_336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_317_, v___f_318_, v_snd_321_, v___x_334_, v___x_335_, v___x_315_);
v___x_337_ = lean_apply_4(v_toBind_316_, lean_box(0), lean_box(0), v___x_336_, v___f_322_);
return v___x_337_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__3___boxed(lean_object* v_toPure_338_, lean_object* v___x_339_, lean_object* v___x_340_, lean_object* v_toBind_341_, lean_object* v_inst_342_, lean_object* v___f_343_, lean_object* v_____x_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Meta_repeat_x27Core___redArg___lam__3(v_toPure_338_, v___x_339_, v___x_340_, v_toBind_341_, v_inst_342_, v___f_343_, v_____x_344_);
lean_dec(v___x_339_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg(lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_f_352_, lean_object* v_goals_353_, lean_object* v_maxIters_354_){
_start:
{
lean_object* v_toApplicative_355_; lean_object* v_toBind_356_; lean_object* v_toFunctor_357_; lean_object* v_toPure_358_; uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___f_364_; lean_object* v___f_365_; lean_object* v___x_366_; 
v_toApplicative_355_ = lean_ctor_get(v_inst_348_, 0);
v_toBind_356_ = lean_ctor_get(v_inst_348_, 1);
lean_inc(v_toBind_356_);
v_toFunctor_357_ = lean_ctor_get(v_toApplicative_355_, 0);
v_toPure_358_ = lean_ctor_get(v_toApplicative_355_, 1);
lean_inc(v_toPure_358_);
v___x_359_ = 0;
v___x_360_ = lean_box(0);
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___redArg___closed__0));
lean_inc_ref(v_inst_351_);
lean_inc_ref(v_inst_348_);
v___x_363_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(v_inst_348_, v_inst_349_, v_inst_350_, v_inst_351_, v_f_352_, v_maxIters_354_, v___x_359_, v_goals_353_, v___x_360_, v___x_362_);
lean_inc(v_toBind_356_);
lean_inc_ref(v_inst_348_);
lean_inc(v_toPure_358_);
lean_inc_ref(v_toFunctor_357_);
v___f_364_ = lean_alloc_closure((void*)(l_Lean_Meta_repeat_x27Core___redArg___lam__1), 7, 5);
lean_closure_set(v___f_364_, 0, v_toFunctor_357_);
lean_closure_set(v___f_364_, 1, v_toPure_358_);
lean_closure_set(v___f_364_, 2, v_inst_348_);
lean_closure_set(v___f_364_, 3, v_inst_351_);
lean_closure_set(v___f_364_, 4, v_toBind_356_);
lean_inc(v_toBind_356_);
v___f_365_ = lean_alloc_closure((void*)(l_Lean_Meta_repeat_x27Core___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_365_, 0, v_toPure_358_);
lean_closure_set(v___f_365_, 1, v___x_361_);
lean_closure_set(v___f_365_, 2, v___x_362_);
lean_closure_set(v___f_365_, 3, v_toBind_356_);
lean_closure_set(v___f_365_, 4, v_inst_348_);
lean_closure_set(v___f_365_, 5, v___f_364_);
v___x_366_ = lean_apply_4(v_toBind_356_, lean_box(0), lean_box(0), v___x_363_, v___f_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core(lean_object* v_m_367_, lean_object* v_00_u03b5_368_, lean_object* v_s_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_f_374_, lean_object* v_goals_375_, lean_object* v_maxIters_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Meta_repeat_x27Core___redArg(v_inst_370_, v_inst_371_, v_inst_372_, v_inst_373_, v_f_374_, v_goals_375_, v_maxIters_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___redArg___lam__0(lean_object* v_x_378_){
_start:
{
lean_object* v_snd_379_; 
v_snd_379_ = lean_ctor_get(v_x_378_, 1);
lean_inc(v_snd_379_);
return v_snd_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___redArg___lam__0___boxed(lean_object* v_x_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Meta_repeat_x27___redArg___lam__0(v_x_380_);
lean_dec_ref(v_x_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___redArg(lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_inst_385_, lean_object* v_inst_386_, lean_object* v_f_387_, lean_object* v_goals_388_, lean_object* v_maxIters_389_){
_start:
{
lean_object* v_toApplicative_390_; lean_object* v_toFunctor_391_; lean_object* v___f_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_toApplicative_390_ = lean_ctor_get(v_inst_383_, 0);
v_toFunctor_391_ = lean_ctor_get(v_toApplicative_390_, 0);
lean_inc_ref(v_toFunctor_391_);
v___f_392_ = ((lean_object*)(l_Lean_Meta_repeat_x27___redArg___closed__0));
v___x_393_ = l_Lean_Meta_repeat_x27Core___redArg(v_inst_383_, v_inst_384_, v_inst_385_, v_inst_386_, v_f_387_, v_goals_388_, v_maxIters_389_);
v___x_394_ = l_Functor_mapRev___redArg(v_toFunctor_391_, v___x_393_, v___f_392_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27(lean_object* v_m_395_, lean_object* v_00_u03b5_396_, lean_object* v_s_397_, lean_object* v_inst_398_, lean_object* v_inst_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_f_402_, lean_object* v_goals_403_, lean_object* v_maxIters_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Meta_repeat_x27___redArg(v_inst_398_, v_inst_399_, v_inst_400_, v_inst_401_, v_f_402_, v_goals_403_, v_maxIters_404_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__0));
v___x_408_ = l_Lean_stringToMessageData(v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___redArg___lam__0(lean_object* v_toPure_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_____x_412_){
_start:
{
lean_object* v_fst_413_; uint8_t v___x_414_; 
v_fst_413_ = lean_ctor_get(v_____x_412_, 0);
v___x_414_ = lean_unbox(v_fst_413_);
if (v___x_414_ == 1)
{
lean_object* v_snd_415_; lean_object* v___x_416_; 
lean_dec_ref(v_inst_411_);
lean_dec_ref(v_inst_410_);
v_snd_415_ = lean_ctor_get(v_____x_412_, 1);
lean_inc(v_snd_415_);
lean_dec_ref(v_____x_412_);
v___x_416_ = lean_apply_2(v_toPure_409_, lean_box(0), v_snd_415_);
return v___x_416_;
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec_ref(v_____x_412_);
lean_dec(v_toPure_409_);
v___x_417_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1, &l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1);
v___x_418_ = l_Lean_throwError___redArg(v_inst_410_, v_inst_411_, v___x_417_);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___redArg(lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_f_424_, lean_object* v_goals_425_, lean_object* v_maxIters_426_){
_start:
{
lean_object* v_toApplicative_427_; lean_object* v_toBind_428_; lean_object* v_toPure_429_; lean_object* v___x_430_; lean_object* v___f_431_; lean_object* v___x_432_; 
v_toApplicative_427_ = lean_ctor_get(v_inst_419_, 0);
v_toBind_428_ = lean_ctor_get(v_inst_419_, 1);
lean_inc(v_toBind_428_);
v_toPure_429_ = lean_ctor_get(v_toApplicative_427_, 1);
lean_inc(v_toPure_429_);
lean_inc_ref(v_inst_419_);
v___x_430_ = l_Lean_Meta_repeat_x27Core___redArg(v_inst_419_, v_inst_421_, v_inst_422_, v_inst_423_, v_f_424_, v_goals_425_, v_maxIters_426_);
v___f_431_ = lean_alloc_closure((void*)(l_Lean_Meta_repeat1_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_431_, 0, v_toPure_429_);
lean_closure_set(v___f_431_, 1, v_inst_419_);
lean_closure_set(v___f_431_, 2, v_inst_420_);
v___x_432_ = lean_apply_4(v_toBind_428_, lean_box(0), lean_box(0), v___x_430_, v___f_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27(lean_object* v_m_433_, lean_object* v_00_u03b5_434_, lean_object* v_s_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_f_441_, lean_object* v_goals_442_, lean_object* v_maxIters_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Meta_repeat1_x27___redArg(v_inst_436_, v_inst_437_, v_inst_438_, v_inst_439_, v_inst_440_, v_f_441_, v_goals_442_, v_maxIters_443_);
return v___x_444_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Repeat(builtin);
}
#ifdef __cplusplus
}
#endif
