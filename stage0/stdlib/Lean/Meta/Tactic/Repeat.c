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
uint8_t v_x_36__boxed_188_; lean_object* v_res_189_; 
v_x_36__boxed_188_ = lean_unbox(v_x_181_);
v_res_189_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___redArg(v_x_180_, v_x_36__boxed_188_, v_x_182_, v_x_183_, v_x_184_, v_h__1_185_, v_h__2_186_, v_h__3_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter(lean_object* v_motive_190_, lean_object* v_x_191_, uint8_t v_x_192_, lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_h__1_196_, lean_object* v_h__2_197_, lean_object* v_h__3_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___redArg(v_x_191_, v_x_192_, v_x_193_, v_x_194_, v_x_195_, v_h__1_196_, v_h__2_197_, v_h__3_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___boxed(lean_object* v_motive_200_, lean_object* v_x_201_, lean_object* v_x_202_, lean_object* v_x_203_, lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_h__1_206_, lean_object* v_h__2_207_, lean_object* v_h__3_208_){
_start:
{
uint8_t v_x_71__boxed_209_; lean_object* v_res_210_; 
v_x_71__boxed_209_ = lean_unbox(v_x_202_);
v_res_210_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter(v_motive_200_, v_x_201_, v_x_71__boxed_209_, v_x_203_, v_x_204_, v_x_205_, v_h__1_206_, v_h__2_207_, v_h__3_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___redArg(lean_object* v_n_211_, lean_object* v_h__1_212_, lean_object* v_h__2_213_){
_start:
{
lean_object* v_zero_214_; uint8_t v_isZero_215_; 
v_zero_214_ = lean_unsigned_to_nat(0u);
v_isZero_215_ = lean_nat_dec_eq(v_n_211_, v_zero_214_);
if (v_isZero_215_ == 1)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec(v_h__2_213_);
v___x_216_ = lean_box(0);
v___x_217_ = lean_apply_1(v_h__1_212_, v___x_216_);
return v___x_217_;
}
else
{
lean_object* v_one_218_; lean_object* v_n_219_; lean_object* v___x_220_; 
lean_dec(v_h__1_212_);
v_one_218_ = lean_unsigned_to_nat(1u);
v_n_219_ = lean_nat_sub(v_n_211_, v_one_218_);
v___x_220_ = lean_apply_1(v_h__2_213_, v_n_219_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___redArg___boxed(lean_object* v_n_221_, lean_object* v_h__1_222_, lean_object* v_h__2_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___redArg(v_n_221_, v_h__1_222_, v_h__2_223_);
lean_dec(v_n_221_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter(lean_object* v_motive_225_, lean_object* v_n_226_, lean_object* v_h__1_227_, lean_object* v_h__2_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___redArg(v_n_226_, v_h__1_227_, v_h__2_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___boxed(lean_object* v_motive_230_, lean_object* v_n_231_, lean_object* v_h__1_232_, lean_object* v_h__2_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter(v_motive_230_, v_n_231_, v_h__1_232_, v_h__2_233_);
lean_dec(v_n_231_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__List_map__unattach_match__1_splitter___redArg(lean_object* v_x_235_, lean_object* v_h__1_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = lean_apply_2(v_h__1_236_, v_x_235_, lean_box(0));
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__List_map__unattach_match__1_splitter(lean_object* v_00_u03b1_238_, lean_object* v_P_239_, lean_object* v_motive_240_, lean_object* v_x_241_, lean_object* v_h__1_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lean_apply_2(v_h__1_242_, v_x_241_, lean_box(0));
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__1_splitter___redArg(lean_object* v_____do__lift_244_, lean_object* v_h__1_245_, lean_object* v_h__2_246_){
_start:
{
if (lean_obj_tag(v_____do__lift_244_) == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec(v_h__1_245_);
v___x_247_ = lean_box(0);
v___x_248_ = lean_apply_1(v_h__2_246_, v___x_247_);
return v___x_248_;
}
else
{
lean_object* v_val_249_; lean_object* v___x_250_; 
lean_dec(v_h__2_246_);
v_val_249_ = lean_ctor_get(v_____do__lift_244_, 0);
lean_inc(v_val_249_);
lean_dec_ref(v_____do__lift_244_);
v___x_250_ = lean_apply_1(v_h__1_245_, v_val_249_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__1_splitter(lean_object* v_motive_251_, lean_object* v_____do__lift_252_, lean_object* v_h__1_253_, lean_object* v_h__2_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__1_splitter___redArg(v_____do__lift_252_, v_h__1_253_, v_h__2_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__0(lean_object* v_toPure_256_, lean_object* v_acc_257_, lean_object* v_a_258_, uint8_t v_____do__lift_259_){
_start:
{
if (v_____do__lift_259_ == 0)
{
lean_object* v___x_260_; 
lean_dec(v_a_258_);
v___x_260_ = lean_apply_2(v_toPure_256_, lean_box(0), v_acc_257_);
return v___x_260_;
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_array_push(v_acc_257_, v_a_258_);
v___x_262_ = lean_apply_2(v_toPure_256_, lean_box(0), v___x_261_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__0___boxed(lean_object* v_toPure_263_, lean_object* v_acc_264_, lean_object* v_a_265_, lean_object* v_____do__lift_266_){
_start:
{
uint8_t v_____do__lift_200__boxed_267_; lean_object* v_res_268_; 
v_____do__lift_200__boxed_267_ = lean_unbox(v_____do__lift_266_);
v_res_268_ = l_Lean_Meta_repeat_x27Core___redArg___lam__0(v_toPure_263_, v_acc_264_, v_a_265_, v_____do__lift_200__boxed_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__1(lean_object* v_toFunctor_270_, lean_object* v_toPure_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_toBind_274_, lean_object* v_acc_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_map_277_; lean_object* v___f_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_map_277_ = lean_ctor_get(v_toFunctor_270_, 0);
lean_inc(v_map_277_);
lean_dec_ref(v_toFunctor_270_);
lean_inc(v_a_276_);
v___f_278_ = lean_alloc_closure((void*)(l_Lean_Meta_repeat_x27Core___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_278_, 0, v_toPure_271_);
lean_closure_set(v___f_278_, 1, v_acc_275_);
lean_closure_set(v___f_278_, 2, v_a_276_);
v___x_279_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___redArg___lam__1___closed__0));
v___x_280_ = l_Lean_MVarId_isAssigned___redArg(v_inst_272_, v_inst_273_, v_a_276_);
v___x_281_ = lean_apply_4(v_map_277_, lean_box(0), lean_box(0), v___x_279_, v___x_280_);
v___x_282_ = lean_apply_4(v_toBind_274_, lean_box(0), lean_box(0), v___x_281_, v___f_278_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__2(uint8_t v_fst_283_, lean_object* v_toPure_284_, lean_object* v_____do__lift_285_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_286_ = lean_array_to_list(v_____do__lift_285_);
v___x_287_ = lean_box(v_fst_283_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_286_);
v___x_289_ = lean_apply_2(v_toPure_284_, lean_box(0), v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__2___boxed(lean_object* v_fst_290_, lean_object* v_toPure_291_, lean_object* v_____do__lift_292_){
_start:
{
uint8_t v_fst_226__boxed_293_; lean_object* v_res_294_; 
v_fst_226__boxed_293_ = lean_unbox(v_fst_290_);
v_res_294_ = l_Lean_Meta_repeat_x27Core___redArg___lam__2(v_fst_226__boxed_293_, v_toPure_291_, v_____do__lift_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__3(lean_object* v_toPure_295_, lean_object* v___x_296_, lean_object* v___x_297_, lean_object* v_toBind_298_, lean_object* v_inst_299_, lean_object* v___f_300_, lean_object* v_____x_301_){
_start:
{
lean_object* v_fst_302_; lean_object* v_snd_303_; lean_object* v___f_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v_fst_302_ = lean_ctor_get(v_____x_301_, 0);
lean_inc(v_fst_302_);
v_snd_303_ = lean_ctor_get(v_____x_301_, 1);
lean_inc(v_snd_303_);
lean_dec_ref(v_____x_301_);
lean_inc(v_toPure_295_);
v___f_304_ = lean_alloc_closure((void*)(l_Lean_Meta_repeat_x27Core___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_304_, 0, v_fst_302_);
lean_closure_set(v___f_304_, 1, v_toPure_295_);
v___x_305_ = lean_array_get_size(v_snd_303_);
v___x_306_ = lean_nat_dec_lt(v___x_296_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec(v_snd_303_);
lean_dec(v___f_300_);
lean_dec_ref(v_inst_299_);
v___x_307_ = lean_apply_2(v_toPure_295_, lean_box(0), v___x_297_);
v___x_308_ = lean_apply_4(v_toBind_298_, lean_box(0), lean_box(0), v___x_307_, v___f_304_);
return v___x_308_;
}
else
{
uint8_t v___x_309_; 
v___x_309_ = lean_nat_dec_le(v___x_305_, v___x_305_);
if (v___x_309_ == 0)
{
if (v___x_306_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec(v_snd_303_);
lean_dec(v___f_300_);
lean_dec_ref(v_inst_299_);
v___x_310_ = lean_apply_2(v_toPure_295_, lean_box(0), v___x_297_);
v___x_311_ = lean_apply_4(v_toBind_298_, lean_box(0), lean_box(0), v___x_310_, v___f_304_);
return v___x_311_;
}
else
{
size_t v___x_312_; size_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_toPure_295_);
v___x_312_ = ((size_t)0ULL);
v___x_313_ = lean_usize_of_nat(v___x_305_);
v___x_314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_299_, v___f_300_, v_snd_303_, v___x_312_, v___x_313_, v___x_297_);
v___x_315_ = lean_apply_4(v_toBind_298_, lean_box(0), lean_box(0), v___x_314_, v___f_304_);
return v___x_315_;
}
}
else
{
size_t v___x_316_; size_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec(v_toPure_295_);
v___x_316_ = ((size_t)0ULL);
v___x_317_ = lean_usize_of_nat(v___x_305_);
v___x_318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_299_, v___f_300_, v_snd_303_, v___x_316_, v___x_317_, v___x_297_);
v___x_319_ = lean_apply_4(v_toBind_298_, lean_box(0), lean_box(0), v___x_318_, v___f_304_);
return v___x_319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__3___boxed(lean_object* v_toPure_320_, lean_object* v___x_321_, lean_object* v___x_322_, lean_object* v_toBind_323_, lean_object* v_inst_324_, lean_object* v___f_325_, lean_object* v_____x_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Meta_repeat_x27Core___redArg___lam__3(v_toPure_320_, v___x_321_, v___x_322_, v_toBind_323_, v_inst_324_, v___f_325_, v_____x_326_);
lean_dec(v___x_321_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg(lean_object* v_inst_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_inst_333_, lean_object* v_f_334_, lean_object* v_goals_335_, lean_object* v_maxIters_336_){
_start:
{
lean_object* v_toApplicative_337_; lean_object* v_toBind_338_; lean_object* v_toFunctor_339_; lean_object* v_toPure_340_; uint8_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___f_346_; lean_object* v___f_347_; lean_object* v___x_348_; 
v_toApplicative_337_ = lean_ctor_get(v_inst_330_, 0);
v_toBind_338_ = lean_ctor_get(v_inst_330_, 1);
lean_inc(v_toBind_338_);
v_toFunctor_339_ = lean_ctor_get(v_toApplicative_337_, 0);
v_toPure_340_ = lean_ctor_get(v_toApplicative_337_, 1);
lean_inc(v_toPure_340_);
v___x_341_ = 0;
v___x_342_ = lean_box(0);
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___redArg___closed__0));
lean_inc_ref(v_inst_333_);
lean_inc_ref(v_inst_330_);
v___x_345_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(v_inst_330_, v_inst_331_, v_inst_332_, v_inst_333_, v_f_334_, v_maxIters_336_, v___x_341_, v_goals_335_, v___x_342_, v___x_344_);
lean_inc(v_toBind_338_);
lean_inc_ref(v_inst_330_);
lean_inc(v_toPure_340_);
lean_inc_ref(v_toFunctor_339_);
v___f_346_ = lean_alloc_closure((void*)(l_Lean_Meta_repeat_x27Core___redArg___lam__1), 7, 5);
lean_closure_set(v___f_346_, 0, v_toFunctor_339_);
lean_closure_set(v___f_346_, 1, v_toPure_340_);
lean_closure_set(v___f_346_, 2, v_inst_330_);
lean_closure_set(v___f_346_, 3, v_inst_333_);
lean_closure_set(v___f_346_, 4, v_toBind_338_);
lean_inc(v_toBind_338_);
v___f_347_ = lean_alloc_closure((void*)(l_Lean_Meta_repeat_x27Core___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_347_, 0, v_toPure_340_);
lean_closure_set(v___f_347_, 1, v___x_343_);
lean_closure_set(v___f_347_, 2, v___x_344_);
lean_closure_set(v___f_347_, 3, v_toBind_338_);
lean_closure_set(v___f_347_, 4, v_inst_330_);
lean_closure_set(v___f_347_, 5, v___f_346_);
v___x_348_ = lean_apply_4(v_toBind_338_, lean_box(0), lean_box(0), v___x_345_, v___f_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core(lean_object* v_m_349_, lean_object* v_00_u03b5_350_, lean_object* v_s_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_f_356_, lean_object* v_goals_357_, lean_object* v_maxIters_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_Meta_repeat_x27Core___redArg(v_inst_352_, v_inst_353_, v_inst_354_, v_inst_355_, v_f_356_, v_goals_357_, v_maxIters_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___redArg___lam__0(lean_object* v_x_360_){
_start:
{
lean_object* v_snd_361_; 
v_snd_361_ = lean_ctor_get(v_x_360_, 1);
lean_inc(v_snd_361_);
return v_snd_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___redArg___lam__0___boxed(lean_object* v_x_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Meta_repeat_x27___redArg___lam__0(v_x_362_);
lean_dec_ref(v_x_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___redArg(lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_f_369_, lean_object* v_goals_370_, lean_object* v_maxIters_371_){
_start:
{
lean_object* v_toApplicative_372_; lean_object* v_toFunctor_373_; lean_object* v___f_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_toApplicative_372_ = lean_ctor_get(v_inst_365_, 0);
v_toFunctor_373_ = lean_ctor_get(v_toApplicative_372_, 0);
lean_inc_ref(v_toFunctor_373_);
v___f_374_ = ((lean_object*)(l_Lean_Meta_repeat_x27___redArg___closed__0));
v___x_375_ = l_Lean_Meta_repeat_x27Core___redArg(v_inst_365_, v_inst_366_, v_inst_367_, v_inst_368_, v_f_369_, v_goals_370_, v_maxIters_371_);
v___x_376_ = l_Functor_mapRev___redArg(v_toFunctor_373_, v___x_375_, v___f_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27(lean_object* v_m_377_, lean_object* v_00_u03b5_378_, lean_object* v_s_379_, lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_f_384_, lean_object* v_goals_385_, lean_object* v_maxIters_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Meta_repeat_x27___redArg(v_inst_380_, v_inst_381_, v_inst_382_, v_inst_383_, v_f_384_, v_goals_385_, v_maxIters_386_);
return v___x_387_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__0));
v___x_390_ = l_Lean_stringToMessageData(v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___redArg___lam__0(lean_object* v_toPure_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_____x_394_){
_start:
{
lean_object* v_fst_395_; uint8_t v___x_396_; 
v_fst_395_ = lean_ctor_get(v_____x_394_, 0);
v___x_396_ = lean_unbox(v_fst_395_);
if (v___x_396_ == 1)
{
lean_object* v_snd_397_; lean_object* v___x_398_; 
lean_dec_ref(v_inst_393_);
lean_dec_ref(v_inst_392_);
v_snd_397_ = lean_ctor_get(v_____x_394_, 1);
lean_inc(v_snd_397_);
lean_dec_ref(v_____x_394_);
v___x_398_ = lean_apply_2(v_toPure_391_, lean_box(0), v_snd_397_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; 
lean_dec_ref(v_____x_394_);
lean_dec(v_toPure_391_);
v___x_399_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1, &l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1);
v___x_400_ = l_Lean_throwError___redArg(v_inst_392_, v_inst_393_, v___x_399_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___redArg(lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_f_406_, lean_object* v_goals_407_, lean_object* v_maxIters_408_){
_start:
{
lean_object* v_toApplicative_409_; lean_object* v_toBind_410_; lean_object* v_toPure_411_; lean_object* v___x_412_; lean_object* v___f_413_; lean_object* v___x_414_; 
v_toApplicative_409_ = lean_ctor_get(v_inst_401_, 0);
v_toBind_410_ = lean_ctor_get(v_inst_401_, 1);
lean_inc(v_toBind_410_);
v_toPure_411_ = lean_ctor_get(v_toApplicative_409_, 1);
lean_inc(v_toPure_411_);
lean_inc_ref(v_inst_401_);
v___x_412_ = l_Lean_Meta_repeat_x27Core___redArg(v_inst_401_, v_inst_403_, v_inst_404_, v_inst_405_, v_f_406_, v_goals_407_, v_maxIters_408_);
v___f_413_ = lean_alloc_closure((void*)(l_Lean_Meta_repeat1_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_413_, 0, v_toPure_411_);
lean_closure_set(v___f_413_, 1, v_inst_401_);
lean_closure_set(v___f_413_, 2, v_inst_402_);
v___x_414_ = lean_apply_4(v_toBind_410_, lean_box(0), lean_box(0), v___x_412_, v___f_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27(lean_object* v_m_415_, lean_object* v_00_u03b5_416_, lean_object* v_s_417_, lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_f_423_, lean_object* v_goals_424_, lean_object* v_maxIters_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Meta_repeat1_x27___redArg(v_inst_418_, v_inst_419_, v_inst_420_, v_inst_421_, v_inst_422_, v_f_423_, v_goals_424_, v_maxIters_425_);
return v___x_426_;
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
