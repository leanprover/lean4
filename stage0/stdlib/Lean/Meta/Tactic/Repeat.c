// Lean compiler output
// Module: Lean.Meta.Tactic.Repeat
// Imports: public import Lean.Meta.Basic import Init.Data.Nat.Internal.Linear import Init.Omega
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
lean_object* l_Bool_Internal_not___boxed(lean_object*);
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
static const lean_closure_object l_Lean_Meta_repeat_x27Core___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Bool_Internal_not___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
uint8_t v_a_219__boxed_15_; uint8_t v___x_222__boxed_16_; lean_object* v_res_17_; 
v_a_219__boxed_15_ = lean_unbox(v_a_10_);
v___x_222__boxed_16_ = lean_unbox(v___x_13_);
v_res_17_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__0(v_a_2_, v_head_3_, v_inst_4_, v_inst_5_, v_inst_6_, v_inst_7_, v_f_8_, v_n_9_, v_a_219__boxed_15_, v_tail_11_, v_a_12_, v___x_222__boxed_16_, v_____do__lift_14_);
return v_res_17_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1(lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_head_20_, lean_object* v_tail_21_, lean_object* v_a_22_, uint8_t v_a_23_, lean_object* v_toPure_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_f_29_, lean_object* v_toBind_30_, uint8_t v_____do__lift_31_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_18_ = stack[0].m_obj;
lean_object* v_a_19_ = stack[1].m_obj;
lean_object* v_head_20_ = stack[2].m_obj;
lean_object* v_tail_21_ = stack[3].m_obj;
lean_object* v_a_22_ = stack[4].m_obj;
uint8_t v_a_23_ = stack[5].m_num;
lean_object* v_toPure_24_ = stack[6].m_obj;
lean_object* v_inst_25_ = stack[7].m_obj;
lean_object* v_inst_26_ = stack[8].m_obj;
lean_object* v_inst_27_ = stack[9].m_obj;
lean_object* v_inst_28_ = stack[10].m_obj;
lean_object* v_f_29_ = stack[11].m_obj;
lean_object* v_toBind_30_ = stack[12].m_obj;
uint8_t v_____do__lift_31_ = stack[13].m_num;
lean_object* v_res_51_;
v_res_51_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1(v_a_18_, v_a_19_, v_head_20_, v_tail_21_, v_a_22_, v_a_23_, v_toPure_24_, v_inst_25_, v_inst_26_, v_inst_27_, v_inst_28_, v_f_29_, v_toBind_30_, v_____do__lift_31_);
stack->m_obj
 = v_res_51_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1___boxed(lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_head_54_, lean_object* v_tail_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_toPure_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_f_63_, lean_object* v_toBind_64_, lean_object* v_____do__lift_65_){
_start:
{
uint8_t v_a_254__boxed_66_; uint8_t v_____do__lift_259__boxed_67_; lean_object* v_res_68_; 
v_a_254__boxed_66_ = lean_unbox(v_a_57_);
v_____do__lift_259__boxed_67_ = lean_unbox(v_____do__lift_65_);
v_res_68_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1(v_a_52_, v_a_53_, v_head_54_, v_tail_55_, v_a_56_, v_a_254__boxed_66_, v_toPure_58_, v_inst_59_, v_inst_60_, v_inst_61_, v_inst_62_, v_f_63_, v_toBind_64_, v_____do__lift_259__boxed_67_);
return v_res_68_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_f_73_, lean_object* v_a_74_, uint8_t v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
if (lean_obj_tag(v_a_76_) == 0)
{
if (lean_obj_tag(v_a_77_) == 0)
{
lean_object* v_toApplicative_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_89_; 
v_toApplicative_79_ = lean_ctor_get(v_inst_69_, 0);
lean_inc_ref(v_toApplicative_79_);
lean_dec(v_a_74_);
lean_dec(v_f_73_);
lean_dec_ref(v_inst_72_);
lean_dec_ref(v_inst_71_);
lean_dec_ref(v_inst_70_);
v_isSharedCheck_89_ = !lean_is_exclusive(v_inst_69_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; lean_object* v_unused_91_; 
v_unused_90_ = lean_ctor_get(v_inst_69_, 1);
lean_dec(v_unused_90_);
v_unused_91_ = lean_ctor_get(v_inst_69_, 0);
lean_dec(v_unused_91_);
v___x_81_ = v_inst_69_;
v_isShared_82_ = v_isSharedCheck_89_;
goto v_resetjp_80_;
}
else
{
lean_dec(v_inst_69_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_89_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v_toPure_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v_toPure_83_ = lean_ctor_get(v_toApplicative_79_, 1);
lean_inc(v_toPure_83_);
lean_dec_ref(v_toApplicative_79_);
v___x_84_ = lean_box(v_a_75_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v_a_78_);
lean_ctor_set(v___x_81_, 0, v___x_84_);
v___x_86_ = v___x_81_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_a_78_);
v___x_86_ = v_reuseFailAlloc_88_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_87_; 
v___x_87_ = lean_apply_2(v_toPure_83_, lean_box(0), v___x_86_);
return v___x_87_;
}
}
}
else
{
lean_object* v_head_92_; lean_object* v_tail_93_; 
v_head_92_ = lean_ctor_get(v_a_77_, 0);
lean_inc(v_head_92_);
v_tail_93_ = lean_ctor_get(v_a_77_, 1);
lean_inc(v_tail_93_);
lean_dec_ref_known(v_a_77_, 2);
v_a_76_ = v_head_92_;
v_a_77_ = v_tail_93_;
goto _start;
}
}
else
{
lean_object* v_toApplicative_95_; lean_object* v_toBind_96_; lean_object* v_toPure_97_; lean_object* v_head_98_; lean_object* v_tail_99_; lean_object* v___x_100_; lean_object* v___f_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_toApplicative_95_ = lean_ctor_get(v_inst_69_, 0);
v_toBind_96_ = lean_ctor_get(v_inst_69_, 1);
lean_inc_n(v_toBind_96_, 2);
v_toPure_97_ = lean_ctor_get(v_toApplicative_95_, 1);
v_head_98_ = lean_ctor_get(v_a_76_, 0);
lean_inc_n(v_head_98_, 2);
v_tail_99_ = lean_ctor_get(v_a_76_, 1);
lean_inc(v_tail_99_);
lean_dec_ref_known(v_a_76_, 2);
v___x_100_ = lean_box(v_a_75_);
lean_inc_ref(v_inst_72_);
lean_inc_ref(v_inst_69_);
lean_inc(v_toPure_97_);
v___f_101_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1___boxed), 14, 13);
lean_closure_set(v___f_101_, 0, v_a_74_);
lean_closure_set(v___f_101_, 1, v_a_78_);
lean_closure_set(v___f_101_, 2, v_head_98_);
lean_closure_set(v___f_101_, 3, v_tail_99_);
lean_closure_set(v___f_101_, 4, v_a_77_);
lean_closure_set(v___f_101_, 5, v___x_100_);
lean_closure_set(v___f_101_, 6, v_toPure_97_);
lean_closure_set(v___f_101_, 7, v_inst_69_);
lean_closure_set(v___f_101_, 8, v_inst_70_);
lean_closure_set(v___f_101_, 9, v_inst_71_);
lean_closure_set(v___f_101_, 10, v_inst_72_);
lean_closure_set(v___f_101_, 11, v_f_73_);
lean_closure_set(v___f_101_, 12, v_toBind_96_);
v___x_102_ = l_Lean_MVarId_isAssigned___redArg(v_inst_69_, v_inst_72_, v_head_98_);
v___x_103_ = lean_apply_4(v_toBind_96_, lean_box(0), lean_box(0), v___x_102_, v___f_101_);
return v___x_103_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_69_ = stack[0].m_obj;
lean_object* v_inst_70_ = stack[1].m_obj;
lean_object* v_inst_71_ = stack[2].m_obj;
lean_object* v_inst_72_ = stack[3].m_obj;
lean_object* v_f_73_ = stack[4].m_obj;
lean_object* v_a_74_ = stack[5].m_obj;
uint8_t v_a_75_ = stack[6].m_num;
lean_object* v_a_76_ = stack[7].m_obj;
lean_object* v_a_77_ = stack[8].m_obj;
lean_object* v_a_78_ = stack[9].m_obj;
lean_object* v_res_104_;
v_res_104_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(v_inst_69_, v_inst_70_, v_inst_71_, v_inst_72_, v_f_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_);
stack->m_obj
 = v_res_104_;
}
lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__0(lean_object* v_a_105_, lean_object* v_head_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_f_111_, lean_object* v_n_112_, uint8_t v_a_113_, lean_object* v_tail_114_, lean_object* v_a_115_, uint8_t v___x_116_, lean_object* v_____do__lift_117_){
_start:
{
if (lean_obj_tag(v_____do__lift_117_) == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_array_push(v_a_105_, v_head_106_);
v___x_119_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(v_inst_107_, v_inst_108_, v_inst_109_, v_inst_110_, v_f_111_, v_n_112_, v_a_113_, v_tail_114_, v_a_115_, v___x_118_);
return v___x_119_;
}
else
{
lean_object* v_val_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
lean_dec(v_head_106_);
v_val_120_ = lean_ctor_get(v_____do__lift_117_, 0);
lean_inc(v_val_120_);
lean_dec_ref_known(v_____do__lift_117_, 1);
v___x_121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_121_, 0, v_tail_114_);
lean_ctor_set(v___x_121_, 1, v_a_115_);
v___x_122_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(v_inst_107_, v_inst_108_, v_inst_109_, v_inst_110_, v_f_111_, v_n_112_, v___x_116_, v_val_120_, v___x_121_, v_a_105_);
return v___x_122_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_105_ = stack[0].m_obj;
lean_object* v_head_106_ = stack[1].m_obj;
lean_object* v_inst_107_ = stack[2].m_obj;
lean_object* v_inst_108_ = stack[3].m_obj;
lean_object* v_inst_109_ = stack[4].m_obj;
lean_object* v_inst_110_ = stack[5].m_obj;
lean_object* v_f_111_ = stack[6].m_obj;
lean_object* v_n_112_ = stack[7].m_obj;
uint8_t v_a_113_ = stack[8].m_num;
lean_object* v_tail_114_ = stack[9].m_obj;
lean_object* v_a_115_ = stack[10].m_obj;
uint8_t v___x_116_ = stack[11].m_num;
lean_object* v_____do__lift_117_ = stack[12].m_obj;
lean_object* v_res_123_;
v_res_123_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__0(v_a_105_, v_head_106_, v_inst_107_, v_inst_108_, v_inst_109_, v_inst_110_, v_f_111_, v_n_112_, v_a_113_, v_tail_114_, v_a_115_, v___x_116_, v_____do__lift_117_);
stack->m_obj
 = v_res_123_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___boxed(lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_f_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
uint8_t v_a_234__boxed_134_; lean_object* v_res_135_; 
v_a_234__boxed_134_ = lean_unbox(v_a_130_);
v_res_135_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(v_inst_124_, v_inst_125_, v_inst_126_, v_inst_127_, v_f_128_, v_a_129_, v_a_234__boxed_134_, v_a_131_, v_a_132_, v_a_133_);
return v_res_135_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go(lean_object* v_m_136_, lean_object* v_00_u03b5_137_, lean_object* v_s_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_f_143_, lean_object* v_a_144_, uint8_t v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(v_inst_139_, v_inst_140_, v_inst_141_, v_inst_142_, v_f_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
return v___x_149_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_139_ = stack[3].m_obj;
lean_object* v_inst_140_ = stack[4].m_obj;
lean_object* v_inst_141_ = stack[5].m_obj;
lean_object* v_inst_142_ = stack[6].m_obj;
lean_object* v_f_143_ = stack[7].m_obj;
lean_object* v_a_144_ = stack[8].m_obj;
uint8_t v_a_145_ = stack[9].m_num;
lean_object* v_a_146_ = stack[10].m_obj;
lean_object* v_a_147_ = stack[11].m_obj;
lean_object* v_a_148_ = stack[12].m_obj;
lean_object* v_res_150_;
v_res_150_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go(lean_box(0), lean_box(0), lean_box(0), v_inst_139_, v_inst_140_, v_inst_141_, v_inst_142_, v_f_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
stack->m_obj
 = v_res_150_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___boxed(lean_object* v_m_151_, lean_object* v_00_u03b5_152_, lean_object* v_s_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_f_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
uint8_t v_a_503__boxed_164_; lean_object* v_res_165_; 
v_a_503__boxed_164_ = lean_unbox(v_a_160_);
v_res_165_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go(v_m_151_, v_00_u03b5_152_, v_s_153_, v_inst_154_, v_inst_155_, v_inst_156_, v_inst_157_, v_f_158_, v_a_159_, v_a_503__boxed_164_, v_a_161_, v_a_162_, v_a_163_);
return v_res_165_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___redArg(lean_object* v_x_166_, uint8_t v_x_167_, lean_object* v_x_168_, lean_object* v_x_169_, lean_object* v_x_170_, lean_object* v_h__1_171_, lean_object* v_h__2_172_, lean_object* v_h__3_173_){
_start:
{
if (lean_obj_tag(v_x_168_) == 0)
{
lean_dec(v_h__3_173_);
if (lean_obj_tag(v_x_169_) == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec(v_h__2_172_);
v___x_174_ = lean_box(v_x_167_);
v___x_175_ = lean_apply_3(v_h__1_171_, v_x_166_, v___x_174_, v_x_170_);
return v___x_175_;
}
else
{
lean_object* v_head_176_; lean_object* v_tail_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v_h__1_171_);
v_head_176_ = lean_ctor_get(v_x_169_, 0);
lean_inc(v_head_176_);
v_tail_177_ = lean_ctor_get(v_x_169_, 1);
lean_inc(v_tail_177_);
lean_dec_ref_known(v_x_169_, 2);
v___x_178_ = lean_box(v_x_167_);
v___x_179_ = lean_apply_5(v_h__2_172_, v_x_166_, v___x_178_, v_head_176_, v_tail_177_, v_x_170_);
return v___x_179_;
}
}
else
{
lean_object* v_head_180_; lean_object* v_tail_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec(v_h__2_172_);
lean_dec(v_h__1_171_);
v_head_180_ = lean_ctor_get(v_x_168_, 0);
lean_inc(v_head_180_);
v_tail_181_ = lean_ctor_get(v_x_168_, 1);
lean_inc(v_tail_181_);
lean_dec_ref_known(v_x_168_, 2);
v___x_182_ = lean_box(v_x_167_);
v___x_183_ = lean_apply_6(v_h__3_173_, v_x_166_, v___x_182_, v_head_180_, v_tail_181_, v_x_169_, v_x_170_);
return v___x_183_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_166_ = stack[0].m_obj;
uint8_t v_x_167_ = stack[1].m_num;
lean_object* v_x_168_ = stack[2].m_obj;
lean_object* v_x_169_ = stack[3].m_obj;
lean_object* v_x_170_ = stack[4].m_obj;
lean_object* v_h__1_171_ = stack[5].m_obj;
lean_object* v_h__2_172_ = stack[6].m_obj;
lean_object* v_h__3_173_ = stack[7].m_obj;
lean_object* v_res_184_;
v_res_184_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___redArg(v_x_166_, v_x_167_, v_x_168_, v_x_169_, v_x_170_, v_h__1_171_, v_h__2_172_, v_h__3_173_);
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___redArg___boxed(lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_h__1_190_, lean_object* v_h__2_191_, lean_object* v_h__3_192_){
_start:
{
uint8_t v_x_43__boxed_193_; lean_object* v_res_194_; 
v_x_43__boxed_193_ = lean_unbox(v_x_186_);
v_res_194_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___redArg(v_x_185_, v_x_43__boxed_193_, v_x_187_, v_x_188_, v_x_189_, v_h__1_190_, v_h__2_191_, v_h__3_192_);
return v_res_194_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter(lean_object* v_motive_195_, lean_object* v_x_196_, uint8_t v_x_197_, lean_object* v_x_198_, lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v_h__1_201_, lean_object* v_h__2_202_, lean_object* v_h__3_203_){
_start:
{
if (lean_obj_tag(v_x_198_) == 0)
{
lean_dec(v_h__3_203_);
if (lean_obj_tag(v_x_199_) == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec(v_h__2_202_);
v___x_204_ = lean_box(v_x_197_);
v___x_205_ = lean_apply_3(v_h__1_201_, v_x_196_, v___x_204_, v_x_200_);
return v___x_205_;
}
else
{
lean_object* v_head_206_; lean_object* v_tail_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec(v_h__1_201_);
v_head_206_ = lean_ctor_get(v_x_199_, 0);
lean_inc(v_head_206_);
v_tail_207_ = lean_ctor_get(v_x_199_, 1);
lean_inc(v_tail_207_);
lean_dec_ref_known(v_x_199_, 2);
v___x_208_ = lean_box(v_x_197_);
v___x_209_ = lean_apply_5(v_h__2_202_, v_x_196_, v___x_208_, v_head_206_, v_tail_207_, v_x_200_);
return v___x_209_;
}
}
else
{
lean_object* v_head_210_; lean_object* v_tail_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v_h__2_202_);
lean_dec(v_h__1_201_);
v_head_210_ = lean_ctor_get(v_x_198_, 0);
lean_inc(v_head_210_);
v_tail_211_ = lean_ctor_get(v_x_198_, 1);
lean_inc(v_tail_211_);
lean_dec_ref_known(v_x_198_, 2);
v___x_212_ = lean_box(v_x_197_);
v___x_213_ = lean_apply_6(v_h__3_203_, v_x_196_, v___x_212_, v_head_210_, v_tail_211_, v_x_199_, v_x_200_);
return v___x_213_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_196_ = stack[1].m_obj;
uint8_t v_x_197_ = stack[2].m_num;
lean_object* v_x_198_ = stack[3].m_obj;
lean_object* v_x_199_ = stack[4].m_obj;
lean_object* v_x_200_ = stack[5].m_obj;
lean_object* v_h__1_201_ = stack[6].m_obj;
lean_object* v_h__2_202_ = stack[7].m_obj;
lean_object* v_h__3_203_ = stack[8].m_obj;
lean_object* v_res_214_;
v_res_214_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter(lean_box(0), v_x_196_, v_x_197_, v_x_198_, v_x_199_, v_x_200_, v_h__1_201_, v_h__2_202_, v_h__3_203_);
stack->m_obj
 = v_res_214_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___boxed(lean_object* v_motive_215_, lean_object* v_x_216_, lean_object* v_x_217_, lean_object* v_x_218_, lean_object* v_x_219_, lean_object* v_x_220_, lean_object* v_h__1_221_, lean_object* v_h__2_222_, lean_object* v_h__3_223_){
_start:
{
uint8_t v_x_98__boxed_224_; lean_object* v_res_225_; 
v_x_98__boxed_224_ = lean_unbox(v_x_217_);
v_res_225_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter(v_motive_215_, v_x_216_, v_x_98__boxed_224_, v_x_218_, v_x_219_, v_x_220_, v_h__1_221_, v_h__2_222_, v_h__3_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___redArg(lean_object* v_n_226_, lean_object* v_h__1_227_, lean_object* v_h__2_228_){
_start:
{
lean_object* v_zero_229_; uint8_t v_isZero_230_; 
v_zero_229_ = lean_unsigned_to_nat(0u);
v_isZero_230_ = lean_nat_dec_eq(v_n_226_, v_zero_229_);
if (v_isZero_230_ == 1)
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_dec(v_h__2_228_);
v___x_231_ = lean_box(0);
v___x_232_ = lean_apply_1(v_h__1_227_, v___x_231_);
return v___x_232_;
}
else
{
lean_object* v_one_233_; lean_object* v_n_234_; lean_object* v___x_235_; 
lean_dec(v_h__1_227_);
v_one_233_ = lean_unsigned_to_nat(1u);
v_n_234_ = lean_nat_sub(v_n_226_, v_one_233_);
v___x_235_ = lean_apply_1(v_h__2_228_, v_n_234_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___redArg___boxed(lean_object* v_n_236_, lean_object* v_h__1_237_, lean_object* v_h__2_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___redArg(v_n_236_, v_h__1_237_, v_h__2_238_);
lean_dec(v_n_236_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter(lean_object* v_motive_240_, lean_object* v_n_241_, lean_object* v_h__1_242_, lean_object* v_h__2_243_){
_start:
{
lean_object* v_zero_244_; uint8_t v_isZero_245_; 
v_zero_244_ = lean_unsigned_to_nat(0u);
v_isZero_245_ = lean_nat_dec_eq(v_n_241_, v_zero_244_);
if (v_isZero_245_ == 1)
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec(v_h__2_243_);
v___x_246_ = lean_box(0);
v___x_247_ = lean_apply_1(v_h__1_242_, v___x_246_);
return v___x_247_;
}
else
{
lean_object* v_one_248_; lean_object* v_n_249_; lean_object* v___x_250_; 
lean_dec(v_h__1_242_);
v_one_248_ = lean_unsigned_to_nat(1u);
v_n_249_ = lean_nat_sub(v_n_241_, v_one_248_);
v___x_250_ = lean_apply_1(v_h__2_243_, v_n_249_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___boxed(lean_object* v_motive_251_, lean_object* v_n_252_, lean_object* v_h__1_253_, lean_object* v_h__2_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter(v_motive_251_, v_n_252_, v_h__1_253_, v_h__2_254_);
lean_dec(v_n_252_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__List_map__unattach_match__1_splitter___redArg(lean_object* v_x_256_, lean_object* v_h__1_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lean_apply_2(v_h__1_257_, v_x_256_, lean_box(0));
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__List_map__unattach_match__1_splitter(lean_object* v_00_u03b1_259_, lean_object* v_P_260_, lean_object* v_motive_261_, lean_object* v_x_262_, lean_object* v_h__1_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = lean_apply_2(v_h__1_263_, v_x_262_, lean_box(0));
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__1_splitter___redArg(lean_object* v_____do__lift_265_, lean_object* v_h__1_266_, lean_object* v_h__2_267_){
_start:
{
if (lean_obj_tag(v_____do__lift_265_) == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec(v_h__1_266_);
v___x_268_ = lean_box(0);
v___x_269_ = lean_apply_1(v_h__2_267_, v___x_268_);
return v___x_269_;
}
else
{
lean_object* v_val_270_; lean_object* v___x_271_; 
lean_dec(v_h__2_267_);
v_val_270_ = lean_ctor_get(v_____do__lift_265_, 0);
lean_inc(v_val_270_);
lean_dec_ref_known(v_____do__lift_265_, 1);
v___x_271_ = lean_apply_1(v_h__1_266_, v_val_270_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__1_splitter(lean_object* v_motive_272_, lean_object* v_____do__lift_273_, lean_object* v_h__1_274_, lean_object* v_h__2_275_){
_start:
{
if (lean_obj_tag(v_____do__lift_273_) == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec(v_h__1_274_);
v___x_276_ = lean_box(0);
v___x_277_ = lean_apply_1(v_h__2_275_, v___x_276_);
return v___x_277_;
}
else
{
lean_object* v_val_278_; lean_object* v___x_279_; 
lean_dec(v_h__2_275_);
v_val_278_ = lean_ctor_get(v_____do__lift_273_, 0);
lean_inc(v_val_278_);
lean_dec_ref_known(v_____do__lift_273_, 1);
v___x_279_ = lean_apply_1(v_h__1_274_, v_val_278_);
return v___x_279_;
}
}
}
lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__0(lean_object* v_toPure_280_, lean_object* v_acc_281_, lean_object* v_a_282_, uint8_t v_____do__lift_283_){
_start:
{
if (v_____do__lift_283_ == 0)
{
lean_object* v___x_284_; 
lean_dec(v_a_282_);
v___x_284_ = lean_apply_2(v_toPure_280_, lean_box(0), v_acc_281_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_array_push(v_acc_281_, v_a_282_);
v___x_286_ = lean_apply_2(v_toPure_280_, lean_box(0), v___x_285_);
return v___x_286_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_repeat_x27Core___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_280_ = stack[0].m_obj;
lean_object* v_acc_281_ = stack[1].m_obj;
lean_object* v_a_282_ = stack[2].m_obj;
uint8_t v_____do__lift_283_ = stack[3].m_num;
lean_object* v_res_287_;
v_res_287_ = l_Lean_Meta_repeat_x27Core___redArg___lam__0(v_toPure_280_, v_acc_281_, v_a_282_, v_____do__lift_283_);
stack->m_obj
 = v_res_287_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__0___boxed(lean_object* v_toPure_288_, lean_object* v_acc_289_, lean_object* v_a_290_, lean_object* v_____do__lift_291_){
_start:
{
uint8_t v_____do__lift_184__boxed_292_; lean_object* v_res_293_; 
v_____do__lift_184__boxed_292_ = lean_unbox(v_____do__lift_291_);
v_res_293_ = l_Lean_Meta_repeat_x27Core___redArg___lam__0(v_toPure_288_, v_acc_289_, v_a_290_, v_____do__lift_184__boxed_292_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__1(lean_object* v_toFunctor_295_, lean_object* v_toPure_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_toBind_299_, lean_object* v_acc_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_map_302_; lean_object* v___f_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_map_302_ = lean_ctor_get(v_toFunctor_295_, 0);
lean_inc(v_map_302_);
lean_dec_ref(v_toFunctor_295_);
lean_inc(v_a_301_);
v___f_303_ = lean_alloc_closure((void*)(l_Lean_Meta_repeat_x27Core___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_303_, 0, v_toPure_296_);
lean_closure_set(v___f_303_, 1, v_acc_300_);
lean_closure_set(v___f_303_, 2, v_a_301_);
v___x_304_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___redArg___lam__1___closed__0));
v___x_305_ = l_Lean_MVarId_isAssigned___redArg(v_inst_297_, v_inst_298_, v_a_301_);
v___x_306_ = lean_apply_4(v_map_302_, lean_box(0), lean_box(0), v___x_304_, v___x_305_);
v___x_307_ = lean_apply_4(v_toBind_299_, lean_box(0), lean_box(0), v___x_306_, v___f_303_);
return v___x_307_;
}
}
lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__2(uint8_t v_fst_308_, lean_object* v_toPure_309_, lean_object* v_____do__lift_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_311_ = lean_array_to_list(v_____do__lift_310_);
v___x_312_ = lean_box(v_fst_308_);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
v___x_314_ = lean_apply_2(v_toPure_309_, lean_box(0), v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT void l_Lean_Meta_repeat_x27Core___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_fst_308_ = stack[0].m_num;
lean_object* v_toPure_309_ = stack[1].m_obj;
lean_object* v_____do__lift_310_ = stack[2].m_obj;
lean_object* v_res_315_;
v_res_315_ = l_Lean_Meta_repeat_x27Core___redArg___lam__2(v_fst_308_, v_toPure_309_, v_____do__lift_310_);
stack->m_obj
 = v_res_315_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__2___boxed(lean_object* v_fst_316_, lean_object* v_toPure_317_, lean_object* v_____do__lift_318_){
_start:
{
uint8_t v_fst_223__boxed_319_; lean_object* v_res_320_; 
v_fst_223__boxed_319_ = lean_unbox(v_fst_316_);
v_res_320_ = l_Lean_Meta_repeat_x27Core___redArg___lam__2(v_fst_223__boxed_319_, v_toPure_317_, v_____do__lift_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__3(lean_object* v_toPure_321_, lean_object* v___x_322_, lean_object* v___x_323_, lean_object* v_toBind_324_, lean_object* v_inst_325_, lean_object* v___f_326_, lean_object* v_____x_327_){
_start:
{
lean_object* v_fst_328_; lean_object* v_snd_329_; lean_object* v___f_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v_fst_328_ = lean_ctor_get(v_____x_327_, 0);
lean_inc(v_fst_328_);
v_snd_329_ = lean_ctor_get(v_____x_327_, 1);
lean_inc(v_snd_329_);
lean_dec_ref(v_____x_327_);
lean_inc(v_toPure_321_);
v___f_330_ = lean_alloc_closure((void*)(l_Lean_Meta_repeat_x27Core___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_330_, 0, v_fst_328_);
lean_closure_set(v___f_330_, 1, v_toPure_321_);
v___x_331_ = lean_array_get_size(v_snd_329_);
v___x_332_ = lean_nat_dec_lt(v___x_322_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec(v_snd_329_);
lean_dec(v___f_326_);
lean_dec_ref(v_inst_325_);
v___x_333_ = lean_apply_2(v_toPure_321_, lean_box(0), v___x_323_);
v___x_334_ = lean_apply_4(v_toBind_324_, lean_box(0), lean_box(0), v___x_333_, v___f_330_);
return v___x_334_;
}
else
{
uint8_t v___x_335_; 
v___x_335_ = lean_nat_dec_le(v___x_331_, v___x_331_);
if (v___x_335_ == 0)
{
if (v___x_332_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec(v_snd_329_);
lean_dec(v___f_326_);
lean_dec_ref(v_inst_325_);
v___x_336_ = lean_apply_2(v_toPure_321_, lean_box(0), v___x_323_);
v___x_337_ = lean_apply_4(v_toBind_324_, lean_box(0), lean_box(0), v___x_336_, v___f_330_);
return v___x_337_;
}
else
{
size_t v___x_338_; size_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec(v_toPure_321_);
v___x_338_ = ((size_t)0ULL);
v___x_339_ = lean_usize_of_nat(v___x_331_);
v___x_340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_325_, v___f_326_, v_snd_329_, v___x_338_, v___x_339_, v___x_323_);
v___x_341_ = lean_apply_4(v_toBind_324_, lean_box(0), lean_box(0), v___x_340_, v___f_330_);
return v___x_341_;
}
}
else
{
size_t v___x_342_; size_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
lean_dec(v_toPure_321_);
v___x_342_ = ((size_t)0ULL);
v___x_343_ = lean_usize_of_nat(v___x_331_);
v___x_344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_325_, v___f_326_, v_snd_329_, v___x_342_, v___x_343_, v___x_323_);
v___x_345_ = lean_apply_4(v_toBind_324_, lean_box(0), lean_box(0), v___x_344_, v___f_330_);
return v___x_345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg___lam__3___boxed(lean_object* v_toPure_346_, lean_object* v___x_347_, lean_object* v___x_348_, lean_object* v_toBind_349_, lean_object* v_inst_350_, lean_object* v___f_351_, lean_object* v_____x_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_Meta_repeat_x27Core___redArg___lam__3(v_toPure_346_, v___x_347_, v___x_348_, v_toBind_349_, v_inst_350_, v___f_351_, v_____x_352_);
lean_dec(v___x_347_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___redArg(lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_f_360_, lean_object* v_goals_361_, lean_object* v_maxIters_362_){
_start:
{
lean_object* v_toApplicative_363_; lean_object* v_toBind_364_; lean_object* v_toFunctor_365_; lean_object* v_toPure_366_; uint8_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___x_374_; 
v_toApplicative_363_ = lean_ctor_get(v_inst_356_, 0);
v_toBind_364_ = lean_ctor_get(v_inst_356_, 1);
lean_inc_n(v_toBind_364_, 3);
v_toFunctor_365_ = lean_ctor_get(v_toApplicative_363_, 0);
v_toPure_366_ = lean_ctor_get(v_toApplicative_363_, 1);
lean_inc_n(v_toPure_366_, 2);
v___x_367_ = 0;
v___x_368_ = lean_box(0);
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___redArg___closed__0));
lean_inc_ref(v_inst_359_);
lean_inc_ref_n(v_inst_356_, 2);
v___x_371_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(v_inst_356_, v_inst_357_, v_inst_358_, v_inst_359_, v_f_360_, v_maxIters_362_, v___x_367_, v_goals_361_, v___x_368_, v___x_370_);
lean_inc_ref(v_toFunctor_365_);
v___f_372_ = lean_alloc_closure((void*)(l_Lean_Meta_repeat_x27Core___redArg___lam__1), 7, 5);
lean_closure_set(v___f_372_, 0, v_toFunctor_365_);
lean_closure_set(v___f_372_, 1, v_toPure_366_);
lean_closure_set(v___f_372_, 2, v_inst_356_);
lean_closure_set(v___f_372_, 3, v_inst_359_);
lean_closure_set(v___f_372_, 4, v_toBind_364_);
v___f_373_ = lean_alloc_closure((void*)(l_Lean_Meta_repeat_x27Core___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_373_, 0, v_toPure_366_);
lean_closure_set(v___f_373_, 1, v___x_369_);
lean_closure_set(v___f_373_, 2, v___x_370_);
lean_closure_set(v___f_373_, 3, v_toBind_364_);
lean_closure_set(v___f_373_, 4, v_inst_356_);
lean_closure_set(v___f_373_, 5, v___f_372_);
v___x_374_ = lean_apply_4(v_toBind_364_, lean_box(0), lean_box(0), v___x_371_, v___f_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core(lean_object* v_m_375_, lean_object* v_00_u03b5_376_, lean_object* v_s_377_, lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_f_382_, lean_object* v_goals_383_, lean_object* v_maxIters_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Meta_repeat_x27Core___redArg(v_inst_378_, v_inst_379_, v_inst_380_, v_inst_381_, v_f_382_, v_goals_383_, v_maxIters_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___redArg___lam__0(lean_object* v_x_386_){
_start:
{
lean_object* v_snd_387_; 
v_snd_387_ = lean_ctor_get(v_x_386_, 1);
lean_inc(v_snd_387_);
return v_snd_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___redArg___lam__0___boxed(lean_object* v_x_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Meta_repeat_x27___redArg___lam__0(v_x_388_);
lean_dec_ref(v_x_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27___redArg(lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_f_395_, lean_object* v_goals_396_, lean_object* v_maxIters_397_){
_start:
{
lean_object* v_toApplicative_398_; lean_object* v_toFunctor_399_; lean_object* v___f_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_toApplicative_398_ = lean_ctor_get(v_inst_391_, 0);
v_toFunctor_399_ = lean_ctor_get(v_toApplicative_398_, 0);
lean_inc_ref(v_toFunctor_399_);
v___f_400_ = ((lean_object*)(l_Lean_Meta_repeat_x27___redArg___closed__0));
v___x_401_ = l_Lean_Meta_repeat_x27Core___redArg(v_inst_391_, v_inst_392_, v_inst_393_, v_inst_394_, v_f_395_, v_goals_396_, v_maxIters_397_);
v___x_402_ = l_Functor_mapRev___redArg(v_toFunctor_399_, v___x_401_, v___f_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27(lean_object* v_m_403_, lean_object* v_00_u03b5_404_, lean_object* v_s_405_, lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_f_410_, lean_object* v_goals_411_, lean_object* v_maxIters_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Meta_repeat_x27___redArg(v_inst_406_, v_inst_407_, v_inst_408_, v_inst_409_, v_f_410_, v_goals_411_, v_maxIters_412_);
return v___x_413_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__0));
v___x_416_ = l_Lean_stringToMessageData(v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___redArg___lam__0(lean_object* v_toPure_417_, lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_____x_420_){
_start:
{
lean_object* v_fst_421_; uint8_t v___x_422_; 
v_fst_421_ = lean_ctor_get(v_____x_420_, 0);
v___x_422_ = lean_unbox(v_fst_421_);
if (v___x_422_ == 1)
{
lean_object* v_snd_423_; lean_object* v___x_424_; 
lean_dec_ref(v_inst_419_);
lean_dec_ref(v_inst_418_);
v_snd_423_ = lean_ctor_get(v_____x_420_, 1);
lean_inc(v_snd_423_);
lean_dec_ref(v_____x_420_);
v___x_424_ = lean_apply_2(v_toPure_417_, lean_box(0), v_snd_423_);
return v___x_424_;
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec_ref(v_____x_420_);
lean_dec(v_toPure_417_);
v___x_425_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1, &l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1);
v___x_426_ = l_Lean_throwError___redArg(v_inst_418_, v_inst_419_, v___x_425_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___redArg(lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_f_432_, lean_object* v_goals_433_, lean_object* v_maxIters_434_){
_start:
{
lean_object* v_toApplicative_435_; lean_object* v_toBind_436_; lean_object* v_toPure_437_; lean_object* v___x_438_; lean_object* v___f_439_; lean_object* v___x_440_; 
v_toApplicative_435_ = lean_ctor_get(v_inst_427_, 0);
v_toBind_436_ = lean_ctor_get(v_inst_427_, 1);
lean_inc(v_toBind_436_);
v_toPure_437_ = lean_ctor_get(v_toApplicative_435_, 1);
lean_inc(v_toPure_437_);
lean_inc_ref(v_inst_427_);
v___x_438_ = l_Lean_Meta_repeat_x27Core___redArg(v_inst_427_, v_inst_429_, v_inst_430_, v_inst_431_, v_f_432_, v_goals_433_, v_maxIters_434_);
v___f_439_ = lean_alloc_closure((void*)(l_Lean_Meta_repeat1_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_439_, 0, v_toPure_437_);
lean_closure_set(v___f_439_, 1, v_inst_427_);
lean_closure_set(v___f_439_, 2, v_inst_428_);
v___x_440_ = lean_apply_4(v_toBind_436_, lean_box(0), lean_box(0), v___x_438_, v___f_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27(lean_object* v_m_441_, lean_object* v_00_u03b5_442_, lean_object* v_s_443_, lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_f_449_, lean_object* v_goals_450_, lean_object* v_maxIters_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_Meta_repeat1_x27___redArg(v_inst_444_, v_inst_445_, v_inst_446_, v_inst_447_, v_inst_448_, v_f_449_, v_goals_450_, v_maxIters_451_);
return v___x_452_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
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
