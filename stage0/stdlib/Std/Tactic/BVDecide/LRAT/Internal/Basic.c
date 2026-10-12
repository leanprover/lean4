// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Basic
// Imports: public import Std.Sat.CNF.Basic public import Std.Sat.CNF.Entails import Init.Omega
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_State_ofCNF_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_State_ofCNF_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_ofCNF(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_toCNF(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_toCNF___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_all___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_State_ofCNF_spec__0(size_t v_sz_1_, size_t v_i_2_, lean_object* v_bs_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = lean_usize_dec_lt(v_i_2_, v_sz_1_);
if (v___x_4_ == 0)
{
return v_bs_3_;
}
else
{
lean_object* v_v_5_; lean_object* v___x_6_; lean_object* v_bs_x27_7_; lean_object* v___x_8_; size_t v___x_9_; size_t v___x_10_; lean_object* v___x_11_; 
v_v_5_ = lean_array_uget(v_bs_3_, v_i_2_);
v___x_6_ = lean_unsigned_to_nat(0u);
v_bs_x27_7_ = lean_array_uset(v_bs_3_, v_i_2_, v___x_6_);
v___x_8_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_8_, 0, v_v_5_);
v___x_9_ = ((size_t)1ULL);
v___x_10_ = lean_usize_add(v_i_2_, v___x_9_);
v___x_11_ = lean_array_uset(v_bs_x27_7_, v_i_2_, v___x_8_);
v_i_2_ = v___x_10_;
v_bs_3_ = v___x_11_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_State_ofCNF_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1_ = stack[0].m_num;
size_t v_i_2_ = stack[1].m_num;
lean_object* v_bs_3_ = stack[2].m_obj;
lean_object* v_res_13_;
v_res_13_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_State_ofCNF_spec__0(v_sz_1_, v_i_2_, v_bs_3_);
stack->m_obj
 = v_res_13_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_State_ofCNF_spec__0___boxed(lean_object* v_sz_14_, lean_object* v_i_15_, lean_object* v_bs_16_){
_start:
{
size_t v_sz_boxed_17_; size_t v_i_boxed_18_; lean_object* v_res_19_; 
v_sz_boxed_17_ = lean_unbox_usize(v_sz_14_);
lean_dec(v_sz_14_);
v_i_boxed_18_ = lean_unbox_usize(v_i_15_);
lean_dec(v_i_15_);
v_res_19_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_State_ofCNF_spec__0(v_sz_boxed_17_, v_i_boxed_18_, v_bs_16_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_ofCNF(lean_object* v_cnf_20_){
_start:
{
size_t v_sz_21_; size_t v___x_22_; lean_object* v___x_23_; 
v_sz_21_ = lean_array_size(v_cnf_20_);
v___x_22_ = ((size_t)0ULL);
v___x_23_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_State_ofCNF_spec__0(v_sz_21_, v___x_22_, v_cnf_20_);
return v___x_23_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0_spec__0(lean_object* v_as_24_, size_t v_i_25_, size_t v_stop_26_, lean_object* v_b_27_){
_start:
{
lean_object* v___y_29_; uint8_t v___x_33_; 
v___x_33_ = lean_usize_dec_eq(v_i_25_, v_stop_26_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; 
v___x_34_ = lean_array_uget_borrowed(v_as_24_, v_i_25_);
if (lean_obj_tag(v___x_34_) == 0)
{
v___y_29_ = v_b_27_;
goto v___jp_28_;
}
else
{
lean_object* v_val_35_; lean_object* v___x_36_; 
v_val_35_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_val_35_);
v___x_36_ = lean_array_push(v_b_27_, v_val_35_);
v___y_29_ = v___x_36_;
goto v___jp_28_;
}
}
else
{
return v_b_27_;
}
v___jp_28_:
{
size_t v___x_30_; size_t v___x_31_; 
v___x_30_ = ((size_t)1ULL);
v___x_31_ = lean_usize_add(v_i_25_, v___x_30_);
v_i_25_ = v___x_31_;
v_b_27_ = v___y_29_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_24_ = stack[0].m_obj;
size_t v_i_25_ = stack[1].m_num;
size_t v_stop_26_ = stack[2].m_num;
lean_object* v_b_27_ = stack[3].m_obj;
lean_object* v_res_37_;
v_res_37_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0_spec__0(v_as_24_, v_i_25_, v_stop_26_, v_b_27_);
stack->m_obj
 = v_res_37_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0_spec__0___boxed(lean_object* v_as_38_, lean_object* v_i_39_, lean_object* v_stop_40_, lean_object* v_b_41_){
_start:
{
size_t v_i_boxed_42_; size_t v_stop_boxed_43_; lean_object* v_res_44_; 
v_i_boxed_42_ = lean_unbox_usize(v_i_39_);
lean_dec(v_i_39_);
v_stop_boxed_43_ = lean_unbox_usize(v_stop_40_);
lean_dec(v_stop_40_);
v_res_44_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0_spec__0(v_as_38_, v_i_boxed_42_, v_stop_boxed_43_, v_b_41_);
lean_dec_ref(v_as_38_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0(lean_object* v_as_47_, lean_object* v_start_48_, lean_object* v_stop_49_){
_start:
{
lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_50_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0___closed__0));
v___x_51_ = lean_nat_dec_lt(v_start_48_, v_stop_49_);
if (v___x_51_ == 0)
{
return v___x_50_;
}
else
{
lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_52_ = lean_array_get_size(v_as_47_);
v___x_53_ = lean_nat_dec_le(v_stop_49_, v___x_52_);
if (v___x_53_ == 0)
{
uint8_t v___x_54_; 
v___x_54_ = lean_nat_dec_lt(v_start_48_, v___x_52_);
if (v___x_54_ == 0)
{
return v___x_50_;
}
else
{
size_t v___x_55_; size_t v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_usize_of_nat(v_start_48_);
v___x_56_ = lean_usize_of_nat(v___x_52_);
v___x_57_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0_spec__0(v_as_47_, v___x_55_, v___x_56_, v___x_50_);
return v___x_57_;
}
}
else
{
size_t v___x_58_; size_t v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_usize_of_nat(v_start_48_);
v___x_59_ = lean_usize_of_nat(v_stop_49_);
v___x_60_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0_spec__0(v_as_47_, v___x_58_, v___x_59_, v___x_50_);
return v___x_60_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0___boxed(lean_object* v_as_61_, lean_object* v_start_62_, lean_object* v_stop_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0(v_as_61_, v_start_62_, v_stop_63_);
lean_dec(v_stop_63_);
lean_dec(v_start_62_);
lean_dec_ref(v_as_61_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_toCNF(lean_object* v_s_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = lean_array_get_size(v_s_65_);
v___x_68_ = l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0(v_s_65_, v___x_66_, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_toCNF___boxed(lean_object* v_s_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_toCNF(v_s_69_);
lean_dec_ref(v_s_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_get_x3f(lean_object* v_s_71_, lean_object* v_idx_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_nat_sub(v_idx_72_, v___x_73_);
v___x_75_ = lean_array_get_size(v_s_71_);
v___x_76_ = lean_nat_dec_lt(v___x_74_, v___x_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
lean_dec(v___x_74_);
v___x_77_ = lean_box(0);
return v___x_77_;
}
else
{
lean_object* v___x_78_; 
v___x_78_ = lean_array_fget_borrowed(v_s_71_, v___x_74_);
lean_dec(v___x_74_);
lean_inc(v___x_78_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_get_x3f___boxed(lean_object* v_s_79_, lean_object* v_idx_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_get_x3f(v_s_79_, v_idx_80_);
lean_dec(v_idx_80_);
lean_dec_ref(v_s_79_);
return v_res_81_;
}
}
uint8_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go(lean_object* v_s_82_, lean_object* v_p_83_, lean_object* v_i_84_){
_start:
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = lean_array_get_size(v_s_82_);
v___x_86_ = lean_nat_dec_lt(v_i_84_, v___x_85_);
if (v___x_86_ == 0)
{
uint8_t v___x_87_; 
lean_dec(v_i_84_);
lean_dec_ref(v_p_83_);
v___x_87_ = 1;
return v___x_87_;
}
else
{
lean_object* v___x_88_; 
v___x_88_ = lean_array_fget_borrowed(v_s_82_, v_i_84_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(1u);
v___x_90_ = lean_nat_add(v_i_84_, v___x_89_);
lean_dec(v_i_84_);
v_i_84_ = v___x_90_;
goto _start;
}
else
{
lean_object* v_val_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v_val_92_ = lean_ctor_get(v___x_88_, 0);
v___x_93_ = lean_unsigned_to_nat(1u);
v___x_94_ = lean_nat_add(v_i_84_, v___x_93_);
lean_dec(v_i_84_);
lean_inc_ref(v_p_83_);
lean_inc(v_val_92_);
lean_inc(v___x_94_);
v___x_95_ = lean_apply_2(v_p_83_, v___x_94_, v_val_92_);
v___x_96_ = lean_unbox(v___x_95_);
if (v___x_96_ == 0)
{
uint8_t v___x_97_; 
lean_dec(v___x_94_);
lean_dec_ref(v_p_83_);
v___x_97_ = lean_unbox(v___x_95_);
return v___x_97_;
}
else
{
v_i_84_ = v___x_94_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_82_ = stack[0].m_obj;
lean_object* v_p_83_ = stack[1].m_obj;
lean_object* v_i_84_ = stack[2].m_obj;
uint8_t v_res_99_;
v_res_99_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go(v_s_82_, v_p_83_, v_i_84_);
stack->m_num = v_res_99_;
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___boxed(lean_object* v_s_100_, lean_object* v_p_101_, lean_object* v_i_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go(v_s_100_, v_p_101_, v_i_102_);
lean_dec_ref(v_s_100_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go_match__1_splitter___redArg(lean_object* v_x_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec(v_h__1_106_);
v___x_108_ = lean_box(0);
v___x_109_ = lean_apply_1(v_h__2_107_, v___x_108_);
return v___x_109_;
}
else
{
lean_object* v_val_110_; lean_object* v___x_111_; 
lean_dec(v_h__2_107_);
v_val_110_ = lean_ctor_get(v_x_105_, 0);
lean_inc(v_val_110_);
lean_dec_ref_known(v_x_105_, 1);
v___x_111_ = lean_apply_1(v_h__1_106_, v_val_110_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go_match__1_splitter(lean_object* v_motive_112_, lean_object* v_x_113_, lean_object* v_h__1_114_, lean_object* v_h__2_115_){
_start:
{
if (lean_obj_tag(v_x_113_) == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_dec(v_h__1_114_);
v___x_116_ = lean_box(0);
v___x_117_ = lean_apply_1(v_h__2_115_, v___x_116_);
return v___x_117_;
}
else
{
lean_object* v_val_118_; lean_object* v___x_119_; 
lean_dec(v_h__2_115_);
v_val_118_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_val_118_);
lean_dec_ref_known(v_x_113_, 1);
v___x_119_ = lean_apply_1(v_h__1_114_, v_val_118_);
return v___x_119_;
}
}
}
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_all(lean_object* v_s_120_, lean_object* v_p_121_){
_start:
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go(v_s_120_, v_p_121_, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_Internal_State_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_120_ = stack[0].m_obj;
lean_object* v_p_121_ = stack[1].m_obj;
uint8_t v_res_124_;
v_res_124_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_all(v_s_120_, v_p_121_);
stack->m_num = v_res_124_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_all___boxed(lean_object* v_s_125_, lean_object* v_p_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_all(v_s_125_, v_p_126_);
lean_dec_ref(v_s_125_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
lean_object* runtime_initialize_Std_Sat_CNF_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_Entails(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_CNF_Basic(uint8_t builtin);
lean_object* initialize_Std_Sat_CNF_Entails(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
