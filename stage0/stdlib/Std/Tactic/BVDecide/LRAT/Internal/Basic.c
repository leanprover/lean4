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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_State_ofCNF_spec__0(size_t v_sz_1_, size_t v_i_2_, lean_object* v_bs_3_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_State_ofCNF_spec__0___boxed(lean_object* v_sz_13_, lean_object* v_i_14_, lean_object* v_bs_15_){
_start:
{
size_t v_sz_boxed_16_; size_t v_i_boxed_17_; lean_object* v_res_18_; 
v_sz_boxed_16_ = lean_unbox_usize(v_sz_13_);
lean_dec(v_sz_13_);
v_i_boxed_17_ = lean_unbox_usize(v_i_14_);
lean_dec(v_i_14_);
v_res_18_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_State_ofCNF_spec__0(v_sz_boxed_16_, v_i_boxed_17_, v_bs_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_ofCNF(lean_object* v_cnf_19_){
_start:
{
size_t v_sz_20_; size_t v___x_21_; lean_object* v___x_22_; 
v_sz_20_ = lean_array_size(v_cnf_19_);
v___x_21_ = ((size_t)0ULL);
v___x_22_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_State_ofCNF_spec__0(v_sz_20_, v___x_21_, v_cnf_19_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0_spec__0(lean_object* v_as_23_, size_t v_i_24_, size_t v_stop_25_, lean_object* v_b_26_){
_start:
{
lean_object* v___y_28_; uint8_t v___x_32_; 
v___x_32_ = lean_usize_dec_eq(v_i_24_, v_stop_25_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; 
v___x_33_ = lean_array_uget_borrowed(v_as_23_, v_i_24_);
if (lean_obj_tag(v___x_33_) == 0)
{
v___y_28_ = v_b_26_;
goto v___jp_27_;
}
else
{
lean_object* v_val_34_; lean_object* v___x_35_; 
v_val_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_val_34_);
v___x_35_ = lean_array_push(v_b_26_, v_val_34_);
v___y_28_ = v___x_35_;
goto v___jp_27_;
}
}
else
{
return v_b_26_;
}
v___jp_27_:
{
size_t v___x_29_; size_t v___x_30_; 
v___x_29_ = ((size_t)1ULL);
v___x_30_ = lean_usize_add(v_i_24_, v___x_29_);
v_i_24_ = v___x_30_;
v_b_26_ = v___y_28_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0_spec__0___boxed(lean_object* v_as_36_, lean_object* v_i_37_, lean_object* v_stop_38_, lean_object* v_b_39_){
_start:
{
size_t v_i_boxed_40_; size_t v_stop_boxed_41_; lean_object* v_res_42_; 
v_i_boxed_40_ = lean_unbox_usize(v_i_37_);
lean_dec(v_i_37_);
v_stop_boxed_41_ = lean_unbox_usize(v_stop_38_);
lean_dec(v_stop_38_);
v_res_42_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0_spec__0(v_as_36_, v_i_boxed_40_, v_stop_boxed_41_, v_b_39_);
lean_dec_ref(v_as_36_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0(lean_object* v_as_45_, lean_object* v_start_46_, lean_object* v_stop_47_){
_start:
{
lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_48_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0___closed__0));
v___x_49_ = lean_nat_dec_lt(v_start_46_, v_stop_47_);
if (v___x_49_ == 0)
{
return v___x_48_;
}
else
{
lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_50_ = lean_array_get_size(v_as_45_);
v___x_51_ = lean_nat_dec_le(v_stop_47_, v___x_50_);
if (v___x_51_ == 0)
{
uint8_t v___x_52_; 
v___x_52_ = lean_nat_dec_lt(v_start_46_, v___x_50_);
if (v___x_52_ == 0)
{
return v___x_48_;
}
else
{
size_t v___x_53_; size_t v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_usize_of_nat(v_start_46_);
v___x_54_ = lean_usize_of_nat(v___x_50_);
v___x_55_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0_spec__0(v_as_45_, v___x_53_, v___x_54_, v___x_48_);
return v___x_55_;
}
}
else
{
size_t v___x_56_; size_t v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_usize_of_nat(v_start_46_);
v___x_57_ = lean_usize_of_nat(v_stop_47_);
v___x_58_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0_spec__0(v_as_45_, v___x_56_, v___x_57_, v___x_48_);
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0___boxed(lean_object* v_as_59_, lean_object* v_start_60_, lean_object* v_stop_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0(v_as_59_, v_start_60_, v_stop_61_);
lean_dec(v_stop_61_);
lean_dec(v_start_60_);
lean_dec_ref(v_as_59_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_toCNF(lean_object* v_s_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = lean_array_get_size(v_s_63_);
v___x_66_ = l_Array_filterMapM___at___00Std_Tactic_BVDecide_LRAT_Internal_State_toCNF_spec__0(v_s_63_, v___x_64_, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_toCNF___boxed(lean_object* v_s_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_toCNF(v_s_67_);
lean_dec_ref(v_s_67_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_get_x3f(lean_object* v_s_69_, lean_object* v_idx_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_71_ = lean_unsigned_to_nat(1u);
v___x_72_ = lean_nat_sub(v_idx_70_, v___x_71_);
v___x_73_ = lean_array_get_size(v_s_69_);
v___x_74_ = lean_nat_dec_lt(v___x_72_, v___x_73_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; 
lean_dec(v___x_72_);
v___x_75_ = lean_box(0);
return v___x_75_;
}
else
{
lean_object* v___x_76_; 
v___x_76_ = lean_array_fget_borrowed(v_s_69_, v___x_72_);
lean_dec(v___x_72_);
lean_inc(v___x_76_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_get_x3f___boxed(lean_object* v_s_77_, lean_object* v_idx_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_get_x3f(v_s_77_, v_idx_78_);
lean_dec(v_idx_78_);
lean_dec_ref(v_s_77_);
return v_res_79_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go(lean_object* v_s_80_, lean_object* v_p_81_, lean_object* v_i_82_){
_start:
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = lean_array_get_size(v_s_80_);
v___x_84_ = lean_nat_dec_lt(v_i_82_, v___x_83_);
if (v___x_84_ == 0)
{
uint8_t v___x_85_; 
lean_dec(v_i_82_);
lean_dec_ref(v_p_81_);
v___x_85_ = 1;
return v___x_85_;
}
else
{
lean_object* v___x_86_; 
v___x_86_ = lean_array_fget_borrowed(v_s_80_, v_i_82_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_add(v_i_82_, v___x_87_);
lean_dec(v_i_82_);
v_i_82_ = v___x_88_;
goto _start;
}
else
{
lean_object* v_val_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v_val_90_ = lean_ctor_get(v___x_86_, 0);
v___x_91_ = lean_unsigned_to_nat(1u);
v___x_92_ = lean_nat_add(v_i_82_, v___x_91_);
lean_dec(v_i_82_);
lean_inc_ref(v_p_81_);
lean_inc(v_val_90_);
lean_inc(v___x_92_);
v___x_93_ = lean_apply_2(v_p_81_, v___x_92_, v_val_90_);
v___x_94_ = lean_unbox(v___x_93_);
if (v___x_94_ == 0)
{
uint8_t v___x_95_; 
lean_dec(v___x_92_);
lean_dec_ref(v_p_81_);
v___x_95_ = lean_unbox(v___x_93_);
return v___x_95_;
}
else
{
v_i_82_ = v___x_92_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go___boxed(lean_object* v_s_97_, lean_object* v_p_98_, lean_object* v_i_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go(v_s_97_, v_p_98_, v_i_99_);
lean_dec_ref(v_s_97_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go_match__1_splitter___redArg(lean_object* v_x_102_, lean_object* v_h__1_103_, lean_object* v_h__2_104_){
_start:
{
if (lean_obj_tag(v_x_102_) == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec(v_h__1_103_);
v___x_105_ = lean_box(0);
v___x_106_ = lean_apply_1(v_h__2_104_, v___x_105_);
return v___x_106_;
}
else
{
lean_object* v_val_107_; lean_object* v___x_108_; 
lean_dec(v_h__2_104_);
v_val_107_ = lean_ctor_get(v_x_102_, 0);
lean_inc(v_val_107_);
lean_dec_ref_known(v_x_102_, 1);
v___x_108_ = lean_apply_1(v_h__1_103_, v_val_107_);
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go_match__1_splitter(lean_object* v_motive_109_, lean_object* v_x_110_, lean_object* v_h__1_111_, lean_object* v_h__2_112_){
_start:
{
if (lean_obj_tag(v_x_110_) == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec(v_h__1_111_);
v___x_113_ = lean_box(0);
v___x_114_ = lean_apply_1(v_h__2_112_, v___x_113_);
return v___x_114_;
}
else
{
lean_object* v_val_115_; lean_object* v___x_116_; 
lean_dec(v_h__2_112_);
v_val_115_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_val_115_);
lean_dec_ref_known(v_x_110_, 1);
v___x_116_ = lean_apply_1(v_h__1_111_, v_val_115_);
return v___x_116_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_all(lean_object* v_s_117_, lean_object* v_p_118_){
_start:
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Basic_0__Std_Tactic_BVDecide_LRAT_Internal_State_all_go(v_s_117_, v_p_118_, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_all___boxed(lean_object* v_s_121_, lean_object* v_p_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_all(v_s_121_, v_p_122_);
lean_dec_ref(v_s_121_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
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
