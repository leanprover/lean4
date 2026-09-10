// Lean compiler output
// Module: Std.Sat.CNF.Sat
// Imports: public import Std.Sat.CNF.Basic import Init.ByCases
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
lean_object* l_Std_Sat_CNF_Clause_literals___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
lean_dec_ref(v_a_1_);
v___x_3_ = 0;
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v_fst_6_; lean_object* v_snd_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v_head_4_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_head_4_);
v_tail_5_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_tail_5_);
lean_dec_ref_known(v_x_2_, 2);
v_fst_6_ = lean_ctor_get(v_head_4_, 0);
lean_inc(v_fst_6_);
v_snd_7_ = lean_ctor_get(v_head_4_, 1);
lean_inc(v_snd_7_);
lean_dec(v_head_4_);
lean_inc_ref(v_a_1_);
v___x_8_ = lean_apply_1(v_a_1_, v_fst_6_);
v___x_9_ = lean_unbox(v_snd_7_);
lean_dec(v_snd_7_);
if (v___x_9_ == 0)
{
uint8_t v___x_10_; 
v___x_10_ = lean_unbox(v___x_8_);
if (v___x_10_ == 0)
{
uint8_t v___x_11_; 
lean_dec(v_tail_5_);
lean_dec_ref(v_a_1_);
v___x_11_ = 1;
return v___x_11_;
}
else
{
v_x_2_ = v_tail_5_;
goto _start;
}
}
else
{
uint8_t v___x_13_; 
v___x_13_ = lean_unbox(v___x_8_);
if (v___x_13_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
uint8_t v___x_15_; 
lean_dec(v_tail_5_);
lean_dec_ref(v_a_1_);
v___x_15_ = lean_unbox(v___x_8_);
return v___x_15_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg___boxed(lean_object* v_a_16_, lean_object* v_x_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(v_a_16_, v_x_17_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval___redArg(lean_object* v_a_20_, lean_object* v_c_21_){
_start:
{
lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_22_ = l_Std_Sat_CNF_Clause_literals___redArg(v_c_21_);
v___x_23_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(v_a_20_, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___redArg___boxed(lean_object* v_a_24_, lean_object* v_c_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_Std_Sat_CNF_Clause_eval___redArg(v_a_24_, v_c_25_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval(lean_object* v_00_u03b1_28_, lean_object* v_a_29_, lean_object* v_c_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = l_Std_Sat_CNF_Clause_eval___redArg(v_a_29_, v_c_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___boxed(lean_object* v_00_u03b1_32_, lean_object* v_a_33_, lean_object* v_c_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Std_Sat_CNF_Clause_eval(v_00_u03b1_32_, v_a_33_, v_c_34_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0(lean_object* v_00_u03b1_37_, lean_object* v_a_38_, lean_object* v_x_39_){
_start:
{
uint8_t v___x_40_; 
v___x_40_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___redArg(v_a_38_, v_x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0___boxed(lean_object* v_00_u03b1_41_, lean_object* v_a_42_, lean_object* v_x_43_){
_start:
{
uint8_t v_res_44_; lean_object* v_r_45_; 
v_res_44_ = l_List_any___at___00Std_Sat_CNF_Clause_eval_spec__0(v_00_u03b1_41_, v_a_42_, v_x_43_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(lean_object* v_a_46_, lean_object* v_as_47_, size_t v_i_48_, size_t v_stop_49_){
_start:
{
uint8_t v___x_50_; 
v___x_50_ = lean_usize_dec_eq(v_i_48_, v_stop_49_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_51_ = lean_array_uget_borrowed(v_as_47_, v_i_48_);
lean_inc(v___x_51_);
lean_inc_ref(v_a_46_);
v___x_52_ = l_Std_Sat_CNF_Clause_eval___redArg(v_a_46_, v___x_51_);
if (v___x_52_ == 0)
{
uint8_t v___x_53_; 
lean_dec_ref(v_a_46_);
v___x_53_ = 1;
return v___x_53_;
}
else
{
size_t v___x_54_; size_t v___x_55_; 
v___x_54_ = ((size_t)1ULL);
v___x_55_ = lean_usize_add(v_i_48_, v___x_54_);
v_i_48_ = v___x_55_;
goto _start;
}
}
else
{
uint8_t v___x_57_; 
lean_dec_ref(v_a_46_);
v___x_57_ = 0;
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg___boxed(lean_object* v_a_58_, lean_object* v_as_59_, lean_object* v_i_60_, lean_object* v_stop_61_){
_start:
{
size_t v_i_boxed_62_; size_t v_stop_boxed_63_; uint8_t v_res_64_; lean_object* v_r_65_; 
v_i_boxed_62_ = lean_unbox_usize(v_i_60_);
lean_dec(v_i_60_);
v_stop_boxed_63_ = lean_unbox_usize(v_stop_61_);
lean_dec(v_stop_61_);
v_res_64_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(v_a_58_, v_as_59_, v_i_boxed_62_, v_stop_boxed_63_);
lean_dec_ref(v_as_59_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval___redArg(lean_object* v_a_66_, lean_object* v_f_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = lean_array_get_size(v_f_67_);
v___x_70_ = lean_nat_dec_lt(v___x_68_, v___x_69_);
if (v___x_70_ == 0)
{
uint8_t v___x_71_; 
lean_dec_ref(v_a_66_);
v___x_71_ = 1;
return v___x_71_;
}
else
{
if (v___x_70_ == 0)
{
lean_dec_ref(v_a_66_);
return v___x_70_;
}
else
{
size_t v___x_72_; size_t v___x_73_; uint8_t v___x_74_; 
v___x_72_ = ((size_t)0ULL);
v___x_73_ = lean_usize_of_nat(v___x_69_);
v___x_74_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(v_a_66_, v_f_67_, v___x_72_, v___x_73_);
if (v___x_74_ == 0)
{
return v___x_70_;
}
else
{
uint8_t v___x_75_; 
v___x_75_ = 0;
return v___x_75_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___redArg___boxed(lean_object* v_a_76_, lean_object* v_f_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Std_Sat_CNF_eval___redArg(v_a_76_, v_f_77_);
lean_dec_ref(v_f_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval(lean_object* v_00_u03b1_80_, lean_object* v_a_81_, lean_object* v_f_82_){
_start:
{
uint8_t v___x_83_; 
v___x_83_ = l_Std_Sat_CNF_eval___redArg(v_a_81_, v_f_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___boxed(lean_object* v_00_u03b1_84_, lean_object* v_a_85_, lean_object* v_f_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_Std_Sat_CNF_eval(v_00_u03b1_84_, v_a_85_, v_f_86_);
lean_dec_ref(v_f_86_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0(lean_object* v_00_u03b1_89_, lean_object* v_a_90_, lean_object* v_as_91_, size_t v_i_92_, size_t v_stop_93_){
_start:
{
uint8_t v___x_94_; 
v___x_94_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___redArg(v_a_90_, v_as_91_, v_i_92_, v_stop_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0___boxed(lean_object* v_00_u03b1_95_, lean_object* v_a_96_, lean_object* v_as_97_, lean_object* v_i_98_, lean_object* v_stop_99_){
_start:
{
size_t v_i_boxed_100_; size_t v_stop_boxed_101_; uint8_t v_res_102_; lean_object* v_r_103_; 
v_i_boxed_100_ = lean_unbox_usize(v_i_98_);
lean_dec(v_i_98_);
v_stop_boxed_101_ = lean_unbox_usize(v_stop_99_);
lean_dec(v_stop_99_);
v_res_102_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Sat_CNF_eval_spec__0(v_00_u03b1_95_, v_a_96_, v_as_97_, v_i_boxed_100_, v_stop_boxed_101_);
lean_dec_ref(v_as_97_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
lean_object* runtime_initialize_Std_Sat_CNF_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_CNF_Sat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_CNF_Sat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_CNF_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_Sat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Sat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_CNF_Sat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_CNF_Sat(builtin);
}
#ifdef __cplusplus
}
#endif
