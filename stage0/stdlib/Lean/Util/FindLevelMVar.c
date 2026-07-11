// Lean compiler output
// Module: Lean.Util.FindLevelMVar
// Imports: public import Lean.Expr
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
uint8_t l_Lean_Expr_hasLevelMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_mainLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_visitLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_visitLevel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_mainLevel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_main___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_main___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_FindLevelMVar_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_FindLevelMVar_main___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_FindLevelMVar_main___closed__0 = (const lean_object*)&l_Lean_FindLevelMVar_main___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_main(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_visit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_findLevelMVar_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_mainLevel(lean_object* v_p_1_, lean_object* v_x_2_, lean_object* v_a_3_){
_start:
{
lean_object* v_l_u2081_5_; lean_object* v_l_u2082_6_; lean_object* v___y_7_; 
switch(lean_obj_tag(v_x_2_))
{
case 1:
{
lean_object* v_a_10_; lean_object* v___x_11_; 
v_a_10_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_a_10_);
lean_dec_ref_known(v_x_2_, 1);
v___x_11_ = l_Lean_FindLevelMVar_visitLevel(v_p_1_, v_a_10_, v_a_3_);
return v___x_11_;
}
case 2:
{
lean_object* v_a_12_; lean_object* v_a_13_; 
v_a_12_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_a_12_);
v_a_13_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_a_13_);
lean_dec_ref_known(v_x_2_, 2);
v_l_u2081_5_ = v_a_12_;
v_l_u2082_6_ = v_a_13_;
v___y_7_ = v_a_3_;
goto v___jp_4_;
}
case 3:
{
lean_object* v_a_14_; lean_object* v_a_15_; 
v_a_14_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_a_14_);
v_a_15_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_a_15_);
lean_dec_ref_known(v_x_2_, 2);
v_l_u2081_5_ = v_a_14_;
v_l_u2082_6_ = v_a_15_;
v___y_7_ = v_a_3_;
goto v___jp_4_;
}
case 5:
{
lean_object* v_a_16_; lean_object* v___x_17_; uint8_t v___x_18_; 
v_a_16_ = lean_ctor_get(v_x_2_, 0);
lean_inc_n(v_a_16_, 2);
lean_dec_ref_known(v_x_2_, 1);
v___x_17_ = lean_apply_1(v_p_1_, v_a_16_);
v___x_18_ = lean_unbox(v___x_17_);
if (v___x_18_ == 0)
{
lean_dec(v_a_16_);
lean_inc(v_a_3_);
return v_a_3_;
}
else
{
lean_object* v___x_19_; 
v___x_19_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_19_, 0, v_a_16_);
return v___x_19_;
}
}
default: 
{
lean_dec(v_x_2_);
lean_dec_ref(v_p_1_);
lean_inc(v_a_3_);
return v_a_3_;
}
}
v___jp_4_:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
lean_inc_ref(v_p_1_);
v___x_8_ = l_Lean_FindLevelMVar_visitLevel(v_p_1_, v_l_u2082_6_, v___y_7_);
v___x_9_ = l_Lean_FindLevelMVar_visitLevel(v_p_1_, v_l_u2081_5_, v___x_8_);
lean_dec(v___x_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_visitLevel(lean_object* v_p_20_, lean_object* v_l_21_, lean_object* v_s_22_){
_start:
{
if (lean_obj_tag(v_s_22_) == 0)
{
uint8_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = l_Lean_Level_hasMVar(v_l_21_);
v___x_24_ = lean_bool_not(v___x_23_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_FindLevelMVar_mainLevel(v_p_20_, v_l_21_, v_s_22_);
return v___x_25_;
}
else
{
lean_dec(v_l_21_);
lean_dec_ref(v_p_20_);
return v_s_22_;
}
}
else
{
lean_dec(v_l_21_);
lean_dec_ref(v_p_20_);
lean_inc_ref(v_s_22_);
return v_s_22_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_visitLevel___boxed(lean_object* v_p_26_, lean_object* v_l_27_, lean_object* v_s_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_FindLevelMVar_visitLevel(v_p_26_, v_l_27_, v_s_28_);
lean_dec(v_s_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_mainLevel___boxed(lean_object* v_p_30_, lean_object* v_x_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_FindLevelMVar_mainLevel(v_p_30_, v_x_31_, v_a_32_);
lean_dec(v_a_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1___lam__0(lean_object* v_b_34_, lean_object* v_p_35_, lean_object* v___x_36_, lean_object* v___y_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_apply_1(v_b_34_, v___y_37_);
v___x_39_ = l_Lean_FindLevelMVar_visitLevel(v_p_35_, v___x_36_, v___x_38_);
lean_dec(v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1(lean_object* v_p_40_, lean_object* v_as_41_, size_t v_i_42_, size_t v_stop_43_, lean_object* v_b_44_, lean_object* v___y_45_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = lean_usize_dec_eq(v_i_42_, v_stop_43_);
if (v___x_46_ == 0)
{
size_t v___x_47_; size_t v___x_48_; lean_object* v___x_49_; lean_object* v___f_50_; 
v___x_47_ = ((size_t)1ULL);
v___x_48_ = lean_usize_sub(v_i_42_, v___x_47_);
v___x_49_ = lean_array_uget_borrowed(v_as_41_, v___x_48_);
lean_inc(v___x_49_);
lean_inc_ref(v_p_40_);
v___f_50_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1___lam__0), 4, 3);
lean_closure_set(v___f_50_, 0, v_b_44_);
lean_closure_set(v___f_50_, 1, v_p_40_);
lean_closure_set(v___f_50_, 2, v___x_49_);
v_i_42_ = v___x_48_;
v_b_44_ = v___f_50_;
goto _start;
}
else
{
lean_object* v___x_52_; 
lean_dec_ref(v_p_40_);
v___x_52_ = lean_apply_1(v_b_44_, v___y_45_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1___boxed(lean_object* v_p_53_, lean_object* v_as_54_, lean_object* v_i_55_, lean_object* v_stop_56_, lean_object* v_b_57_, lean_object* v___y_58_){
_start:
{
size_t v_i_boxed_59_; size_t v_stop_boxed_60_; lean_object* v_res_61_; 
v_i_boxed_59_ = lean_unbox_usize(v_i_55_);
lean_dec(v_i_55_);
v_stop_boxed_60_ = lean_unbox_usize(v_stop_56_);
lean_dec(v_stop_56_);
v_res_61_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1(v_p_53_, v_as_54_, v_i_boxed_59_, v_stop_boxed_60_, v_b_57_, v___y_58_);
lean_dec_ref(v_as_54_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1(lean_object* v_p_62_, lean_object* v_init_63_, lean_object* v_l_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_66_ = lean_array_mk(v_l_64_);
v___x_67_ = lean_array_get_size(v___x_66_);
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = lean_nat_dec_lt(v___x_68_, v___x_67_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; 
lean_dec_ref(v___x_66_);
lean_dec_ref(v_p_62_);
v___x_70_ = lean_apply_1(v_init_63_, v___y_65_);
return v___x_70_;
}
else
{
size_t v___x_71_; size_t v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_usize_of_nat(v___x_67_);
v___x_72_ = ((size_t)0ULL);
v___x_73_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1(v_p_62_, v___x_66_, v___x_71_, v___x_72_, v_init_63_, v___y_65_);
lean_dec_ref(v___x_66_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_main___lam__0(lean_object* v___y_74_){
_start:
{
lean_inc(v___y_74_);
return v___y_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_main___lam__0___boxed(lean_object* v___y_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_FindLevelMVar_main___lam__0(v___y_75_);
lean_dec(v___y_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_main(lean_object* v_p_78_, lean_object* v_x_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_d_82_; lean_object* v_b_83_; lean_object* v___y_84_; 
switch(lean_obj_tag(v_x_79_))
{
case 3:
{
lean_object* v_u_87_; lean_object* v___x_88_; 
v_u_87_ = lean_ctor_get(v_x_79_, 0);
lean_inc(v_u_87_);
lean_dec_ref_known(v_x_79_, 1);
v___x_88_ = l_Lean_FindLevelMVar_visitLevel(v_p_78_, v_u_87_, v_a_80_);
lean_dec(v_a_80_);
return v___x_88_;
}
case 4:
{
lean_object* v_us_89_; lean_object* v___f_90_; lean_object* v___x_91_; 
v_us_89_ = lean_ctor_get(v_x_79_, 1);
lean_inc(v_us_89_);
lean_dec_ref_known(v_x_79_, 2);
v___f_90_ = ((lean_object*)(l_Lean_FindLevelMVar_main___closed__0));
v___x_91_ = l_List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1(v_p_78_, v___f_90_, v_us_89_, v_a_80_);
return v___x_91_;
}
case 7:
{
lean_object* v_binderType_92_; lean_object* v_body_93_; 
v_binderType_92_ = lean_ctor_get(v_x_79_, 1);
lean_inc_ref(v_binderType_92_);
v_body_93_ = lean_ctor_get(v_x_79_, 2);
lean_inc_ref(v_body_93_);
lean_dec_ref_known(v_x_79_, 3);
v_d_82_ = v_binderType_92_;
v_b_83_ = v_body_93_;
v___y_84_ = v_a_80_;
goto v___jp_81_;
}
case 6:
{
lean_object* v_binderType_94_; lean_object* v_body_95_; 
v_binderType_94_ = lean_ctor_get(v_x_79_, 1);
lean_inc_ref(v_binderType_94_);
v_body_95_ = lean_ctor_get(v_x_79_, 2);
lean_inc_ref(v_body_95_);
lean_dec_ref_known(v_x_79_, 3);
v_d_82_ = v_binderType_94_;
v_b_83_ = v_body_95_;
v___y_84_ = v_a_80_;
goto v___jp_81_;
}
case 8:
{
lean_object* v_type_96_; lean_object* v_value_97_; lean_object* v_body_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v_type_96_ = lean_ctor_get(v_x_79_, 1);
lean_inc_ref(v_type_96_);
v_value_97_ = lean_ctor_get(v_x_79_, 2);
lean_inc_ref(v_value_97_);
v_body_98_ = lean_ctor_get(v_x_79_, 3);
lean_inc_ref(v_body_98_);
lean_dec_ref_known(v_x_79_, 4);
lean_inc_ref_n(v_p_78_, 2);
v___x_99_ = l_Lean_FindLevelMVar_visit(v_p_78_, v_type_96_, v_a_80_);
v___x_100_ = l_Lean_FindLevelMVar_visit(v_p_78_, v_value_97_, v___x_99_);
v___x_101_ = l_Lean_FindLevelMVar_visit(v_p_78_, v_body_98_, v___x_100_);
return v___x_101_;
}
case 5:
{
lean_object* v_fn_102_; lean_object* v_arg_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v_fn_102_ = lean_ctor_get(v_x_79_, 0);
lean_inc_ref(v_fn_102_);
v_arg_103_ = lean_ctor_get(v_x_79_, 1);
lean_inc_ref(v_arg_103_);
lean_dec_ref_known(v_x_79_, 2);
lean_inc_ref(v_p_78_);
v___x_104_ = l_Lean_FindLevelMVar_visit(v_p_78_, v_fn_102_, v_a_80_);
v___x_105_ = l_Lean_FindLevelMVar_visit(v_p_78_, v_arg_103_, v___x_104_);
return v___x_105_;
}
case 10:
{
lean_object* v_expr_106_; lean_object* v___x_107_; 
v_expr_106_ = lean_ctor_get(v_x_79_, 1);
lean_inc_ref(v_expr_106_);
lean_dec_ref_known(v_x_79_, 2);
v___x_107_ = l_Lean_FindLevelMVar_visit(v_p_78_, v_expr_106_, v_a_80_);
return v___x_107_;
}
case 11:
{
lean_object* v_struct_108_; lean_object* v___x_109_; 
v_struct_108_ = lean_ctor_get(v_x_79_, 2);
lean_inc_ref(v_struct_108_);
lean_dec_ref_known(v_x_79_, 3);
v___x_109_ = l_Lean_FindLevelMVar_visit(v_p_78_, v_struct_108_, v_a_80_);
return v___x_109_;
}
default: 
{
lean_dec_ref(v_x_79_);
lean_dec_ref(v_p_78_);
return v_a_80_;
}
}
v___jp_81_:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_inc_ref(v_p_78_);
v___x_85_ = l_Lean_FindLevelMVar_visit(v_p_78_, v_d_82_, v___y_84_);
v___x_86_ = l_Lean_FindLevelMVar_visit(v_p_78_, v_b_83_, v___x_85_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_visit(lean_object* v_p_110_, lean_object* v_e_111_, lean_object* v_s_112_){
_start:
{
if (lean_obj_tag(v_s_112_) == 0)
{
uint8_t v___x_113_; uint8_t v___x_114_; 
v___x_113_ = l_Lean_Expr_hasLevelMVar(v_e_111_);
v___x_114_ = lean_bool_not(v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_FindLevelMVar_main(v_p_110_, v_e_111_, v_s_112_);
return v___x_115_;
}
else
{
lean_dec_ref(v_e_111_);
lean_dec_ref(v_p_110_);
return v_s_112_;
}
}
else
{
lean_dec_ref(v_e_111_);
lean_dec_ref(v_p_110_);
return v_s_112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_findLevelMVar_x3f(lean_object* v_e_116_, lean_object* v_p_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_box(0);
v___x_119_ = l_Lean_FindLevelMVar_main(v_p_117_, v_e_116_, v___x_118_);
return v___x_119_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_FindLevelMVar(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_FindLevelMVar(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_FindLevelMVar(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_FindLevelMVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_FindLevelMVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_FindLevelMVar(builtin);
}
#ifdef __cplusplus
}
#endif
