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
lean_dec_ref(v_x_2_);
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
lean_dec_ref(v_x_2_);
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
lean_dec_ref(v_x_2_);
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
lean_dec_ref(v_x_2_);
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
uint8_t v___x_23_; 
v___x_23_ = l_Lean_Level_hasMVar(v_l_21_);
if (v___x_23_ == 0)
{
lean_dec(v_l_21_);
lean_dec_ref(v_p_20_);
return v_s_22_;
}
else
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_FindLevelMVar_mainLevel(v_p_20_, v_l_21_, v_s_22_);
return v___x_24_;
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
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_visitLevel___boxed(lean_object* v_p_25_, lean_object* v_l_26_, lean_object* v_s_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_FindLevelMVar_visitLevel(v_p_25_, v_l_26_, v_s_27_);
lean_dec(v_s_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_mainLevel___boxed(lean_object* v_p_29_, lean_object* v_x_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_FindLevelMVar_mainLevel(v_p_29_, v_x_30_, v_a_31_);
lean_dec(v_a_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1___lam__0(lean_object* v_b_33_, lean_object* v_p_34_, lean_object* v___x_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_apply_1(v_b_33_, v___y_36_);
v___x_38_ = l_Lean_FindLevelMVar_visitLevel(v_p_34_, v___x_35_, v___x_37_);
lean_dec(v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1(lean_object* v_p_39_, lean_object* v_as_40_, size_t v_i_41_, size_t v_stop_42_, lean_object* v_b_43_, lean_object* v___y_44_){
_start:
{
uint8_t v___x_45_; 
v___x_45_ = lean_usize_dec_eq(v_i_41_, v_stop_42_);
if (v___x_45_ == 0)
{
size_t v___x_46_; size_t v___x_47_; lean_object* v___x_48_; lean_object* v___f_49_; 
v___x_46_ = ((size_t)1ULL);
v___x_47_ = lean_usize_sub(v_i_41_, v___x_46_);
v___x_48_ = lean_array_uget_borrowed(v_as_40_, v___x_47_);
lean_inc(v___x_48_);
lean_inc_ref(v_p_39_);
v___f_49_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1___lam__0), 4, 3);
lean_closure_set(v___f_49_, 0, v_b_43_);
lean_closure_set(v___f_49_, 1, v_p_39_);
lean_closure_set(v___f_49_, 2, v___x_48_);
v_i_41_ = v___x_47_;
v_b_43_ = v___f_49_;
goto _start;
}
else
{
lean_object* v___x_51_; 
lean_dec_ref(v_p_39_);
v___x_51_ = lean_apply_1(v_b_43_, v___y_44_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1___boxed(lean_object* v_p_52_, lean_object* v_as_53_, lean_object* v_i_54_, lean_object* v_stop_55_, lean_object* v_b_56_, lean_object* v___y_57_){
_start:
{
size_t v_i_boxed_58_; size_t v_stop_boxed_59_; lean_object* v_res_60_; 
v_i_boxed_58_ = lean_unbox_usize(v_i_54_);
lean_dec(v_i_54_);
v_stop_boxed_59_ = lean_unbox_usize(v_stop_55_);
lean_dec(v_stop_55_);
v_res_60_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1(v_p_52_, v_as_53_, v_i_boxed_58_, v_stop_boxed_59_, v_b_56_, v___y_57_);
lean_dec_ref(v_as_53_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1(lean_object* v_p_61_, lean_object* v_init_62_, lean_object* v_l_63_, lean_object* v___y_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_65_ = lean_array_mk(v_l_63_);
v___x_66_ = lean_array_get_size(v___x_65_);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_nat_dec_lt(v___x_67_, v___x_66_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; 
lean_dec_ref(v___x_65_);
lean_dec_ref(v_p_61_);
v___x_69_ = lean_apply_1(v_init_62_, v___y_64_);
return v___x_69_;
}
else
{
size_t v___x_70_; size_t v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_usize_of_nat(v___x_66_);
v___x_71_ = ((size_t)0ULL);
v___x_72_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1(v_p_61_, v___x_65_, v___x_70_, v___x_71_, v_init_62_, v___y_64_);
lean_dec_ref(v___x_65_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_main___lam__0(lean_object* v___y_73_){
_start:
{
lean_inc(v___y_73_);
return v___y_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_main___lam__0___boxed(lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_FindLevelMVar_main___lam__0(v___y_74_);
lean_dec(v___y_74_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_main(lean_object* v_p_77_, lean_object* v_x_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_d_81_; lean_object* v_b_82_; lean_object* v___y_83_; 
switch(lean_obj_tag(v_x_78_))
{
case 3:
{
lean_object* v_u_86_; lean_object* v___x_87_; 
v_u_86_ = lean_ctor_get(v_x_78_, 0);
lean_inc(v_u_86_);
lean_dec_ref(v_x_78_);
v___x_87_ = l_Lean_FindLevelMVar_visitLevel(v_p_77_, v_u_86_, v_a_79_);
lean_dec(v_a_79_);
return v___x_87_;
}
case 4:
{
lean_object* v_us_88_; lean_object* v___f_89_; lean_object* v___x_90_; 
v_us_88_ = lean_ctor_get(v_x_78_, 1);
lean_inc(v_us_88_);
lean_dec_ref(v_x_78_);
v___f_89_ = ((lean_object*)(l_Lean_FindLevelMVar_main___closed__0));
v___x_90_ = l_List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1(v_p_77_, v___f_89_, v_us_88_, v_a_79_);
return v___x_90_;
}
case 7:
{
lean_object* v_binderType_91_; lean_object* v_body_92_; 
v_binderType_91_ = lean_ctor_get(v_x_78_, 1);
lean_inc_ref(v_binderType_91_);
v_body_92_ = lean_ctor_get(v_x_78_, 2);
lean_inc_ref(v_body_92_);
lean_dec_ref(v_x_78_);
v_d_81_ = v_binderType_91_;
v_b_82_ = v_body_92_;
v___y_83_ = v_a_79_;
goto v___jp_80_;
}
case 6:
{
lean_object* v_binderType_93_; lean_object* v_body_94_; 
v_binderType_93_ = lean_ctor_get(v_x_78_, 1);
lean_inc_ref(v_binderType_93_);
v_body_94_ = lean_ctor_get(v_x_78_, 2);
lean_inc_ref(v_body_94_);
lean_dec_ref(v_x_78_);
v_d_81_ = v_binderType_93_;
v_b_82_ = v_body_94_;
v___y_83_ = v_a_79_;
goto v___jp_80_;
}
case 8:
{
lean_object* v_type_95_; lean_object* v_value_96_; lean_object* v_body_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_type_95_ = lean_ctor_get(v_x_78_, 1);
lean_inc_ref(v_type_95_);
v_value_96_ = lean_ctor_get(v_x_78_, 2);
lean_inc_ref(v_value_96_);
v_body_97_ = lean_ctor_get(v_x_78_, 3);
lean_inc_ref(v_body_97_);
lean_dec_ref(v_x_78_);
lean_inc_ref_n(v_p_77_, 2);
v___x_98_ = l_Lean_FindLevelMVar_visit(v_p_77_, v_type_95_, v_a_79_);
v___x_99_ = l_Lean_FindLevelMVar_visit(v_p_77_, v_value_96_, v___x_98_);
v___x_100_ = l_Lean_FindLevelMVar_visit(v_p_77_, v_body_97_, v___x_99_);
return v___x_100_;
}
case 5:
{
lean_object* v_fn_101_; lean_object* v_arg_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_fn_101_ = lean_ctor_get(v_x_78_, 0);
lean_inc_ref(v_fn_101_);
v_arg_102_ = lean_ctor_get(v_x_78_, 1);
lean_inc_ref(v_arg_102_);
lean_dec_ref(v_x_78_);
lean_inc_ref(v_p_77_);
v___x_103_ = l_Lean_FindLevelMVar_visit(v_p_77_, v_fn_101_, v_a_79_);
v___x_104_ = l_Lean_FindLevelMVar_visit(v_p_77_, v_arg_102_, v___x_103_);
return v___x_104_;
}
case 10:
{
lean_object* v_expr_105_; lean_object* v___x_106_; 
v_expr_105_ = lean_ctor_get(v_x_78_, 1);
lean_inc_ref(v_expr_105_);
lean_dec_ref(v_x_78_);
v___x_106_ = l_Lean_FindLevelMVar_visit(v_p_77_, v_expr_105_, v_a_79_);
return v___x_106_;
}
case 11:
{
lean_object* v_struct_107_; lean_object* v___x_108_; 
v_struct_107_ = lean_ctor_get(v_x_78_, 2);
lean_inc_ref(v_struct_107_);
lean_dec_ref(v_x_78_);
v___x_108_ = l_Lean_FindLevelMVar_visit(v_p_77_, v_struct_107_, v_a_79_);
return v___x_108_;
}
default: 
{
lean_dec_ref(v_x_78_);
lean_dec_ref(v_p_77_);
return v_a_79_;
}
}
v___jp_80_:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_inc_ref(v_p_77_);
v___x_84_ = l_Lean_FindLevelMVar_visit(v_p_77_, v_d_81_, v___y_83_);
v___x_85_ = l_Lean_FindLevelMVar_visit(v_p_77_, v_b_82_, v___x_84_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FindLevelMVar_visit(lean_object* v_p_109_, lean_object* v_e_110_, lean_object* v_s_111_){
_start:
{
if (lean_obj_tag(v_s_111_) == 0)
{
uint8_t v___x_112_; 
v___x_112_ = l_Lean_Expr_hasLevelMVar(v_e_110_);
if (v___x_112_ == 0)
{
lean_dec_ref(v_e_110_);
lean_dec_ref(v_p_109_);
return v_s_111_;
}
else
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_FindLevelMVar_main(v_p_109_, v_e_110_, v_s_111_);
return v___x_113_;
}
}
else
{
lean_dec_ref(v_e_110_);
lean_dec_ref(v_p_109_);
return v_s_111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_findLevelMVar_x3f(lean_object* v_e_114_, lean_object* v_p_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_box(0);
v___x_117_ = l_Lean_FindLevelMVar_main(v_p_115_, v_e_114_, v___x_116_);
return v___x_117_;
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
