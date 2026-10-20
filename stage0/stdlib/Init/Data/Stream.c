// Lean compiler output
// Module: Init.Data.Stream
// Imports: public import Init.Data.Range public import Init.Data.Array.Subarray import Init.Data.Slice.Array.Basic
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Stream_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Stream_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInOfMonadOfStream___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInOfMonadOfStream___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInOfMonadOfStream(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamList___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamList___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_instToStreamList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToStreamList___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instToStreamList___redArg___closed__0 = (const lean_object*)&l_Std_instToStreamList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instToStreamList___redArg();
LEAN_EXPORT lean_object* l_Std_instToStreamList___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamList(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray___redArg___lam__0(lean_object*);
static const lean_closure_object l_Std_instToStreamArraySubarray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToStreamArraySubarray___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instToStreamArraySubarray___redArg___closed__0 = (const lean_object*)&l_Std_instToStreamArraySubarray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray___redArg();
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_instToStreamSubarray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToStreamSubarray___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instToStreamSubarray___redArg___closed__0 = (const lean_object*)&l_Std_instToStreamSubarray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___redArg();
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamStringRaw___lam__0(lean_object*);
static const lean_closure_object l_Std_instToStreamStringRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToStreamStringRaw___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instToStreamStringRaw___closed__0 = (const lean_object*)&l_Std_instToStreamStringRaw___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instToStreamStringRaw = (const lean_object*)&l_Std_instToStreamStringRaw___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instToStreamRange___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamRange___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_instToStreamRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToStreamRange___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instToStreamRange___closed__0 = (const lean_object*)&l_Std_instToStreamRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instToStreamRange = (const lean_object*)&l_Std_instToStreamRange___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instStreamProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instStreamProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instStreamProd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instStreamList___redArg___lam__0(lean_object*);
static const lean_closure_object l_Std_instStreamList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instStreamList___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instStreamList___redArg___closed__0 = (const lean_object*)&l_Std_instStreamList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instStreamList___redArg();
LEAN_EXPORT lean_object* l_Std_instStreamList___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_instStreamList(lean_object*);
LEAN_EXPORT lean_object* l_Std_instStreamSubarray___redArg___lam__0(lean_object*);
static const lean_closure_object l_Std_instStreamSubarray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instStreamSubarray___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instStreamSubarray___redArg___closed__0 = (const lean_object*)&l_Std_instStreamSubarray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instStreamSubarray___redArg();
LEAN_EXPORT lean_object* l_Std_instStreamSubarray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_instStreamSubarray(lean_object*);
LEAN_EXPORT lean_object* l_Std_instStreamRangeNat___lam__0(lean_object*);
static const lean_closure_object l_Std_instStreamRangeNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instStreamRangeNat___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instStreamRangeNat___closed__0 = (const lean_object*)&l_Std_instStreamRangeNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instStreamRangeNat = (const lean_object*)&l_Std_instStreamRangeNat___closed__0_value;
LEAN_EXPORT lean_object* l_Stream_next_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stream_next_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ToStream_toStream___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ToStream_toStream(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_f_3_, lean_object* v_s_4_, lean_object* v_b_5_){
_start:
{
lean_object* v_toApplicative_6_; lean_object* v_toBind_7_; lean_object* v_toPure_8_; lean_object* v___x_9_; 
v_toApplicative_6_ = lean_ctor_get(v_inst_2_, 0);
v_toBind_7_ = lean_ctor_get(v_inst_2_, 1);
lean_inc(v_toBind_7_);
v_toPure_8_ = lean_ctor_get(v_toApplicative_6_, 1);
lean_inc(v_toPure_8_);
lean_inc_ref(v_inst_1_);
v___x_9_ = lean_apply_1(v_inst_1_, v_s_4_);
if (lean_obj_tag(v___x_9_) == 0)
{
lean_object* v___x_10_; 
lean_dec(v_toBind_7_);
lean_dec(v_f_3_);
lean_dec_ref(v_inst_2_);
lean_dec_ref(v_inst_1_);
v___x_10_ = lean_apply_2(v_toPure_8_, lean_box(0), v_b_5_);
return v___x_10_;
}
else
{
lean_object* v_val_11_; lean_object* v_fst_12_; lean_object* v_snd_13_; lean_object* v___f_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_val_11_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_val_11_);
lean_dec_ref_known(v___x_9_, 1);
v_fst_12_ = lean_ctor_get(v_val_11_, 0);
lean_inc(v_fst_12_);
v_snd_13_ = lean_ctor_get(v_val_11_, 1);
lean_inc(v_snd_13_);
lean_dec(v_val_11_);
lean_inc(v_f_3_);
v___f_14_ = lean_alloc_closure((void*)(l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg___lam__0), 6, 5);
lean_closure_set(v___f_14_, 0, v_toPure_8_);
lean_closure_set(v___f_14_, 1, v_inst_1_);
lean_closure_set(v___f_14_, 2, v_inst_2_);
lean_closure_set(v___f_14_, 3, v_f_3_);
lean_closure_set(v___f_14_, 4, v_snd_13_);
v___x_15_ = lean_apply_2(v_f_3_, v_fst_12_, v_b_5_);
v___x_16_ = lean_apply_4(v_toBind_7_, lean_box(0), lean_box(0), v___x_15_, v___f_14_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg___lam__0(lean_object* v_toPure_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_f_20_, lean_object* v_snd_21_, lean_object* v_____do__lift_22_){
_start:
{
if (lean_obj_tag(v_____do__lift_22_) == 0)
{
lean_object* v_a_23_; lean_object* v___x_24_; 
lean_dec(v_snd_21_);
lean_dec(v_f_20_);
lean_dec_ref(v_inst_19_);
lean_dec_ref(v_inst_18_);
v_a_23_ = lean_ctor_get(v_____do__lift_22_, 0);
lean_inc(v_a_23_);
lean_dec_ref_known(v_____do__lift_22_, 1);
v___x_24_ = lean_apply_2(v_toPure_17_, lean_box(0), v_a_23_);
return v___x_24_;
}
else
{
lean_object* v_a_25_; lean_object* v___x_26_; 
lean_dec(v_toPure_17_);
v_a_25_ = lean_ctor_get(v_____do__lift_22_, 0);
lean_inc(v_a_25_);
lean_dec_ref_known(v_____do__lift_22_, 1);
v___x_26_ = l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(v_inst_18_, v_inst_19_, v_f_20_, v_snd_21_, v_a_25_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit(lean_object* v_00_u03c1_27_, lean_object* v_00_u03b1_28_, lean_object* v_m_29_, lean_object* v_00_u03b2_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_f_33_, lean_object* v_s_34_, lean_object* v_b_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(v_inst_31_, v_inst_32_, v_f_33_, v_s_34_, v_b_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Stream_forIn___redArg(lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_s_39_, lean_object* v_b_40_, lean_object* v_f_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(v_inst_37_, v_inst_38_, v_f_41_, v_s_39_, v_b_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Stream_forIn(lean_object* v_00_u03c1_43_, lean_object* v_00_u03b1_44_, lean_object* v_m_45_, lean_object* v_00_u03b2_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_s_49_, lean_object* v_b_50_, lean_object* v_f_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(v_inst_47_, v_inst_48_, v_f_51_, v_s_49_, v_b_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInOfMonadOfStream___redArg___lam__0(lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_00_u03b2_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(v_inst_53_, v_inst_54_, v___y_58_, v___y_56_, v___y_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInOfMonadOfStream___redArg(lean_object* v_inst_60_, lean_object* v_inst_61_){
_start:
{
lean_object* v___f_62_; 
v___f_62_ = lean_alloc_closure((void*)(l_Std_instForInOfMonadOfStream___redArg___lam__0), 6, 2);
lean_closure_set(v___f_62_, 0, v_inst_61_);
lean_closure_set(v___f_62_, 1, v_inst_60_);
return v___f_62_;
}
}
LEAN_EXPORT lean_object* l_Std_instForInOfMonadOfStream(lean_object* v_m_63_, lean_object* v_00_u03c1_64_, lean_object* v_00_u03b1_65_, lean_object* v_inst_66_, lean_object* v_inst_67_){
_start:
{
lean_object* v___f_68_; 
v___f_68_ = lean_alloc_closure((void*)(l_Std_instForInOfMonadOfStream___redArg___lam__0), 6, 2);
lean_closure_set(v___f_68_, 0, v_inst_67_);
lean_closure_set(v___f_68_, 1, v_inst_66_);
return v___f_68_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamList___redArg___lam__0(lean_object* v_c_69_){
_start:
{
lean_inc(v_c_69_);
return v_c_69_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamList___redArg___lam__0___boxed(lean_object* v_c_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Std_instToStreamList___redArg___lam__0(v_c_70_);
lean_dec(v_c_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamList___redArg(){
_start:
{
lean_object* v___f_74_; 
v___f_74_ = ((lean_object*)(l_Std_instToStreamList___redArg___closed__0));
return v___f_74_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamList___redArg___boxed(lean_object* v___dummy_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Std_instToStreamList___redArg();
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamList(lean_object* v_00_u03b1_77_){
_start:
{
lean_object* v___f_78_; 
v___f_78_ = ((lean_object*)(l_Std_instToStreamList___redArg___closed__0));
return v___f_78_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray___redArg___lam__0(lean_object* v_a_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_array_get_size(v_a_79_);
v___x_82_ = l_Array_toSubarray___redArg(v_a_79_, v___x_80_, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray___redArg(){
_start:
{
lean_object* v___f_85_; 
v___f_85_ = ((lean_object*)(l_Std_instToStreamArraySubarray___redArg___closed__0));
return v___f_85_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray___redArg___boxed(lean_object* v___dummy_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Std_instToStreamArraySubarray___redArg();
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray(lean_object* v_00_u03b1_88_){
_start:
{
lean_object* v___f_89_; 
v___f_89_ = ((lean_object*)(l_Std_instToStreamArraySubarray___redArg___closed__0));
return v___f_89_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___redArg___lam__0(lean_object* v_a_90_){
_start:
{
lean_inc_ref(v_a_90_);
return v_a_90_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___redArg___lam__0___boxed(lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Std_instToStreamSubarray___redArg___lam__0(v_a_91_);
lean_dec_ref(v_a_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___redArg(){
_start:
{
lean_object* v___f_95_; 
v___f_95_ = ((lean_object*)(l_Std_instToStreamSubarray___redArg___closed__0));
return v___f_95_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___redArg___boxed(lean_object* v___dummy_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Std_instToStreamSubarray___redArg();
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray(lean_object* v_00_u03b1_98_){
_start:
{
lean_object* v___f_99_; 
v___f_99_ = ((lean_object*)(l_Std_instToStreamSubarray___redArg___closed__0));
return v___f_99_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamStringRaw___lam__0(lean_object* v_s_100_){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = lean_string_utf8_byte_size(v_s_100_);
v___x_103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_103_, 0, v_s_100_);
lean_ctor_set(v___x_103_, 1, v___x_101_);
lean_ctor_set(v___x_103_, 2, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamRange___lam__0(lean_object* v_r_106_){
_start:
{
lean_inc_ref(v_r_106_);
return v_r_106_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamRange___lam__0___boxed(lean_object* v_r_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_instToStreamRange___lam__0(v_r_107_);
lean_dec_ref(v_r_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamProd___redArg___lam__0(lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_x_113_){
_start:
{
lean_object* v_fst_114_; lean_object* v_snd_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_153_; 
v_fst_114_ = lean_ctor_get(v_x_113_, 0);
v_snd_115_ = lean_ctor_get(v_x_113_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v_x_113_);
if (v_isSharedCheck_153_ == 0)
{
v___x_117_ = v_x_113_;
v_isShared_118_ = v_isSharedCheck_153_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_snd_115_);
lean_inc(v_fst_114_);
lean_dec(v_x_113_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_153_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; 
v___x_119_ = lean_apply_1(v_inst_111_, v_fst_114_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v___x_120_; 
lean_del_object(v___x_117_);
lean_dec(v_snd_115_);
lean_dec_ref(v_inst_112_);
v___x_120_ = lean_box(0);
return v___x_120_;
}
else
{
lean_object* v_val_121_; lean_object* v_fst_122_; lean_object* v_snd_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_152_; 
v_val_121_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_val_121_);
lean_dec_ref_known(v___x_119_, 1);
v_fst_122_ = lean_ctor_get(v_val_121_, 0);
v_snd_123_ = lean_ctor_get(v_val_121_, 1);
v_isSharedCheck_152_ = !lean_is_exclusive(v_val_121_);
if (v_isSharedCheck_152_ == 0)
{
v___x_125_ = v_val_121_;
v_isShared_126_ = v_isSharedCheck_152_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_snd_123_);
lean_inc(v_fst_122_);
lean_dec(v_val_121_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_152_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; 
v___x_127_ = lean_apply_1(v_inst_112_, v_snd_115_);
if (lean_obj_tag(v___x_127_) == 0)
{
lean_object* v___x_128_; 
lean_del_object(v___x_125_);
lean_dec(v_snd_123_);
lean_dec(v_fst_122_);
lean_del_object(v___x_117_);
v___x_128_ = lean_box(0);
return v___x_128_;
}
else
{
lean_object* v_val_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_151_; 
v_val_129_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_151_ == 0)
{
v___x_131_ = v___x_127_;
v_isShared_132_ = v_isSharedCheck_151_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_val_129_);
lean_dec(v___x_127_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_151_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v_fst_133_; lean_object* v_snd_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_150_; 
v_fst_133_ = lean_ctor_get(v_val_129_, 0);
v_snd_134_ = lean_ctor_get(v_val_129_, 1);
v_isSharedCheck_150_ = !lean_is_exclusive(v_val_129_);
if (v_isSharedCheck_150_ == 0)
{
v___x_136_ = v_val_129_;
v_isShared_137_ = v_isSharedCheck_150_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_snd_134_);
lean_inc(v_fst_133_);
lean_dec(v_val_129_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_150_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v_fst_133_);
lean_ctor_set(v___x_136_, 0, v_fst_122_);
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_fst_122_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_fst_133_);
v___x_139_ = v_reuseFailAlloc_149_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_141_; 
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v_snd_134_);
lean_ctor_set(v___x_125_, 0, v_snd_123_);
v___x_141_ = v___x_125_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_snd_123_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_snd_134_);
v___x_141_ = v_reuseFailAlloc_148_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_143_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v___x_141_);
lean_ctor_set(v___x_117_, 0, v___x_139_);
v___x_143_ = v___x_117_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v___x_141_);
v___x_143_ = v_reuseFailAlloc_147_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_145_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 0, v___x_143_);
v___x_145_ = v___x_131_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instStreamProd___redArg(lean_object* v_inst_154_, lean_object* v_inst_155_){
_start:
{
lean_object* v___f_156_; 
v___f_156_ = lean_alloc_closure((void*)(l_Std_instStreamProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_156_, 0, v_inst_154_);
lean_closure_set(v___f_156_, 1, v_inst_155_);
return v___f_156_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamProd(lean_object* v_00_u03c1_157_, lean_object* v_00_u03b1_158_, lean_object* v_00_u03b3_159_, lean_object* v_00_u03b2_160_, lean_object* v_inst_161_, lean_object* v_inst_162_){
_start:
{
lean_object* v___f_163_; 
v___f_163_ = lean_alloc_closure((void*)(l_Std_instStreamProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_163_, 0, v_inst_161_);
lean_closure_set(v___f_163_, 1, v_inst_162_);
return v___f_163_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamList___redArg___lam__0(lean_object* v_x_164_){
_start:
{
if (lean_obj_tag(v_x_164_) == 0)
{
lean_object* v___x_165_; 
v___x_165_ = lean_box(0);
return v___x_165_;
}
else
{
lean_object* v_head_166_; lean_object* v_tail_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_175_; 
v_head_166_ = lean_ctor_get(v_x_164_, 0);
v_tail_167_ = lean_ctor_get(v_x_164_, 1);
v_isSharedCheck_175_ = !lean_is_exclusive(v_x_164_);
if (v_isSharedCheck_175_ == 0)
{
v___x_169_ = v_x_164_;
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_tail_167_);
lean_inc(v_head_166_);
lean_dec(v_x_164_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
lean_ctor_set_tag(v___x_169_, 0);
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_head_166_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_tail_167_);
v___x_172_ = v_reuseFailAlloc_174_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_173_; 
v___x_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
return v___x_173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instStreamList___redArg(){
_start:
{
lean_object* v___f_178_; 
v___f_178_ = ((lean_object*)(l_Std_instStreamList___redArg___closed__0));
return v___f_178_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamList___redArg___boxed(lean_object* v___dummy_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_instStreamList___redArg();
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamList(lean_object* v_00_u03b1_181_){
_start:
{
lean_object* v___f_182_; 
v___f_182_ = ((lean_object*)(l_Std_instStreamList___redArg___closed__0));
return v___f_182_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamSubarray___redArg___lam__0(lean_object* v_s_183_){
_start:
{
lean_object* v_array_184_; lean_object* v_start_185_; lean_object* v_stop_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_200_; 
v_array_184_ = lean_ctor_get(v_s_183_, 0);
v_start_185_ = lean_ctor_get(v_s_183_, 1);
v_stop_186_ = lean_ctor_get(v_s_183_, 2);
v_isSharedCheck_200_ = !lean_is_exclusive(v_s_183_);
if (v_isSharedCheck_200_ == 0)
{
v___x_188_ = v_s_183_;
v_isShared_189_ = v_isSharedCheck_200_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_stop_186_);
lean_inc(v_start_185_);
lean_inc(v_array_184_);
lean_dec(v_s_183_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_200_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
uint8_t v___x_190_; 
v___x_190_ = lean_nat_dec_lt(v_start_185_, v_stop_186_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
lean_del_object(v___x_188_);
lean_dec(v_stop_186_);
lean_dec(v_start_185_);
lean_dec_ref(v_array_184_);
v___x_191_ = lean_box(0);
return v___x_191_;
}
else
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_192_ = lean_array_fget(v_array_184_, v_start_185_);
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = lean_nat_add(v_start_185_, v___x_193_);
lean_dec(v_start_185_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 1, v___x_194_);
v___x_196_ = v___x_188_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_array_184_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v_stop_186_);
v___x_196_ = v_reuseFailAlloc_199_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_192_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instStreamSubarray___redArg(){
_start:
{
lean_object* v___f_203_; 
v___f_203_ = ((lean_object*)(l_Std_instStreamSubarray___redArg___closed__0));
return v___f_203_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamSubarray___redArg___boxed(lean_object* v___dummy_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Std_instStreamSubarray___redArg();
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamSubarray(lean_object* v_00_u03b1_206_){
_start:
{
lean_object* v___f_207_; 
v___f_207_ = ((lean_object*)(l_Std_instStreamSubarray___redArg___closed__0));
return v___f_207_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamRangeNat___lam__0(lean_object* v_r_208_){
_start:
{
lean_object* v_start_209_; lean_object* v_stop_210_; lean_object* v_step_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_223_; 
v_start_209_ = lean_ctor_get(v_r_208_, 0);
v_stop_210_ = lean_ctor_get(v_r_208_, 1);
v_step_211_ = lean_ctor_get(v_r_208_, 2);
v_isSharedCheck_223_ = !lean_is_exclusive(v_r_208_);
if (v_isSharedCheck_223_ == 0)
{
v___x_213_ = v_r_208_;
v_isShared_214_ = v_isSharedCheck_223_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_step_211_);
lean_inc(v_stop_210_);
lean_inc(v_start_209_);
lean_dec(v_r_208_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_223_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
uint8_t v___x_215_; 
v___x_215_ = lean_nat_dec_lt(v_start_209_, v_stop_210_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
lean_del_object(v___x_213_);
lean_dec(v_step_211_);
lean_dec(v_stop_210_);
lean_dec(v_start_209_);
v___x_216_ = lean_box(0);
return v___x_216_;
}
else
{
lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_217_ = lean_nat_add(v_start_209_, v_step_211_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_217_);
v___x_219_ = v___x_213_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_stop_210_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v_step_211_);
v___x_219_ = v_reuseFailAlloc_222_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v_start_209_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v___x_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Stream_next_x3f___redArg(lean_object* v_self_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = lean_apply_1(v_self_226_, v_a_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Stream_next_x3f(lean_object* v_stream_229_, lean_object* v_value_230_, lean_object* v_self_231_, lean_object* v_a_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_apply_1(v_self_231_, v_a_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_ToStream_toStream___redArg(lean_object* v_self_234_, lean_object* v_a_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_apply_1(v_self_234_, v_a_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_ToStream_toStream(lean_object* v_collection_237_, lean_object* v_stream_238_, lean_object* v_self_239_, lean_object* v_a_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_apply_1(v_self_239_, v_a_240_);
return v___x_241_;
}
}
lean_object* runtime_initialize_Init_Data_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Array_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Stream(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Stream(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Range(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Array_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Stream(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Subarray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Stream(builtin);
}
#ifdef __cplusplus
}
#endif
