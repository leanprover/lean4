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
lean_object* l_Std_instToStreamList___redArg(){
_start:
{
lean_object* v___f_74_; 
v___f_74_ = ((lean_object*)(l_Std_instToStreamList___redArg___closed__0));
return v___f_74_;
}
}
LEAN_EXPORT void l_Std_instToStreamList___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_75_;
v_res_75_ = l_Std_instToStreamList___redArg();
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Std_instToStreamList___redArg___boxed(lean_object* v___dummy_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Std_instToStreamList___redArg();
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamList(lean_object* v_00_u03b1_78_){
_start:
{
lean_object* v___f_79_; 
v___f_79_ = ((lean_object*)(l_Std_instToStreamList___redArg___closed__0));
return v___f_79_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray___redArg___lam__0(lean_object* v_a_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = lean_array_get_size(v_a_80_);
v___x_83_ = l_Array_toSubarray___redArg(v_a_80_, v___x_81_, v___x_82_);
return v___x_83_;
}
}
lean_object* l_Std_instToStreamArraySubarray___redArg(){
_start:
{
lean_object* v___f_86_; 
v___f_86_ = ((lean_object*)(l_Std_instToStreamArraySubarray___redArg___closed__0));
return v___f_86_;
}
}
LEAN_EXPORT void l_Std_instToStreamArraySubarray___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_87_;
v_res_87_ = l_Std_instToStreamArraySubarray___redArg();
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray___redArg___boxed(lean_object* v___dummy_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Std_instToStreamArraySubarray___redArg();
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray(lean_object* v_00_u03b1_90_){
_start:
{
lean_object* v___f_91_; 
v___f_91_ = ((lean_object*)(l_Std_instToStreamArraySubarray___redArg___closed__0));
return v___f_91_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___redArg___lam__0(lean_object* v_a_92_){
_start:
{
lean_inc_ref(v_a_92_);
return v_a_92_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___redArg___lam__0___boxed(lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_instToStreamSubarray___redArg___lam__0(v_a_93_);
lean_dec_ref(v_a_93_);
return v_res_94_;
}
}
lean_object* l_Std_instToStreamSubarray___redArg(){
_start:
{
lean_object* v___f_97_; 
v___f_97_ = ((lean_object*)(l_Std_instToStreamSubarray___redArg___closed__0));
return v___f_97_;
}
}
LEAN_EXPORT void l_Std_instToStreamSubarray___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_98_;
v_res_98_ = l_Std_instToStreamSubarray___redArg();
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___redArg___boxed(lean_object* v___dummy_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_instToStreamSubarray___redArg();
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray(lean_object* v_00_u03b1_101_){
_start:
{
lean_object* v___f_102_; 
v___f_102_ = ((lean_object*)(l_Std_instToStreamSubarray___redArg___closed__0));
return v___f_102_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamStringRaw___lam__0(lean_object* v_s_103_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = lean_string_utf8_byte_size(v_s_103_);
v___x_106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_106_, 0, v_s_103_);
lean_ctor_set(v___x_106_, 1, v___x_104_);
lean_ctor_set(v___x_106_, 2, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamRange___lam__0(lean_object* v_r_109_){
_start:
{
lean_inc_ref(v_r_109_);
return v_r_109_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamRange___lam__0___boxed(lean_object* v_r_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Std_instToStreamRange___lam__0(v_r_110_);
lean_dec_ref(v_r_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamProd___redArg___lam__0(lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_x_116_){
_start:
{
lean_object* v_fst_117_; lean_object* v_snd_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_156_; 
v_fst_117_ = lean_ctor_get(v_x_116_, 0);
v_snd_118_ = lean_ctor_get(v_x_116_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v_x_116_);
if (v_isSharedCheck_156_ == 0)
{
v___x_120_ = v_x_116_;
v_isShared_121_ = v_isSharedCheck_156_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_snd_118_);
lean_inc(v_fst_117_);
lean_dec(v_x_116_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_156_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; 
v___x_122_ = lean_apply_1(v_inst_114_, v_fst_117_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v___x_123_; 
lean_del_object(v___x_120_);
lean_dec(v_snd_118_);
lean_dec_ref(v_inst_115_);
v___x_123_ = lean_box(0);
return v___x_123_;
}
else
{
lean_object* v_val_124_; lean_object* v_fst_125_; lean_object* v_snd_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_155_; 
v_val_124_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_val_124_);
lean_dec_ref_known(v___x_122_, 1);
v_fst_125_ = lean_ctor_get(v_val_124_, 0);
v_snd_126_ = lean_ctor_get(v_val_124_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_val_124_);
if (v_isSharedCheck_155_ == 0)
{
v___x_128_ = v_val_124_;
v_isShared_129_ = v_isSharedCheck_155_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_snd_126_);
lean_inc(v_fst_125_);
lean_dec(v_val_124_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_155_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; 
v___x_130_ = lean_apply_1(v_inst_115_, v_snd_118_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v___x_131_; 
lean_del_object(v___x_128_);
lean_dec(v_snd_126_);
lean_dec(v_fst_125_);
lean_del_object(v___x_120_);
v___x_131_ = lean_box(0);
return v___x_131_;
}
else
{
lean_object* v_val_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_154_; 
v_val_132_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_154_ == 0)
{
v___x_134_ = v___x_130_;
v_isShared_135_ = v_isSharedCheck_154_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_val_132_);
lean_dec(v___x_130_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_154_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v_fst_136_; lean_object* v_snd_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_153_; 
v_fst_136_ = lean_ctor_get(v_val_132_, 0);
v_snd_137_ = lean_ctor_get(v_val_132_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v_val_132_);
if (v_isSharedCheck_153_ == 0)
{
v___x_139_ = v_val_132_;
v_isShared_140_ = v_isSharedCheck_153_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_snd_137_);
lean_inc(v_fst_136_);
lean_dec(v_val_132_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_153_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v_fst_136_);
lean_ctor_set(v___x_139_, 0, v_fst_125_);
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_fst_125_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_fst_136_);
v___x_142_ = v_reuseFailAlloc_152_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_144_; 
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v_snd_137_);
lean_ctor_set(v___x_128_, 0, v_snd_126_);
v___x_144_ = v___x_128_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_snd_126_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_snd_137_);
v___x_144_ = v_reuseFailAlloc_151_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_146_; 
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v___x_144_);
lean_ctor_set(v___x_120_, 0, v___x_142_);
v___x_146_ = v___x_120_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v___x_144_);
v___x_146_ = v_reuseFailAlloc_150_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_148_; 
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v___x_146_);
v___x_148_ = v___x_134_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_146_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
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
LEAN_EXPORT lean_object* l_Std_instStreamProd___redArg(lean_object* v_inst_157_, lean_object* v_inst_158_){
_start:
{
lean_object* v___f_159_; 
v___f_159_ = lean_alloc_closure((void*)(l_Std_instStreamProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_159_, 0, v_inst_157_);
lean_closure_set(v___f_159_, 1, v_inst_158_);
return v___f_159_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamProd(lean_object* v_00_u03c1_160_, lean_object* v_00_u03b1_161_, lean_object* v_00_u03b3_162_, lean_object* v_00_u03b2_163_, lean_object* v_inst_164_, lean_object* v_inst_165_){
_start:
{
lean_object* v___f_166_; 
v___f_166_ = lean_alloc_closure((void*)(l_Std_instStreamProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_166_, 0, v_inst_164_);
lean_closure_set(v___f_166_, 1, v_inst_165_);
return v___f_166_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamList___redArg___lam__0(lean_object* v_x_167_){
_start:
{
if (lean_obj_tag(v_x_167_) == 0)
{
lean_object* v___x_168_; 
v___x_168_ = lean_box(0);
return v___x_168_;
}
else
{
lean_object* v_head_169_; lean_object* v_tail_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_178_; 
v_head_169_ = lean_ctor_get(v_x_167_, 0);
v_tail_170_ = lean_ctor_get(v_x_167_, 1);
v_isSharedCheck_178_ = !lean_is_exclusive(v_x_167_);
if (v_isSharedCheck_178_ == 0)
{
v___x_172_ = v_x_167_;
v_isShared_173_ = v_isSharedCheck_178_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_tail_170_);
lean_inc(v_head_169_);
lean_dec(v_x_167_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_178_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
lean_ctor_set_tag(v___x_172_, 0);
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_head_169_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_tail_170_);
v___x_175_ = v_reuseFailAlloc_177_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_176_; 
v___x_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
}
}
}
}
lean_object* l_Std_instStreamList___redArg(){
_start:
{
lean_object* v___f_181_; 
v___f_181_ = ((lean_object*)(l_Std_instStreamList___redArg___closed__0));
return v___f_181_;
}
}
LEAN_EXPORT void l_Std_instStreamList___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_182_;
v_res_182_ = l_Std_instStreamList___redArg();
stack->m_obj
 = v_res_182_;
}
LEAN_EXPORT lean_object* l_Std_instStreamList___redArg___boxed(lean_object* v___dummy_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Std_instStreamList___redArg();
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamList(lean_object* v_00_u03b1_185_){
_start:
{
lean_object* v___f_186_; 
v___f_186_ = ((lean_object*)(l_Std_instStreamList___redArg___closed__0));
return v___f_186_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamSubarray___redArg___lam__0(lean_object* v_s_187_){
_start:
{
lean_object* v_array_188_; lean_object* v_start_189_; lean_object* v_stop_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_204_; 
v_array_188_ = lean_ctor_get(v_s_187_, 0);
v_start_189_ = lean_ctor_get(v_s_187_, 1);
v_stop_190_ = lean_ctor_get(v_s_187_, 2);
v_isSharedCheck_204_ = !lean_is_exclusive(v_s_187_);
if (v_isSharedCheck_204_ == 0)
{
v___x_192_ = v_s_187_;
v_isShared_193_ = v_isSharedCheck_204_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_stop_190_);
lean_inc(v_start_189_);
lean_inc(v_array_188_);
lean_dec(v_s_187_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_204_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
uint8_t v___x_194_; 
v___x_194_ = lean_nat_dec_lt(v_start_189_, v_stop_190_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
lean_del_object(v___x_192_);
lean_dec(v_stop_190_);
lean_dec(v_start_189_);
lean_dec_ref(v_array_188_);
v___x_195_ = lean_box(0);
return v___x_195_;
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_196_ = lean_array_fget(v_array_188_, v_start_189_);
v___x_197_ = lean_unsigned_to_nat(1u);
v___x_198_ = lean_nat_add(v_start_189_, v___x_197_);
lean_dec(v_start_189_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v___x_198_);
v___x_200_ = v___x_192_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_array_188_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v_stop_190_);
v___x_200_ = v_reuseFailAlloc_203_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_196_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
}
}
}
}
lean_object* l_Std_instStreamSubarray___redArg(){
_start:
{
lean_object* v___f_207_; 
v___f_207_ = ((lean_object*)(l_Std_instStreamSubarray___redArg___closed__0));
return v___f_207_;
}
}
LEAN_EXPORT void l_Std_instStreamSubarray___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_208_;
v_res_208_ = l_Std_instStreamSubarray___redArg();
stack->m_obj
 = v_res_208_;
}
LEAN_EXPORT lean_object* l_Std_instStreamSubarray___redArg___boxed(lean_object* v___dummy_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_instStreamSubarray___redArg();
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamSubarray(lean_object* v_00_u03b1_211_){
_start:
{
lean_object* v___f_212_; 
v___f_212_ = ((lean_object*)(l_Std_instStreamSubarray___redArg___closed__0));
return v___f_212_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamRangeNat___lam__0(lean_object* v_r_213_){
_start:
{
lean_object* v_start_214_; lean_object* v_stop_215_; lean_object* v_step_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_228_; 
v_start_214_ = lean_ctor_get(v_r_213_, 0);
v_stop_215_ = lean_ctor_get(v_r_213_, 1);
v_step_216_ = lean_ctor_get(v_r_213_, 2);
v_isSharedCheck_228_ = !lean_is_exclusive(v_r_213_);
if (v_isSharedCheck_228_ == 0)
{
v___x_218_ = v_r_213_;
v_isShared_219_ = v_isSharedCheck_228_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_step_216_);
lean_inc(v_stop_215_);
lean_inc(v_start_214_);
lean_dec(v_r_213_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_228_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
uint8_t v___x_220_; 
v___x_220_ = lean_nat_dec_lt(v_start_214_, v_stop_215_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; 
lean_del_object(v___x_218_);
lean_dec(v_step_216_);
lean_dec(v_stop_215_);
lean_dec(v_start_214_);
v___x_221_ = lean_box(0);
return v___x_221_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_222_ = lean_nat_add(v_start_214_, v_step_216_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_222_);
v___x_224_ = v___x_218_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_stop_215_);
lean_ctor_set(v_reuseFailAlloc_227_, 2, v_step_216_);
v___x_224_ = v_reuseFailAlloc_227_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v_start_214_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Stream_next_x3f___redArg(lean_object* v_self_231_, lean_object* v_a_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_apply_1(v_self_231_, v_a_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Stream_next_x3f(lean_object* v_stream_234_, lean_object* v_value_235_, lean_object* v_self_236_, lean_object* v_a_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_apply_1(v_self_236_, v_a_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_ToStream_toStream___redArg(lean_object* v_self_239_, lean_object* v_a_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_apply_1(v_self_239_, v_a_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_ToStream_toStream(lean_object* v_collection_242_, lean_object* v_stream_243_, lean_object* v_self_244_, lean_object* v_a_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_apply_1(v_self_244_, v_a_245_);
return v___x_246_;
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
