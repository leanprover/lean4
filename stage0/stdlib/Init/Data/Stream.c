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
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Stream_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Stream_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInOfMonadOfStream___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInOfMonadOfStream___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instForInOfMonadOfStream(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamList___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamList___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_instToStreamList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToStreamList___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instToStreamList___closed__0 = (const lean_object*)&l_Std_instToStreamList___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instToStreamList(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray___lam__0(lean_object*);
static const lean_closure_object l_Std_instToStreamArraySubarray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToStreamArraySubarray___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instToStreamArraySubarray___closed__0 = (const lean_object*)&l_Std_instToStreamArraySubarray___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_instToStreamSubarray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToStreamSubarray___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instToStreamSubarray___closed__0 = (const lean_object*)&l_Std_instToStreamSubarray___closed__0_value;
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
LEAN_EXPORT lean_object* l_Std_instStreamList___lam__0(lean_object*);
static const lean_closure_object l_Std_instStreamList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instStreamList___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instStreamList___closed__0 = (const lean_object*)&l_Std_instStreamList___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instStreamList(lean_object*);
LEAN_EXPORT lean_object* l_Std_instStreamSubarray___lam__0(lean_object*);
static const lean_closure_object l_Std_instStreamSubarray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instStreamSubarray___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instStreamSubarray___closed__0 = (const lean_object*)&l_Std_instStreamSubarray___closed__0_value;
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
lean_dec_ref(v___x_9_);
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
lean_dec_ref(v_____do__lift_22_);
v___x_24_ = lean_apply_2(v_toPure_17_, lean_box(0), v_a_23_);
return v___x_24_;
}
else
{
lean_object* v_a_25_; lean_object* v___x_26_; 
lean_dec(v_toPure_17_);
v_a_25_ = lean_ctor_get(v_____do__lift_22_, 0);
lean_inc(v_a_25_);
lean_dec_ref(v_____do__lift_22_);
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
LEAN_EXPORT lean_object* l_Std_instToStreamList___lam__0(lean_object* v_c_69_){
_start:
{
lean_inc(v_c_69_);
return v_c_69_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamList___lam__0___boxed(lean_object* v_c_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Std_instToStreamList___lam__0(v_c_70_);
lean_dec(v_c_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamList(lean_object* v_00_u03b1_73_){
_start:
{
lean_object* v___f_74_; 
v___f_74_ = ((lean_object*)(l_Std_instToStreamList___closed__0));
return v___f_74_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray___lam__0(lean_object* v_a_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = lean_array_get_size(v_a_75_);
v___x_78_ = l_Array_toSubarray___redArg(v_a_75_, v___x_76_, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamArraySubarray(lean_object* v_00_u03b1_80_){
_start:
{
lean_object* v___f_81_; 
v___f_81_ = ((lean_object*)(l_Std_instToStreamArraySubarray___closed__0));
return v___f_81_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___lam__0(lean_object* v_a_82_){
_start:
{
lean_inc_ref(v_a_82_);
return v_a_82_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray___lam__0___boxed(lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_instToStreamSubarray___lam__0(v_a_83_);
lean_dec_ref(v_a_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamSubarray(lean_object* v_00_u03b1_86_){
_start:
{
lean_object* v___f_87_; 
v___f_87_ = ((lean_object*)(l_Std_instToStreamSubarray___closed__0));
return v___f_87_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamStringRaw___lam__0(lean_object* v_s_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_string_utf8_byte_size(v_s_88_);
v___x_91_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_91_, 0, v_s_88_);
lean_ctor_set(v___x_91_, 1, v___x_89_);
lean_ctor_set(v___x_91_, 2, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamRange___lam__0(lean_object* v_r_94_){
_start:
{
lean_inc_ref(v_r_94_);
return v_r_94_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStreamRange___lam__0___boxed(lean_object* v_r_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_instToStreamRange___lam__0(v_r_95_);
lean_dec_ref(v_r_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamProd___redArg___lam__0(lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_x_101_){
_start:
{
lean_object* v_fst_102_; lean_object* v_snd_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_141_; 
v_fst_102_ = lean_ctor_get(v_x_101_, 0);
v_snd_103_ = lean_ctor_get(v_x_101_, 1);
v_isSharedCheck_141_ = !lean_is_exclusive(v_x_101_);
if (v_isSharedCheck_141_ == 0)
{
v___x_105_ = v_x_101_;
v_isShared_106_ = v_isSharedCheck_141_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_snd_103_);
lean_inc(v_fst_102_);
lean_dec(v_x_101_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_141_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; 
v___x_107_ = lean_apply_1(v_inst_99_, v_fst_102_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v___x_108_; 
lean_del_object(v___x_105_);
lean_dec(v_snd_103_);
lean_dec_ref(v_inst_100_);
v___x_108_ = lean_box(0);
return v___x_108_;
}
else
{
lean_object* v_val_109_; lean_object* v_fst_110_; lean_object* v_snd_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_140_; 
v_val_109_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_val_109_);
lean_dec_ref(v___x_107_);
v_fst_110_ = lean_ctor_get(v_val_109_, 0);
v_snd_111_ = lean_ctor_get(v_val_109_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v_val_109_);
if (v_isSharedCheck_140_ == 0)
{
v___x_113_ = v_val_109_;
v_isShared_114_ = v_isSharedCheck_140_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_snd_111_);
lean_inc(v_fst_110_);
lean_dec(v_val_109_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_140_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; 
v___x_115_ = lean_apply_1(v_inst_100_, v_snd_103_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v___x_116_; 
lean_del_object(v___x_113_);
lean_dec(v_snd_111_);
lean_dec(v_fst_110_);
lean_del_object(v___x_105_);
v___x_116_ = lean_box(0);
return v___x_116_;
}
else
{
lean_object* v_val_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_139_; 
v_val_117_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_139_ == 0)
{
v___x_119_ = v___x_115_;
v_isShared_120_ = v_isSharedCheck_139_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_val_117_);
lean_dec(v___x_115_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_139_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v_fst_121_; lean_object* v_snd_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_138_; 
v_fst_121_ = lean_ctor_get(v_val_117_, 0);
v_snd_122_ = lean_ctor_get(v_val_117_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v_val_117_);
if (v_isSharedCheck_138_ == 0)
{
v___x_124_ = v_val_117_;
v_isShared_125_ = v_isSharedCheck_138_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_snd_122_);
lean_inc(v_fst_121_);
lean_dec(v_val_117_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_138_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v_fst_121_);
lean_ctor_set(v___x_124_, 0, v_fst_110_);
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_fst_110_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_fst_121_);
v___x_127_ = v_reuseFailAlloc_137_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v_snd_122_);
lean_ctor_set(v___x_113_, 0, v_snd_111_);
v___x_129_ = v___x_113_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_snd_111_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_snd_122_);
v___x_129_ = v_reuseFailAlloc_136_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_131_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v___x_129_);
lean_ctor_set(v___x_105_, 0, v___x_127_);
v___x_131_ = v___x_105_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___x_129_);
v___x_131_ = v_reuseFailAlloc_135_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_133_; 
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v___x_131_);
v___x_133_ = v___x_119_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
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
LEAN_EXPORT lean_object* l_Std_instStreamProd___redArg(lean_object* v_inst_142_, lean_object* v_inst_143_){
_start:
{
lean_object* v___f_144_; 
v___f_144_ = lean_alloc_closure((void*)(l_Std_instStreamProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_144_, 0, v_inst_142_);
lean_closure_set(v___f_144_, 1, v_inst_143_);
return v___f_144_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamProd(lean_object* v_00_u03c1_145_, lean_object* v_00_u03b1_146_, lean_object* v_00_u03b3_147_, lean_object* v_00_u03b2_148_, lean_object* v_inst_149_, lean_object* v_inst_150_){
_start:
{
lean_object* v___f_151_; 
v___f_151_ = lean_alloc_closure((void*)(l_Std_instStreamProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_151_, 0, v_inst_149_);
lean_closure_set(v___f_151_, 1, v_inst_150_);
return v___f_151_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamList___lam__0(lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
lean_object* v___x_153_; 
v___x_153_ = lean_box(0);
return v___x_153_;
}
else
{
lean_object* v_head_154_; lean_object* v_tail_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_163_; 
v_head_154_ = lean_ctor_get(v_x_152_, 0);
v_tail_155_ = lean_ctor_get(v_x_152_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v_x_152_);
if (v_isSharedCheck_163_ == 0)
{
v___x_157_ = v_x_152_;
v_isShared_158_ = v_isSharedCheck_163_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_tail_155_);
lean_inc(v_head_154_);
lean_dec(v_x_152_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_163_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
lean_ctor_set_tag(v___x_157_, 0);
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_head_154_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_tail_155_);
v___x_160_ = v_reuseFailAlloc_162_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_161_; 
v___x_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
return v___x_161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instStreamList(lean_object* v_00_u03b1_165_){
_start:
{
lean_object* v___f_166_; 
v___f_166_ = ((lean_object*)(l_Std_instStreamList___closed__0));
return v___f_166_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamSubarray___lam__0(lean_object* v_s_167_){
_start:
{
lean_object* v_array_168_; lean_object* v_start_169_; lean_object* v_stop_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_184_; 
v_array_168_ = lean_ctor_get(v_s_167_, 0);
v_start_169_ = lean_ctor_get(v_s_167_, 1);
v_stop_170_ = lean_ctor_get(v_s_167_, 2);
v_isSharedCheck_184_ = !lean_is_exclusive(v_s_167_);
if (v_isSharedCheck_184_ == 0)
{
v___x_172_ = v_s_167_;
v_isShared_173_ = v_isSharedCheck_184_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_stop_170_);
lean_inc(v_start_169_);
lean_inc(v_array_168_);
lean_dec(v_s_167_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_184_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
uint8_t v___x_174_; 
v___x_174_ = lean_nat_dec_lt(v_start_169_, v_stop_170_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
lean_del_object(v___x_172_);
lean_dec(v_stop_170_);
lean_dec(v_start_169_);
lean_dec_ref(v_array_168_);
v___x_175_ = lean_box(0);
return v___x_175_;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_176_ = lean_array_fget(v_array_168_, v_start_169_);
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = lean_nat_add(v_start_169_, v___x_177_);
lean_dec(v_start_169_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 1, v___x_178_);
v___x_180_ = v___x_172_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_array_168_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_183_, 2, v_stop_170_);
v___x_180_ = v_reuseFailAlloc_183_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_176_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instStreamSubarray(lean_object* v_00_u03b1_186_){
_start:
{
lean_object* v___f_187_; 
v___f_187_ = ((lean_object*)(l_Std_instStreamSubarray___closed__0));
return v___f_187_;
}
}
LEAN_EXPORT lean_object* l_Std_instStreamRangeNat___lam__0(lean_object* v_r_188_){
_start:
{
lean_object* v_start_189_; lean_object* v_stop_190_; lean_object* v_step_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_203_; 
v_start_189_ = lean_ctor_get(v_r_188_, 0);
v_stop_190_ = lean_ctor_get(v_r_188_, 1);
v_step_191_ = lean_ctor_get(v_r_188_, 2);
v_isSharedCheck_203_ = !lean_is_exclusive(v_r_188_);
if (v_isSharedCheck_203_ == 0)
{
v___x_193_ = v_r_188_;
v_isShared_194_ = v_isSharedCheck_203_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_step_191_);
lean_inc(v_stop_190_);
lean_inc(v_start_189_);
lean_dec(v_r_188_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_203_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
uint8_t v___x_195_; 
v___x_195_ = lean_nat_dec_lt(v_start_189_, v_stop_190_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; 
lean_del_object(v___x_193_);
lean_dec(v_step_191_);
lean_dec(v_stop_190_);
lean_dec(v_start_189_);
v___x_196_ = lean_box(0);
return v___x_196_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_197_ = lean_nat_add(v_start_189_, v_step_191_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v___x_197_);
v___x_199_ = v___x_193_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_stop_190_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v_step_191_);
v___x_199_ = v_reuseFailAlloc_202_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v_start_189_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Stream_next_x3f___redArg(lean_object* v_self_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lean_apply_1(v_self_206_, v_a_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Stream_next_x3f(lean_object* v_stream_209_, lean_object* v_value_210_, lean_object* v_self_211_, lean_object* v_a_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lean_apply_1(v_self_211_, v_a_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_ToStream_toStream___redArg(lean_object* v_self_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_apply_1(v_self_214_, v_a_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_ToStream_toStream(lean_object* v_collection_217_, lean_object* v_stream_218_, lean_object* v_self_219_, lean_object* v_a_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_apply_1(v_self_219_, v_a_220_);
return v___x_221_;
}
}
lean_object* runtime_initialize_Init_Data_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Subarray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Array_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Stream(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
