// Lean compiler output
// Module: Std.Data.DHashMap.RawDef
// Imports: public import Std.Data.DHashMap.Internal.AssocList.Basic public import Init.Data.Array.Basic
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
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_fold___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Raw_fold___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__1_value;
static const lean_closure_object l_Std_DHashMap_Raw_fold___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__2 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__2_value;
static const lean_closure_object l_Std_DHashMap_Raw_fold___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__3 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__3_value;
static const lean_closure_object l_Std_DHashMap_Raw_fold___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__4 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__4_value;
static const lean_closure_object l_Std_DHashMap_Raw_fold___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__5 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__5_value;
static const lean_closure_object l_Std_DHashMap_Raw_fold___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__6 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__6_value;
static const lean_ctor_object l_Std_DHashMap_Raw_fold___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__0_value),((lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__1_value)}};
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__7 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__7_value;
static const lean_ctor_object l_Std_DHashMap_Raw_fold___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__7_value),((lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__2_value),((lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__3_value),((lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__4_value),((lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__5_value)}};
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__8 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__8_value;
static const lean_ctor_object l_Std_DHashMap_Raw_fold___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__8_value),((lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__6_value)}};
static const lean_object* l_Std_DHashMap_Raw_fold___redArg___closed__9 = (const lean_object*)&l_Std_DHashMap_Raw_fold___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DHashMap_Raw_all___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DHashMap_Raw_all___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_all___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_all(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_any(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_f_2_, lean_object* v_acc_3_, lean_object* v_l_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1_, v_f_2_, v_acc_3_, v_l_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___redArg(lean_object* v_inst_6_, lean_object* v_f_7_, lean_object* v_init_8_, lean_object* v_b_9_){
_start:
{
lean_object* v_toApplicative_10_; lean_object* v_buckets_11_; lean_object* v_toPure_12_; lean_object* v___x_13_; lean_object* v___x_14_; uint8_t v___x_15_; 
v_toApplicative_10_ = lean_ctor_get(v_inst_6_, 0);
v_buckets_11_ = lean_ctor_get(v_b_9_, 1);
lean_inc_ref(v_buckets_11_);
lean_dec_ref(v_b_9_);
v_toPure_12_ = lean_ctor_get(v_toApplicative_10_, 1);
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_array_get_size(v_buckets_11_);
v___x_15_ = lean_nat_dec_lt(v___x_13_, v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; 
lean_inc(v_toPure_12_);
lean_dec_ref(v_buckets_11_);
lean_dec(v_f_7_);
lean_dec_ref(v_inst_6_);
v___x_16_ = lean_apply_2(v_toPure_12_, lean_box(0), v_init_8_);
return v___x_16_;
}
else
{
lean_object* v___f_17_; size_t v___x_18_; size_t v___x_19_; lean_object* v___x_20_; 
lean_inc_ref(v_inst_6_);
v___f_17_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_17_, 0, v_inst_6_);
lean_closure_set(v___f_17_, 1, v_f_7_);
v___x_18_ = ((size_t)0ULL);
v___x_19_ = lean_usize_of_nat(v___x_14_);
v___x_20_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_6_, v___f_17_, v_buckets_11_, v___x_18_, v___x_19_, v_init_8_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM(lean_object* v_00_u03b1_21_, lean_object* v_00_u03b2_22_, lean_object* v_00_u03b4_23_, lean_object* v_m_24_, lean_object* v_inst_25_, lean_object* v_f_26_, lean_object* v_init_27_, lean_object* v_b_28_){
_start:
{
lean_object* v_toApplicative_29_; lean_object* v_buckets_30_; lean_object* v_toPure_31_; lean_object* v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
v_toApplicative_29_ = lean_ctor_get(v_inst_25_, 0);
v_buckets_30_ = lean_ctor_get(v_b_28_, 1);
lean_inc_ref(v_buckets_30_);
lean_dec_ref(v_b_28_);
v_toPure_31_ = lean_ctor_get(v_toApplicative_29_, 1);
v___x_32_ = lean_unsigned_to_nat(0u);
v___x_33_ = lean_array_get_size(v_buckets_30_);
v___x_34_ = lean_nat_dec_lt(v___x_32_, v___x_33_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; 
lean_inc(v_toPure_31_);
lean_dec_ref(v_buckets_30_);
lean_dec(v_f_26_);
lean_dec_ref(v_inst_25_);
v___x_35_ = lean_apply_2(v_toPure_31_, lean_box(0), v_init_27_);
return v___x_35_;
}
else
{
lean_object* v___f_36_; size_t v___x_37_; size_t v___x_38_; lean_object* v___x_39_; 
lean_inc_ref(v_inst_25_);
v___f_36_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_36_, 0, v_inst_25_);
lean_closure_set(v___f_36_, 1, v_f_26_);
v___x_37_ = ((size_t)0ULL);
v___x_38_ = lean_usize_of_nat(v___x_33_);
v___x_39_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_25_, v___f_36_, v_buckets_30_, v___x_37_, v___x_38_, v_init_27_);
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold___redArg___lam__0(lean_object* v_f_40_, lean_object* v_x1_41_, lean_object* v_x2_42_, lean_object* v_x3_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_apply_3(v_f_40_, v_x1_41_, v_x2_42_, v_x3_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold___redArg___lam__1(lean_object* v___x_45_, lean_object* v___f_46_, lean_object* v_acc_47_, lean_object* v_l_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_45_, v___f_46_, v_acc_47_, v_l_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold___redArg(lean_object* v_f_69_, lean_object* v_init_70_, lean_object* v_b_71_){
_start:
{
lean_object* v___x_72_; lean_object* v_buckets_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_72_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v_buckets_73_ = lean_ctor_get(v_b_71_, 1);
lean_inc_ref(v_buckets_73_);
lean_dec_ref(v_b_71_);
v___x_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = lean_array_get_size(v_buckets_73_);
v___x_76_ = lean_nat_dec_lt(v___x_74_, v___x_75_);
if (v___x_76_ == 0)
{
lean_dec_ref(v_buckets_73_);
lean_dec(v_f_69_);
return v_init_70_;
}
else
{
lean_object* v___f_77_; lean_object* v___f_78_; size_t v___x_79_; size_t v___x_80_; lean_object* v___x_81_; 
v___f_77_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_77_, 0, v_f_69_);
v___f_78_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_78_, 0, v___x_72_);
lean_closure_set(v___f_78_, 1, v___f_77_);
v___x_79_ = ((size_t)0ULL);
v___x_80_ = lean_usize_of_nat(v___x_75_);
v___x_81_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_72_, v___f_78_, v_buckets_73_, v___x_79_, v___x_80_, v_init_70_);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold(lean_object* v_00_u03b1_82_, lean_object* v_00_u03b2_83_, lean_object* v_00_u03b4_84_, lean_object* v_f_85_, lean_object* v_init_86_, lean_object* v_b_87_){
_start:
{
lean_object* v___x_88_; lean_object* v_buckets_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_88_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v_buckets_89_ = lean_ctor_get(v_b_87_, 1);
lean_inc_ref(v_buckets_89_);
lean_dec_ref(v_b_87_);
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_array_get_size(v_buckets_89_);
v___x_92_ = lean_nat_dec_lt(v___x_90_, v___x_91_);
if (v___x_92_ == 0)
{
lean_dec_ref(v_buckets_89_);
lean_dec(v_f_85_);
return v_init_86_;
}
else
{
lean_object* v___f_93_; lean_object* v___f_94_; size_t v___x_95_; size_t v___x_96_; lean_object* v___x_97_; 
v___f_93_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_93_, 0, v_f_85_);
v___f_94_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_94_, 0, v___x_88_);
lean_closure_set(v___f_94_, 1, v___f_93_);
v___x_95_ = ((size_t)0ULL);
v___x_96_ = lean_usize_of_nat(v___x_91_);
v___x_97_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_88_, v___f_94_, v_buckets_89_, v___x_95_, v___x_96_, v_init_86_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM___redArg___lam__0(lean_object* v_f_98_, lean_object* v_x_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_apply_2(v_f_98_, v___y_100_, v___y_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM___redArg___lam__1(lean_object* v_inst_103_, lean_object* v___f_104_, lean_object* v_x_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_box(0);
v___x_108_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_103_, v___f_104_, v___x_107_, v___y_106_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM___redArg(lean_object* v_inst_109_, lean_object* v_f_110_, lean_object* v_b_111_){
_start:
{
lean_object* v_toApplicative_112_; lean_object* v_buckets_113_; lean_object* v_toPure_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v_toApplicative_112_ = lean_ctor_get(v_inst_109_, 0);
v_buckets_113_ = lean_ctor_get(v_b_111_, 1);
lean_inc_ref(v_buckets_113_);
lean_dec_ref(v_b_111_);
v_toPure_114_ = lean_ctor_get(v_toApplicative_112_, 1);
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_array_get_size(v_buckets_113_);
v___x_117_ = lean_box(0);
v___x_118_ = lean_nat_dec_lt(v___x_115_, v___x_116_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; 
lean_inc(v_toPure_114_);
lean_dec_ref(v_buckets_113_);
lean_dec(v_f_110_);
lean_dec_ref(v_inst_109_);
v___x_119_ = lean_apply_2(v_toPure_114_, lean_box(0), v___x_117_);
return v___x_119_;
}
else
{
lean_object* v___f_120_; lean_object* v___f_121_; size_t v___x_122_; size_t v___x_123_; lean_object* v___x_124_; 
v___f_120_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_120_, 0, v_f_110_);
lean_inc_ref(v_inst_109_);
v___f_121_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_121_, 0, v_inst_109_);
lean_closure_set(v___f_121_, 1, v___f_120_);
v___x_122_ = ((size_t)0ULL);
v___x_123_ = lean_usize_of_nat(v___x_116_);
v___x_124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_109_, v___f_121_, v_buckets_113_, v___x_122_, v___x_123_, v___x_117_);
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_m_127_, lean_object* v_inst_128_, lean_object* v_f_129_, lean_object* v_b_130_){
_start:
{
lean_object* v_toApplicative_131_; lean_object* v_buckets_132_; lean_object* v_toPure_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v_toApplicative_131_ = lean_ctor_get(v_inst_128_, 0);
v_buckets_132_ = lean_ctor_get(v_b_130_, 1);
lean_inc_ref(v_buckets_132_);
lean_dec_ref(v_b_130_);
v_toPure_133_ = lean_ctor_get(v_toApplicative_131_, 1);
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_array_get_size(v_buckets_132_);
v___x_136_ = lean_box(0);
v___x_137_ = lean_nat_dec_lt(v___x_134_, v___x_135_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; 
lean_inc(v_toPure_133_);
lean_dec_ref(v_buckets_132_);
lean_dec(v_f_129_);
lean_dec_ref(v_inst_128_);
v___x_138_ = lean_apply_2(v_toPure_133_, lean_box(0), v___x_136_);
return v___x_138_;
}
else
{
lean_object* v___f_139_; lean_object* v___f_140_; size_t v___x_141_; size_t v___x_142_; lean_object* v___x_143_; 
v___f_139_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_139_, 0, v_f_129_);
lean_inc_ref(v_inst_128_);
v___f_140_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_140_, 0, v_inst_128_);
lean_closure_set(v___f_140_, 1, v___f_139_);
v___x_141_ = ((size_t)0ULL);
v___x_142_ = lean_usize_of_nat(v___x_135_);
v___x_143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_128_, v___f_140_, v_buckets_132_, v___x_141_, v___x_142_, v___x_136_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___redArg___lam__0(lean_object* v_inst_144_, lean_object* v_f_145_, lean_object* v_a_146_, lean_object* v_x_147_, lean_object* v___y_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_144_, v_f_145_, v_a_146_, v___y_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___redArg(lean_object* v_inst_150_, lean_object* v_f_151_, lean_object* v_init_152_, lean_object* v_b_153_){
_start:
{
lean_object* v_buckets_154_; lean_object* v___f_155_; size_t v_sz_156_; size_t v___x_157_; lean_object* v___x_158_; 
v_buckets_154_ = lean_ctor_get(v_b_153_, 1);
lean_inc_ref(v_buckets_154_);
lean_dec_ref(v_b_153_);
lean_inc_ref(v_inst_150_);
v___f_155_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_155_, 0, v_inst_150_);
lean_closure_set(v___f_155_, 1, v_f_151_);
v_sz_156_ = lean_array_size(v_buckets_154_);
v___x_157_ = ((size_t)0ULL);
v___x_158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_150_, v_buckets_154_, v___f_155_, v_sz_156_, v___x_157_, v_init_152_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn(lean_object* v_00_u03b1_159_, lean_object* v_00_u03b2_160_, lean_object* v_00_u03b4_161_, lean_object* v_m_162_, lean_object* v_inst_163_, lean_object* v_f_164_, lean_object* v_init_165_, lean_object* v_b_166_){
_start:
{
lean_object* v_buckets_167_; lean_object* v___f_168_; size_t v_sz_169_; size_t v___x_170_; lean_object* v___x_171_; 
v_buckets_167_ = lean_ctor_get(v_b_166_, 1);
lean_inc_ref(v_buckets_167_);
lean_dec_ref(v_b_166_);
lean_inc_ref(v_inst_163_);
v___f_168_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_168_, 0, v_inst_163_);
lean_closure_set(v___f_168_, 1, v_f_164_);
v_sz_169_ = lean_array_size(v_buckets_167_);
v___x_170_ = ((size_t)0ULL);
v___x_171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_163_, v_buckets_167_, v___f_168_, v_sz_169_, v___x_170_, v_init_165_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__0(lean_object* v_f_172_, lean_object* v_x_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___y_174_);
lean_ctor_set(v___x_176_, 1, v___y_175_);
v___x_177_ = lean_apply_1(v_f_172_, v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__2(lean_object* v_inst_178_, lean_object* v_m_179_, lean_object* v_f_180_){
_start:
{
lean_object* v_toApplicative_181_; lean_object* v_buckets_182_; lean_object* v_toPure_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v_toApplicative_181_ = lean_ctor_get(v_inst_178_, 0);
v_buckets_182_ = lean_ctor_get(v_m_179_, 1);
lean_inc_ref(v_buckets_182_);
lean_dec_ref(v_m_179_);
v_toPure_183_ = lean_ctor_get(v_toApplicative_181_, 1);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_array_get_size(v_buckets_182_);
v___x_186_ = lean_box(0);
v___x_187_ = lean_nat_dec_lt(v___x_184_, v___x_185_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; 
lean_inc(v_toPure_183_);
lean_dec_ref(v_buckets_182_);
lean_dec(v_f_180_);
lean_dec_ref(v_inst_178_);
v___x_188_ = lean_apply_2(v_toPure_183_, lean_box(0), v___x_186_);
return v___x_188_;
}
else
{
lean_object* v___f_189_; lean_object* v___f_190_; size_t v___x_191_; size_t v___x_192_; lean_object* v___x_193_; 
v___f_189_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_189_, 0, v_f_180_);
lean_inc_ref(v_inst_178_);
v___f_190_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_190_, 0, v_inst_178_);
lean_closure_set(v___f_190_, 1, v___f_189_);
v___x_191_ = ((size_t)0ULL);
v___x_192_ = lean_usize_of_nat(v___x_185_);
v___x_193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_178_, v___f_190_, v_buckets_182_, v___x_191_, v___x_192_, v___x_186_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg(lean_object* v_inst_194_){
_start:
{
lean_object* v___f_195_; 
v___f_195_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_195_, 0, v_inst_194_);
return v___f_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad(lean_object* v_00_u03b1_196_, lean_object* v_00_u03b2_197_, lean_object* v_m_198_, lean_object* v_inst_199_){
_start:
{
lean_object* v___f_200_; 
v___f_200_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_200_, 0, v_inst_199_);
return v___f_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_201_, lean_object* v_a_202_, lean_object* v_b_203_, lean_object* v_acc_204_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v_a_202_);
lean_ctor_set(v___x_205_, 1, v_b_203_);
v___x_206_ = lean_apply_2(v_f_201_, v___x_205_, v_acc_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1(lean_object* v_inst_207_, lean_object* v___f_208_, lean_object* v_a_209_, lean_object* v_x_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_207_, v___f_208_, v_a_209_, v___y_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_213_, lean_object* v_00_u03b2_214_, lean_object* v_m_215_, lean_object* v_init_216_, lean_object* v_f_217_){
_start:
{
lean_object* v_buckets_218_; lean_object* v___f_219_; lean_object* v___f_220_; size_t v_sz_221_; size_t v___x_222_; lean_object* v___x_223_; 
v_buckets_218_ = lean_ctor_get(v_m_215_, 1);
lean_inc_ref(v_buckets_218_);
lean_dec_ref(v_m_215_);
v___f_219_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_219_, 0, v_f_217_);
lean_inc_ref(v_inst_213_);
v___f_220_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_220_, 0, v_inst_213_);
lean_closure_set(v___f_220_, 1, v___f_219_);
v_sz_221_ = lean_array_size(v_buckets_218_);
v___x_222_ = ((size_t)0ULL);
v___x_223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_213_, v_buckets_218_, v___f_220_, v_sz_221_, v___x_222_, v_init_216_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg(lean_object* v_inst_224_){
_start:
{
lean_object* v___f_225_; 
v___f_225_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_225_, 0, v_inst_224_);
return v___f_225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad(lean_object* v_00_u03b1_226_, lean_object* v_00_u03b2_227_, lean_object* v_m_228_, lean_object* v_inst_229_){
_start:
{
lean_object* v___f_230_; 
v___f_230_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_230_, 0, v_inst_229_);
return v___f_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___lam__0(lean_object* v_p_231_, lean_object* v___x_232_, lean_object* v___x_233_, lean_object* v_a_234_, lean_object* v_b_235_, lean_object* v_acc_236_){
_start:
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_apply_2(v_p_231_, v_a_234_, v_b_235_);
v___x_238_ = lean_unbox(v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec_ref(v___x_233_);
v___x_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_237_);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_232_);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
else
{
lean_object* v___x_242_; 
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_233_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_243_, lean_object* v___x_244_, lean_object* v___x_245_, lean_object* v_a_246_, lean_object* v_b_247_, lean_object* v_acc_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Std_DHashMap_Raw_all___redArg___lam__0(v_p_243_, v___x_244_, v___x_245_, v_a_246_, v_b_247_, v_acc_248_);
lean_dec_ref(v_acc_248_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___lam__1(lean_object* v___x_250_, lean_object* v___f_251_, lean_object* v_a_252_, lean_object* v_x_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_250_, v___f_251_, v_a_252_, v___y_254_);
return v___x_255_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_all___redArg(lean_object* v_m_259_, lean_object* v_p_260_){
_start:
{
lean_object* v___x_261_; lean_object* v_buckets_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___f_265_; lean_object* v___f_266_; size_t v_sz_267_; size_t v___x_268_; lean_object* v___x_269_; lean_object* v_fst_270_; 
v___x_261_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v_buckets_262_ = lean_ctor_get(v_m_259_, 1);
lean_inc_ref(v_buckets_262_);
lean_dec_ref(v_m_259_);
v___x_263_ = lean_box(0);
v___x_264_ = ((lean_object*)(l_Std_DHashMap_Raw_all___redArg___closed__0));
v___f_265_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_265_, 0, v_p_260_);
lean_closure_set(v___f_265_, 1, v___x_263_);
lean_closure_set(v___f_265_, 2, v___x_264_);
v___f_266_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_266_, 0, v___x_261_);
lean_closure_set(v___f_266_, 1, v___f_265_);
v_sz_267_ = lean_array_size(v_buckets_262_);
v___x_268_ = ((size_t)0ULL);
v___x_269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_261_, v_buckets_262_, v___f_266_, v_sz_267_, v___x_268_, v___x_264_);
v_fst_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_fst_270_);
lean_dec(v___x_269_);
if (lean_obj_tag(v_fst_270_) == 0)
{
uint8_t v___x_271_; 
v___x_271_ = 1;
return v___x_271_;
}
else
{
lean_object* v_val_272_; uint8_t v___x_273_; 
v_val_272_ = lean_ctor_get(v_fst_270_, 0);
lean_inc(v_val_272_);
lean_dec_ref_known(v_fst_270_, 1);
v___x_273_ = lean_unbox(v_val_272_);
lean_dec(v_val_272_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___boxed(lean_object* v_m_274_, lean_object* v_p_275_){
_start:
{
uint8_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l_Std_DHashMap_Raw_all___redArg(v_m_274_, v_p_275_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_all(lean_object* v_00_u03b1_278_, lean_object* v_00_u03b2_279_, lean_object* v_m_280_, lean_object* v_p_281_){
_start:
{
lean_object* v___x_282_; lean_object* v_buckets_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___f_286_; lean_object* v___f_287_; size_t v_sz_288_; size_t v___x_289_; lean_object* v___x_290_; lean_object* v_fst_291_; 
v___x_282_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v_buckets_283_ = lean_ctor_get(v_m_280_, 1);
lean_inc_ref(v_buckets_283_);
lean_dec_ref(v_m_280_);
v___x_284_ = lean_box(0);
v___x_285_ = ((lean_object*)(l_Std_DHashMap_Raw_all___redArg___closed__0));
v___f_286_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_286_, 0, v_p_281_);
lean_closure_set(v___f_286_, 1, v___x_284_);
lean_closure_set(v___f_286_, 2, v___x_285_);
v___f_287_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_287_, 0, v___x_282_);
lean_closure_set(v___f_287_, 1, v___f_286_);
v_sz_288_ = lean_array_size(v_buckets_283_);
v___x_289_ = ((size_t)0ULL);
v___x_290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_282_, v_buckets_283_, v___f_287_, v_sz_288_, v___x_289_, v___x_285_);
v_fst_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_fst_291_);
lean_dec(v___x_290_);
if (lean_obj_tag(v_fst_291_) == 0)
{
uint8_t v___x_292_; 
v___x_292_ = 1;
return v___x_292_;
}
else
{
lean_object* v_val_293_; uint8_t v___x_294_; 
v_val_293_ = lean_ctor_get(v_fst_291_, 0);
lean_inc(v_val_293_);
lean_dec_ref_known(v_fst_291_, 1);
v___x_294_ = lean_unbox(v_val_293_);
lean_dec(v_val_293_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___boxed(lean_object* v_00_u03b1_295_, lean_object* v_00_u03b2_296_, lean_object* v_m_297_, lean_object* v_p_298_){
_start:
{
uint8_t v_res_299_; lean_object* v_r_300_; 
v_res_299_ = l_Std_DHashMap_Raw_all(v_00_u03b1_295_, v_00_u03b2_296_, v_m_297_, v_p_298_);
v_r_300_ = lean_box(v_res_299_);
return v_r_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___redArg___lam__0(lean_object* v_p_301_, lean_object* v___x_302_, lean_object* v___x_303_, lean_object* v_a_304_, lean_object* v_b_305_, lean_object* v_acc_306_){
_start:
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = lean_apply_2(v_p_301_, v_a_304_, v_b_305_);
v___x_308_ = lean_unbox(v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
v___x_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_302_);
return v___x_309_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec_ref(v___x_302_);
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_307_);
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_303_);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_313_, lean_object* v___x_314_, lean_object* v___x_315_, lean_object* v_a_316_, lean_object* v_b_317_, lean_object* v_acc_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Std_DHashMap_Raw_any___redArg___lam__0(v_p_313_, v___x_314_, v___x_315_, v_a_316_, v_b_317_, v_acc_318_);
lean_dec_ref(v_acc_318_);
return v_res_319_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_any___redArg(lean_object* v_m_320_, lean_object* v_p_321_){
_start:
{
lean_object* v___x_322_; lean_object* v_buckets_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___f_326_; lean_object* v___f_327_; size_t v_sz_328_; size_t v___x_329_; lean_object* v___x_330_; lean_object* v_fst_331_; 
v___x_322_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v_buckets_323_ = lean_ctor_get(v_m_320_, 1);
lean_inc_ref(v_buckets_323_);
lean_dec_ref(v_m_320_);
v___x_324_ = lean_box(0);
v___x_325_ = ((lean_object*)(l_Std_DHashMap_Raw_all___redArg___closed__0));
v___f_326_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_326_, 0, v_p_321_);
lean_closure_set(v___f_326_, 1, v___x_325_);
lean_closure_set(v___f_326_, 2, v___x_324_);
v___f_327_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_327_, 0, v___x_322_);
lean_closure_set(v___f_327_, 1, v___f_326_);
v_sz_328_ = lean_array_size(v_buckets_323_);
v___x_329_ = ((size_t)0ULL);
v___x_330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_322_, v_buckets_323_, v___f_327_, v_sz_328_, v___x_329_, v___x_325_);
v_fst_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_fst_331_);
lean_dec(v___x_330_);
if (lean_obj_tag(v_fst_331_) == 0)
{
uint8_t v___x_332_; 
v___x_332_ = 0;
return v___x_332_;
}
else
{
lean_object* v_val_333_; uint8_t v___x_334_; 
v_val_333_ = lean_ctor_get(v_fst_331_, 0);
lean_inc(v_val_333_);
lean_dec_ref_known(v_fst_331_, 1);
v___x_334_ = lean_unbox(v_val_333_);
lean_dec(v_val_333_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___redArg___boxed(lean_object* v_m_335_, lean_object* v_p_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_Std_DHashMap_Raw_any___redArg(v_m_335_, v_p_336_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_any(lean_object* v_00_u03b1_339_, lean_object* v_00_u03b2_340_, lean_object* v_m_341_, lean_object* v_p_342_){
_start:
{
lean_object* v___x_343_; lean_object* v_buckets_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___f_347_; lean_object* v___f_348_; size_t v_sz_349_; size_t v___x_350_; lean_object* v___x_351_; lean_object* v_fst_352_; 
v___x_343_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v_buckets_344_ = lean_ctor_get(v_m_341_, 1);
lean_inc_ref(v_buckets_344_);
lean_dec_ref(v_m_341_);
v___x_345_ = lean_box(0);
v___x_346_ = ((lean_object*)(l_Std_DHashMap_Raw_all___redArg___closed__0));
v___f_347_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_347_, 0, v_p_342_);
lean_closure_set(v___f_347_, 1, v___x_346_);
lean_closure_set(v___f_347_, 2, v___x_345_);
v___f_348_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_348_, 0, v___x_343_);
lean_closure_set(v___f_348_, 1, v___f_347_);
v_sz_349_ = lean_array_size(v_buckets_344_);
v___x_350_ = ((size_t)0ULL);
v___x_351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_343_, v_buckets_344_, v___f_348_, v_sz_349_, v___x_350_, v___x_346_);
v_fst_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_fst_352_);
lean_dec(v___x_351_);
if (lean_obj_tag(v_fst_352_) == 0)
{
uint8_t v___x_353_; 
v___x_353_ = 0;
return v___x_353_;
}
else
{
lean_object* v_val_354_; uint8_t v___x_355_; 
v_val_354_ = lean_ctor_get(v_fst_352_, 0);
lean_inc(v_val_354_);
lean_dec_ref_known(v_fst_352_, 1);
v___x_355_ = lean_unbox(v_val_354_);
lean_dec(v_val_354_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___boxed(lean_object* v_00_u03b1_356_, lean_object* v_00_u03b2_357_, lean_object* v_m_358_, lean_object* v_p_359_){
_start:
{
uint8_t v_res_360_; lean_object* v_r_361_; 
v_res_360_ = l_Std_DHashMap_Raw_any(v_00_u03b1_356_, v_00_u03b2_357_, v_m_358_, v_p_359_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_RawDef(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DHashMap_RawDef(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_RawDef(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_RawDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DHashMap_RawDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DHashMap_RawDef(builtin);
}
#ifdef __cplusplus
}
#endif
