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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* v_buckets_10_; lean_object* v___x_11_; lean_object* v___x_12_; uint8_t v___x_13_; 
v_buckets_10_ = lean_ctor_get(v_b_9_, 1);
lean_inc_ref(v_buckets_10_);
lean_dec_ref(v_b_9_);
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_array_get_size(v_buckets_10_);
v___x_13_ = lean_nat_dec_lt(v___x_11_, v___x_12_);
if (v___x_13_ == 0)
{
lean_object* v_toApplicative_14_; lean_object* v_toPure_15_; lean_object* v___x_16_; 
lean_dec_ref(v_buckets_10_);
lean_dec(v_f_7_);
v_toApplicative_14_ = lean_ctor_get(v_inst_6_, 0);
lean_inc_ref(v_toApplicative_14_);
lean_dec_ref(v_inst_6_);
v_toPure_15_ = lean_ctor_get(v_toApplicative_14_, 1);
lean_inc(v_toPure_15_);
lean_dec_ref(v_toApplicative_14_);
v___x_16_ = lean_apply_2(v_toPure_15_, lean_box(0), v_init_8_);
return v___x_16_;
}
else
{
lean_object* v___f_17_; uint8_t v___x_18_; 
lean_inc_ref(v_inst_6_);
v___f_17_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_17_, 0, v_inst_6_);
lean_closure_set(v___f_17_, 1, v_f_7_);
v___x_18_ = lean_nat_dec_le(v___x_12_, v___x_12_);
if (v___x_18_ == 0)
{
if (v___x_13_ == 0)
{
lean_object* v_toApplicative_19_; lean_object* v_toPure_20_; lean_object* v___x_21_; 
lean_dec_ref(v___f_17_);
lean_dec_ref(v_buckets_10_);
v_toApplicative_19_ = lean_ctor_get(v_inst_6_, 0);
lean_inc_ref(v_toApplicative_19_);
lean_dec_ref(v_inst_6_);
v_toPure_20_ = lean_ctor_get(v_toApplicative_19_, 1);
lean_inc(v_toPure_20_);
lean_dec_ref(v_toApplicative_19_);
v___x_21_ = lean_apply_2(v_toPure_20_, lean_box(0), v_init_8_);
return v___x_21_;
}
else
{
size_t v___x_22_; size_t v___x_23_; lean_object* v___x_24_; 
v___x_22_ = ((size_t)0ULL);
v___x_23_ = lean_usize_of_nat(v___x_12_);
v___x_24_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_6_, v___f_17_, v_buckets_10_, v___x_22_, v___x_23_, v_init_8_);
return v___x_24_;
}
}
else
{
size_t v___x_25_; size_t v___x_26_; lean_object* v___x_27_; 
v___x_25_ = ((size_t)0ULL);
v___x_26_ = lean_usize_of_nat(v___x_12_);
v___x_27_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_6_, v___f_17_, v_buckets_10_, v___x_25_, v___x_26_, v_init_8_);
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM(lean_object* v_00_u03b1_28_, lean_object* v_00_u03b2_29_, lean_object* v_00_u03b4_30_, lean_object* v_m_31_, lean_object* v_inst_32_, lean_object* v_f_33_, lean_object* v_init_34_, lean_object* v_b_35_){
_start:
{
lean_object* v_buckets_36_; lean_object* v___x_37_; lean_object* v___x_38_; uint8_t v___x_39_; 
v_buckets_36_ = lean_ctor_get(v_b_35_, 1);
lean_inc_ref(v_buckets_36_);
lean_dec_ref(v_b_35_);
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = lean_array_get_size(v_buckets_36_);
v___x_39_ = lean_nat_dec_lt(v___x_37_, v___x_38_);
if (v___x_39_ == 0)
{
lean_object* v_toApplicative_40_; lean_object* v_toPure_41_; lean_object* v___x_42_; 
lean_dec_ref(v_buckets_36_);
lean_dec(v_f_33_);
v_toApplicative_40_ = lean_ctor_get(v_inst_32_, 0);
lean_inc_ref(v_toApplicative_40_);
lean_dec_ref(v_inst_32_);
v_toPure_41_ = lean_ctor_get(v_toApplicative_40_, 1);
lean_inc(v_toPure_41_);
lean_dec_ref(v_toApplicative_40_);
v___x_42_ = lean_apply_2(v_toPure_41_, lean_box(0), v_init_34_);
return v___x_42_;
}
else
{
lean_object* v___f_43_; uint8_t v___x_44_; 
lean_inc_ref(v_inst_32_);
v___f_43_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_43_, 0, v_inst_32_);
lean_closure_set(v___f_43_, 1, v_f_33_);
v___x_44_ = lean_nat_dec_le(v___x_38_, v___x_38_);
if (v___x_44_ == 0)
{
if (v___x_39_ == 0)
{
lean_object* v_toApplicative_45_; lean_object* v_toPure_46_; lean_object* v___x_47_; 
lean_dec_ref(v___f_43_);
lean_dec_ref(v_buckets_36_);
v_toApplicative_45_ = lean_ctor_get(v_inst_32_, 0);
lean_inc_ref(v_toApplicative_45_);
lean_dec_ref(v_inst_32_);
v_toPure_46_ = lean_ctor_get(v_toApplicative_45_, 1);
lean_inc(v_toPure_46_);
lean_dec_ref(v_toApplicative_45_);
v___x_47_ = lean_apply_2(v_toPure_46_, lean_box(0), v_init_34_);
return v___x_47_;
}
else
{
size_t v___x_48_; size_t v___x_49_; lean_object* v___x_50_; 
v___x_48_ = ((size_t)0ULL);
v___x_49_ = lean_usize_of_nat(v___x_38_);
v___x_50_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_32_, v___f_43_, v_buckets_36_, v___x_48_, v___x_49_, v_init_34_);
return v___x_50_;
}
}
else
{
size_t v___x_51_; size_t v___x_52_; lean_object* v___x_53_; 
v___x_51_ = ((size_t)0ULL);
v___x_52_ = lean_usize_of_nat(v___x_38_);
v___x_53_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_32_, v___f_43_, v_buckets_36_, v___x_51_, v___x_52_, v_init_34_);
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold___redArg___lam__0(lean_object* v_f_54_, lean_object* v_x1_55_, lean_object* v_x2_56_, lean_object* v_x3_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_apply_3(v_f_54_, v_x1_55_, v_x2_56_, v_x3_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold___redArg___lam__1(lean_object* v___x_59_, lean_object* v___f_60_, lean_object* v_acc_61_, lean_object* v_l_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_59_, v___f_60_, v_acc_61_, v_l_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold___redArg(lean_object* v_f_83_, lean_object* v_init_84_, lean_object* v_b_85_){
_start:
{
lean_object* v___x_86_; lean_object* v_buckets_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_86_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v_buckets_87_ = lean_ctor_get(v_b_85_, 1);
lean_inc_ref(v_buckets_87_);
lean_dec_ref(v_b_85_);
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_89_ = lean_array_get_size(v_buckets_87_);
v___x_90_ = lean_nat_dec_lt(v___x_88_, v___x_89_);
if (v___x_90_ == 0)
{
lean_dec_ref(v_buckets_87_);
lean_dec(v_f_83_);
return v_init_84_;
}
else
{
lean_object* v___f_91_; lean_object* v___f_92_; uint8_t v___x_93_; 
v___f_91_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_91_, 0, v_f_83_);
v___f_92_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_92_, 0, v___x_86_);
lean_closure_set(v___f_92_, 1, v___f_91_);
v___x_93_ = lean_nat_dec_le(v___x_89_, v___x_89_);
if (v___x_93_ == 0)
{
if (v___x_90_ == 0)
{
lean_dec_ref(v___f_92_);
lean_dec_ref(v_buckets_87_);
return v_init_84_;
}
else
{
size_t v___x_94_; size_t v___x_95_; lean_object* v___x_96_; 
v___x_94_ = ((size_t)0ULL);
v___x_95_ = lean_usize_of_nat(v___x_89_);
v___x_96_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_86_, v___f_92_, v_buckets_87_, v___x_94_, v___x_95_, v_init_84_);
return v___x_96_;
}
}
else
{
size_t v___x_97_; size_t v___x_98_; lean_object* v___x_99_; 
v___x_97_ = ((size_t)0ULL);
v___x_98_ = lean_usize_of_nat(v___x_89_);
v___x_99_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_86_, v___f_92_, v_buckets_87_, v___x_97_, v___x_98_, v_init_84_);
return v___x_99_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold(lean_object* v_00_u03b1_100_, lean_object* v_00_u03b2_101_, lean_object* v_00_u03b4_102_, lean_object* v_f_103_, lean_object* v_init_104_, lean_object* v_b_105_){
_start:
{
lean_object* v___x_106_; lean_object* v_buckets_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_106_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v_buckets_107_ = lean_ctor_get(v_b_105_, 1);
lean_inc_ref(v_buckets_107_);
lean_dec_ref(v_b_105_);
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = lean_array_get_size(v_buckets_107_);
v___x_110_ = lean_nat_dec_lt(v___x_108_, v___x_109_);
if (v___x_110_ == 0)
{
lean_dec_ref(v_buckets_107_);
lean_dec(v_f_103_);
return v_init_104_;
}
else
{
lean_object* v___f_111_; lean_object* v___f_112_; uint8_t v___x_113_; 
v___f_111_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_111_, 0, v_f_103_);
v___f_112_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_112_, 0, v___x_106_);
lean_closure_set(v___f_112_, 1, v___f_111_);
v___x_113_ = lean_nat_dec_le(v___x_109_, v___x_109_);
if (v___x_113_ == 0)
{
if (v___x_110_ == 0)
{
lean_dec_ref(v___f_112_);
lean_dec_ref(v_buckets_107_);
return v_init_104_;
}
else
{
size_t v___x_114_; size_t v___x_115_; lean_object* v___x_116_; 
v___x_114_ = ((size_t)0ULL);
v___x_115_ = lean_usize_of_nat(v___x_109_);
v___x_116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_106_, v___f_112_, v_buckets_107_, v___x_114_, v___x_115_, v_init_104_);
return v___x_116_;
}
}
else
{
size_t v___x_117_; size_t v___x_118_; lean_object* v___x_119_; 
v___x_117_ = ((size_t)0ULL);
v___x_118_ = lean_usize_of_nat(v___x_109_);
v___x_119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_106_, v___f_112_, v_buckets_107_, v___x_117_, v___x_118_, v_init_104_);
return v___x_119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM___redArg___lam__0(lean_object* v_f_120_, lean_object* v_x_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_apply_2(v_f_120_, v___y_122_, v___y_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM___redArg___lam__1(lean_object* v_inst_125_, lean_object* v___f_126_, lean_object* v_x_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_box(0);
v___x_130_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_125_, v___f_126_, v___x_129_, v___y_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM___redArg(lean_object* v_inst_131_, lean_object* v_f_132_, lean_object* v_b_133_){
_start:
{
lean_object* v_buckets_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v_buckets_134_ = lean_ctor_get(v_b_133_, 1);
lean_inc_ref(v_buckets_134_);
lean_dec_ref(v_b_133_);
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = lean_array_get_size(v_buckets_134_);
v___x_137_ = lean_box(0);
v___x_138_ = lean_nat_dec_lt(v___x_135_, v___x_136_);
if (v___x_138_ == 0)
{
lean_object* v_toApplicative_139_; lean_object* v_toPure_140_; lean_object* v___x_141_; 
lean_dec_ref(v_buckets_134_);
lean_dec(v_f_132_);
v_toApplicative_139_ = lean_ctor_get(v_inst_131_, 0);
lean_inc_ref(v_toApplicative_139_);
lean_dec_ref(v_inst_131_);
v_toPure_140_ = lean_ctor_get(v_toApplicative_139_, 1);
lean_inc(v_toPure_140_);
lean_dec_ref(v_toApplicative_139_);
v___x_141_ = lean_apply_2(v_toPure_140_, lean_box(0), v___x_137_);
return v___x_141_;
}
else
{
lean_object* v___f_142_; lean_object* v___f_143_; uint8_t v___x_144_; 
v___f_142_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_142_, 0, v_f_132_);
lean_inc_ref(v_inst_131_);
v___f_143_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_143_, 0, v_inst_131_);
lean_closure_set(v___f_143_, 1, v___f_142_);
v___x_144_ = lean_nat_dec_le(v___x_136_, v___x_136_);
if (v___x_144_ == 0)
{
if (v___x_138_ == 0)
{
lean_object* v_toApplicative_145_; lean_object* v_toPure_146_; lean_object* v___x_147_; 
lean_dec_ref(v___f_143_);
lean_dec_ref(v_buckets_134_);
v_toApplicative_145_ = lean_ctor_get(v_inst_131_, 0);
lean_inc_ref(v_toApplicative_145_);
lean_dec_ref(v_inst_131_);
v_toPure_146_ = lean_ctor_get(v_toApplicative_145_, 1);
lean_inc(v_toPure_146_);
lean_dec_ref(v_toApplicative_145_);
v___x_147_ = lean_apply_2(v_toPure_146_, lean_box(0), v___x_137_);
return v___x_147_;
}
else
{
size_t v___x_148_; size_t v___x_149_; lean_object* v___x_150_; 
v___x_148_ = ((size_t)0ULL);
v___x_149_ = lean_usize_of_nat(v___x_136_);
v___x_150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_131_, v___f_143_, v_buckets_134_, v___x_148_, v___x_149_, v___x_137_);
return v___x_150_;
}
}
else
{
size_t v___x_151_; size_t v___x_152_; lean_object* v___x_153_; 
v___x_151_ = ((size_t)0ULL);
v___x_152_ = lean_usize_of_nat(v___x_136_);
v___x_153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_131_, v___f_143_, v_buckets_134_, v___x_151_, v___x_152_, v___x_137_);
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM(lean_object* v_00_u03b1_154_, lean_object* v_00_u03b2_155_, lean_object* v_m_156_, lean_object* v_inst_157_, lean_object* v_f_158_, lean_object* v_b_159_){
_start:
{
lean_object* v_buckets_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v_buckets_160_ = lean_ctor_get(v_b_159_, 1);
lean_inc_ref(v_buckets_160_);
lean_dec_ref(v_b_159_);
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_array_get_size(v_buckets_160_);
v___x_163_ = lean_box(0);
v___x_164_ = lean_nat_dec_lt(v___x_161_, v___x_162_);
if (v___x_164_ == 0)
{
lean_object* v_toApplicative_165_; lean_object* v_toPure_166_; lean_object* v___x_167_; 
lean_dec_ref(v_buckets_160_);
lean_dec(v_f_158_);
v_toApplicative_165_ = lean_ctor_get(v_inst_157_, 0);
lean_inc_ref(v_toApplicative_165_);
lean_dec_ref(v_inst_157_);
v_toPure_166_ = lean_ctor_get(v_toApplicative_165_, 1);
lean_inc(v_toPure_166_);
lean_dec_ref(v_toApplicative_165_);
v___x_167_ = lean_apply_2(v_toPure_166_, lean_box(0), v___x_163_);
return v___x_167_;
}
else
{
lean_object* v___f_168_; lean_object* v___f_169_; uint8_t v___x_170_; 
v___f_168_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_168_, 0, v_f_158_);
lean_inc_ref(v_inst_157_);
v___f_169_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_169_, 0, v_inst_157_);
lean_closure_set(v___f_169_, 1, v___f_168_);
v___x_170_ = lean_nat_dec_le(v___x_162_, v___x_162_);
if (v___x_170_ == 0)
{
if (v___x_164_ == 0)
{
lean_object* v_toApplicative_171_; lean_object* v_toPure_172_; lean_object* v___x_173_; 
lean_dec_ref(v___f_169_);
lean_dec_ref(v_buckets_160_);
v_toApplicative_171_ = lean_ctor_get(v_inst_157_, 0);
lean_inc_ref(v_toApplicative_171_);
lean_dec_ref(v_inst_157_);
v_toPure_172_ = lean_ctor_get(v_toApplicative_171_, 1);
lean_inc(v_toPure_172_);
lean_dec_ref(v_toApplicative_171_);
v___x_173_ = lean_apply_2(v_toPure_172_, lean_box(0), v___x_163_);
return v___x_173_;
}
else
{
size_t v___x_174_; size_t v___x_175_; lean_object* v___x_176_; 
v___x_174_ = ((size_t)0ULL);
v___x_175_ = lean_usize_of_nat(v___x_162_);
v___x_176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_157_, v___f_169_, v_buckets_160_, v___x_174_, v___x_175_, v___x_163_);
return v___x_176_;
}
}
else
{
size_t v___x_177_; size_t v___x_178_; lean_object* v___x_179_; 
v___x_177_ = ((size_t)0ULL);
v___x_178_ = lean_usize_of_nat(v___x_162_);
v___x_179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_157_, v___f_169_, v_buckets_160_, v___x_177_, v___x_178_, v___x_163_);
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___redArg___lam__0(lean_object* v_inst_180_, lean_object* v_f_181_, lean_object* v_a_182_, lean_object* v_x_183_, lean_object* v___y_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_180_, v_f_181_, v_a_182_, v___y_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___redArg(lean_object* v_inst_186_, lean_object* v_f_187_, lean_object* v_init_188_, lean_object* v_b_189_){
_start:
{
lean_object* v_buckets_190_; lean_object* v___f_191_; size_t v_sz_192_; size_t v___x_193_; lean_object* v___x_194_; 
v_buckets_190_ = lean_ctor_get(v_b_189_, 1);
lean_inc_ref(v_buckets_190_);
lean_dec_ref(v_b_189_);
lean_inc_ref(v_inst_186_);
v___f_191_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_191_, 0, v_inst_186_);
lean_closure_set(v___f_191_, 1, v_f_187_);
v_sz_192_ = lean_array_size(v_buckets_190_);
v___x_193_ = ((size_t)0ULL);
v___x_194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_186_, v_buckets_190_, v___f_191_, v_sz_192_, v___x_193_, v_init_188_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn(lean_object* v_00_u03b1_195_, lean_object* v_00_u03b2_196_, lean_object* v_00_u03b4_197_, lean_object* v_m_198_, lean_object* v_inst_199_, lean_object* v_f_200_, lean_object* v_init_201_, lean_object* v_b_202_){
_start:
{
lean_object* v_buckets_203_; lean_object* v___f_204_; size_t v_sz_205_; size_t v___x_206_; lean_object* v___x_207_; 
v_buckets_203_ = lean_ctor_get(v_b_202_, 1);
lean_inc_ref(v_buckets_203_);
lean_dec_ref(v_b_202_);
lean_inc_ref(v_inst_199_);
v___f_204_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_204_, 0, v_inst_199_);
lean_closure_set(v___f_204_, 1, v_f_200_);
v_sz_205_ = lean_array_size(v_buckets_203_);
v___x_206_ = ((size_t)0ULL);
v___x_207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_199_, v_buckets_203_, v___f_204_, v_sz_205_, v___x_206_, v_init_201_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__0(lean_object* v_f_208_, lean_object* v_x_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___y_210_);
lean_ctor_set(v___x_212_, 1, v___y_211_);
v___x_213_ = lean_apply_1(v_f_208_, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__2(lean_object* v_inst_214_, lean_object* v_m_215_, lean_object* v_f_216_){
_start:
{
lean_object* v_buckets_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_buckets_217_ = lean_ctor_get(v_m_215_, 1);
lean_inc_ref(v_buckets_217_);
lean_dec_ref(v_m_215_);
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_array_get_size(v_buckets_217_);
v___x_220_ = lean_box(0);
v___x_221_ = lean_nat_dec_lt(v___x_218_, v___x_219_);
if (v___x_221_ == 0)
{
lean_object* v_toApplicative_222_; lean_object* v_toPure_223_; lean_object* v___x_224_; 
lean_dec_ref(v_buckets_217_);
lean_dec(v_f_216_);
v_toApplicative_222_ = lean_ctor_get(v_inst_214_, 0);
lean_inc_ref(v_toApplicative_222_);
lean_dec_ref(v_inst_214_);
v_toPure_223_ = lean_ctor_get(v_toApplicative_222_, 1);
lean_inc(v_toPure_223_);
lean_dec_ref(v_toApplicative_222_);
v___x_224_ = lean_apply_2(v_toPure_223_, lean_box(0), v___x_220_);
return v___x_224_;
}
else
{
lean_object* v___f_225_; lean_object* v___f_226_; uint8_t v___x_227_; 
v___f_225_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_225_, 0, v_f_216_);
lean_inc_ref(v_inst_214_);
v___f_226_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_226_, 0, v_inst_214_);
lean_closure_set(v___f_226_, 1, v___f_225_);
v___x_227_ = lean_nat_dec_le(v___x_219_, v___x_219_);
if (v___x_227_ == 0)
{
if (v___x_221_ == 0)
{
lean_object* v_toApplicative_228_; lean_object* v_toPure_229_; lean_object* v___x_230_; 
lean_dec_ref(v___f_226_);
lean_dec_ref(v_buckets_217_);
v_toApplicative_228_ = lean_ctor_get(v_inst_214_, 0);
lean_inc_ref(v_toApplicative_228_);
lean_dec_ref(v_inst_214_);
v_toPure_229_ = lean_ctor_get(v_toApplicative_228_, 1);
lean_inc(v_toPure_229_);
lean_dec_ref(v_toApplicative_228_);
v___x_230_ = lean_apply_2(v_toPure_229_, lean_box(0), v___x_220_);
return v___x_230_;
}
else
{
size_t v___x_231_; size_t v___x_232_; lean_object* v___x_233_; 
v___x_231_ = ((size_t)0ULL);
v___x_232_ = lean_usize_of_nat(v___x_219_);
v___x_233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_214_, v___f_226_, v_buckets_217_, v___x_231_, v___x_232_, v___x_220_);
return v___x_233_;
}
}
else
{
size_t v___x_234_; size_t v___x_235_; lean_object* v___x_236_; 
v___x_234_ = ((size_t)0ULL);
v___x_235_ = lean_usize_of_nat(v___x_219_);
v___x_236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_214_, v___f_226_, v_buckets_217_, v___x_234_, v___x_235_, v___x_220_);
return v___x_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg(lean_object* v_inst_237_){
_start:
{
lean_object* v___f_238_; 
v___f_238_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_238_, 0, v_inst_237_);
return v___f_238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad(lean_object* v_00_u03b1_239_, lean_object* v_00_u03b2_240_, lean_object* v_m_241_, lean_object* v_inst_242_){
_start:
{
lean_object* v___f_243_; 
v___f_243_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_243_, 0, v_inst_242_);
return v___f_243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_244_, lean_object* v_a_245_, lean_object* v_b_246_, lean_object* v_acc_247_){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v_a_245_);
lean_ctor_set(v___x_248_, 1, v_b_246_);
v___x_249_ = lean_apply_2(v_f_244_, v___x_248_, v_acc_247_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1(lean_object* v_inst_250_, lean_object* v___f_251_, lean_object* v_a_252_, lean_object* v_x_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_250_, v___f_251_, v_a_252_, v___y_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_256_, lean_object* v_00_u03b2_257_, lean_object* v_m_258_, lean_object* v_init_259_, lean_object* v_f_260_){
_start:
{
lean_object* v_buckets_261_; lean_object* v___f_262_; lean_object* v___f_263_; size_t v_sz_264_; size_t v___x_265_; lean_object* v___x_266_; 
v_buckets_261_ = lean_ctor_get(v_m_258_, 1);
lean_inc_ref(v_buckets_261_);
lean_dec_ref(v_m_258_);
v___f_262_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_262_, 0, v_f_260_);
lean_inc_ref(v_inst_256_);
v___f_263_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_263_, 0, v_inst_256_);
lean_closure_set(v___f_263_, 1, v___f_262_);
v_sz_264_ = lean_array_size(v_buckets_261_);
v___x_265_ = ((size_t)0ULL);
v___x_266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_256_, v_buckets_261_, v___f_263_, v_sz_264_, v___x_265_, v_init_259_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg(lean_object* v_inst_267_){
_start:
{
lean_object* v___f_268_; 
v___f_268_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_268_, 0, v_inst_267_);
return v___f_268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad(lean_object* v_00_u03b1_269_, lean_object* v_00_u03b2_270_, lean_object* v_m_271_, lean_object* v_inst_272_){
_start:
{
lean_object* v___f_273_; 
v___f_273_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_273_, 0, v_inst_272_);
return v___f_273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___lam__0(lean_object* v_p_274_, lean_object* v___x_275_, lean_object* v___x_276_, lean_object* v_a_277_, lean_object* v_b_278_, lean_object* v_acc_279_){
_start:
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = lean_apply_2(v_p_274_, v_a_277_, v_b_278_);
v___x_281_ = lean_unbox(v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec_ref(v___x_276_);
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v___x_275_);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; 
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_276_);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_286_, lean_object* v___x_287_, lean_object* v___x_288_, lean_object* v_a_289_, lean_object* v_b_290_, lean_object* v_acc_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Std_DHashMap_Raw_all___redArg___lam__0(v_p_286_, v___x_287_, v___x_288_, v_a_289_, v_b_290_, v_acc_291_);
lean_dec_ref(v_acc_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___lam__1(lean_object* v___x_293_, lean_object* v___f_294_, lean_object* v_a_295_, lean_object* v_x_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_293_, v___f_294_, v_a_295_, v___y_297_);
return v___x_298_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_all___redArg(lean_object* v_m_302_, lean_object* v_p_303_){
_start:
{
lean_object* v___x_304_; lean_object* v_buckets_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___f_308_; lean_object* v___f_309_; size_t v_sz_310_; size_t v___x_311_; lean_object* v___x_312_; lean_object* v_fst_313_; 
v___x_304_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v_buckets_305_ = lean_ctor_get(v_m_302_, 1);
lean_inc_ref(v_buckets_305_);
lean_dec_ref(v_m_302_);
v___x_306_ = lean_box(0);
v___x_307_ = ((lean_object*)(l_Std_DHashMap_Raw_all___redArg___closed__0));
v___f_308_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_308_, 0, v_p_303_);
lean_closure_set(v___f_308_, 1, v___x_306_);
lean_closure_set(v___f_308_, 2, v___x_307_);
v___f_309_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_309_, 0, v___x_304_);
lean_closure_set(v___f_309_, 1, v___f_308_);
v_sz_310_ = lean_array_size(v_buckets_305_);
v___x_311_ = ((size_t)0ULL);
v___x_312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_304_, v_buckets_305_, v___f_309_, v_sz_310_, v___x_311_, v___x_307_);
v_fst_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_fst_313_);
lean_dec(v___x_312_);
if (lean_obj_tag(v_fst_313_) == 0)
{
uint8_t v___x_314_; 
v___x_314_ = 1;
return v___x_314_;
}
else
{
lean_object* v_val_315_; uint8_t v___x_316_; 
v_val_315_ = lean_ctor_get(v_fst_313_, 0);
lean_inc(v_val_315_);
lean_dec_ref(v_fst_313_);
v___x_316_ = lean_unbox(v_val_315_);
lean_dec(v_val_315_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___boxed(lean_object* v_m_317_, lean_object* v_p_318_){
_start:
{
uint8_t v_res_319_; lean_object* v_r_320_; 
v_res_319_ = l_Std_DHashMap_Raw_all___redArg(v_m_317_, v_p_318_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_all(lean_object* v_00_u03b1_321_, lean_object* v_00_u03b2_322_, lean_object* v_m_323_, lean_object* v_p_324_){
_start:
{
lean_object* v___x_325_; lean_object* v_buckets_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___f_329_; lean_object* v___f_330_; size_t v_sz_331_; size_t v___x_332_; lean_object* v___x_333_; lean_object* v_fst_334_; 
v___x_325_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v_buckets_326_ = lean_ctor_get(v_m_323_, 1);
lean_inc_ref(v_buckets_326_);
lean_dec_ref(v_m_323_);
v___x_327_ = lean_box(0);
v___x_328_ = ((lean_object*)(l_Std_DHashMap_Raw_all___redArg___closed__0));
v___f_329_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_329_, 0, v_p_324_);
lean_closure_set(v___f_329_, 1, v___x_327_);
lean_closure_set(v___f_329_, 2, v___x_328_);
v___f_330_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_330_, 0, v___x_325_);
lean_closure_set(v___f_330_, 1, v___f_329_);
v_sz_331_ = lean_array_size(v_buckets_326_);
v___x_332_ = ((size_t)0ULL);
v___x_333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_325_, v_buckets_326_, v___f_330_, v_sz_331_, v___x_332_, v___x_328_);
v_fst_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_fst_334_);
lean_dec(v___x_333_);
if (lean_obj_tag(v_fst_334_) == 0)
{
uint8_t v___x_335_; 
v___x_335_ = 1;
return v___x_335_;
}
else
{
lean_object* v_val_336_; uint8_t v___x_337_; 
v_val_336_ = lean_ctor_get(v_fst_334_, 0);
lean_inc(v_val_336_);
lean_dec_ref(v_fst_334_);
v___x_337_ = lean_unbox(v_val_336_);
lean_dec(v_val_336_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___boxed(lean_object* v_00_u03b1_338_, lean_object* v_00_u03b2_339_, lean_object* v_m_340_, lean_object* v_p_341_){
_start:
{
uint8_t v_res_342_; lean_object* v_r_343_; 
v_res_342_ = l_Std_DHashMap_Raw_all(v_00_u03b1_338_, v_00_u03b2_339_, v_m_340_, v_p_341_);
v_r_343_ = lean_box(v_res_342_);
return v_r_343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___redArg___lam__0(lean_object* v_p_344_, lean_object* v___x_345_, lean_object* v___x_346_, lean_object* v_a_347_, lean_object* v_b_348_, lean_object* v_acc_349_){
_start:
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = lean_apply_2(v_p_344_, v_a_347_, v_b_348_);
v___x_351_ = lean_unbox(v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
v___x_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_345_);
return v___x_352_;
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec_ref(v___x_345_);
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_350_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___x_346_);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_356_, lean_object* v___x_357_, lean_object* v___x_358_, lean_object* v_a_359_, lean_object* v_b_360_, lean_object* v_acc_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Std_DHashMap_Raw_any___redArg___lam__0(v_p_356_, v___x_357_, v___x_358_, v_a_359_, v_b_360_, v_acc_361_);
lean_dec_ref(v_acc_361_);
return v_res_362_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_any___redArg(lean_object* v_m_363_, lean_object* v_p_364_){
_start:
{
lean_object* v___x_365_; lean_object* v_buckets_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___f_369_; lean_object* v___f_370_; size_t v_sz_371_; size_t v___x_372_; lean_object* v___x_373_; lean_object* v_fst_374_; 
v___x_365_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v_buckets_366_ = lean_ctor_get(v_m_363_, 1);
lean_inc_ref(v_buckets_366_);
lean_dec_ref(v_m_363_);
v___x_367_ = lean_box(0);
v___x_368_ = ((lean_object*)(l_Std_DHashMap_Raw_all___redArg___closed__0));
v___f_369_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_369_, 0, v_p_364_);
lean_closure_set(v___f_369_, 1, v___x_368_);
lean_closure_set(v___f_369_, 2, v___x_367_);
v___f_370_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_370_, 0, v___x_365_);
lean_closure_set(v___f_370_, 1, v___f_369_);
v_sz_371_ = lean_array_size(v_buckets_366_);
v___x_372_ = ((size_t)0ULL);
v___x_373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_365_, v_buckets_366_, v___f_370_, v_sz_371_, v___x_372_, v___x_368_);
v_fst_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_fst_374_);
lean_dec(v___x_373_);
if (lean_obj_tag(v_fst_374_) == 0)
{
uint8_t v___x_375_; 
v___x_375_ = 0;
return v___x_375_;
}
else
{
lean_object* v_val_376_; uint8_t v___x_377_; 
v_val_376_ = lean_ctor_get(v_fst_374_, 0);
lean_inc(v_val_376_);
lean_dec_ref(v_fst_374_);
v___x_377_ = lean_unbox(v_val_376_);
lean_dec(v_val_376_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___redArg___boxed(lean_object* v_m_378_, lean_object* v_p_379_){
_start:
{
uint8_t v_res_380_; lean_object* v_r_381_; 
v_res_380_ = l_Std_DHashMap_Raw_any___redArg(v_m_378_, v_p_379_);
v_r_381_ = lean_box(v_res_380_);
return v_r_381_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_any(lean_object* v_00_u03b1_382_, lean_object* v_00_u03b2_383_, lean_object* v_m_384_, lean_object* v_p_385_){
_start:
{
lean_object* v___x_386_; lean_object* v_buckets_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___f_390_; lean_object* v___f_391_; size_t v_sz_392_; size_t v___x_393_; lean_object* v___x_394_; lean_object* v_fst_395_; 
v___x_386_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v_buckets_387_ = lean_ctor_get(v_m_384_, 1);
lean_inc_ref(v_buckets_387_);
lean_dec_ref(v_m_384_);
v___x_388_ = lean_box(0);
v___x_389_ = ((lean_object*)(l_Std_DHashMap_Raw_all___redArg___closed__0));
v___f_390_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_390_, 0, v_p_385_);
lean_closure_set(v___f_390_, 1, v___x_389_);
lean_closure_set(v___f_390_, 2, v___x_388_);
v___f_391_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_391_, 0, v___x_386_);
lean_closure_set(v___f_391_, 1, v___f_390_);
v_sz_392_ = lean_array_size(v_buckets_387_);
v___x_393_ = ((size_t)0ULL);
v___x_394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_386_, v_buckets_387_, v___f_391_, v_sz_392_, v___x_393_, v___x_389_);
v_fst_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_fst_395_);
lean_dec(v___x_394_);
if (lean_obj_tag(v_fst_395_) == 0)
{
uint8_t v___x_396_; 
v___x_396_ = 0;
return v___x_396_;
}
else
{
lean_object* v_val_397_; uint8_t v___x_398_; 
v_val_397_ = lean_ctor_get(v_fst_395_, 0);
lean_inc(v_val_397_);
lean_dec_ref(v_fst_395_);
v___x_398_ = lean_unbox(v_val_397_);
lean_dec(v_val_397_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___boxed(lean_object* v_00_u03b1_399_, lean_object* v_00_u03b2_400_, lean_object* v_m_401_, lean_object* v_p_402_){
_start:
{
uint8_t v_res_403_; lean_object* v_r_404_; 
v_res_403_ = l_Std_DHashMap_Raw_any(v_00_u03b1_399_, v_00_u03b2_400_, v_m_401_, v_p_402_);
v_r_404_ = lean_box(v_res_403_);
return v_r_404_;
}
}
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_RawDef(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
