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
lean_object* v___f_17_; uint8_t v___x_18_; 
lean_inc_ref(v_inst_6_);
v___f_17_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_17_, 0, v_inst_6_);
lean_closure_set(v___f_17_, 1, v_f_7_);
v___x_18_ = lean_nat_dec_le(v___x_14_, v___x_14_);
if (v___x_18_ == 0)
{
if (v___x_15_ == 0)
{
lean_object* v___x_19_; 
lean_inc(v_toPure_12_);
lean_dec_ref(v___f_17_);
lean_dec_ref(v_buckets_11_);
lean_dec_ref(v_inst_6_);
v___x_19_ = lean_apply_2(v_toPure_12_, lean_box(0), v_init_8_);
return v___x_19_;
}
else
{
size_t v___x_20_; size_t v___x_21_; lean_object* v___x_22_; 
v___x_20_ = ((size_t)0ULL);
v___x_21_ = lean_usize_of_nat(v___x_14_);
v___x_22_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_6_, v___f_17_, v_buckets_11_, v___x_20_, v___x_21_, v_init_8_);
return v___x_22_;
}
}
else
{
size_t v___x_23_; size_t v___x_24_; lean_object* v___x_25_; 
v___x_23_ = ((size_t)0ULL);
v___x_24_ = lean_usize_of_nat(v___x_14_);
v___x_25_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_6_, v___f_17_, v_buckets_11_, v___x_23_, v___x_24_, v_init_8_);
return v___x_25_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM(lean_object* v_00_u03b1_26_, lean_object* v_00_u03b2_27_, lean_object* v_00_u03b4_28_, lean_object* v_m_29_, lean_object* v_inst_30_, lean_object* v_f_31_, lean_object* v_init_32_, lean_object* v_b_33_){
_start:
{
lean_object* v_toApplicative_34_; lean_object* v_buckets_35_; lean_object* v_toPure_36_; lean_object* v___x_37_; lean_object* v___x_38_; uint8_t v___x_39_; 
v_toApplicative_34_ = lean_ctor_get(v_inst_30_, 0);
v_buckets_35_ = lean_ctor_get(v_b_33_, 1);
lean_inc_ref(v_buckets_35_);
lean_dec_ref(v_b_33_);
v_toPure_36_ = lean_ctor_get(v_toApplicative_34_, 1);
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = lean_array_get_size(v_buckets_35_);
v___x_39_ = lean_nat_dec_lt(v___x_37_, v___x_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; 
lean_inc(v_toPure_36_);
lean_dec_ref(v_buckets_35_);
lean_dec(v_f_31_);
lean_dec_ref(v_inst_30_);
v___x_40_ = lean_apply_2(v_toPure_36_, lean_box(0), v_init_32_);
return v___x_40_;
}
else
{
lean_object* v___f_41_; uint8_t v___x_42_; 
lean_inc_ref(v_inst_30_);
v___f_41_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_41_, 0, v_inst_30_);
lean_closure_set(v___f_41_, 1, v_f_31_);
v___x_42_ = lean_nat_dec_le(v___x_38_, v___x_38_);
if (v___x_42_ == 0)
{
if (v___x_39_ == 0)
{
lean_object* v___x_43_; 
lean_inc(v_toPure_36_);
lean_dec_ref(v___f_41_);
lean_dec_ref(v_buckets_35_);
lean_dec_ref(v_inst_30_);
v___x_43_ = lean_apply_2(v_toPure_36_, lean_box(0), v_init_32_);
return v___x_43_;
}
else
{
size_t v___x_44_; size_t v___x_45_; lean_object* v___x_46_; 
v___x_44_ = ((size_t)0ULL);
v___x_45_ = lean_usize_of_nat(v___x_38_);
v___x_46_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_30_, v___f_41_, v_buckets_35_, v___x_44_, v___x_45_, v_init_32_);
return v___x_46_;
}
}
else
{
size_t v___x_47_; size_t v___x_48_; lean_object* v___x_49_; 
v___x_47_ = ((size_t)0ULL);
v___x_48_ = lean_usize_of_nat(v___x_38_);
v___x_49_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_30_, v___f_41_, v_buckets_35_, v___x_47_, v___x_48_, v_init_32_);
return v___x_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold___redArg___lam__0(lean_object* v_f_50_, lean_object* v_x1_51_, lean_object* v_x2_52_, lean_object* v_x3_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lean_apply_3(v_f_50_, v_x1_51_, v_x2_52_, v_x3_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold___redArg___lam__1(lean_object* v___x_55_, lean_object* v___f_56_, lean_object* v_acc_57_, lean_object* v_l_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_55_, v___f_56_, v_acc_57_, v_l_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold___redArg(lean_object* v_f_79_, lean_object* v_init_80_, lean_object* v_b_81_){
_start:
{
lean_object* v___x_82_; lean_object* v_buckets_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_82_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v_buckets_83_ = lean_ctor_get(v_b_81_, 1);
lean_inc_ref(v_buckets_83_);
lean_dec_ref(v_b_81_);
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = lean_array_get_size(v_buckets_83_);
v___x_86_ = lean_nat_dec_lt(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
lean_dec_ref(v_buckets_83_);
lean_dec(v_f_79_);
return v_init_80_;
}
else
{
lean_object* v___f_87_; lean_object* v___f_88_; size_t v___x_89_; size_t v___x_90_; lean_object* v___x_91_; 
v___f_87_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_87_, 0, v_f_79_);
v___f_88_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_88_, 0, v___x_82_);
lean_closure_set(v___f_88_, 1, v___f_87_);
v___x_89_ = ((size_t)0ULL);
v___x_90_ = lean_usize_of_nat(v___x_85_);
v___x_91_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_82_, v___f_88_, v_buckets_83_, v___x_89_, v___x_90_, v_init_80_);
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_fold(lean_object* v_00_u03b1_92_, lean_object* v_00_u03b2_93_, lean_object* v_00_u03b4_94_, lean_object* v_f_95_, lean_object* v_init_96_, lean_object* v_b_97_){
_start:
{
lean_object* v___x_98_; lean_object* v_buckets_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_98_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v_buckets_99_ = lean_ctor_get(v_b_97_, 1);
lean_inc_ref(v_buckets_99_);
lean_dec_ref(v_b_97_);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_array_get_size(v_buckets_99_);
v___x_102_ = lean_nat_dec_lt(v___x_100_, v___x_101_);
if (v___x_102_ == 0)
{
lean_dec_ref(v_buckets_99_);
lean_dec(v_f_95_);
return v_init_96_;
}
else
{
lean_object* v___f_103_; lean_object* v___f_104_; size_t v___x_105_; size_t v___x_106_; lean_object* v___x_107_; 
v___f_103_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_103_, 0, v_f_95_);
v___f_104_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_104_, 0, v___x_98_);
lean_closure_set(v___f_104_, 1, v___f_103_);
v___x_105_ = ((size_t)0ULL);
v___x_106_ = lean_usize_of_nat(v___x_101_);
v___x_107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_98_, v___f_104_, v_buckets_99_, v___x_105_, v___x_106_, v_init_96_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM___redArg___lam__0(lean_object* v_f_108_, lean_object* v_x_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_apply_2(v_f_108_, v___y_110_, v___y_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM___redArg___lam__1(lean_object* v_inst_113_, lean_object* v___f_114_, lean_object* v_x_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_box(0);
v___x_118_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_113_, v___f_114_, v___x_117_, v___y_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM___redArg(lean_object* v_inst_119_, lean_object* v_f_120_, lean_object* v_b_121_){
_start:
{
lean_object* v_toApplicative_122_; lean_object* v_buckets_123_; lean_object* v_toPure_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v_toApplicative_122_ = lean_ctor_get(v_inst_119_, 0);
v_buckets_123_ = lean_ctor_get(v_b_121_, 1);
lean_inc_ref(v_buckets_123_);
lean_dec_ref(v_b_121_);
v_toPure_124_ = lean_ctor_get(v_toApplicative_122_, 1);
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_array_get_size(v_buckets_123_);
v___x_127_ = lean_box(0);
v___x_128_ = lean_nat_dec_lt(v___x_125_, v___x_126_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
lean_inc(v_toPure_124_);
lean_dec_ref(v_buckets_123_);
lean_dec(v_f_120_);
lean_dec_ref(v_inst_119_);
v___x_129_ = lean_apply_2(v_toPure_124_, lean_box(0), v___x_127_);
return v___x_129_;
}
else
{
lean_object* v___f_130_; lean_object* v___f_131_; uint8_t v___x_132_; 
v___f_130_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_130_, 0, v_f_120_);
lean_inc_ref(v_inst_119_);
v___f_131_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_131_, 0, v_inst_119_);
lean_closure_set(v___f_131_, 1, v___f_130_);
v___x_132_ = lean_nat_dec_le(v___x_126_, v___x_126_);
if (v___x_132_ == 0)
{
if (v___x_128_ == 0)
{
lean_object* v___x_133_; 
lean_inc(v_toPure_124_);
lean_dec_ref(v___f_131_);
lean_dec_ref(v_buckets_123_);
lean_dec_ref(v_inst_119_);
v___x_133_ = lean_apply_2(v_toPure_124_, lean_box(0), v___x_127_);
return v___x_133_;
}
else
{
size_t v___x_134_; size_t v___x_135_; lean_object* v___x_136_; 
v___x_134_ = ((size_t)0ULL);
v___x_135_ = lean_usize_of_nat(v___x_126_);
v___x_136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_119_, v___f_131_, v_buckets_123_, v___x_134_, v___x_135_, v___x_127_);
return v___x_136_;
}
}
else
{
size_t v___x_137_; size_t v___x_138_; lean_object* v___x_139_; 
v___x_137_ = ((size_t)0ULL);
v___x_138_ = lean_usize_of_nat(v___x_126_);
v___x_139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_119_, v___f_131_, v_buckets_123_, v___x_137_, v___x_138_, v___x_127_);
return v___x_139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forM(lean_object* v_00_u03b1_140_, lean_object* v_00_u03b2_141_, lean_object* v_m_142_, lean_object* v_inst_143_, lean_object* v_f_144_, lean_object* v_b_145_){
_start:
{
lean_object* v_toApplicative_146_; lean_object* v_buckets_147_; lean_object* v_toPure_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v_toApplicative_146_ = lean_ctor_get(v_inst_143_, 0);
v_buckets_147_ = lean_ctor_get(v_b_145_, 1);
lean_inc_ref(v_buckets_147_);
lean_dec_ref(v_b_145_);
v_toPure_148_ = lean_ctor_get(v_toApplicative_146_, 1);
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = lean_array_get_size(v_buckets_147_);
v___x_151_ = lean_box(0);
v___x_152_ = lean_nat_dec_lt(v___x_149_, v___x_150_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; 
lean_inc(v_toPure_148_);
lean_dec_ref(v_buckets_147_);
lean_dec(v_f_144_);
lean_dec_ref(v_inst_143_);
v___x_153_ = lean_apply_2(v_toPure_148_, lean_box(0), v___x_151_);
return v___x_153_;
}
else
{
lean_object* v___f_154_; lean_object* v___f_155_; uint8_t v___x_156_; 
v___f_154_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_154_, 0, v_f_144_);
lean_inc_ref(v_inst_143_);
v___f_155_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_155_, 0, v_inst_143_);
lean_closure_set(v___f_155_, 1, v___f_154_);
v___x_156_ = lean_nat_dec_le(v___x_150_, v___x_150_);
if (v___x_156_ == 0)
{
if (v___x_152_ == 0)
{
lean_object* v___x_157_; 
lean_inc(v_toPure_148_);
lean_dec_ref(v___f_155_);
lean_dec_ref(v_buckets_147_);
lean_dec_ref(v_inst_143_);
v___x_157_ = lean_apply_2(v_toPure_148_, lean_box(0), v___x_151_);
return v___x_157_;
}
else
{
size_t v___x_158_; size_t v___x_159_; lean_object* v___x_160_; 
v___x_158_ = ((size_t)0ULL);
v___x_159_ = lean_usize_of_nat(v___x_150_);
v___x_160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_143_, v___f_155_, v_buckets_147_, v___x_158_, v___x_159_, v___x_151_);
return v___x_160_;
}
}
else
{
size_t v___x_161_; size_t v___x_162_; lean_object* v___x_163_; 
v___x_161_ = ((size_t)0ULL);
v___x_162_ = lean_usize_of_nat(v___x_150_);
v___x_163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_143_, v___f_155_, v_buckets_147_, v___x_161_, v___x_162_, v___x_151_);
return v___x_163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___redArg___lam__0(lean_object* v_inst_164_, lean_object* v_f_165_, lean_object* v_a_166_, lean_object* v_x_167_, lean_object* v___y_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_164_, v_f_165_, v_a_166_, v___y_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn___redArg(lean_object* v_inst_170_, lean_object* v_f_171_, lean_object* v_init_172_, lean_object* v_b_173_){
_start:
{
lean_object* v_buckets_174_; lean_object* v___f_175_; size_t v_sz_176_; size_t v___x_177_; lean_object* v___x_178_; 
v_buckets_174_ = lean_ctor_get(v_b_173_, 1);
lean_inc_ref(v_buckets_174_);
lean_dec_ref(v_b_173_);
lean_inc_ref(v_inst_170_);
v___f_175_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_175_, 0, v_inst_170_);
lean_closure_set(v___f_175_, 1, v_f_171_);
v_sz_176_ = lean_array_size(v_buckets_174_);
v___x_177_ = ((size_t)0ULL);
v___x_178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_170_, v_buckets_174_, v___f_175_, v_sz_176_, v___x_177_, v_init_172_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_forIn(lean_object* v_00_u03b1_179_, lean_object* v_00_u03b2_180_, lean_object* v_00_u03b4_181_, lean_object* v_m_182_, lean_object* v_inst_183_, lean_object* v_f_184_, lean_object* v_init_185_, lean_object* v_b_186_){
_start:
{
lean_object* v_buckets_187_; lean_object* v___f_188_; size_t v_sz_189_; size_t v___x_190_; lean_object* v___x_191_; 
v_buckets_187_ = lean_ctor_get(v_b_186_, 1);
lean_inc_ref(v_buckets_187_);
lean_dec_ref(v_b_186_);
lean_inc_ref(v_inst_183_);
v___f_188_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_188_, 0, v_inst_183_);
lean_closure_set(v___f_188_, 1, v_f_184_);
v_sz_189_ = lean_array_size(v_buckets_187_);
v___x_190_ = ((size_t)0ULL);
v___x_191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_183_, v_buckets_187_, v___f_188_, v_sz_189_, v___x_190_, v_init_185_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__0(lean_object* v_f_192_, lean_object* v_x_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___y_194_);
lean_ctor_set(v___x_196_, 1, v___y_195_);
v___x_197_ = lean_apply_1(v_f_192_, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__2(lean_object* v_inst_198_, lean_object* v_m_199_, lean_object* v_f_200_){
_start:
{
lean_object* v_toApplicative_201_; lean_object* v_buckets_202_; lean_object* v_toPure_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v_toApplicative_201_ = lean_ctor_get(v_inst_198_, 0);
v_buckets_202_ = lean_ctor_get(v_m_199_, 1);
lean_inc_ref(v_buckets_202_);
lean_dec_ref(v_m_199_);
v_toPure_203_ = lean_ctor_get(v_toApplicative_201_, 1);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_array_get_size(v_buckets_202_);
v___x_206_ = lean_box(0);
v___x_207_ = lean_nat_dec_lt(v___x_204_, v___x_205_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; 
lean_inc(v_toPure_203_);
lean_dec_ref(v_buckets_202_);
lean_dec(v_f_200_);
lean_dec_ref(v_inst_198_);
v___x_208_ = lean_apply_2(v_toPure_203_, lean_box(0), v___x_206_);
return v___x_208_;
}
else
{
lean_object* v___f_209_; lean_object* v___f_210_; size_t v___x_211_; size_t v___x_212_; lean_object* v___x_213_; 
v___f_209_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_209_, 0, v_f_200_);
lean_inc_ref(v_inst_198_);
v___f_210_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_210_, 0, v_inst_198_);
lean_closure_set(v___f_210_, 1, v___f_209_);
v___x_211_ = ((size_t)0ULL);
v___x_212_ = lean_usize_of_nat(v___x_205_);
v___x_213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_198_, v___f_210_, v_buckets_202_, v___x_211_, v___x_212_, v___x_206_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg(lean_object* v_inst_214_){
_start:
{
lean_object* v___f_215_; 
v___f_215_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_215_, 0, v_inst_214_);
return v___f_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForMSigmaOfMonad(lean_object* v_00_u03b1_216_, lean_object* v_00_u03b2_217_, lean_object* v_m_218_, lean_object* v_inst_219_){
_start:
{
lean_object* v___f_220_; 
v___f_220_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForMSigmaOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_220_, 0, v_inst_219_);
return v___f_220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_221_, lean_object* v_a_222_, lean_object* v_b_223_, lean_object* v_acc_224_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v_a_222_);
lean_ctor_set(v___x_225_, 1, v_b_223_);
v___x_226_ = lean_apply_2(v_f_221_, v___x_225_, v_acc_224_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1(lean_object* v_inst_227_, lean_object* v___f_228_, lean_object* v_a_229_, lean_object* v_x_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_227_, v___f_228_, v_a_229_, v___y_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_233_, lean_object* v_00_u03b2_234_, lean_object* v_m_235_, lean_object* v_init_236_, lean_object* v_f_237_){
_start:
{
lean_object* v_buckets_238_; lean_object* v___f_239_; lean_object* v___f_240_; size_t v_sz_241_; size_t v___x_242_; lean_object* v___x_243_; 
v_buckets_238_ = lean_ctor_get(v_m_235_, 1);
lean_inc_ref(v_buckets_238_);
lean_dec_ref(v_m_235_);
v___f_239_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_239_, 0, v_f_237_);
lean_inc_ref(v_inst_233_);
v___f_240_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_240_, 0, v_inst_233_);
lean_closure_set(v___f_240_, 1, v___f_239_);
v_sz_241_ = lean_array_size(v_buckets_238_);
v___x_242_ = ((size_t)0ULL);
v___x_243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_233_, v_buckets_238_, v___f_240_, v_sz_241_, v___x_242_, v_init_236_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg(lean_object* v_inst_244_){
_start:
{
lean_object* v___f_245_; 
v___f_245_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_245_, 0, v_inst_244_);
return v___f_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad(lean_object* v_00_u03b1_246_, lean_object* v_00_u03b2_247_, lean_object* v_m_248_, lean_object* v_inst_249_){
_start:
{
lean_object* v___f_250_; 
v___f_250_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_250_, 0, v_inst_249_);
return v___f_250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___lam__0(lean_object* v_p_251_, lean_object* v___x_252_, lean_object* v___x_253_, lean_object* v_a_254_, lean_object* v_b_255_, lean_object* v_acc_256_){
_start:
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_apply_2(v_p_251_, v_a_254_, v_b_255_);
v___x_258_ = lean_unbox(v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec_ref(v___x_253_);
v___x_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_257_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___x_252_);
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
return v___x_261_;
}
else
{
lean_object* v___x_262_; 
v___x_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_253_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_263_, lean_object* v___x_264_, lean_object* v___x_265_, lean_object* v_a_266_, lean_object* v_b_267_, lean_object* v_acc_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Std_DHashMap_Raw_all___redArg___lam__0(v_p_263_, v___x_264_, v___x_265_, v_a_266_, v_b_267_, v_acc_268_);
lean_dec_ref(v_acc_268_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___lam__1(lean_object* v___x_270_, lean_object* v___f_271_, lean_object* v_a_272_, lean_object* v_x_273_, lean_object* v___y_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_270_, v___f_271_, v_a_272_, v___y_274_);
return v___x_275_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_all___redArg(lean_object* v_m_279_, lean_object* v_p_280_){
_start:
{
lean_object* v___x_281_; lean_object* v_buckets_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___f_285_; lean_object* v___f_286_; size_t v_sz_287_; size_t v___x_288_; lean_object* v___x_289_; lean_object* v_fst_290_; 
v___x_281_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v_buckets_282_ = lean_ctor_get(v_m_279_, 1);
lean_inc_ref(v_buckets_282_);
lean_dec_ref(v_m_279_);
v___x_283_ = lean_box(0);
v___x_284_ = ((lean_object*)(l_Std_DHashMap_Raw_all___redArg___closed__0));
v___f_285_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_285_, 0, v_p_280_);
lean_closure_set(v___f_285_, 1, v___x_283_);
lean_closure_set(v___f_285_, 2, v___x_284_);
v___f_286_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_286_, 0, v___x_281_);
lean_closure_set(v___f_286_, 1, v___f_285_);
v_sz_287_ = lean_array_size(v_buckets_282_);
v___x_288_ = ((size_t)0ULL);
v___x_289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_281_, v_buckets_282_, v___f_286_, v_sz_287_, v___x_288_, v___x_284_);
v_fst_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_fst_290_);
lean_dec(v___x_289_);
if (lean_obj_tag(v_fst_290_) == 0)
{
uint8_t v___x_291_; 
v___x_291_ = 1;
return v___x_291_;
}
else
{
lean_object* v_val_292_; uint8_t v___x_293_; 
v_val_292_ = lean_ctor_get(v_fst_290_, 0);
lean_inc(v_val_292_);
lean_dec_ref_known(v_fst_290_, 1);
v___x_293_ = lean_unbox(v_val_292_);
lean_dec(v_val_292_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___redArg___boxed(lean_object* v_m_294_, lean_object* v_p_295_){
_start:
{
uint8_t v_res_296_; lean_object* v_r_297_; 
v_res_296_ = l_Std_DHashMap_Raw_all___redArg(v_m_294_, v_p_295_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_all(lean_object* v_00_u03b1_298_, lean_object* v_00_u03b2_299_, lean_object* v_m_300_, lean_object* v_p_301_){
_start:
{
lean_object* v___x_302_; lean_object* v_buckets_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___f_306_; lean_object* v___f_307_; size_t v_sz_308_; size_t v___x_309_; lean_object* v___x_310_; lean_object* v_fst_311_; 
v___x_302_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v_buckets_303_ = lean_ctor_get(v_m_300_, 1);
lean_inc_ref(v_buckets_303_);
lean_dec_ref(v_m_300_);
v___x_304_ = lean_box(0);
v___x_305_ = ((lean_object*)(l_Std_DHashMap_Raw_all___redArg___closed__0));
v___f_306_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_306_, 0, v_p_301_);
lean_closure_set(v___f_306_, 1, v___x_304_);
lean_closure_set(v___f_306_, 2, v___x_305_);
v___f_307_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_307_, 0, v___x_302_);
lean_closure_set(v___f_307_, 1, v___f_306_);
v_sz_308_ = lean_array_size(v_buckets_303_);
v___x_309_ = ((size_t)0ULL);
v___x_310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_302_, v_buckets_303_, v___f_307_, v_sz_308_, v___x_309_, v___x_305_);
v_fst_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_fst_311_);
lean_dec(v___x_310_);
if (lean_obj_tag(v_fst_311_) == 0)
{
uint8_t v___x_312_; 
v___x_312_ = 1;
return v___x_312_;
}
else
{
lean_object* v_val_313_; uint8_t v___x_314_; 
v_val_313_ = lean_ctor_get(v_fst_311_, 0);
lean_inc(v_val_313_);
lean_dec_ref_known(v_fst_311_, 1);
v___x_314_ = lean_unbox(v_val_313_);
lean_dec(v_val_313_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_all___boxed(lean_object* v_00_u03b1_315_, lean_object* v_00_u03b2_316_, lean_object* v_m_317_, lean_object* v_p_318_){
_start:
{
uint8_t v_res_319_; lean_object* v_r_320_; 
v_res_319_ = l_Std_DHashMap_Raw_all(v_00_u03b1_315_, v_00_u03b2_316_, v_m_317_, v_p_318_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___redArg___lam__0(lean_object* v_p_321_, lean_object* v___x_322_, lean_object* v___x_323_, lean_object* v_a_324_, lean_object* v_b_325_, lean_object* v_acc_326_){
_start:
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = lean_apply_2(v_p_321_, v_a_324_, v_b_325_);
v___x_328_ = lean_unbox(v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_322_);
return v___x_329_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec_ref(v___x_322_);
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_327_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___x_323_);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_333_, lean_object* v___x_334_, lean_object* v___x_335_, lean_object* v_a_336_, lean_object* v_b_337_, lean_object* v_acc_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Std_DHashMap_Raw_any___redArg___lam__0(v_p_333_, v___x_334_, v___x_335_, v_a_336_, v_b_337_, v_acc_338_);
lean_dec_ref(v_acc_338_);
return v_res_339_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_any___redArg(lean_object* v_m_340_, lean_object* v_p_341_){
_start:
{
lean_object* v___x_342_; lean_object* v_buckets_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___f_346_; lean_object* v___f_347_; size_t v_sz_348_; size_t v___x_349_; lean_object* v___x_350_; lean_object* v_fst_351_; 
v___x_342_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v_buckets_343_ = lean_ctor_get(v_m_340_, 1);
lean_inc_ref(v_buckets_343_);
lean_dec_ref(v_m_340_);
v___x_344_ = lean_box(0);
v___x_345_ = ((lean_object*)(l_Std_DHashMap_Raw_all___redArg___closed__0));
v___f_346_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_346_, 0, v_p_341_);
lean_closure_set(v___f_346_, 1, v___x_345_);
lean_closure_set(v___f_346_, 2, v___x_344_);
v___f_347_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_347_, 0, v___x_342_);
lean_closure_set(v___f_347_, 1, v___f_346_);
v_sz_348_ = lean_array_size(v_buckets_343_);
v___x_349_ = ((size_t)0ULL);
v___x_350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_342_, v_buckets_343_, v___f_347_, v_sz_348_, v___x_349_, v___x_345_);
v_fst_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_fst_351_);
lean_dec(v___x_350_);
if (lean_obj_tag(v_fst_351_) == 0)
{
uint8_t v___x_352_; 
v___x_352_ = 0;
return v___x_352_;
}
else
{
lean_object* v_val_353_; uint8_t v___x_354_; 
v_val_353_ = lean_ctor_get(v_fst_351_, 0);
lean_inc(v_val_353_);
lean_dec_ref_known(v_fst_351_, 1);
v___x_354_ = lean_unbox(v_val_353_);
lean_dec(v_val_353_);
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___redArg___boxed(lean_object* v_m_355_, lean_object* v_p_356_){
_start:
{
uint8_t v_res_357_; lean_object* v_r_358_; 
v_res_357_ = l_Std_DHashMap_Raw_any___redArg(v_m_355_, v_p_356_);
v_r_358_ = lean_box(v_res_357_);
return v_r_358_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_any(lean_object* v_00_u03b1_359_, lean_object* v_00_u03b2_360_, lean_object* v_m_361_, lean_object* v_p_362_){
_start:
{
lean_object* v___x_363_; lean_object* v_buckets_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___f_367_; lean_object* v___f_368_; size_t v_sz_369_; size_t v___x_370_; lean_object* v___x_371_; lean_object* v_fst_372_; 
v___x_363_ = ((lean_object*)(l_Std_DHashMap_Raw_fold___redArg___closed__9));
v_buckets_364_ = lean_ctor_get(v_m_361_, 1);
lean_inc_ref(v_buckets_364_);
lean_dec_ref(v_m_361_);
v___x_365_ = lean_box(0);
v___x_366_ = ((lean_object*)(l_Std_DHashMap_Raw_all___redArg___closed__0));
v___f_367_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_367_, 0, v_p_362_);
lean_closure_set(v___f_367_, 1, v___x_366_);
lean_closure_set(v___f_367_, 2, v___x_365_);
v___f_368_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_368_, 0, v___x_363_);
lean_closure_set(v___f_368_, 1, v___f_367_);
v_sz_369_ = lean_array_size(v_buckets_364_);
v___x_370_ = ((size_t)0ULL);
v___x_371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_363_, v_buckets_364_, v___f_368_, v_sz_369_, v___x_370_, v___x_366_);
v_fst_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_fst_372_);
lean_dec(v___x_371_);
if (lean_obj_tag(v_fst_372_) == 0)
{
uint8_t v___x_373_; 
v___x_373_ = 0;
return v___x_373_;
}
else
{
lean_object* v_val_374_; uint8_t v___x_375_; 
v_val_374_ = lean_ctor_get(v_fst_372_, 0);
lean_inc(v_val_374_);
lean_dec_ref_known(v_fst_372_, 1);
v___x_375_ = lean_unbox(v_val_374_);
lean_dec(v_val_374_);
return v___x_375_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_any___boxed(lean_object* v_00_u03b1_376_, lean_object* v_00_u03b2_377_, lean_object* v_m_378_, lean_object* v_p_379_){
_start:
{
uint8_t v_res_380_; lean_object* v_r_381_; 
v_res_380_ = l_Std_DHashMap_Raw_any(v_00_u03b1_376_, v_00_u03b2_377_, v_m_378_, v_p_379_);
v_r_381_ = lean_box(v_res_380_);
return v_r_381_;
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
