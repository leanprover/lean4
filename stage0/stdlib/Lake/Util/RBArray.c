// Lean compiler output
// Module: Lake.Util.RBArray
// Imports: public import Std.Data.TreeMap.Basic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_RBArray_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_RBArray_empty___closed__0 = (const lean_object*)&l_Lake_RBArray_empty___closed__0_value;
static const lean_ctor_object l_Lake_RBArray_empty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lake_RBArray_empty___closed__0_value)}};
static const lean_object* l_Lake_RBArray_empty___closed__1 = (const lean_object*)&l_Lake_RBArray_empty___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_RBArray_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_mkEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_mkEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_mkEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_mkEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_RBArray_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_RBArray_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_RBArray_all___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_all___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_RBArray_all___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_RBArray_all___redArg___closed__0 = (const lean_object*)&l_Lake_RBArray_all___redArg___closed__0_value;
static const lean_closure_object l_Lake_RBArray_all___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_RBArray_all___redArg___closed__1 = (const lean_object*)&l_Lake_RBArray_all___redArg___closed__1_value;
static const lean_closure_object l_Lake_RBArray_all___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_RBArray_all___redArg___closed__2 = (const lean_object*)&l_Lake_RBArray_all___redArg___closed__2_value;
static const lean_closure_object l_Lake_RBArray_all___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_RBArray_all___redArg___closed__3 = (const lean_object*)&l_Lake_RBArray_all___redArg___closed__3_value;
static const lean_closure_object l_Lake_RBArray_all___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_RBArray_all___redArg___closed__4 = (const lean_object*)&l_Lake_RBArray_all___redArg___closed__4_value;
static const lean_closure_object l_Lake_RBArray_all___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_RBArray_all___redArg___closed__5 = (const lean_object*)&l_Lake_RBArray_all___redArg___closed__5_value;
static const lean_closure_object l_Lake_RBArray_all___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_RBArray_all___redArg___closed__6 = (const lean_object*)&l_Lake_RBArray_all___redArg___closed__6_value;
static const lean_ctor_object l_Lake_RBArray_all___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_RBArray_all___redArg___closed__0_value),((lean_object*)&l_Lake_RBArray_all___redArg___closed__1_value)}};
static const lean_object* l_Lake_RBArray_all___redArg___closed__7 = (const lean_object*)&l_Lake_RBArray_all___redArg___closed__7_value;
static const lean_ctor_object l_Lake_RBArray_all___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_RBArray_all___redArg___closed__7_value),((lean_object*)&l_Lake_RBArray_all___redArg___closed__2_value),((lean_object*)&l_Lake_RBArray_all___redArg___closed__3_value),((lean_object*)&l_Lake_RBArray_all___redArg___closed__4_value),((lean_object*)&l_Lake_RBArray_all___redArg___closed__5_value)}};
static const lean_object* l_Lake_RBArray_all___redArg___closed__8 = (const lean_object*)&l_Lake_RBArray_all___redArg___closed__8_value;
static const lean_ctor_object l_Lake_RBArray_all___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_RBArray_all___redArg___closed__8_value),((lean_object*)&l_Lake_RBArray_all___redArg___closed__6_value)}};
static const lean_object* l_Lake_RBArray_all___redArg___closed__9 = (const lean_object*)&l_Lake_RBArray_all___redArg___closed__9_value;
LEAN_EXPORT uint8_t l_Lake_RBArray_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_RBArray_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_RBArray_any___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_any___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_RBArray_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_RBArray_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_foldr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_foldr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_foldrM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkRBArray___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkRBArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkRBArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_empty(lean_object* v_00_u03b1_6_, lean_object* v_00_u03b2_7_, lean_object* v_cmp_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = ((lean_object*)(l_Lake_RBArray_empty___closed__1));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_empty___boxed(lean_object* v_00_u03b1_10_, lean_object* v_00_u03b2_11_, lean_object* v_cmp_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lake_RBArray_empty(v_00_u03b1_10_, v_00_u03b2_11_, v_cmp_12_);
lean_dec_ref(v_cmp_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg(lean_object* v_cmp_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lake_RBArray_empty(lean_box(0), lean_box(0), v_cmp_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg___boxed(lean_object* v_cmp_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg(v_cmp_16_);
lean_dec_ref(v_cmp_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection(lean_object* v_00_u03b1_18_, lean_object* v_00_u03b2_19_, lean_object* v_cmp_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lake_RBArray_empty(lean_box(0), lean_box(0), v_cmp_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___boxed(lean_object* v_00_u03b1_22_, lean_object* v_00_u03b2_23_, lean_object* v_cmp_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection(v_00_u03b1_22_, v_00_u03b2_23_, v_cmp_24_);
lean_dec_ref(v_cmp_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_mkEmpty___redArg(lean_object* v_size_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_box(1);
v___x_28_ = lean_mk_empty_array_with_capacity(v_size_26_);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_27_);
lean_ctor_set(v___x_29_, 1, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_mkEmpty___redArg___boxed(lean_object* v_size_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lake_RBArray_mkEmpty___redArg(v_size_30_);
lean_dec(v_size_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_mkEmpty(lean_object* v_00_u03b1_32_, lean_object* v_00_u03b2_33_, lean_object* v_cmp_34_, lean_object* v_size_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lake_RBArray_mkEmpty___redArg(v_size_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_mkEmpty___boxed(lean_object* v_00_u03b1_37_, lean_object* v_00_u03b2_38_, lean_object* v_cmp_39_, lean_object* v_size_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lake_RBArray_mkEmpty(v_00_u03b1_37_, v_00_u03b2_38_, v_cmp_39_, v_size_40_);
lean_dec(v_size_40_);
lean_dec_ref(v_cmp_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_find_x3f___redArg(lean_object* v_cmp_42_, lean_object* v_self_43_, lean_object* v_a_44_){
_start:
{
lean_object* v_toTreeMap_45_; lean_object* v___x_46_; 
v_toTreeMap_45_ = lean_ctor_get(v_self_43_, 0);
lean_inc(v_toTreeMap_45_);
lean_dec_ref(v_self_43_);
v___x_46_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_42_, v_toTreeMap_45_, v_a_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_find_x3f(lean_object* v_00_u03b1_47_, lean_object* v_00_u03b2_48_, lean_object* v_cmp_49_, lean_object* v_self_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_toTreeMap_52_; lean_object* v___x_53_; 
v_toTreeMap_52_ = lean_ctor_get(v_self_50_, 0);
lean_inc(v_toTreeMap_52_);
lean_dec_ref(v_self_50_);
v___x_53_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_49_, v_toTreeMap_52_, v_a_51_);
return v___x_53_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_contains___redArg(lean_object* v_cmp_54_, lean_object* v_self_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_toTreeMap_57_; uint8_t v___x_58_; 
v_toTreeMap_57_ = lean_ctor_get(v_self_55_, 0);
lean_inc(v_toTreeMap_57_);
lean_dec_ref(v_self_55_);
v___x_58_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_54_, v_a_56_, v_toTreeMap_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_contains___redArg___boxed(lean_object* v_cmp_59_, lean_object* v_self_60_, lean_object* v_a_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l_Lake_RBArray_contains___redArg(v_cmp_59_, v_self_60_, v_a_61_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_contains(lean_object* v_00_u03b1_64_, lean_object* v_00_u03b2_65_, lean_object* v_cmp_66_, lean_object* v_self_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_toTreeMap_69_; uint8_t v___x_70_; 
v_toTreeMap_69_ = lean_ctor_get(v_self_67_, 0);
lean_inc(v_toTreeMap_69_);
lean_dec_ref(v_self_67_);
v___x_70_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_66_, v_a_68_, v_toTreeMap_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_contains___boxed(lean_object* v_00_u03b1_71_, lean_object* v_00_u03b2_72_, lean_object* v_cmp_73_, lean_object* v_self_74_, lean_object* v_a_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Lake_RBArray_contains(v_00_u03b1_71_, v_00_u03b2_72_, v_cmp_73_, v_self_74_, v_a_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(lean_object* v_cmp_78_, lean_object* v_k_79_, lean_object* v_v_80_, lean_object* v_t_81_){
_start:
{
if (lean_obj_tag(v_t_81_) == 0)
{
lean_object* v_size_82_; lean_object* v_k_83_; lean_object* v_v_84_; lean_object* v_l_85_; lean_object* v_r_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_367_; 
v_size_82_ = lean_ctor_get(v_t_81_, 0);
v_k_83_ = lean_ctor_get(v_t_81_, 1);
v_v_84_ = lean_ctor_get(v_t_81_, 2);
v_l_85_ = lean_ctor_get(v_t_81_, 3);
v_r_86_ = lean_ctor_get(v_t_81_, 4);
v_isSharedCheck_367_ = !lean_is_exclusive(v_t_81_);
if (v_isSharedCheck_367_ == 0)
{
v___x_88_ = v_t_81_;
v_isShared_89_ = v_isSharedCheck_367_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_r_86_);
lean_inc(v_l_85_);
lean_inc(v_v_84_);
lean_inc(v_k_83_);
lean_inc(v_size_82_);
lean_dec(v_t_81_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_367_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; uint8_t v___x_91_; 
lean_inc_ref(v_cmp_78_);
lean_inc(v_k_83_);
lean_inc(v_k_79_);
v___x_90_ = lean_apply_2(v_cmp_78_, v_k_79_, v_k_83_);
v___x_91_ = lean_unbox(v___x_90_);
switch(v___x_91_)
{
case 0:
{
lean_object* v_impl_92_; lean_object* v___x_93_; 
lean_dec(v_size_82_);
v_impl_92_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_78_, v_k_79_, v_v_80_, v_l_85_);
v___x_93_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_86_) == 0)
{
lean_object* v_size_94_; lean_object* v_size_95_; lean_object* v_k_96_; lean_object* v_v_97_; lean_object* v_l_98_; lean_object* v_r_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v_size_94_ = lean_ctor_get(v_r_86_, 0);
v_size_95_ = lean_ctor_get(v_impl_92_, 0);
lean_inc(v_size_95_);
v_k_96_ = lean_ctor_get(v_impl_92_, 1);
lean_inc(v_k_96_);
v_v_97_ = lean_ctor_get(v_impl_92_, 2);
lean_inc(v_v_97_);
v_l_98_ = lean_ctor_get(v_impl_92_, 3);
lean_inc(v_l_98_);
v_r_99_ = lean_ctor_get(v_impl_92_, 4);
lean_inc(v_r_99_);
v___x_100_ = lean_unsigned_to_nat(3u);
v___x_101_ = lean_nat_mul(v___x_100_, v_size_94_);
v___x_102_ = lean_nat_dec_lt(v___x_101_, v_size_95_);
lean_dec(v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
lean_dec(v_r_99_);
lean_dec(v_l_98_);
lean_dec(v_v_97_);
lean_dec(v_k_96_);
v___x_103_ = lean_nat_add(v___x_93_, v_size_95_);
lean_dec(v_size_95_);
v___x_104_ = lean_nat_add(v___x_103_, v_size_94_);
lean_dec(v___x_103_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 3, v_impl_92_);
lean_ctor_set(v___x_88_, 0, v___x_104_);
v___x_106_ = v___x_88_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_107_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_107_, 3, v_impl_92_);
lean_ctor_set(v_reuseFailAlloc_107_, 4, v_r_86_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
else
{
lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_173_; 
v_isSharedCheck_173_ = !lean_is_exclusive(v_impl_92_);
if (v_isSharedCheck_173_ == 0)
{
lean_object* v_unused_174_; lean_object* v_unused_175_; lean_object* v_unused_176_; lean_object* v_unused_177_; lean_object* v_unused_178_; 
v_unused_174_ = lean_ctor_get(v_impl_92_, 4);
lean_dec(v_unused_174_);
v_unused_175_ = lean_ctor_get(v_impl_92_, 3);
lean_dec(v_unused_175_);
v_unused_176_ = lean_ctor_get(v_impl_92_, 2);
lean_dec(v_unused_176_);
v_unused_177_ = lean_ctor_get(v_impl_92_, 1);
lean_dec(v_unused_177_);
v_unused_178_ = lean_ctor_get(v_impl_92_, 0);
lean_dec(v_unused_178_);
v___x_109_ = v_impl_92_;
v_isShared_110_ = v_isSharedCheck_173_;
goto v_resetjp_108_;
}
else
{
lean_dec(v_impl_92_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_173_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v_size_111_; lean_object* v_size_112_; lean_object* v_k_113_; lean_object* v_v_114_; lean_object* v_l_115_; lean_object* v_r_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v_size_111_ = lean_ctor_get(v_l_98_, 0);
v_size_112_ = lean_ctor_get(v_r_99_, 0);
v_k_113_ = lean_ctor_get(v_r_99_, 1);
v_v_114_ = lean_ctor_get(v_r_99_, 2);
v_l_115_ = lean_ctor_get(v_r_99_, 3);
v_r_116_ = lean_ctor_get(v_r_99_, 4);
v___x_117_ = lean_unsigned_to_nat(2u);
v___x_118_ = lean_nat_mul(v___x_117_, v_size_111_);
v___x_119_ = lean_nat_dec_lt(v_size_112_, v___x_118_);
lean_dec(v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_148_; 
lean_inc(v_r_116_);
lean_inc(v_l_115_);
lean_inc(v_v_114_);
lean_inc(v_k_113_);
v_isSharedCheck_148_ = !lean_is_exclusive(v_r_99_);
if (v_isSharedCheck_148_ == 0)
{
lean_object* v_unused_149_; lean_object* v_unused_150_; lean_object* v_unused_151_; lean_object* v_unused_152_; lean_object* v_unused_153_; 
v_unused_149_ = lean_ctor_get(v_r_99_, 4);
lean_dec(v_unused_149_);
v_unused_150_ = lean_ctor_get(v_r_99_, 3);
lean_dec(v_unused_150_);
v_unused_151_ = lean_ctor_get(v_r_99_, 2);
lean_dec(v_unused_151_);
v_unused_152_ = lean_ctor_get(v_r_99_, 1);
lean_dec(v_unused_152_);
v_unused_153_ = lean_ctor_get(v_r_99_, 0);
lean_dec(v_unused_153_);
v___x_121_ = v_r_99_;
v_isShared_122_ = v_isSharedCheck_148_;
goto v_resetjp_120_;
}
else
{
lean_dec(v_r_99_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_148_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___y_126_; lean_object* v___y_127_; lean_object* v___y_128_; lean_object* v___x_136_; lean_object* v___y_138_; 
v___x_123_ = lean_nat_add(v___x_93_, v_size_95_);
lean_dec(v_size_95_);
v___x_124_ = lean_nat_add(v___x_123_, v_size_94_);
lean_dec(v___x_123_);
v___x_136_ = lean_nat_add(v___x_93_, v_size_111_);
if (lean_obj_tag(v_l_115_) == 0)
{
lean_object* v_size_146_; 
v_size_146_ = lean_ctor_get(v_l_115_, 0);
lean_inc(v_size_146_);
v___y_138_ = v_size_146_;
goto v___jp_137_;
}
else
{
lean_object* v___x_147_; 
v___x_147_ = lean_unsigned_to_nat(0u);
v___y_138_ = v___x_147_;
goto v___jp_137_;
}
v___jp_125_:
{
lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_129_ = lean_nat_add(v___y_127_, v___y_128_);
lean_dec(v___y_128_);
lean_dec(v___y_127_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 4, v_r_86_);
lean_ctor_set(v___x_121_, 3, v_r_116_);
lean_ctor_set(v___x_121_, 2, v_v_84_);
lean_ctor_set(v___x_121_, 1, v_k_83_);
lean_ctor_set(v___x_121_, 0, v___x_129_);
v___x_131_ = v___x_121_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_135_, 3, v_r_116_);
lean_ctor_set(v_reuseFailAlloc_135_, 4, v_r_86_);
v___x_131_ = v_reuseFailAlloc_135_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_133_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 4, v___x_131_);
lean_ctor_set(v___x_109_, 3, v___y_126_);
lean_ctor_set(v___x_109_, 2, v_v_114_);
lean_ctor_set(v___x_109_, 1, v_k_113_);
lean_ctor_set(v___x_109_, 0, v___x_124_);
v___x_133_ = v___x_109_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_k_113_);
lean_ctor_set(v_reuseFailAlloc_134_, 2, v_v_114_);
lean_ctor_set(v_reuseFailAlloc_134_, 3, v___y_126_);
lean_ctor_set(v_reuseFailAlloc_134_, 4, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
v___jp_137_:
{
lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_139_ = lean_nat_add(v___x_136_, v___y_138_);
lean_dec(v___y_138_);
lean_dec(v___x_136_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v_l_115_);
lean_ctor_set(v___x_88_, 3, v_l_98_);
lean_ctor_set(v___x_88_, 2, v_v_97_);
lean_ctor_set(v___x_88_, 1, v_k_96_);
lean_ctor_set(v___x_88_, 0, v___x_139_);
v___x_141_ = v___x_88_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_k_96_);
lean_ctor_set(v_reuseFailAlloc_145_, 2, v_v_97_);
lean_ctor_set(v_reuseFailAlloc_145_, 3, v_l_98_);
lean_ctor_set(v_reuseFailAlloc_145_, 4, v_l_115_);
v___x_141_ = v_reuseFailAlloc_145_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; 
v___x_142_ = lean_nat_add(v___x_93_, v_size_94_);
if (lean_obj_tag(v_r_116_) == 0)
{
lean_object* v_size_143_; 
v_size_143_ = lean_ctor_get(v_r_116_, 0);
lean_inc(v_size_143_);
v___y_126_ = v___x_141_;
v___y_127_ = v___x_142_;
v___y_128_ = v_size_143_;
goto v___jp_125_;
}
else
{
lean_object* v___x_144_; 
v___x_144_ = lean_unsigned_to_nat(0u);
v___y_126_ = v___x_141_;
v___y_127_ = v___x_142_;
v___y_128_ = v___x_144_;
goto v___jp_125_;
}
}
}
}
}
else
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_159_; 
lean_del_object(v___x_88_);
v___x_154_ = lean_nat_add(v___x_93_, v_size_95_);
lean_dec(v_size_95_);
v___x_155_ = lean_nat_add(v___x_154_, v_size_94_);
lean_dec(v___x_154_);
v___x_156_ = lean_nat_add(v___x_93_, v_size_94_);
v___x_157_ = lean_nat_add(v___x_156_, v_size_112_);
lean_dec(v___x_156_);
lean_inc_ref(v_r_86_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 4, v_r_86_);
lean_ctor_set(v___x_109_, 3, v_r_99_);
lean_ctor_set(v___x_109_, 2, v_v_84_);
lean_ctor_set(v___x_109_, 1, v_k_83_);
lean_ctor_set(v___x_109_, 0, v___x_157_);
v___x_159_ = v___x_109_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_157_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_172_, 3, v_r_99_);
lean_ctor_set(v_reuseFailAlloc_172_, 4, v_r_86_);
v___x_159_ = v_reuseFailAlloc_172_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
v_isSharedCheck_166_ = !lean_is_exclusive(v_r_86_);
if (v_isSharedCheck_166_ == 0)
{
lean_object* v_unused_167_; lean_object* v_unused_168_; lean_object* v_unused_169_; lean_object* v_unused_170_; lean_object* v_unused_171_; 
v_unused_167_ = lean_ctor_get(v_r_86_, 4);
lean_dec(v_unused_167_);
v_unused_168_ = lean_ctor_get(v_r_86_, 3);
lean_dec(v_unused_168_);
v_unused_169_ = lean_ctor_get(v_r_86_, 2);
lean_dec(v_unused_169_);
v_unused_170_ = lean_ctor_get(v_r_86_, 1);
lean_dec(v_unused_170_);
v_unused_171_ = lean_ctor_get(v_r_86_, 0);
lean_dec(v_unused_171_);
v___x_161_ = v_r_86_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_dec(v_r_86_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 4, v___x_159_);
lean_ctor_set(v___x_161_, 3, v_l_98_);
lean_ctor_set(v___x_161_, 2, v_v_97_);
lean_ctor_set(v___x_161_, 1, v_k_96_);
lean_ctor_set(v___x_161_, 0, v___x_155_);
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_k_96_);
lean_ctor_set(v_reuseFailAlloc_165_, 2, v_v_97_);
lean_ctor_set(v_reuseFailAlloc_165_, 3, v_l_98_);
lean_ctor_set(v_reuseFailAlloc_165_, 4, v___x_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_179_; 
v_l_179_ = lean_ctor_get(v_impl_92_, 3);
lean_inc(v_l_179_);
if (lean_obj_tag(v_l_179_) == 0)
{
lean_object* v_r_180_; lean_object* v_k_181_; lean_object* v_v_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_193_; 
v_r_180_ = lean_ctor_get(v_impl_92_, 4);
v_k_181_ = lean_ctor_get(v_impl_92_, 1);
v_v_182_ = lean_ctor_get(v_impl_92_, 2);
v_isSharedCheck_193_ = !lean_is_exclusive(v_impl_92_);
if (v_isSharedCheck_193_ == 0)
{
lean_object* v_unused_194_; lean_object* v_unused_195_; 
v_unused_194_ = lean_ctor_get(v_impl_92_, 3);
lean_dec(v_unused_194_);
v_unused_195_ = lean_ctor_get(v_impl_92_, 0);
lean_dec(v_unused_195_);
v___x_184_ = v_impl_92_;
v_isShared_185_ = v_isSharedCheck_193_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_r_180_);
lean_inc(v_v_182_);
lean_inc(v_k_181_);
lean_dec(v_impl_92_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_193_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_186_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_180_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 3, v_r_180_);
lean_ctor_set(v___x_184_, 2, v_v_84_);
lean_ctor_set(v___x_184_, 1, v_k_83_);
lean_ctor_set(v___x_184_, 0, v___x_93_);
v___x_188_ = v___x_184_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_192_, 3, v_r_180_);
lean_ctor_set(v_reuseFailAlloc_192_, 4, v_r_180_);
v___x_188_ = v_reuseFailAlloc_192_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_190_; 
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v___x_188_);
lean_ctor_set(v___x_88_, 3, v_l_179_);
lean_ctor_set(v___x_88_, 2, v_v_182_);
lean_ctor_set(v___x_88_, 1, v_k_181_);
lean_ctor_set(v___x_88_, 0, v___x_186_);
v___x_190_ = v___x_88_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_k_181_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_v_182_);
lean_ctor_set(v_reuseFailAlloc_191_, 3, v_l_179_);
lean_ctor_set(v_reuseFailAlloc_191_, 4, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_object* v_r_196_; 
v_r_196_ = lean_ctor_get(v_impl_92_, 4);
lean_inc(v_r_196_);
if (lean_obj_tag(v_r_196_) == 0)
{
lean_object* v_k_197_; lean_object* v_v_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_221_; 
v_k_197_ = lean_ctor_get(v_impl_92_, 1);
v_v_198_ = lean_ctor_get(v_impl_92_, 2);
v_isSharedCheck_221_ = !lean_is_exclusive(v_impl_92_);
if (v_isSharedCheck_221_ == 0)
{
lean_object* v_unused_222_; lean_object* v_unused_223_; lean_object* v_unused_224_; 
v_unused_222_ = lean_ctor_get(v_impl_92_, 4);
lean_dec(v_unused_222_);
v_unused_223_ = lean_ctor_get(v_impl_92_, 3);
lean_dec(v_unused_223_);
v_unused_224_ = lean_ctor_get(v_impl_92_, 0);
lean_dec(v_unused_224_);
v___x_200_ = v_impl_92_;
v_isShared_201_ = v_isSharedCheck_221_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_v_198_);
lean_inc(v_k_197_);
lean_dec(v_impl_92_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_221_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v_k_202_; lean_object* v_v_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_217_; 
v_k_202_ = lean_ctor_get(v_r_196_, 1);
v_v_203_ = lean_ctor_get(v_r_196_, 2);
v_isSharedCheck_217_ = !lean_is_exclusive(v_r_196_);
if (v_isSharedCheck_217_ == 0)
{
lean_object* v_unused_218_; lean_object* v_unused_219_; lean_object* v_unused_220_; 
v_unused_218_ = lean_ctor_get(v_r_196_, 4);
lean_dec(v_unused_218_);
v_unused_219_ = lean_ctor_get(v_r_196_, 3);
lean_dec(v_unused_219_);
v_unused_220_ = lean_ctor_get(v_r_196_, 0);
lean_dec(v_unused_220_);
v___x_205_ = v_r_196_;
v_isShared_206_ = v_isSharedCheck_217_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_v_203_);
lean_inc(v_k_202_);
lean_dec(v_r_196_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_217_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_207_ = lean_unsigned_to_nat(3u);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 4, v_l_179_);
lean_ctor_set(v___x_205_, 3, v_l_179_);
lean_ctor_set(v___x_205_, 2, v_v_198_);
lean_ctor_set(v___x_205_, 1, v_k_197_);
lean_ctor_set(v___x_205_, 0, v___x_93_);
v___x_209_ = v___x_205_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_k_197_);
lean_ctor_set(v_reuseFailAlloc_216_, 2, v_v_198_);
lean_ctor_set(v_reuseFailAlloc_216_, 3, v_l_179_);
lean_ctor_set(v_reuseFailAlloc_216_, 4, v_l_179_);
v___x_209_ = v_reuseFailAlloc_216_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_211_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 4, v_l_179_);
lean_ctor_set(v___x_200_, 2, v_v_84_);
lean_ctor_set(v___x_200_, 1, v_k_83_);
lean_ctor_set(v___x_200_, 0, v___x_93_);
v___x_211_ = v___x_200_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v_l_179_);
lean_ctor_set(v_reuseFailAlloc_215_, 4, v_l_179_);
v___x_211_ = v_reuseFailAlloc_215_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_213_; 
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v___x_211_);
lean_ctor_set(v___x_88_, 3, v___x_209_);
lean_ctor_set(v___x_88_, 2, v_v_203_);
lean_ctor_set(v___x_88_, 1, v_k_202_);
lean_ctor_set(v___x_88_, 0, v___x_207_);
v___x_213_ = v___x_88_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_k_202_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v_v_203_);
lean_ctor_set(v_reuseFailAlloc_214_, 3, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_214_, 4, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
}
else
{
lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_225_ = lean_unsigned_to_nat(2u);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v_r_196_);
lean_ctor_set(v___x_88_, 3, v_impl_92_);
lean_ctor_set(v___x_88_, 0, v___x_225_);
v___x_227_ = v___x_88_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_228_, 3, v_impl_92_);
lean_ctor_set(v_reuseFailAlloc_228_, 4, v_r_196_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
case 1:
{
lean_object* v___x_230_; 
lean_dec(v_v_84_);
lean_dec(v_k_83_);
lean_dec_ref(v_cmp_78_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 2, v_v_80_);
lean_ctor_set(v___x_88_, 1, v_k_79_);
v___x_230_ = v___x_88_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_size_82_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_k_79_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_v_80_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v_l_85_);
lean_ctor_set(v_reuseFailAlloc_231_, 4, v_r_86_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
default: 
{
lean_object* v_impl_232_; lean_object* v___x_233_; 
lean_dec(v_size_82_);
v_impl_232_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_78_, v_k_79_, v_v_80_, v_r_86_);
v___x_233_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_85_) == 0)
{
lean_object* v_size_234_; lean_object* v_size_235_; lean_object* v_k_236_; lean_object* v_v_237_; lean_object* v_l_238_; lean_object* v_r_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_size_234_ = lean_ctor_get(v_l_85_, 0);
v_size_235_ = lean_ctor_get(v_impl_232_, 0);
lean_inc(v_size_235_);
v_k_236_ = lean_ctor_get(v_impl_232_, 1);
lean_inc(v_k_236_);
v_v_237_ = lean_ctor_get(v_impl_232_, 2);
lean_inc(v_v_237_);
v_l_238_ = lean_ctor_get(v_impl_232_, 3);
lean_inc(v_l_238_);
v_r_239_ = lean_ctor_get(v_impl_232_, 4);
lean_inc(v_r_239_);
v___x_240_ = lean_unsigned_to_nat(3u);
v___x_241_ = lean_nat_mul(v___x_240_, v_size_234_);
v___x_242_ = lean_nat_dec_lt(v___x_241_, v_size_235_);
lean_dec(v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
lean_dec(v_r_239_);
lean_dec(v_l_238_);
lean_dec(v_v_237_);
lean_dec(v_k_236_);
v___x_243_ = lean_nat_add(v___x_233_, v_size_234_);
v___x_244_ = lean_nat_add(v___x_243_, v_size_235_);
lean_dec(v_size_235_);
lean_dec(v___x_243_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v_impl_232_);
lean_ctor_set(v___x_88_, 0, v___x_244_);
v___x_246_ = v___x_88_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_247_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_247_, 3, v_l_85_);
lean_ctor_set(v_reuseFailAlloc_247_, 4, v_impl_232_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
else
{
lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_311_; 
v_isSharedCheck_311_ = !lean_is_exclusive(v_impl_232_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; lean_object* v_unused_313_; lean_object* v_unused_314_; lean_object* v_unused_315_; lean_object* v_unused_316_; 
v_unused_312_ = lean_ctor_get(v_impl_232_, 4);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_impl_232_, 3);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_impl_232_, 2);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_impl_232_, 1);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_impl_232_, 0);
lean_dec(v_unused_316_);
v___x_249_ = v_impl_232_;
v_isShared_250_ = v_isSharedCheck_311_;
goto v_resetjp_248_;
}
else
{
lean_dec(v_impl_232_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_311_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v_size_251_; lean_object* v_k_252_; lean_object* v_v_253_; lean_object* v_l_254_; lean_object* v_r_255_; lean_object* v_size_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v_size_251_ = lean_ctor_get(v_l_238_, 0);
v_k_252_ = lean_ctor_get(v_l_238_, 1);
v_v_253_ = lean_ctor_get(v_l_238_, 2);
v_l_254_ = lean_ctor_get(v_l_238_, 3);
v_r_255_ = lean_ctor_get(v_l_238_, 4);
v_size_256_ = lean_ctor_get(v_r_239_, 0);
v___x_257_ = lean_unsigned_to_nat(2u);
v___x_258_ = lean_nat_mul(v___x_257_, v_size_256_);
v___x_259_ = lean_nat_dec_lt(v_size_251_, v___x_258_);
lean_dec(v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_287_; 
lean_inc(v_r_255_);
lean_inc(v_l_254_);
lean_inc(v_v_253_);
lean_inc(v_k_252_);
v_isSharedCheck_287_ = !lean_is_exclusive(v_l_238_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; lean_object* v_unused_289_; lean_object* v_unused_290_; lean_object* v_unused_291_; lean_object* v_unused_292_; 
v_unused_288_ = lean_ctor_get(v_l_238_, 4);
lean_dec(v_unused_288_);
v_unused_289_ = lean_ctor_get(v_l_238_, 3);
lean_dec(v_unused_289_);
v_unused_290_ = lean_ctor_get(v_l_238_, 2);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_l_238_, 1);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_l_238_, 0);
lean_dec(v_unused_292_);
v___x_261_ = v_l_238_;
v_isShared_262_ = v_isSharedCheck_287_;
goto v_resetjp_260_;
}
else
{
lean_dec(v_l_238_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_287_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_277_; 
v___x_263_ = lean_nat_add(v___x_233_, v_size_234_);
v___x_264_ = lean_nat_add(v___x_263_, v_size_235_);
lean_dec(v_size_235_);
if (lean_obj_tag(v_l_254_) == 0)
{
lean_object* v_size_285_; 
v_size_285_ = lean_ctor_get(v_l_254_, 0);
lean_inc(v_size_285_);
v___y_277_ = v_size_285_;
goto v___jp_276_;
}
else
{
lean_object* v___x_286_; 
v___x_286_ = lean_unsigned_to_nat(0u);
v___y_277_ = v___x_286_;
goto v___jp_276_;
}
v___jp_265_:
{
lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_269_ = lean_nat_add(v___y_266_, v___y_268_);
lean_dec(v___y_268_);
lean_dec(v___y_266_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 4, v_r_239_);
lean_ctor_set(v___x_261_, 3, v_r_255_);
lean_ctor_set(v___x_261_, 2, v_v_237_);
lean_ctor_set(v___x_261_, 1, v_k_236_);
lean_ctor_set(v___x_261_, 0, v___x_269_);
v___x_271_ = v___x_261_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_k_236_);
lean_ctor_set(v_reuseFailAlloc_275_, 2, v_v_237_);
lean_ctor_set(v_reuseFailAlloc_275_, 3, v_r_255_);
lean_ctor_set(v_reuseFailAlloc_275_, 4, v_r_239_);
v___x_271_ = v_reuseFailAlloc_275_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_273_; 
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 4, v___x_271_);
lean_ctor_set(v___x_249_, 3, v___y_267_);
lean_ctor_set(v___x_249_, 2, v_v_253_);
lean_ctor_set(v___x_249_, 1, v_k_252_);
lean_ctor_set(v___x_249_, 0, v___x_264_);
v___x_273_ = v___x_249_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_k_252_);
lean_ctor_set(v_reuseFailAlloc_274_, 2, v_v_253_);
lean_ctor_set(v_reuseFailAlloc_274_, 3, v___y_267_);
lean_ctor_set(v_reuseFailAlloc_274_, 4, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
v___jp_276_:
{
lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_278_ = lean_nat_add(v___x_263_, v___y_277_);
lean_dec(v___y_277_);
lean_dec(v___x_263_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v_l_254_);
lean_ctor_set(v___x_88_, 0, v___x_278_);
v___x_280_ = v___x_88_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_284_, 3, v_l_85_);
lean_ctor_set(v_reuseFailAlloc_284_, 4, v_l_254_);
v___x_280_ = v_reuseFailAlloc_284_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v___x_281_; 
v___x_281_ = lean_nat_add(v___x_233_, v_size_256_);
if (lean_obj_tag(v_r_255_) == 0)
{
lean_object* v_size_282_; 
v_size_282_ = lean_ctor_get(v_r_255_, 0);
lean_inc(v_size_282_);
v___y_266_ = v___x_281_;
v___y_267_ = v___x_280_;
v___y_268_ = v_size_282_;
goto v___jp_265_;
}
else
{
lean_object* v___x_283_; 
v___x_283_ = lean_unsigned_to_nat(0u);
v___y_266_ = v___x_281_;
v___y_267_ = v___x_280_;
v___y_268_ = v___x_283_;
goto v___jp_265_;
}
}
}
}
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_297_; 
lean_del_object(v___x_88_);
v___x_293_ = lean_nat_add(v___x_233_, v_size_234_);
v___x_294_ = lean_nat_add(v___x_293_, v_size_235_);
lean_dec(v_size_235_);
v___x_295_ = lean_nat_add(v___x_293_, v_size_251_);
lean_dec(v___x_293_);
lean_inc_ref(v_l_85_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 4, v_l_238_);
lean_ctor_set(v___x_249_, 3, v_l_85_);
lean_ctor_set(v___x_249_, 2, v_v_84_);
lean_ctor_set(v___x_249_, 1, v_k_83_);
lean_ctor_set(v___x_249_, 0, v___x_295_);
v___x_297_ = v___x_249_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_310_, 3, v_l_85_);
lean_ctor_set(v_reuseFailAlloc_310_, 4, v_l_238_);
v___x_297_ = v_reuseFailAlloc_310_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
v_isSharedCheck_304_ = !lean_is_exclusive(v_l_85_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; lean_object* v_unused_306_; lean_object* v_unused_307_; lean_object* v_unused_308_; lean_object* v_unused_309_; 
v_unused_305_ = lean_ctor_get(v_l_85_, 4);
lean_dec(v_unused_305_);
v_unused_306_ = lean_ctor_get(v_l_85_, 3);
lean_dec(v_unused_306_);
v_unused_307_ = lean_ctor_get(v_l_85_, 2);
lean_dec(v_unused_307_);
v_unused_308_ = lean_ctor_get(v_l_85_, 1);
lean_dec(v_unused_308_);
v_unused_309_ = lean_ctor_get(v_l_85_, 0);
lean_dec(v_unused_309_);
v___x_299_ = v_l_85_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_dec(v_l_85_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 4, v_r_239_);
lean_ctor_set(v___x_299_, 3, v___x_297_);
lean_ctor_set(v___x_299_, 2, v_v_237_);
lean_ctor_set(v___x_299_, 1, v_k_236_);
lean_ctor_set(v___x_299_, 0, v___x_294_);
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_k_236_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_v_237_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_303_, 4, v_r_239_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_317_; 
v_l_317_ = lean_ctor_get(v_impl_232_, 3);
lean_inc(v_l_317_);
if (lean_obj_tag(v_l_317_) == 0)
{
lean_object* v_r_318_; lean_object* v_k_319_; lean_object* v_v_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_343_; 
v_r_318_ = lean_ctor_get(v_impl_232_, 4);
v_k_319_ = lean_ctor_get(v_impl_232_, 1);
v_v_320_ = lean_ctor_get(v_impl_232_, 2);
v_isSharedCheck_343_ = !lean_is_exclusive(v_impl_232_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; lean_object* v_unused_345_; 
v_unused_344_ = lean_ctor_get(v_impl_232_, 3);
lean_dec(v_unused_344_);
v_unused_345_ = lean_ctor_get(v_impl_232_, 0);
lean_dec(v_unused_345_);
v___x_322_ = v_impl_232_;
v_isShared_323_ = v_isSharedCheck_343_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_r_318_);
lean_inc(v_v_320_);
lean_inc(v_k_319_);
lean_dec(v_impl_232_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_343_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v_k_324_; lean_object* v_v_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_339_; 
v_k_324_ = lean_ctor_get(v_l_317_, 1);
v_v_325_ = lean_ctor_get(v_l_317_, 2);
v_isSharedCheck_339_ = !lean_is_exclusive(v_l_317_);
if (v_isSharedCheck_339_ == 0)
{
lean_object* v_unused_340_; lean_object* v_unused_341_; lean_object* v_unused_342_; 
v_unused_340_ = lean_ctor_get(v_l_317_, 4);
lean_dec(v_unused_340_);
v_unused_341_ = lean_ctor_get(v_l_317_, 3);
lean_dec(v_unused_341_);
v_unused_342_ = lean_ctor_get(v_l_317_, 0);
lean_dec(v_unused_342_);
v___x_327_ = v_l_317_;
v_isShared_328_ = v_isSharedCheck_339_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_v_325_);
lean_inc(v_k_324_);
lean_dec(v_l_317_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_339_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_329_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_318_, 2);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 4, v_r_318_);
lean_ctor_set(v___x_327_, 3, v_r_318_);
lean_ctor_set(v___x_327_, 2, v_v_84_);
lean_ctor_set(v___x_327_, 1, v_k_83_);
lean_ctor_set(v___x_327_, 0, v___x_233_);
v___x_331_ = v___x_327_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_338_, 3, v_r_318_);
lean_ctor_set(v_reuseFailAlloc_338_, 4, v_r_318_);
v___x_331_ = v_reuseFailAlloc_338_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_333_; 
lean_inc(v_r_318_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 3, v_r_318_);
lean_ctor_set(v___x_322_, 0, v___x_233_);
v___x_333_ = v___x_322_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v_r_318_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v_r_318_);
v___x_333_ = v_reuseFailAlloc_337_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_335_; 
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v___x_333_);
lean_ctor_set(v___x_88_, 3, v___x_331_);
lean_ctor_set(v___x_88_, 2, v_v_325_);
lean_ctor_set(v___x_88_, 1, v_k_324_);
lean_ctor_set(v___x_88_, 0, v___x_329_);
v___x_335_ = v___x_88_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_k_324_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_v_325_);
lean_ctor_set(v_reuseFailAlloc_336_, 3, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_336_, 4, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
}
else
{
lean_object* v_r_346_; 
v_r_346_ = lean_ctor_get(v_impl_232_, 4);
lean_inc(v_r_346_);
if (lean_obj_tag(v_r_346_) == 0)
{
lean_object* v_k_347_; lean_object* v_v_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_359_; 
v_k_347_ = lean_ctor_get(v_impl_232_, 1);
v_v_348_ = lean_ctor_get(v_impl_232_, 2);
v_isSharedCheck_359_ = !lean_is_exclusive(v_impl_232_);
if (v_isSharedCheck_359_ == 0)
{
lean_object* v_unused_360_; lean_object* v_unused_361_; lean_object* v_unused_362_; 
v_unused_360_ = lean_ctor_get(v_impl_232_, 4);
lean_dec(v_unused_360_);
v_unused_361_ = lean_ctor_get(v_impl_232_, 3);
lean_dec(v_unused_361_);
v_unused_362_ = lean_ctor_get(v_impl_232_, 0);
lean_dec(v_unused_362_);
v___x_350_ = v_impl_232_;
v_isShared_351_ = v_isSharedCheck_359_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_v_348_);
lean_inc(v_k_347_);
lean_dec(v_impl_232_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_359_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = lean_unsigned_to_nat(3u);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 4, v_l_317_);
lean_ctor_set(v___x_350_, 2, v_v_84_);
lean_ctor_set(v___x_350_, 1, v_k_83_);
lean_ctor_set(v___x_350_, 0, v___x_233_);
v___x_354_ = v___x_350_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_358_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_358_, 3, v_l_317_);
lean_ctor_set(v_reuseFailAlloc_358_, 4, v_l_317_);
v___x_354_ = v_reuseFailAlloc_358_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_356_; 
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v_r_346_);
lean_ctor_set(v___x_88_, 3, v___x_354_);
lean_ctor_set(v___x_88_, 2, v_v_348_);
lean_ctor_set(v___x_88_, 1, v_k_347_);
lean_ctor_set(v___x_88_, 0, v___x_352_);
v___x_356_ = v___x_88_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_k_347_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_v_348_);
lean_ctor_set(v_reuseFailAlloc_357_, 3, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_357_, 4, v_r_346_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
else
{
lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_363_ = lean_unsigned_to_nat(2u);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v_impl_232_);
lean_ctor_set(v___x_88_, 3, v_r_346_);
lean_ctor_set(v___x_88_, 0, v___x_363_);
v___x_365_ = v___x_88_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_366_, 3, v_r_346_);
lean_ctor_set(v_reuseFailAlloc_366_, 4, v_impl_232_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; 
lean_dec_ref(v_cmp_78_);
v___x_368_ = lean_unsigned_to_nat(1u);
v___x_369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v_k_79_);
lean_ctor_set(v___x_369_, 2, v_v_80_);
lean_ctor_set(v___x_369_, 3, v_t_81_);
lean_ctor_set(v___x_369_, 4, v_t_81_);
return v___x_369_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(lean_object* v_cmp_370_, lean_object* v_k_371_, lean_object* v_t_372_){
_start:
{
if (lean_obj_tag(v_t_372_) == 0)
{
lean_object* v_k_373_; lean_object* v_l_374_; lean_object* v_r_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_k_373_ = lean_ctor_get(v_t_372_, 1);
lean_inc(v_k_373_);
v_l_374_ = lean_ctor_get(v_t_372_, 3);
lean_inc(v_l_374_);
v_r_375_ = lean_ctor_get(v_t_372_, 4);
lean_inc(v_r_375_);
lean_dec_ref_known(v_t_372_, 5);
lean_inc_ref(v_cmp_370_);
lean_inc(v_k_371_);
v___x_376_ = lean_apply_2(v_cmp_370_, v_k_371_, v_k_373_);
v___x_377_ = lean_unbox(v___x_376_);
switch(v___x_377_)
{
case 0:
{
lean_dec(v_r_375_);
v_t_372_ = v_l_374_;
goto _start;
}
case 1:
{
uint8_t v___x_379_; 
lean_dec(v_r_375_);
lean_dec(v_l_374_);
lean_dec(v_k_371_);
lean_dec_ref(v_cmp_370_);
v___x_379_ = 1;
return v___x_379_;
}
default: 
{
lean_dec(v_l_374_);
v_t_372_ = v_r_375_;
goto _start;
}
}
}
else
{
uint8_t v___x_381_; 
lean_dec(v_k_371_);
lean_dec_ref(v_cmp_370_);
v___x_381_ = 0;
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg___boxed(lean_object* v_cmp_382_, lean_object* v_k_383_, lean_object* v_t_384_){
_start:
{
uint8_t v_res_385_; lean_object* v_r_386_; 
v_res_385_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(v_cmp_382_, v_k_383_, v_t_384_);
v_r_386_ = lean_box(v_res_385_);
return v_r_386_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_insert___redArg(lean_object* v_cmp_387_, lean_object* v_self_388_, lean_object* v_a_389_, lean_object* v_b_390_){
_start:
{
lean_object* v_toTreeMap_391_; lean_object* v_toArray_392_; uint8_t v___x_393_; 
v_toTreeMap_391_ = lean_ctor_get(v_self_388_, 0);
v_toArray_392_ = lean_ctor_get(v_self_388_, 1);
lean_inc(v_toTreeMap_391_);
lean_inc(v_a_389_);
lean_inc_ref(v_cmp_387_);
v___x_393_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(v_cmp_387_, v_a_389_, v_toTreeMap_391_);
if (v___x_393_ == 0)
{
lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_402_; 
lean_inc_ref(v_toArray_392_);
lean_inc(v_toTreeMap_391_);
v_isSharedCheck_402_ = !lean_is_exclusive(v_self_388_);
if (v_isSharedCheck_402_ == 0)
{
lean_object* v_unused_403_; lean_object* v_unused_404_; 
v_unused_403_ = lean_ctor_get(v_self_388_, 1);
lean_dec(v_unused_403_);
v_unused_404_ = lean_ctor_get(v_self_388_, 0);
lean_dec(v_unused_404_);
v___x_395_ = v_self_388_;
v_isShared_396_ = v_isSharedCheck_402_;
goto v_resetjp_394_;
}
else
{
lean_dec(v_self_388_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_402_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
lean_inc(v_b_390_);
v___x_397_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_387_, v_a_389_, v_b_390_, v_toTreeMap_391_);
v___x_398_ = lean_array_push(v_toArray_392_, v_b_390_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 1, v___x_398_);
lean_ctor_set(v___x_395_, 0, v___x_397_);
v___x_400_ = v___x_395_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
else
{
lean_dec(v_b_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_cmp_387_);
return v_self_388_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_insert(lean_object* v_00_u03b1_405_, lean_object* v_00_u03b2_406_, lean_object* v_cmp_407_, lean_object* v_self_408_, lean_object* v_a_409_, lean_object* v_b_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lake_RBArray_insert___redArg(v_cmp_407_, v_self_408_, v_a_409_, v_b_410_);
return v___x_411_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0(lean_object* v_00_u03b1_412_, lean_object* v_cmp_413_, lean_object* v_00_u03b2_414_, lean_object* v_k_415_, lean_object* v_t_416_){
_start:
{
uint8_t v___x_417_; 
v___x_417_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(v_cmp_413_, v_k_415_, v_t_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___boxed(lean_object* v_00_u03b1_418_, lean_object* v_cmp_419_, lean_object* v_00_u03b2_420_, lean_object* v_k_421_, lean_object* v_t_422_){
_start:
{
uint8_t v_res_423_; lean_object* v_r_424_; 
v_res_423_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0(v_00_u03b1_418_, v_cmp_419_, v_00_u03b2_420_, v_k_421_, v_t_422_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1(lean_object* v_00_u03b1_425_, lean_object* v_cmp_426_, lean_object* v_00_u03b2_427_, lean_object* v_k_428_, lean_object* v_v_429_, lean_object* v_t_430_, lean_object* v_hl_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_426_, v_k_428_, v_v_429_, v_t_430_);
return v___x_432_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_all___redArg___lam__0(lean_object* v_f_433_, lean_object* v_v_434_){
_start:
{
lean_object* v___x_435_; uint8_t v___x_436_; uint8_t v___x_437_; 
v___x_435_ = lean_apply_1(v_f_433_, v_v_434_);
v___x_436_ = lean_unbox(v___x_435_);
v___x_437_ = lean_bool_not(v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_all___redArg___lam__0___boxed(lean_object* v_f_438_, lean_object* v_v_439_){
_start:
{
uint8_t v_res_440_; lean_object* v_r_441_; 
v_res_440_ = l_Lake_RBArray_all___redArg___lam__0(v_f_438_, v_v_439_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_all___redArg(lean_object* v_f_461_, lean_object* v_self_462_){
_start:
{
lean_object* v_toArray_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v_toArray_463_ = lean_ctor_get(v_self_462_, 1);
lean_inc_ref(v_toArray_463_);
lean_dec_ref(v_self_462_);
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = lean_array_get_size(v_toArray_463_);
v___x_466_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_467_ = lean_nat_dec_lt(v___x_464_, v___x_465_);
if (v___x_467_ == 0)
{
uint8_t v___x_468_; 
lean_dec_ref(v_toArray_463_);
lean_dec_ref(v_f_461_);
v___x_468_ = lean_bool_not(v___x_467_);
return v___x_468_;
}
else
{
if (v___x_467_ == 0)
{
uint8_t v___x_469_; 
lean_dec_ref(v_toArray_463_);
lean_dec_ref(v_f_461_);
v___x_469_ = lean_bool_not(v___x_467_);
return v___x_469_;
}
else
{
lean_object* v___f_470_; size_t v___x_471_; size_t v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; uint8_t v___x_475_; 
v___f_470_ = lean_alloc_closure((void*)(l_Lake_RBArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_470_, 0, v_f_461_);
v___x_471_ = ((size_t)0ULL);
v___x_472_ = lean_usize_of_nat(v___x_465_);
v___x_473_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_466_, v___f_470_, v_toArray_463_, v___x_471_, v___x_472_);
v___x_474_ = lean_unbox(v___x_473_);
lean_dec(v___x_473_);
v___x_475_ = lean_bool_not(v___x_474_);
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_all___redArg___boxed(lean_object* v_f_476_, lean_object* v_self_477_){
_start:
{
uint8_t v_res_478_; lean_object* v_r_479_; 
v_res_478_ = l_Lake_RBArray_all___redArg(v_f_476_, v_self_477_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_all(lean_object* v_00_u03b2_480_, lean_object* v_00_u03b1_481_, lean_object* v_cmp_482_, lean_object* v_f_483_, lean_object* v_self_484_){
_start:
{
lean_object* v_toArray_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_toArray_485_ = lean_ctor_get(v_self_484_, 1);
lean_inc_ref(v_toArray_485_);
lean_dec_ref(v_self_484_);
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = lean_array_get_size(v_toArray_485_);
v___x_488_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_489_ = lean_nat_dec_lt(v___x_486_, v___x_487_);
if (v___x_489_ == 0)
{
uint8_t v___x_490_; 
lean_dec_ref(v_toArray_485_);
lean_dec_ref(v_f_483_);
v___x_490_ = lean_bool_not(v___x_489_);
return v___x_490_;
}
else
{
if (v___x_489_ == 0)
{
uint8_t v___x_491_; 
lean_dec_ref(v_toArray_485_);
lean_dec_ref(v_f_483_);
v___x_491_ = lean_bool_not(v___x_489_);
return v___x_491_;
}
else
{
lean_object* v___f_492_; size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; uint8_t v___x_497_; 
v___f_492_ = lean_alloc_closure((void*)(l_Lake_RBArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_492_, 0, v_f_483_);
v___x_493_ = ((size_t)0ULL);
v___x_494_ = lean_usize_of_nat(v___x_487_);
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_488_, v___f_492_, v_toArray_485_, v___x_493_, v___x_494_);
v___x_496_ = lean_unbox(v___x_495_);
lean_dec(v___x_495_);
v___x_497_ = lean_bool_not(v___x_496_);
return v___x_497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_all___boxed(lean_object* v_00_u03b2_498_, lean_object* v_00_u03b1_499_, lean_object* v_cmp_500_, lean_object* v_f_501_, lean_object* v_self_502_){
_start:
{
uint8_t v_res_503_; lean_object* v_r_504_; 
v_res_503_ = l_Lake_RBArray_all(v_00_u03b2_498_, v_00_u03b1_499_, v_cmp_500_, v_f_501_, v_self_502_);
lean_dec_ref(v_cmp_500_);
v_r_504_ = lean_box(v_res_503_);
return v_r_504_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_any___redArg___lam__0(lean_object* v_f_505_, lean_object* v_x_506_){
_start:
{
lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_507_ = lean_apply_1(v_f_505_, v_x_506_);
v___x_508_ = lean_unbox(v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_any___redArg___lam__0___boxed(lean_object* v_f_509_, lean_object* v_x_510_){
_start:
{
uint8_t v_res_511_; lean_object* v_r_512_; 
v_res_511_ = l_Lake_RBArray_any___redArg___lam__0(v_f_509_, v_x_510_);
v_r_512_ = lean_box(v_res_511_);
return v_r_512_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_any___redArg(lean_object* v_f_513_, lean_object* v_self_514_){
_start:
{
lean_object* v_toArray_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v_toArray_515_ = lean_ctor_get(v_self_514_, 1);
lean_inc_ref(v_toArray_515_);
lean_dec_ref(v_self_514_);
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = lean_array_get_size(v_toArray_515_);
v___x_518_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_519_ = lean_nat_dec_lt(v___x_516_, v___x_517_);
if (v___x_519_ == 0)
{
lean_dec_ref(v_toArray_515_);
lean_dec_ref(v_f_513_);
return v___x_519_;
}
else
{
if (v___x_519_ == 0)
{
lean_dec_ref(v_toArray_515_);
lean_dec_ref(v_f_513_);
return v___x_519_;
}
else
{
lean_object* v___f_520_; size_t v___x_521_; size_t v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___f_520_ = lean_alloc_closure((void*)(l_Lake_RBArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_520_, 0, v_f_513_);
v___x_521_ = ((size_t)0ULL);
v___x_522_ = lean_usize_of_nat(v___x_517_);
v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_518_, v___f_520_, v_toArray_515_, v___x_521_, v___x_522_);
v___x_524_ = lean_unbox(v___x_523_);
lean_dec(v___x_523_);
return v___x_524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_any___redArg___boxed(lean_object* v_f_525_, lean_object* v_self_526_){
_start:
{
uint8_t v_res_527_; lean_object* v_r_528_; 
v_res_527_ = l_Lake_RBArray_any___redArg(v_f_525_, v_self_526_);
v_r_528_ = lean_box(v_res_527_);
return v_r_528_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_any(lean_object* v_00_u03b2_529_, lean_object* v_00_u03b1_530_, lean_object* v_cmp_531_, lean_object* v_f_532_, lean_object* v_self_533_){
_start:
{
lean_object* v_toArray_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v_toArray_534_ = lean_ctor_get(v_self_533_, 1);
lean_inc_ref(v_toArray_534_);
lean_dec_ref(v_self_533_);
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = lean_array_get_size(v_toArray_534_);
v___x_537_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_538_ = lean_nat_dec_lt(v___x_535_, v___x_536_);
if (v___x_538_ == 0)
{
lean_dec_ref(v_toArray_534_);
lean_dec_ref(v_f_532_);
return v___x_538_;
}
else
{
if (v___x_538_ == 0)
{
lean_dec_ref(v_toArray_534_);
lean_dec_ref(v_f_532_);
return v___x_538_;
}
else
{
lean_object* v___f_539_; size_t v___x_540_; size_t v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___f_539_ = lean_alloc_closure((void*)(l_Lake_RBArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_539_, 0, v_f_532_);
v___x_540_ = ((size_t)0ULL);
v___x_541_ = lean_usize_of_nat(v___x_536_);
v___x_542_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_537_, v___f_539_, v_toArray_534_, v___x_540_, v___x_541_);
v___x_543_ = lean_unbox(v___x_542_);
lean_dec(v___x_542_);
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_any___boxed(lean_object* v_00_u03b2_544_, lean_object* v_00_u03b1_545_, lean_object* v_cmp_546_, lean_object* v_f_547_, lean_object* v_self_548_){
_start:
{
uint8_t v_res_549_; lean_object* v_r_550_; 
v_res_549_ = l_Lake_RBArray_any(v_00_u03b2_544_, v_00_u03b1_545_, v_cmp_546_, v_f_547_, v_self_548_);
lean_dec_ref(v_cmp_546_);
v_r_550_ = lean_box(v_res_549_);
return v_r_550_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl___redArg___lam__0(lean_object* v_f_551_, lean_object* v_x1_552_, lean_object* v_x2_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = lean_apply_2(v_f_551_, v_x1_552_, v_x2_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl___redArg(lean_object* v_f_555_, lean_object* v_init_556_, lean_object* v_self_557_){
_start:
{
lean_object* v_toArray_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v_toArray_558_ = lean_ctor_get(v_self_557_, 1);
lean_inc_ref(v_toArray_558_);
lean_dec_ref(v_self_557_);
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = lean_array_get_size(v_toArray_558_);
v___x_561_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_562_ = lean_nat_dec_lt(v___x_559_, v___x_560_);
if (v___x_562_ == 0)
{
lean_dec_ref(v_toArray_558_);
lean_dec(v_f_555_);
return v_init_556_;
}
else
{
lean_object* v___f_563_; uint8_t v___x_564_; 
v___f_563_ = lean_alloc_closure((void*)(l_Lake_RBArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_563_, 0, v_f_555_);
v___x_564_ = lean_nat_dec_le(v___x_560_, v___x_560_);
if (v___x_564_ == 0)
{
if (v___x_562_ == 0)
{
lean_dec_ref(v___f_563_);
lean_dec_ref(v_toArray_558_);
return v_init_556_;
}
else
{
size_t v___x_565_; size_t v___x_566_; lean_object* v___x_567_; 
v___x_565_ = ((size_t)0ULL);
v___x_566_ = lean_usize_of_nat(v___x_560_);
v___x_567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_561_, v___f_563_, v_toArray_558_, v___x_565_, v___x_566_, v_init_556_);
return v___x_567_;
}
}
else
{
size_t v___x_568_; size_t v___x_569_; lean_object* v___x_570_; 
v___x_568_ = ((size_t)0ULL);
v___x_569_ = lean_usize_of_nat(v___x_560_);
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_561_, v___f_563_, v_toArray_558_, v___x_568_, v___x_569_, v_init_556_);
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl(lean_object* v_00_u03c3_571_, lean_object* v_00_u03b2_572_, lean_object* v_00_u03b1_573_, lean_object* v_cmp_574_, lean_object* v_f_575_, lean_object* v_init_576_, lean_object* v_self_577_){
_start:
{
lean_object* v_toArray_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v_toArray_578_ = lean_ctor_get(v_self_577_, 1);
lean_inc_ref(v_toArray_578_);
lean_dec_ref(v_self_577_);
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = lean_array_get_size(v_toArray_578_);
v___x_581_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_582_ = lean_nat_dec_lt(v___x_579_, v___x_580_);
if (v___x_582_ == 0)
{
lean_dec_ref(v_toArray_578_);
lean_dec(v_f_575_);
return v_init_576_;
}
else
{
lean_object* v___f_583_; uint8_t v___x_584_; 
v___f_583_ = lean_alloc_closure((void*)(l_Lake_RBArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_583_, 0, v_f_575_);
v___x_584_ = lean_nat_dec_le(v___x_580_, v___x_580_);
if (v___x_584_ == 0)
{
if (v___x_582_ == 0)
{
lean_dec_ref(v___f_583_);
lean_dec_ref(v_toArray_578_);
return v_init_576_;
}
else
{
size_t v___x_585_; size_t v___x_586_; lean_object* v___x_587_; 
v___x_585_ = ((size_t)0ULL);
v___x_586_ = lean_usize_of_nat(v___x_580_);
v___x_587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_581_, v___f_583_, v_toArray_578_, v___x_585_, v___x_586_, v_init_576_);
return v___x_587_;
}
}
else
{
size_t v___x_588_; size_t v___x_589_; lean_object* v___x_590_; 
v___x_588_ = ((size_t)0ULL);
v___x_589_ = lean_usize_of_nat(v___x_580_);
v___x_590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_581_, v___f_583_, v_toArray_578_, v___x_588_, v___x_589_, v_init_576_);
return v___x_590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl___boxed(lean_object* v_00_u03c3_591_, lean_object* v_00_u03b2_592_, lean_object* v_00_u03b1_593_, lean_object* v_cmp_594_, lean_object* v_f_595_, lean_object* v_init_596_, lean_object* v_self_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lake_RBArray_foldl(v_00_u03c3_591_, v_00_u03b2_592_, v_00_u03b1_593_, v_cmp_594_, v_f_595_, v_init_596_, v_self_597_);
lean_dec_ref(v_cmp_594_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldlM___redArg(lean_object* v_inst_599_, lean_object* v_f_600_, lean_object* v_init_601_, lean_object* v_self_602_){
_start:
{
lean_object* v_toArray_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v_toArray_603_ = lean_ctor_get(v_self_602_, 1);
lean_inc_ref(v_toArray_603_);
lean_dec_ref(v_self_602_);
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = lean_array_get_size(v_toArray_603_);
v___x_606_ = lean_nat_dec_lt(v___x_604_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v_toApplicative_607_; lean_object* v_toPure_608_; lean_object* v___x_609_; 
lean_dec_ref(v_toArray_603_);
lean_dec(v_f_600_);
v_toApplicative_607_ = lean_ctor_get(v_inst_599_, 0);
lean_inc_ref(v_toApplicative_607_);
lean_dec_ref(v_inst_599_);
v_toPure_608_ = lean_ctor_get(v_toApplicative_607_, 1);
lean_inc(v_toPure_608_);
lean_dec_ref(v_toApplicative_607_);
v___x_609_ = lean_apply_2(v_toPure_608_, lean_box(0), v_init_601_);
return v___x_609_;
}
else
{
uint8_t v___x_610_; 
v___x_610_ = lean_nat_dec_le(v___x_605_, v___x_605_);
if (v___x_610_ == 0)
{
if (v___x_606_ == 0)
{
lean_object* v_toApplicative_611_; lean_object* v_toPure_612_; lean_object* v___x_613_; 
lean_dec_ref(v_toArray_603_);
lean_dec(v_f_600_);
v_toApplicative_611_ = lean_ctor_get(v_inst_599_, 0);
lean_inc_ref(v_toApplicative_611_);
lean_dec_ref(v_inst_599_);
v_toPure_612_ = lean_ctor_get(v_toApplicative_611_, 1);
lean_inc(v_toPure_612_);
lean_dec_ref(v_toApplicative_611_);
v___x_613_ = lean_apply_2(v_toPure_612_, lean_box(0), v_init_601_);
return v___x_613_;
}
else
{
size_t v___x_614_; size_t v___x_615_; lean_object* v___x_616_; 
v___x_614_ = ((size_t)0ULL);
v___x_615_ = lean_usize_of_nat(v___x_605_);
v___x_616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_599_, v_f_600_, v_toArray_603_, v___x_614_, v___x_615_, v_init_601_);
return v___x_616_;
}
}
else
{
size_t v___x_617_; size_t v___x_618_; lean_object* v___x_619_; 
v___x_617_ = ((size_t)0ULL);
v___x_618_ = lean_usize_of_nat(v___x_605_);
v___x_619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_599_, v_f_600_, v_toArray_603_, v___x_617_, v___x_618_, v_init_601_);
return v___x_619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldlM(lean_object* v_m_620_, lean_object* v_00_u03c3_621_, lean_object* v_00_u03b2_622_, lean_object* v_00_u03b1_623_, lean_object* v_cmp_624_, lean_object* v_inst_625_, lean_object* v_f_626_, lean_object* v_init_627_, lean_object* v_self_628_){
_start:
{
lean_object* v_toArray_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_toArray_629_ = lean_ctor_get(v_self_628_, 1);
lean_inc_ref(v_toArray_629_);
lean_dec_ref(v_self_628_);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_array_get_size(v_toArray_629_);
v___x_632_ = lean_nat_dec_lt(v___x_630_, v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v_toApplicative_633_; lean_object* v_toPure_634_; lean_object* v___x_635_; 
lean_dec_ref(v_toArray_629_);
lean_dec(v_f_626_);
v_toApplicative_633_ = lean_ctor_get(v_inst_625_, 0);
lean_inc_ref(v_toApplicative_633_);
lean_dec_ref(v_inst_625_);
v_toPure_634_ = lean_ctor_get(v_toApplicative_633_, 1);
lean_inc(v_toPure_634_);
lean_dec_ref(v_toApplicative_633_);
v___x_635_ = lean_apply_2(v_toPure_634_, lean_box(0), v_init_627_);
return v___x_635_;
}
else
{
uint8_t v___x_636_; 
v___x_636_ = lean_nat_dec_le(v___x_631_, v___x_631_);
if (v___x_636_ == 0)
{
if (v___x_632_ == 0)
{
lean_object* v_toApplicative_637_; lean_object* v_toPure_638_; lean_object* v___x_639_; 
lean_dec_ref(v_toArray_629_);
lean_dec(v_f_626_);
v_toApplicative_637_ = lean_ctor_get(v_inst_625_, 0);
lean_inc_ref(v_toApplicative_637_);
lean_dec_ref(v_inst_625_);
v_toPure_638_ = lean_ctor_get(v_toApplicative_637_, 1);
lean_inc(v_toPure_638_);
lean_dec_ref(v_toApplicative_637_);
v___x_639_ = lean_apply_2(v_toPure_638_, lean_box(0), v_init_627_);
return v___x_639_;
}
else
{
size_t v___x_640_; size_t v___x_641_; lean_object* v___x_642_; 
v___x_640_ = ((size_t)0ULL);
v___x_641_ = lean_usize_of_nat(v___x_631_);
v___x_642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_625_, v_f_626_, v_toArray_629_, v___x_640_, v___x_641_, v_init_627_);
return v___x_642_;
}
}
else
{
size_t v___x_643_; size_t v___x_644_; lean_object* v___x_645_; 
v___x_643_ = ((size_t)0ULL);
v___x_644_ = lean_usize_of_nat(v___x_631_);
v___x_645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_625_, v_f_626_, v_toArray_629_, v___x_643_, v___x_644_, v_init_627_);
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldlM___boxed(lean_object* v_m_646_, lean_object* v_00_u03c3_647_, lean_object* v_00_u03b2_648_, lean_object* v_00_u03b1_649_, lean_object* v_cmp_650_, lean_object* v_inst_651_, lean_object* v_f_652_, lean_object* v_init_653_, lean_object* v_self_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lake_RBArray_foldlM(v_m_646_, v_00_u03c3_647_, v_00_u03b2_648_, v_00_u03b1_649_, v_cmp_650_, v_inst_651_, v_f_652_, v_init_653_, v_self_654_);
lean_dec_ref(v_cmp_650_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldr___redArg(lean_object* v_f_656_, lean_object* v_init_657_, lean_object* v_self_658_){
_start:
{
lean_object* v_toArray_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v_toArray_659_ = lean_ctor_get(v_self_658_, 1);
lean_inc_ref(v_toArray_659_);
lean_dec_ref(v_self_658_);
v___x_660_ = lean_array_get_size(v_toArray_659_);
v___x_661_ = lean_unsigned_to_nat(0u);
v___x_662_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_663_ = lean_nat_dec_lt(v___x_661_, v___x_660_);
if (v___x_663_ == 0)
{
lean_dec_ref(v_toArray_659_);
lean_dec(v_f_656_);
return v_init_657_;
}
else
{
lean_object* v___f_664_; size_t v___x_665_; size_t v___x_666_; lean_object* v___x_667_; 
v___f_664_ = lean_alloc_closure((void*)(l_Lake_RBArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_664_, 0, v_f_656_);
v___x_665_ = lean_usize_of_nat(v___x_660_);
v___x_666_ = ((size_t)0ULL);
v___x_667_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_662_, v___f_664_, v_toArray_659_, v___x_665_, v___x_666_, v_init_657_);
return v___x_667_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldr(lean_object* v_00_u03b2_668_, lean_object* v_00_u03c3_669_, lean_object* v_00_u03b1_670_, lean_object* v_cmp_671_, lean_object* v_f_672_, lean_object* v_init_673_, lean_object* v_self_674_){
_start:
{
lean_object* v_toArray_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_toArray_675_ = lean_ctor_get(v_self_674_, 1);
lean_inc_ref(v_toArray_675_);
lean_dec_ref(v_self_674_);
v___x_676_ = lean_array_get_size(v_toArray_675_);
v___x_677_ = lean_unsigned_to_nat(0u);
v___x_678_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_679_ = lean_nat_dec_lt(v___x_677_, v___x_676_);
if (v___x_679_ == 0)
{
lean_dec_ref(v_toArray_675_);
lean_dec(v_f_672_);
return v_init_673_;
}
else
{
lean_object* v___f_680_; size_t v___x_681_; size_t v___x_682_; lean_object* v___x_683_; 
v___f_680_ = lean_alloc_closure((void*)(l_Lake_RBArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_680_, 0, v_f_672_);
v___x_681_ = lean_usize_of_nat(v___x_676_);
v___x_682_ = ((size_t)0ULL);
v___x_683_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_678_, v___f_680_, v_toArray_675_, v___x_681_, v___x_682_, v_init_673_);
return v___x_683_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldr___boxed(lean_object* v_00_u03b2_684_, lean_object* v_00_u03c3_685_, lean_object* v_00_u03b1_686_, lean_object* v_cmp_687_, lean_object* v_f_688_, lean_object* v_init_689_, lean_object* v_self_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lake_RBArray_foldr(v_00_u03b2_684_, v_00_u03c3_685_, v_00_u03b1_686_, v_cmp_687_, v_f_688_, v_init_689_, v_self_690_);
lean_dec_ref(v_cmp_687_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldrM___redArg(lean_object* v_inst_692_, lean_object* v_f_693_, lean_object* v_init_694_, lean_object* v_self_695_){
_start:
{
lean_object* v_toArray_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_toArray_696_ = lean_ctor_get(v_self_695_, 1);
lean_inc_ref(v_toArray_696_);
lean_dec_ref(v_self_695_);
v___x_697_ = lean_array_get_size(v_toArray_696_);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_nat_dec_lt(v___x_698_, v___x_697_);
if (v___x_699_ == 0)
{
lean_object* v_toApplicative_700_; lean_object* v_toPure_701_; lean_object* v___x_702_; 
lean_dec_ref(v_toArray_696_);
lean_dec(v_f_693_);
v_toApplicative_700_ = lean_ctor_get(v_inst_692_, 0);
lean_inc_ref(v_toApplicative_700_);
lean_dec_ref(v_inst_692_);
v_toPure_701_ = lean_ctor_get(v_toApplicative_700_, 1);
lean_inc(v_toPure_701_);
lean_dec_ref(v_toApplicative_700_);
v___x_702_ = lean_apply_2(v_toPure_701_, lean_box(0), v_init_694_);
return v___x_702_;
}
else
{
size_t v___x_703_; size_t v___x_704_; lean_object* v___x_705_; 
v___x_703_ = lean_usize_of_nat(v___x_697_);
v___x_704_ = ((size_t)0ULL);
v___x_705_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_692_, v_f_693_, v_toArray_696_, v___x_703_, v___x_704_, v_init_694_);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldrM(lean_object* v_m_706_, lean_object* v_00_u03b2_707_, lean_object* v_00_u03c3_708_, lean_object* v_00_u03b1_709_, lean_object* v_cmp_710_, lean_object* v_inst_711_, lean_object* v_f_712_, lean_object* v_init_713_, lean_object* v_self_714_){
_start:
{
lean_object* v_toArray_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v_toArray_715_ = lean_ctor_get(v_self_714_, 1);
lean_inc_ref(v_toArray_715_);
lean_dec_ref(v_self_714_);
v___x_716_ = lean_array_get_size(v_toArray_715_);
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = lean_nat_dec_lt(v___x_717_, v___x_716_);
if (v___x_718_ == 0)
{
lean_object* v_toApplicative_719_; lean_object* v_toPure_720_; lean_object* v___x_721_; 
lean_dec_ref(v_toArray_715_);
lean_dec(v_f_712_);
v_toApplicative_719_ = lean_ctor_get(v_inst_711_, 0);
lean_inc_ref(v_toApplicative_719_);
lean_dec_ref(v_inst_711_);
v_toPure_720_ = lean_ctor_get(v_toApplicative_719_, 1);
lean_inc(v_toPure_720_);
lean_dec_ref(v_toApplicative_719_);
v___x_721_ = lean_apply_2(v_toPure_720_, lean_box(0), v_init_713_);
return v___x_721_;
}
else
{
size_t v___x_722_; size_t v___x_723_; lean_object* v___x_724_; 
v___x_722_ = lean_usize_of_nat(v___x_716_);
v___x_723_ = ((size_t)0ULL);
v___x_724_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_711_, v_f_712_, v_toArray_715_, v___x_722_, v___x_723_, v_init_713_);
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldrM___boxed(lean_object* v_m_725_, lean_object* v_00_u03b2_726_, lean_object* v_00_u03c3_727_, lean_object* v_00_u03b1_728_, lean_object* v_cmp_729_, lean_object* v_inst_730_, lean_object* v_f_731_, lean_object* v_init_732_, lean_object* v_self_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lake_RBArray_foldrM(v_m_725_, v_00_u03b2_726_, v_00_u03c3_727_, v_00_u03b1_728_, v_cmp_729_, v_inst_730_, v_f_731_, v_init_732_, v_self_733_);
lean_dec_ref(v_cmp_729_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM___redArg___lam__0(lean_object* v_f_735_, lean_object* v_x_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = lean_apply_1(v_f_735_, v___y_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM___redArg(lean_object* v_inst_739_, lean_object* v_f_740_, lean_object* v_self_741_){
_start:
{
lean_object* v_toArray_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v_toArray_742_ = lean_ctor_get(v_self_741_, 1);
lean_inc_ref(v_toArray_742_);
lean_dec_ref(v_self_741_);
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = lean_array_get_size(v_toArray_742_);
v___x_745_ = lean_box(0);
v___x_746_ = lean_nat_dec_lt(v___x_743_, v___x_744_);
if (v___x_746_ == 0)
{
lean_object* v_toApplicative_747_; lean_object* v_toPure_748_; lean_object* v___x_749_; 
lean_dec_ref(v_toArray_742_);
lean_dec(v_f_740_);
v_toApplicative_747_ = lean_ctor_get(v_inst_739_, 0);
lean_inc_ref(v_toApplicative_747_);
lean_dec_ref(v_inst_739_);
v_toPure_748_ = lean_ctor_get(v_toApplicative_747_, 1);
lean_inc(v_toPure_748_);
lean_dec_ref(v_toApplicative_747_);
v___x_749_ = lean_apply_2(v_toPure_748_, lean_box(0), v___x_745_);
return v___x_749_;
}
else
{
lean_object* v___f_750_; uint8_t v___x_751_; 
v___f_750_ = lean_alloc_closure((void*)(l_Lake_RBArray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_750_, 0, v_f_740_);
v___x_751_ = lean_nat_dec_le(v___x_744_, v___x_744_);
if (v___x_751_ == 0)
{
if (v___x_746_ == 0)
{
lean_object* v_toApplicative_752_; lean_object* v_toPure_753_; lean_object* v___x_754_; 
lean_dec_ref(v___f_750_);
lean_dec_ref(v_toArray_742_);
v_toApplicative_752_ = lean_ctor_get(v_inst_739_, 0);
lean_inc_ref(v_toApplicative_752_);
lean_dec_ref(v_inst_739_);
v_toPure_753_ = lean_ctor_get(v_toApplicative_752_, 1);
lean_inc(v_toPure_753_);
lean_dec_ref(v_toApplicative_752_);
v___x_754_ = lean_apply_2(v_toPure_753_, lean_box(0), v___x_745_);
return v___x_754_;
}
else
{
size_t v___x_755_; size_t v___x_756_; lean_object* v___x_757_; 
v___x_755_ = ((size_t)0ULL);
v___x_756_ = lean_usize_of_nat(v___x_744_);
v___x_757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_739_, v___f_750_, v_toArray_742_, v___x_755_, v___x_756_, v___x_745_);
return v___x_757_;
}
}
else
{
size_t v___x_758_; size_t v___x_759_; lean_object* v___x_760_; 
v___x_758_ = ((size_t)0ULL);
v___x_759_ = lean_usize_of_nat(v___x_744_);
v___x_760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_739_, v___f_750_, v_toArray_742_, v___x_758_, v___x_759_, v___x_745_);
return v___x_760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM(lean_object* v_m_761_, lean_object* v_00_u03b2_762_, lean_object* v_00_u03b1_763_, lean_object* v_cmp_764_, lean_object* v_inst_765_, lean_object* v_f_766_, lean_object* v_self_767_){
_start:
{
lean_object* v_toArray_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v_toArray_768_ = lean_ctor_get(v_self_767_, 1);
lean_inc_ref(v_toArray_768_);
lean_dec_ref(v_self_767_);
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = lean_array_get_size(v_toArray_768_);
v___x_771_ = lean_box(0);
v___x_772_ = lean_nat_dec_lt(v___x_769_, v___x_770_);
if (v___x_772_ == 0)
{
lean_object* v_toApplicative_773_; lean_object* v_toPure_774_; lean_object* v___x_775_; 
lean_dec_ref(v_toArray_768_);
lean_dec(v_f_766_);
v_toApplicative_773_ = lean_ctor_get(v_inst_765_, 0);
lean_inc_ref(v_toApplicative_773_);
lean_dec_ref(v_inst_765_);
v_toPure_774_ = lean_ctor_get(v_toApplicative_773_, 1);
lean_inc(v_toPure_774_);
lean_dec_ref(v_toApplicative_773_);
v___x_775_ = lean_apply_2(v_toPure_774_, lean_box(0), v___x_771_);
return v___x_775_;
}
else
{
lean_object* v___f_776_; uint8_t v___x_777_; 
v___f_776_ = lean_alloc_closure((void*)(l_Lake_RBArray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_776_, 0, v_f_766_);
v___x_777_ = lean_nat_dec_le(v___x_770_, v___x_770_);
if (v___x_777_ == 0)
{
if (v___x_772_ == 0)
{
lean_object* v_toApplicative_778_; lean_object* v_toPure_779_; lean_object* v___x_780_; 
lean_dec_ref(v___f_776_);
lean_dec_ref(v_toArray_768_);
v_toApplicative_778_ = lean_ctor_get(v_inst_765_, 0);
lean_inc_ref(v_toApplicative_778_);
lean_dec_ref(v_inst_765_);
v_toPure_779_ = lean_ctor_get(v_toApplicative_778_, 1);
lean_inc(v_toPure_779_);
lean_dec_ref(v_toApplicative_778_);
v___x_780_ = lean_apply_2(v_toPure_779_, lean_box(0), v___x_771_);
return v___x_780_;
}
else
{
size_t v___x_781_; size_t v___x_782_; lean_object* v___x_783_; 
v___x_781_ = ((size_t)0ULL);
v___x_782_ = lean_usize_of_nat(v___x_770_);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_765_, v___f_776_, v_toArray_768_, v___x_781_, v___x_782_, v___x_771_);
return v___x_783_;
}
}
else
{
size_t v___x_784_; size_t v___x_785_; lean_object* v___x_786_; 
v___x_784_ = ((size_t)0ULL);
v___x_785_ = lean_usize_of_nat(v___x_770_);
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_765_, v___f_776_, v_toArray_768_, v___x_784_, v___x_785_, v___x_771_);
return v___x_786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM___boxed(lean_object* v_m_787_, lean_object* v_00_u03b2_788_, lean_object* v_00_u03b1_789_, lean_object* v_cmp_790_, lean_object* v_inst_791_, lean_object* v_f_792_, lean_object* v_self_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lake_RBArray_forM(v_m_787_, v_00_u03b2_788_, v_00_u03b1_789_, v_cmp_790_, v_inst_791_, v_f_792_, v_self_793_);
lean_dec_ref(v_cmp_790_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn___redArg___lam__0(lean_object* v_f_795_, lean_object* v_a_796_, lean_object* v_x_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = lean_apply_2(v_f_795_, v_a_796_, v___y_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn___redArg(lean_object* v_inst_800_, lean_object* v_self_801_, lean_object* v_init_802_, lean_object* v_f_803_){
_start:
{
lean_object* v_toArray_804_; lean_object* v___f_805_; size_t v_sz_806_; size_t v___x_807_; lean_object* v___x_808_; 
v_toArray_804_ = lean_ctor_get(v_self_801_, 1);
lean_inc_ref(v_toArray_804_);
lean_dec_ref(v_self_801_);
v___f_805_ = lean_alloc_closure((void*)(l_Lake_RBArray_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_805_, 0, v_f_803_);
v_sz_806_ = lean_array_size(v_toArray_804_);
v___x_807_ = ((size_t)0ULL);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_800_, v_toArray_804_, v___f_805_, v_sz_806_, v___x_807_, v_init_802_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn(lean_object* v_m_809_, lean_object* v_00_u03b1_810_, lean_object* v_00_u03b2_811_, lean_object* v_cmp_812_, lean_object* v_00_u03c3_813_, lean_object* v_inst_814_, lean_object* v_self_815_, lean_object* v_init_816_, lean_object* v_f_817_){
_start:
{
lean_object* v_toArray_818_; lean_object* v___f_819_; size_t v_sz_820_; size_t v___x_821_; lean_object* v___x_822_; 
v_toArray_818_ = lean_ctor_get(v_self_815_, 1);
lean_inc_ref(v_toArray_818_);
lean_dec_ref(v_self_815_);
v___f_819_ = lean_alloc_closure((void*)(l_Lake_RBArray_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_819_, 0, v_f_817_);
v_sz_820_ = lean_array_size(v_toArray_818_);
v___x_821_ = ((size_t)0ULL);
v___x_822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_814_, v_toArray_818_, v___f_819_, v_sz_820_, v___x_821_, v_init_816_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn___boxed(lean_object* v_m_823_, lean_object* v_00_u03b1_824_, lean_object* v_00_u03b2_825_, lean_object* v_cmp_826_, lean_object* v_00_u03c3_827_, lean_object* v_inst_828_, lean_object* v_self_829_, lean_object* v_init_830_, lean_object* v_f_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lake_RBArray_forIn(v_m_823_, v_00_u03b1_824_, v_00_u03b2_825_, v_cmp_826_, v_00_u03c3_827_, v_inst_828_, v_self_829_, v_init_830_, v_f_831_);
lean_dec_ref(v_cmp_826_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__0(lean_object* v___y_833_, lean_object* v_a_834_, lean_object* v_x_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = lean_apply_2(v___y_833_, v_a_834_, v___y_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1(lean_object* v_inst_838_, lean_object* v_00_u03b2_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_toArray_843_; lean_object* v___f_844_; size_t v_sz_845_; size_t v___x_846_; lean_object* v___x_847_; 
v_toArray_843_ = lean_ctor_get(v___y_840_, 1);
lean_inc_ref(v_toArray_843_);
lean_dec_ref(v___y_840_);
v___f_844_ = lean_alloc_closure((void*)(l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_844_, 0, v___y_842_);
v_sz_845_ = lean_array_size(v_toArray_843_);
v___x_846_ = ((size_t)0ULL);
v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_838_, v_toArray_843_, v___f_844_, v_sz_845_, v___x_846_, v___y_841_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg(lean_object* v_inst_848_){
_start:
{
lean_object* v___f_849_; 
v___f_849_ = lean_alloc_closure((void*)(l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_849_, 0, v_inst_848_);
return v___f_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad(lean_object* v_m_850_, lean_object* v_00_u03b1_851_, lean_object* v_00_u03b2_852_, lean_object* v_cmp_853_, lean_object* v_inst_854_){
_start:
{
lean_object* v___f_855_; 
v___f_855_ = lean_alloc_closure((void*)(l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_855_, 0, v_inst_854_);
return v___f_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___boxed(lean_object* v_m_856_, lean_object* v_00_u03b1_857_, lean_object* v_00_u03b2_858_, lean_object* v_cmp_859_, lean_object* v_inst_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad(v_m_856_, v_00_u03b1_857_, v_00_u03b2_858_, v_cmp_859_, v_inst_860_);
lean_dec_ref(v_cmp_859_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkRBArray___redArg___lam__0(lean_object* v_f_862_, lean_object* v_cmp_863_, lean_object* v_x1_864_, lean_object* v_x2_865_){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
lean_inc(v_x2_865_);
v___x_866_ = lean_apply_1(v_f_862_, v_x2_865_);
v___x_867_ = l_Lake_RBArray_insert___redArg(v_cmp_863_, v_x1_864_, v___x_866_, v_x2_865_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkRBArray___redArg(lean_object* v_cmp_868_, lean_object* v_f_869_, lean_object* v_vs_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_871_ = lean_array_get_size(v_vs_870_);
v___x_872_ = l_Lake_RBArray_mkEmpty___redArg(v___x_871_);
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_875_ = lean_nat_dec_lt(v___x_873_, v___x_871_);
if (v___x_875_ == 0)
{
lean_dec_ref(v_vs_870_);
lean_dec(v_f_869_);
lean_dec_ref(v_cmp_868_);
return v___x_872_;
}
else
{
lean_object* v___f_876_; uint8_t v___x_877_; 
v___f_876_ = lean_alloc_closure((void*)(l_Lake_mkRBArray___redArg___lam__0), 4, 2);
lean_closure_set(v___f_876_, 0, v_f_869_);
lean_closure_set(v___f_876_, 1, v_cmp_868_);
v___x_877_ = lean_nat_dec_le(v___x_871_, v___x_871_);
if (v___x_877_ == 0)
{
if (v___x_875_ == 0)
{
lean_dec_ref(v___f_876_);
lean_dec_ref(v_vs_870_);
return v___x_872_;
}
else
{
size_t v___x_878_; size_t v___x_879_; lean_object* v___x_880_; 
v___x_878_ = ((size_t)0ULL);
v___x_879_ = lean_usize_of_nat(v___x_871_);
v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_874_, v___f_876_, v_vs_870_, v___x_878_, v___x_879_, v___x_872_);
return v___x_880_;
}
}
else
{
size_t v___x_881_; size_t v___x_882_; lean_object* v___x_883_; 
v___x_881_ = ((size_t)0ULL);
v___x_882_ = lean_usize_of_nat(v___x_871_);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_874_, v___f_876_, v_vs_870_, v___x_881_, v___x_882_, v___x_872_);
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkRBArray(lean_object* v_00_u03b2_884_, lean_object* v_00_u03b1_885_, lean_object* v_cmp_886_, lean_object* v_f_887_, lean_object* v_vs_888_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_889_ = lean_array_get_size(v_vs_888_);
v___x_890_ = l_Lake_RBArray_mkEmpty___redArg(v___x_889_);
v___x_891_ = lean_unsigned_to_nat(0u);
v___x_892_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_893_ = lean_nat_dec_lt(v___x_891_, v___x_889_);
if (v___x_893_ == 0)
{
lean_dec_ref(v_vs_888_);
lean_dec(v_f_887_);
lean_dec_ref(v_cmp_886_);
return v___x_890_;
}
else
{
lean_object* v___f_894_; uint8_t v___x_895_; 
v___f_894_ = lean_alloc_closure((void*)(l_Lake_mkRBArray___redArg___lam__0), 4, 2);
lean_closure_set(v___f_894_, 0, v_f_887_);
lean_closure_set(v___f_894_, 1, v_cmp_886_);
v___x_895_ = lean_nat_dec_le(v___x_889_, v___x_889_);
if (v___x_895_ == 0)
{
if (v___x_893_ == 0)
{
lean_dec_ref(v___f_894_);
lean_dec_ref(v_vs_888_);
return v___x_890_;
}
else
{
size_t v___x_896_; size_t v___x_897_; lean_object* v___x_898_; 
v___x_896_ = ((size_t)0ULL);
v___x_897_ = lean_usize_of_nat(v___x_889_);
v___x_898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_892_, v___f_894_, v_vs_888_, v___x_896_, v___x_897_, v___x_890_);
return v___x_898_;
}
}
else
{
size_t v___x_899_; size_t v___x_900_; lean_object* v___x_901_; 
v___x_899_ = ((size_t)0ULL);
v___x_900_ = lean_usize_of_nat(v___x_889_);
v___x_901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_892_, v___f_894_, v_vs_888_, v___x_899_, v___x_900_, v___x_890_);
return v___x_901_;
}
}
}
}
lean_object* runtime_initialize_Std_Data_TreeMap_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_RBArray(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_RBArray(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_TreeMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_RBArray(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_TreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_RBArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_RBArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_RBArray(builtin);
}
#ifdef __cplusplus
}
#endif
