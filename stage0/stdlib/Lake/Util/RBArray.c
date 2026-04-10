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
LEAN_EXPORT uint8_t l_Lake_RBArray_all___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
v___x_129_ = lean_nat_add(v___y_126_, v___y_128_);
lean_dec(v___y_128_);
lean_dec(v___y_126_);
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
lean_ctor_set(v___x_109_, 3, v___y_127_);
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
lean_ctor_set(v_reuseFailAlloc_134_, 3, v___y_127_);
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
v___y_126_ = v___x_142_;
v___y_127_ = v___x_141_;
v___y_128_ = v_size_143_;
goto v___jp_125_;
}
else
{
lean_object* v___x_144_; 
v___x_144_ = lean_unsigned_to_nat(0u);
v___y_126_ = v___x_142_;
v___y_127_ = v___x_141_;
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
v___x_269_ = lean_nat_add(v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec(v___y_267_);
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
lean_ctor_set(v___x_249_, 3, v___y_266_);
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
lean_ctor_set(v_reuseFailAlloc_274_, 3, v___y_266_);
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
v___y_266_ = v___x_280_;
v___y_267_ = v___x_281_;
v___y_268_ = v_size_282_;
goto v___jp_265_;
}
else
{
lean_object* v___x_283_; 
v___x_283_ = lean_unsigned_to_nat(0u);
v___y_266_ = v___x_280_;
v___y_267_ = v___x_281_;
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
lean_dec_ref(v_t_372_);
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
LEAN_EXPORT uint8_t l_Lake_RBArray_all___redArg___lam__0(lean_object* v_f_433_, uint8_t v___x_434_, lean_object* v_v_435_){
_start:
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_apply_1(v_f_433_, v_v_435_);
v___x_437_ = lean_unbox(v___x_436_);
if (v___x_437_ == 0)
{
return v___x_434_;
}
else
{
uint8_t v___x_438_; 
v___x_438_ = 0;
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_all___redArg___lam__0___boxed(lean_object* v_f_439_, lean_object* v___x_440_, lean_object* v_v_441_){
_start:
{
uint8_t v___x_79__boxed_442_; uint8_t v_res_443_; lean_object* v_r_444_; 
v___x_79__boxed_442_ = lean_unbox(v___x_440_);
v_res_443_ = l_Lake_RBArray_all___redArg___lam__0(v_f_439_, v___x_79__boxed_442_, v_v_441_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_all___redArg(lean_object* v_f_464_, lean_object* v_self_465_){
_start:
{
lean_object* v_toArray_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v_toArray_466_ = lean_ctor_get(v_self_465_, 1);
lean_inc_ref(v_toArray_466_);
lean_dec_ref(v_self_465_);
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = lean_array_get_size(v_toArray_466_);
v___x_469_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_470_ = lean_nat_dec_lt(v___x_467_, v___x_468_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; 
lean_dec_ref(v_toArray_466_);
lean_dec_ref(v_f_464_);
v___x_471_ = 1;
return v___x_471_;
}
else
{
if (v___x_470_ == 0)
{
lean_dec_ref(v_toArray_466_);
lean_dec_ref(v_f_464_);
return v___x_470_;
}
else
{
lean_object* v___x_472_; lean_object* v___f_473_; size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_472_ = lean_box(v___x_470_);
v___f_473_ = lean_alloc_closure((void*)(l_Lake_RBArray_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_473_, 0, v_f_464_);
lean_closure_set(v___f_473_, 1, v___x_472_);
v___x_474_ = ((size_t)0ULL);
v___x_475_ = lean_usize_of_nat(v___x_468_);
v___x_476_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_469_, v___f_473_, v_toArray_466_, v___x_474_, v___x_475_);
v___x_477_ = lean_unbox(v___x_476_);
lean_dec(v___x_476_);
if (v___x_477_ == 0)
{
return v___x_470_;
}
else
{
uint8_t v___x_478_; 
v___x_478_ = 0;
return v___x_478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_all___redArg___boxed(lean_object* v_f_479_, lean_object* v_self_480_){
_start:
{
uint8_t v_res_481_; lean_object* v_r_482_; 
v_res_481_ = l_Lake_RBArray_all___redArg(v_f_479_, v_self_480_);
v_r_482_ = lean_box(v_res_481_);
return v_r_482_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_all(lean_object* v_00_u03b2_483_, lean_object* v_00_u03b1_484_, lean_object* v_cmp_485_, lean_object* v_f_486_, lean_object* v_self_487_){
_start:
{
lean_object* v_toArray_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v_toArray_488_ = lean_ctor_get(v_self_487_, 1);
lean_inc_ref(v_toArray_488_);
lean_dec_ref(v_self_487_);
v___x_489_ = lean_unsigned_to_nat(0u);
v___x_490_ = lean_array_get_size(v_toArray_488_);
v___x_491_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_492_ = lean_nat_dec_lt(v___x_489_, v___x_490_);
if (v___x_492_ == 0)
{
uint8_t v___x_493_; 
lean_dec_ref(v_toArray_488_);
lean_dec_ref(v_f_486_);
v___x_493_ = 1;
return v___x_493_;
}
else
{
if (v___x_492_ == 0)
{
lean_dec_ref(v_toArray_488_);
lean_dec_ref(v_f_486_);
return v___x_492_;
}
else
{
lean_object* v___x_494_; lean_object* v___f_495_; size_t v___x_496_; size_t v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_494_ = lean_box(v___x_492_);
v___f_495_ = lean_alloc_closure((void*)(l_Lake_RBArray_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_495_, 0, v_f_486_);
lean_closure_set(v___f_495_, 1, v___x_494_);
v___x_496_ = ((size_t)0ULL);
v___x_497_ = lean_usize_of_nat(v___x_490_);
v___x_498_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_491_, v___f_495_, v_toArray_488_, v___x_496_, v___x_497_);
v___x_499_ = lean_unbox(v___x_498_);
lean_dec(v___x_498_);
if (v___x_499_ == 0)
{
return v___x_492_;
}
else
{
uint8_t v___x_500_; 
v___x_500_ = 0;
return v___x_500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_all___boxed(lean_object* v_00_u03b2_501_, lean_object* v_00_u03b1_502_, lean_object* v_cmp_503_, lean_object* v_f_504_, lean_object* v_self_505_){
_start:
{
uint8_t v_res_506_; lean_object* v_r_507_; 
v_res_506_ = l_Lake_RBArray_all(v_00_u03b2_501_, v_00_u03b1_502_, v_cmp_503_, v_f_504_, v_self_505_);
lean_dec_ref(v_cmp_503_);
v_r_507_ = lean_box(v_res_506_);
return v_r_507_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_any___redArg___lam__0(lean_object* v_f_508_, lean_object* v_x_509_){
_start:
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_apply_1(v_f_508_, v_x_509_);
v___x_511_ = lean_unbox(v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_any___redArg___lam__0___boxed(lean_object* v_f_512_, lean_object* v_x_513_){
_start:
{
uint8_t v_res_514_; lean_object* v_r_515_; 
v_res_514_ = l_Lake_RBArray_any___redArg___lam__0(v_f_512_, v_x_513_);
v_r_515_ = lean_box(v_res_514_);
return v_r_515_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_any___redArg(lean_object* v_f_516_, lean_object* v_self_517_){
_start:
{
lean_object* v_toArray_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v_toArray_518_ = lean_ctor_get(v_self_517_, 1);
lean_inc_ref(v_toArray_518_);
lean_dec_ref(v_self_517_);
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = lean_array_get_size(v_toArray_518_);
v___x_521_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_522_ = lean_nat_dec_lt(v___x_519_, v___x_520_);
if (v___x_522_ == 0)
{
lean_dec_ref(v_toArray_518_);
lean_dec_ref(v_f_516_);
return v___x_522_;
}
else
{
if (v___x_522_ == 0)
{
lean_dec_ref(v_toArray_518_);
lean_dec_ref(v_f_516_);
return v___x_522_;
}
else
{
lean_object* v___f_523_; size_t v___x_524_; size_t v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v___f_523_ = lean_alloc_closure((void*)(l_Lake_RBArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_523_, 0, v_f_516_);
v___x_524_ = ((size_t)0ULL);
v___x_525_ = lean_usize_of_nat(v___x_520_);
v___x_526_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_521_, v___f_523_, v_toArray_518_, v___x_524_, v___x_525_);
v___x_527_ = lean_unbox(v___x_526_);
lean_dec(v___x_526_);
return v___x_527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_any___redArg___boxed(lean_object* v_f_528_, lean_object* v_self_529_){
_start:
{
uint8_t v_res_530_; lean_object* v_r_531_; 
v_res_530_ = l_Lake_RBArray_any___redArg(v_f_528_, v_self_529_);
v_r_531_ = lean_box(v_res_530_);
return v_r_531_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_any(lean_object* v_00_u03b2_532_, lean_object* v_00_u03b1_533_, lean_object* v_cmp_534_, lean_object* v_f_535_, lean_object* v_self_536_){
_start:
{
lean_object* v_toArray_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_toArray_537_ = lean_ctor_get(v_self_536_, 1);
lean_inc_ref(v_toArray_537_);
lean_dec_ref(v_self_536_);
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_array_get_size(v_toArray_537_);
v___x_540_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_541_ = lean_nat_dec_lt(v___x_538_, v___x_539_);
if (v___x_541_ == 0)
{
lean_dec_ref(v_toArray_537_);
lean_dec_ref(v_f_535_);
return v___x_541_;
}
else
{
if (v___x_541_ == 0)
{
lean_dec_ref(v_toArray_537_);
lean_dec_ref(v_f_535_);
return v___x_541_;
}
else
{
lean_object* v___f_542_; size_t v___x_543_; size_t v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___f_542_ = lean_alloc_closure((void*)(l_Lake_RBArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_542_, 0, v_f_535_);
v___x_543_ = ((size_t)0ULL);
v___x_544_ = lean_usize_of_nat(v___x_539_);
v___x_545_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_540_, v___f_542_, v_toArray_537_, v___x_543_, v___x_544_);
v___x_546_ = lean_unbox(v___x_545_);
lean_dec(v___x_545_);
return v___x_546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_any___boxed(lean_object* v_00_u03b2_547_, lean_object* v_00_u03b1_548_, lean_object* v_cmp_549_, lean_object* v_f_550_, lean_object* v_self_551_){
_start:
{
uint8_t v_res_552_; lean_object* v_r_553_; 
v_res_552_ = l_Lake_RBArray_any(v_00_u03b2_547_, v_00_u03b1_548_, v_cmp_549_, v_f_550_, v_self_551_);
lean_dec_ref(v_cmp_549_);
v_r_553_ = lean_box(v_res_552_);
return v_r_553_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl___redArg___lam__0(lean_object* v_f_554_, lean_object* v_x1_555_, lean_object* v_x2_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = lean_apply_2(v_f_554_, v_x1_555_, v_x2_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl___redArg(lean_object* v_f_558_, lean_object* v_init_559_, lean_object* v_self_560_){
_start:
{
lean_object* v_toArray_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v_toArray_561_ = lean_ctor_get(v_self_560_, 1);
lean_inc_ref(v_toArray_561_);
lean_dec_ref(v_self_560_);
v___x_562_ = lean_unsigned_to_nat(0u);
v___x_563_ = lean_array_get_size(v_toArray_561_);
v___x_564_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_565_ = lean_nat_dec_lt(v___x_562_, v___x_563_);
if (v___x_565_ == 0)
{
lean_dec_ref(v_toArray_561_);
lean_dec(v_f_558_);
return v_init_559_;
}
else
{
lean_object* v___f_566_; uint8_t v___x_567_; 
v___f_566_ = lean_alloc_closure((void*)(l_Lake_RBArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_566_, 0, v_f_558_);
v___x_567_ = lean_nat_dec_le(v___x_563_, v___x_563_);
if (v___x_567_ == 0)
{
if (v___x_565_ == 0)
{
lean_dec_ref(v___f_566_);
lean_dec_ref(v_toArray_561_);
return v_init_559_;
}
else
{
size_t v___x_568_; size_t v___x_569_; lean_object* v___x_570_; 
v___x_568_ = ((size_t)0ULL);
v___x_569_ = lean_usize_of_nat(v___x_563_);
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_564_, v___f_566_, v_toArray_561_, v___x_568_, v___x_569_, v_init_559_);
return v___x_570_;
}
}
else
{
size_t v___x_571_; size_t v___x_572_; lean_object* v___x_573_; 
v___x_571_ = ((size_t)0ULL);
v___x_572_ = lean_usize_of_nat(v___x_563_);
v___x_573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_564_, v___f_566_, v_toArray_561_, v___x_571_, v___x_572_, v_init_559_);
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl(lean_object* v_00_u03c3_574_, lean_object* v_00_u03b2_575_, lean_object* v_00_u03b1_576_, lean_object* v_cmp_577_, lean_object* v_f_578_, lean_object* v_init_579_, lean_object* v_self_580_){
_start:
{
lean_object* v_toArray_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v_toArray_581_ = lean_ctor_get(v_self_580_, 1);
lean_inc_ref(v_toArray_581_);
lean_dec_ref(v_self_580_);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_array_get_size(v_toArray_581_);
v___x_584_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_585_ = lean_nat_dec_lt(v___x_582_, v___x_583_);
if (v___x_585_ == 0)
{
lean_dec_ref(v_toArray_581_);
lean_dec(v_f_578_);
return v_init_579_;
}
else
{
lean_object* v___f_586_; uint8_t v___x_587_; 
v___f_586_ = lean_alloc_closure((void*)(l_Lake_RBArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_586_, 0, v_f_578_);
v___x_587_ = lean_nat_dec_le(v___x_583_, v___x_583_);
if (v___x_587_ == 0)
{
if (v___x_585_ == 0)
{
lean_dec_ref(v___f_586_);
lean_dec_ref(v_toArray_581_);
return v_init_579_;
}
else
{
size_t v___x_588_; size_t v___x_589_; lean_object* v___x_590_; 
v___x_588_ = ((size_t)0ULL);
v___x_589_ = lean_usize_of_nat(v___x_583_);
v___x_590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_584_, v___f_586_, v_toArray_581_, v___x_588_, v___x_589_, v_init_579_);
return v___x_590_;
}
}
else
{
size_t v___x_591_; size_t v___x_592_; lean_object* v___x_593_; 
v___x_591_ = ((size_t)0ULL);
v___x_592_ = lean_usize_of_nat(v___x_583_);
v___x_593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_584_, v___f_586_, v_toArray_581_, v___x_591_, v___x_592_, v_init_579_);
return v___x_593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl___boxed(lean_object* v_00_u03c3_594_, lean_object* v_00_u03b2_595_, lean_object* v_00_u03b1_596_, lean_object* v_cmp_597_, lean_object* v_f_598_, lean_object* v_init_599_, lean_object* v_self_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lake_RBArray_foldl(v_00_u03c3_594_, v_00_u03b2_595_, v_00_u03b1_596_, v_cmp_597_, v_f_598_, v_init_599_, v_self_600_);
lean_dec_ref(v_cmp_597_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldlM___redArg(lean_object* v_inst_602_, lean_object* v_f_603_, lean_object* v_init_604_, lean_object* v_self_605_){
_start:
{
lean_object* v_toArray_606_; lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v_toArray_606_ = lean_ctor_get(v_self_605_, 1);
lean_inc_ref(v_toArray_606_);
lean_dec_ref(v_self_605_);
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_array_get_size(v_toArray_606_);
v___x_609_ = lean_nat_dec_lt(v___x_607_, v___x_608_);
if (v___x_609_ == 0)
{
lean_object* v_toApplicative_610_; lean_object* v_toPure_611_; lean_object* v___x_612_; 
lean_dec_ref(v_toArray_606_);
lean_dec(v_f_603_);
v_toApplicative_610_ = lean_ctor_get(v_inst_602_, 0);
lean_inc_ref(v_toApplicative_610_);
lean_dec_ref(v_inst_602_);
v_toPure_611_ = lean_ctor_get(v_toApplicative_610_, 1);
lean_inc(v_toPure_611_);
lean_dec_ref(v_toApplicative_610_);
v___x_612_ = lean_apply_2(v_toPure_611_, lean_box(0), v_init_604_);
return v___x_612_;
}
else
{
uint8_t v___x_613_; 
v___x_613_ = lean_nat_dec_le(v___x_608_, v___x_608_);
if (v___x_613_ == 0)
{
if (v___x_609_ == 0)
{
lean_object* v_toApplicative_614_; lean_object* v_toPure_615_; lean_object* v___x_616_; 
lean_dec_ref(v_toArray_606_);
lean_dec(v_f_603_);
v_toApplicative_614_ = lean_ctor_get(v_inst_602_, 0);
lean_inc_ref(v_toApplicative_614_);
lean_dec_ref(v_inst_602_);
v_toPure_615_ = lean_ctor_get(v_toApplicative_614_, 1);
lean_inc(v_toPure_615_);
lean_dec_ref(v_toApplicative_614_);
v___x_616_ = lean_apply_2(v_toPure_615_, lean_box(0), v_init_604_);
return v___x_616_;
}
else
{
size_t v___x_617_; size_t v___x_618_; lean_object* v___x_619_; 
v___x_617_ = ((size_t)0ULL);
v___x_618_ = lean_usize_of_nat(v___x_608_);
v___x_619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_602_, v_f_603_, v_toArray_606_, v___x_617_, v___x_618_, v_init_604_);
return v___x_619_;
}
}
else
{
size_t v___x_620_; size_t v___x_621_; lean_object* v___x_622_; 
v___x_620_ = ((size_t)0ULL);
v___x_621_ = lean_usize_of_nat(v___x_608_);
v___x_622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_602_, v_f_603_, v_toArray_606_, v___x_620_, v___x_621_, v_init_604_);
return v___x_622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldlM(lean_object* v_m_623_, lean_object* v_00_u03c3_624_, lean_object* v_00_u03b2_625_, lean_object* v_00_u03b1_626_, lean_object* v_cmp_627_, lean_object* v_inst_628_, lean_object* v_f_629_, lean_object* v_init_630_, lean_object* v_self_631_){
_start:
{
lean_object* v_toArray_632_; lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v_toArray_632_ = lean_ctor_get(v_self_631_, 1);
lean_inc_ref(v_toArray_632_);
lean_dec_ref(v_self_631_);
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_array_get_size(v_toArray_632_);
v___x_635_ = lean_nat_dec_lt(v___x_633_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v_toApplicative_636_; lean_object* v_toPure_637_; lean_object* v___x_638_; 
lean_dec_ref(v_toArray_632_);
lean_dec(v_f_629_);
v_toApplicative_636_ = lean_ctor_get(v_inst_628_, 0);
lean_inc_ref(v_toApplicative_636_);
lean_dec_ref(v_inst_628_);
v_toPure_637_ = lean_ctor_get(v_toApplicative_636_, 1);
lean_inc(v_toPure_637_);
lean_dec_ref(v_toApplicative_636_);
v___x_638_ = lean_apply_2(v_toPure_637_, lean_box(0), v_init_630_);
return v___x_638_;
}
else
{
uint8_t v___x_639_; 
v___x_639_ = lean_nat_dec_le(v___x_634_, v___x_634_);
if (v___x_639_ == 0)
{
if (v___x_635_ == 0)
{
lean_object* v_toApplicative_640_; lean_object* v_toPure_641_; lean_object* v___x_642_; 
lean_dec_ref(v_toArray_632_);
lean_dec(v_f_629_);
v_toApplicative_640_ = lean_ctor_get(v_inst_628_, 0);
lean_inc_ref(v_toApplicative_640_);
lean_dec_ref(v_inst_628_);
v_toPure_641_ = lean_ctor_get(v_toApplicative_640_, 1);
lean_inc(v_toPure_641_);
lean_dec_ref(v_toApplicative_640_);
v___x_642_ = lean_apply_2(v_toPure_641_, lean_box(0), v_init_630_);
return v___x_642_;
}
else
{
size_t v___x_643_; size_t v___x_644_; lean_object* v___x_645_; 
v___x_643_ = ((size_t)0ULL);
v___x_644_ = lean_usize_of_nat(v___x_634_);
v___x_645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_628_, v_f_629_, v_toArray_632_, v___x_643_, v___x_644_, v_init_630_);
return v___x_645_;
}
}
else
{
size_t v___x_646_; size_t v___x_647_; lean_object* v___x_648_; 
v___x_646_ = ((size_t)0ULL);
v___x_647_ = lean_usize_of_nat(v___x_634_);
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_628_, v_f_629_, v_toArray_632_, v___x_646_, v___x_647_, v_init_630_);
return v___x_648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldlM___boxed(lean_object* v_m_649_, lean_object* v_00_u03c3_650_, lean_object* v_00_u03b2_651_, lean_object* v_00_u03b1_652_, lean_object* v_cmp_653_, lean_object* v_inst_654_, lean_object* v_f_655_, lean_object* v_init_656_, lean_object* v_self_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lake_RBArray_foldlM(v_m_649_, v_00_u03c3_650_, v_00_u03b2_651_, v_00_u03b1_652_, v_cmp_653_, v_inst_654_, v_f_655_, v_init_656_, v_self_657_);
lean_dec_ref(v_cmp_653_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldr___redArg(lean_object* v_f_659_, lean_object* v_init_660_, lean_object* v_self_661_){
_start:
{
lean_object* v_toArray_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_toArray_662_ = lean_ctor_get(v_self_661_, 1);
lean_inc_ref(v_toArray_662_);
lean_dec_ref(v_self_661_);
v___x_663_ = lean_array_get_size(v_toArray_662_);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_666_ = lean_nat_dec_lt(v___x_664_, v___x_663_);
if (v___x_666_ == 0)
{
lean_dec_ref(v_toArray_662_);
lean_dec(v_f_659_);
return v_init_660_;
}
else
{
lean_object* v___f_667_; size_t v___x_668_; size_t v___x_669_; lean_object* v___x_670_; 
v___f_667_ = lean_alloc_closure((void*)(l_Lake_RBArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_667_, 0, v_f_659_);
v___x_668_ = lean_usize_of_nat(v___x_663_);
v___x_669_ = ((size_t)0ULL);
v___x_670_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_665_, v___f_667_, v_toArray_662_, v___x_668_, v___x_669_, v_init_660_);
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldr(lean_object* v_00_u03b2_671_, lean_object* v_00_u03c3_672_, lean_object* v_00_u03b1_673_, lean_object* v_cmp_674_, lean_object* v_f_675_, lean_object* v_init_676_, lean_object* v_self_677_){
_start:
{
lean_object* v_toArray_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_toArray_678_ = lean_ctor_get(v_self_677_, 1);
lean_inc_ref(v_toArray_678_);
lean_dec_ref(v_self_677_);
v___x_679_ = lean_array_get_size(v_toArray_678_);
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_682_ = lean_nat_dec_lt(v___x_680_, v___x_679_);
if (v___x_682_ == 0)
{
lean_dec_ref(v_toArray_678_);
lean_dec(v_f_675_);
return v_init_676_;
}
else
{
lean_object* v___f_683_; size_t v___x_684_; size_t v___x_685_; lean_object* v___x_686_; 
v___f_683_ = lean_alloc_closure((void*)(l_Lake_RBArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_683_, 0, v_f_675_);
v___x_684_ = lean_usize_of_nat(v___x_679_);
v___x_685_ = ((size_t)0ULL);
v___x_686_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_681_, v___f_683_, v_toArray_678_, v___x_684_, v___x_685_, v_init_676_);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldr___boxed(lean_object* v_00_u03b2_687_, lean_object* v_00_u03c3_688_, lean_object* v_00_u03b1_689_, lean_object* v_cmp_690_, lean_object* v_f_691_, lean_object* v_init_692_, lean_object* v_self_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lake_RBArray_foldr(v_00_u03b2_687_, v_00_u03c3_688_, v_00_u03b1_689_, v_cmp_690_, v_f_691_, v_init_692_, v_self_693_);
lean_dec_ref(v_cmp_690_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldrM___redArg(lean_object* v_inst_695_, lean_object* v_f_696_, lean_object* v_init_697_, lean_object* v_self_698_){
_start:
{
lean_object* v_toArray_699_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v_toArray_699_ = lean_ctor_get(v_self_698_, 1);
lean_inc_ref(v_toArray_699_);
lean_dec_ref(v_self_698_);
v___x_700_ = lean_array_get_size(v_toArray_699_);
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = lean_nat_dec_lt(v___x_701_, v___x_700_);
if (v___x_702_ == 0)
{
lean_object* v_toApplicative_703_; lean_object* v_toPure_704_; lean_object* v___x_705_; 
lean_dec_ref(v_toArray_699_);
lean_dec(v_f_696_);
v_toApplicative_703_ = lean_ctor_get(v_inst_695_, 0);
lean_inc_ref(v_toApplicative_703_);
lean_dec_ref(v_inst_695_);
v_toPure_704_ = lean_ctor_get(v_toApplicative_703_, 1);
lean_inc(v_toPure_704_);
lean_dec_ref(v_toApplicative_703_);
v___x_705_ = lean_apply_2(v_toPure_704_, lean_box(0), v_init_697_);
return v___x_705_;
}
else
{
size_t v___x_706_; size_t v___x_707_; lean_object* v___x_708_; 
v___x_706_ = lean_usize_of_nat(v___x_700_);
v___x_707_ = ((size_t)0ULL);
v___x_708_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_695_, v_f_696_, v_toArray_699_, v___x_706_, v___x_707_, v_init_697_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldrM(lean_object* v_m_709_, lean_object* v_00_u03b2_710_, lean_object* v_00_u03c3_711_, lean_object* v_00_u03b1_712_, lean_object* v_cmp_713_, lean_object* v_inst_714_, lean_object* v_f_715_, lean_object* v_init_716_, lean_object* v_self_717_){
_start:
{
lean_object* v_toArray_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v_toArray_718_ = lean_ctor_get(v_self_717_, 1);
lean_inc_ref(v_toArray_718_);
lean_dec_ref(v_self_717_);
v___x_719_ = lean_array_get_size(v_toArray_718_);
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = lean_nat_dec_lt(v___x_720_, v___x_719_);
if (v___x_721_ == 0)
{
lean_object* v_toApplicative_722_; lean_object* v_toPure_723_; lean_object* v___x_724_; 
lean_dec_ref(v_toArray_718_);
lean_dec(v_f_715_);
v_toApplicative_722_ = lean_ctor_get(v_inst_714_, 0);
lean_inc_ref(v_toApplicative_722_);
lean_dec_ref(v_inst_714_);
v_toPure_723_ = lean_ctor_get(v_toApplicative_722_, 1);
lean_inc(v_toPure_723_);
lean_dec_ref(v_toApplicative_722_);
v___x_724_ = lean_apply_2(v_toPure_723_, lean_box(0), v_init_716_);
return v___x_724_;
}
else
{
size_t v___x_725_; size_t v___x_726_; lean_object* v___x_727_; 
v___x_725_ = lean_usize_of_nat(v___x_719_);
v___x_726_ = ((size_t)0ULL);
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_714_, v_f_715_, v_toArray_718_, v___x_725_, v___x_726_, v_init_716_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldrM___boxed(lean_object* v_m_728_, lean_object* v_00_u03b2_729_, lean_object* v_00_u03c3_730_, lean_object* v_00_u03b1_731_, lean_object* v_cmp_732_, lean_object* v_inst_733_, lean_object* v_f_734_, lean_object* v_init_735_, lean_object* v_self_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lake_RBArray_foldrM(v_m_728_, v_00_u03b2_729_, v_00_u03c3_730_, v_00_u03b1_731_, v_cmp_732_, v_inst_733_, v_f_734_, v_init_735_, v_self_736_);
lean_dec_ref(v_cmp_732_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM___redArg___lam__0(lean_object* v_f_738_, lean_object* v_x_739_, lean_object* v___y_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = lean_apply_1(v_f_738_, v___y_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM___redArg(lean_object* v_inst_742_, lean_object* v_f_743_, lean_object* v_self_744_){
_start:
{
lean_object* v_toArray_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v_toArray_745_ = lean_ctor_get(v_self_744_, 1);
lean_inc_ref(v_toArray_745_);
lean_dec_ref(v_self_744_);
v___x_746_ = lean_unsigned_to_nat(0u);
v___x_747_ = lean_array_get_size(v_toArray_745_);
v___x_748_ = lean_box(0);
v___x_749_ = lean_nat_dec_lt(v___x_746_, v___x_747_);
if (v___x_749_ == 0)
{
lean_object* v_toApplicative_750_; lean_object* v_toPure_751_; lean_object* v___x_752_; 
lean_dec_ref(v_toArray_745_);
lean_dec(v_f_743_);
v_toApplicative_750_ = lean_ctor_get(v_inst_742_, 0);
lean_inc_ref(v_toApplicative_750_);
lean_dec_ref(v_inst_742_);
v_toPure_751_ = lean_ctor_get(v_toApplicative_750_, 1);
lean_inc(v_toPure_751_);
lean_dec_ref(v_toApplicative_750_);
v___x_752_ = lean_apply_2(v_toPure_751_, lean_box(0), v___x_748_);
return v___x_752_;
}
else
{
lean_object* v___f_753_; uint8_t v___x_754_; 
v___f_753_ = lean_alloc_closure((void*)(l_Lake_RBArray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_753_, 0, v_f_743_);
v___x_754_ = lean_nat_dec_le(v___x_747_, v___x_747_);
if (v___x_754_ == 0)
{
if (v___x_749_ == 0)
{
lean_object* v_toApplicative_755_; lean_object* v_toPure_756_; lean_object* v___x_757_; 
lean_dec_ref(v___f_753_);
lean_dec_ref(v_toArray_745_);
v_toApplicative_755_ = lean_ctor_get(v_inst_742_, 0);
lean_inc_ref(v_toApplicative_755_);
lean_dec_ref(v_inst_742_);
v_toPure_756_ = lean_ctor_get(v_toApplicative_755_, 1);
lean_inc(v_toPure_756_);
lean_dec_ref(v_toApplicative_755_);
v___x_757_ = lean_apply_2(v_toPure_756_, lean_box(0), v___x_748_);
return v___x_757_;
}
else
{
size_t v___x_758_; size_t v___x_759_; lean_object* v___x_760_; 
v___x_758_ = ((size_t)0ULL);
v___x_759_ = lean_usize_of_nat(v___x_747_);
v___x_760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_742_, v___f_753_, v_toArray_745_, v___x_758_, v___x_759_, v___x_748_);
return v___x_760_;
}
}
else
{
size_t v___x_761_; size_t v___x_762_; lean_object* v___x_763_; 
v___x_761_ = ((size_t)0ULL);
v___x_762_ = lean_usize_of_nat(v___x_747_);
v___x_763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_742_, v___f_753_, v_toArray_745_, v___x_761_, v___x_762_, v___x_748_);
return v___x_763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM(lean_object* v_m_764_, lean_object* v_00_u03b2_765_, lean_object* v_00_u03b1_766_, lean_object* v_cmp_767_, lean_object* v_inst_768_, lean_object* v_f_769_, lean_object* v_self_770_){
_start:
{
lean_object* v_toArray_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_toArray_771_ = lean_ctor_get(v_self_770_, 1);
lean_inc_ref(v_toArray_771_);
lean_dec_ref(v_self_770_);
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = lean_array_get_size(v_toArray_771_);
v___x_774_ = lean_box(0);
v___x_775_ = lean_nat_dec_lt(v___x_772_, v___x_773_);
if (v___x_775_ == 0)
{
lean_object* v_toApplicative_776_; lean_object* v_toPure_777_; lean_object* v___x_778_; 
lean_dec_ref(v_toArray_771_);
lean_dec(v_f_769_);
v_toApplicative_776_ = lean_ctor_get(v_inst_768_, 0);
lean_inc_ref(v_toApplicative_776_);
lean_dec_ref(v_inst_768_);
v_toPure_777_ = lean_ctor_get(v_toApplicative_776_, 1);
lean_inc(v_toPure_777_);
lean_dec_ref(v_toApplicative_776_);
v___x_778_ = lean_apply_2(v_toPure_777_, lean_box(0), v___x_774_);
return v___x_778_;
}
else
{
lean_object* v___f_779_; uint8_t v___x_780_; 
v___f_779_ = lean_alloc_closure((void*)(l_Lake_RBArray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_779_, 0, v_f_769_);
v___x_780_ = lean_nat_dec_le(v___x_773_, v___x_773_);
if (v___x_780_ == 0)
{
if (v___x_775_ == 0)
{
lean_object* v_toApplicative_781_; lean_object* v_toPure_782_; lean_object* v___x_783_; 
lean_dec_ref(v___f_779_);
lean_dec_ref(v_toArray_771_);
v_toApplicative_781_ = lean_ctor_get(v_inst_768_, 0);
lean_inc_ref(v_toApplicative_781_);
lean_dec_ref(v_inst_768_);
v_toPure_782_ = lean_ctor_get(v_toApplicative_781_, 1);
lean_inc(v_toPure_782_);
lean_dec_ref(v_toApplicative_781_);
v___x_783_ = lean_apply_2(v_toPure_782_, lean_box(0), v___x_774_);
return v___x_783_;
}
else
{
size_t v___x_784_; size_t v___x_785_; lean_object* v___x_786_; 
v___x_784_ = ((size_t)0ULL);
v___x_785_ = lean_usize_of_nat(v___x_773_);
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_768_, v___f_779_, v_toArray_771_, v___x_784_, v___x_785_, v___x_774_);
return v___x_786_;
}
}
else
{
size_t v___x_787_; size_t v___x_788_; lean_object* v___x_789_; 
v___x_787_ = ((size_t)0ULL);
v___x_788_ = lean_usize_of_nat(v___x_773_);
v___x_789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_768_, v___f_779_, v_toArray_771_, v___x_787_, v___x_788_, v___x_774_);
return v___x_789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM___boxed(lean_object* v_m_790_, lean_object* v_00_u03b2_791_, lean_object* v_00_u03b1_792_, lean_object* v_cmp_793_, lean_object* v_inst_794_, lean_object* v_f_795_, lean_object* v_self_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lake_RBArray_forM(v_m_790_, v_00_u03b2_791_, v_00_u03b1_792_, v_cmp_793_, v_inst_794_, v_f_795_, v_self_796_);
lean_dec_ref(v_cmp_793_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn___redArg___lam__0(lean_object* v_f_798_, lean_object* v_a_799_, lean_object* v_x_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = lean_apply_2(v_f_798_, v_a_799_, v___y_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn___redArg(lean_object* v_inst_803_, lean_object* v_self_804_, lean_object* v_init_805_, lean_object* v_f_806_){
_start:
{
lean_object* v_toArray_807_; lean_object* v___f_808_; size_t v_sz_809_; size_t v___x_810_; lean_object* v___x_811_; 
v_toArray_807_ = lean_ctor_get(v_self_804_, 1);
lean_inc_ref(v_toArray_807_);
lean_dec_ref(v_self_804_);
v___f_808_ = lean_alloc_closure((void*)(l_Lake_RBArray_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_808_, 0, v_f_806_);
v_sz_809_ = lean_array_size(v_toArray_807_);
v___x_810_ = ((size_t)0ULL);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_803_, v_toArray_807_, v___f_808_, v_sz_809_, v___x_810_, v_init_805_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn(lean_object* v_m_812_, lean_object* v_00_u03b1_813_, lean_object* v_00_u03b2_814_, lean_object* v_cmp_815_, lean_object* v_00_u03c3_816_, lean_object* v_inst_817_, lean_object* v_self_818_, lean_object* v_init_819_, lean_object* v_f_820_){
_start:
{
lean_object* v_toArray_821_; lean_object* v___f_822_; size_t v_sz_823_; size_t v___x_824_; lean_object* v___x_825_; 
v_toArray_821_ = lean_ctor_get(v_self_818_, 1);
lean_inc_ref(v_toArray_821_);
lean_dec_ref(v_self_818_);
v___f_822_ = lean_alloc_closure((void*)(l_Lake_RBArray_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_822_, 0, v_f_820_);
v_sz_823_ = lean_array_size(v_toArray_821_);
v___x_824_ = ((size_t)0ULL);
v___x_825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_817_, v_toArray_821_, v___f_822_, v_sz_823_, v___x_824_, v_init_819_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn___boxed(lean_object* v_m_826_, lean_object* v_00_u03b1_827_, lean_object* v_00_u03b2_828_, lean_object* v_cmp_829_, lean_object* v_00_u03c3_830_, lean_object* v_inst_831_, lean_object* v_self_832_, lean_object* v_init_833_, lean_object* v_f_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lake_RBArray_forIn(v_m_826_, v_00_u03b1_827_, v_00_u03b2_828_, v_cmp_829_, v_00_u03c3_830_, v_inst_831_, v_self_832_, v_init_833_, v_f_834_);
lean_dec_ref(v_cmp_829_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__0(lean_object* v___y_836_, lean_object* v_a_837_, lean_object* v_x_838_, lean_object* v___y_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = lean_apply_2(v___y_836_, v_a_837_, v___y_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1(lean_object* v_inst_841_, lean_object* v_00_u03b2_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_toArray_846_; lean_object* v___f_847_; size_t v_sz_848_; size_t v___x_849_; lean_object* v___x_850_; 
v_toArray_846_ = lean_ctor_get(v___y_843_, 1);
lean_inc_ref(v_toArray_846_);
lean_dec_ref(v___y_843_);
v___f_847_ = lean_alloc_closure((void*)(l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_847_, 0, v___y_845_);
v_sz_848_ = lean_array_size(v_toArray_846_);
v___x_849_ = ((size_t)0ULL);
v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_841_, v_toArray_846_, v___f_847_, v_sz_848_, v___x_849_, v___y_844_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg(lean_object* v_inst_851_){
_start:
{
lean_object* v___f_852_; 
v___f_852_ = lean_alloc_closure((void*)(l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_852_, 0, v_inst_851_);
return v___f_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad(lean_object* v_m_853_, lean_object* v_00_u03b1_854_, lean_object* v_00_u03b2_855_, lean_object* v_cmp_856_, lean_object* v_inst_857_){
_start:
{
lean_object* v___f_858_; 
v___f_858_ = lean_alloc_closure((void*)(l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_858_, 0, v_inst_857_);
return v___f_858_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___boxed(lean_object* v_m_859_, lean_object* v_00_u03b1_860_, lean_object* v_00_u03b2_861_, lean_object* v_cmp_862_, lean_object* v_inst_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad(v_m_859_, v_00_u03b1_860_, v_00_u03b2_861_, v_cmp_862_, v_inst_863_);
lean_dec_ref(v_cmp_862_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkRBArray___redArg___lam__0(lean_object* v_f_865_, lean_object* v_cmp_866_, lean_object* v_x1_867_, lean_object* v_x2_868_){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
lean_inc(v_x2_868_);
v___x_869_ = lean_apply_1(v_f_865_, v_x2_868_);
v___x_870_ = l_Lake_RBArray_insert___redArg(v_cmp_866_, v_x1_867_, v___x_869_, v_x2_868_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkRBArray___redArg(lean_object* v_cmp_871_, lean_object* v_f_872_, lean_object* v_vs_873_){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_874_ = lean_array_get_size(v_vs_873_);
v___x_875_ = l_Lake_RBArray_mkEmpty___redArg(v___x_874_);
v___x_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_878_ = lean_nat_dec_lt(v___x_876_, v___x_874_);
if (v___x_878_ == 0)
{
lean_dec_ref(v_vs_873_);
lean_dec(v_f_872_);
lean_dec_ref(v_cmp_871_);
return v___x_875_;
}
else
{
lean_object* v___f_879_; uint8_t v___x_880_; 
v___f_879_ = lean_alloc_closure((void*)(l_Lake_mkRBArray___redArg___lam__0), 4, 2);
lean_closure_set(v___f_879_, 0, v_f_872_);
lean_closure_set(v___f_879_, 1, v_cmp_871_);
v___x_880_ = lean_nat_dec_le(v___x_874_, v___x_874_);
if (v___x_880_ == 0)
{
if (v___x_878_ == 0)
{
lean_dec_ref(v___f_879_);
lean_dec_ref(v_vs_873_);
return v___x_875_;
}
else
{
size_t v___x_881_; size_t v___x_882_; lean_object* v___x_883_; 
v___x_881_ = ((size_t)0ULL);
v___x_882_ = lean_usize_of_nat(v___x_874_);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_877_, v___f_879_, v_vs_873_, v___x_881_, v___x_882_, v___x_875_);
return v___x_883_;
}
}
else
{
size_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; 
v___x_884_ = ((size_t)0ULL);
v___x_885_ = lean_usize_of_nat(v___x_874_);
v___x_886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_877_, v___f_879_, v_vs_873_, v___x_884_, v___x_885_, v___x_875_);
return v___x_886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkRBArray(lean_object* v_00_u03b2_887_, lean_object* v_00_u03b1_888_, lean_object* v_cmp_889_, lean_object* v_f_890_, lean_object* v_vs_891_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_892_ = lean_array_get_size(v_vs_891_);
v___x_893_ = l_Lake_RBArray_mkEmpty___redArg(v___x_892_);
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_896_ = lean_nat_dec_lt(v___x_894_, v___x_892_);
if (v___x_896_ == 0)
{
lean_dec_ref(v_vs_891_);
lean_dec(v_f_890_);
lean_dec_ref(v_cmp_889_);
return v___x_893_;
}
else
{
lean_object* v___f_897_; uint8_t v___x_898_; 
v___f_897_ = lean_alloc_closure((void*)(l_Lake_mkRBArray___redArg___lam__0), 4, 2);
lean_closure_set(v___f_897_, 0, v_f_890_);
lean_closure_set(v___f_897_, 1, v_cmp_889_);
v___x_898_ = lean_nat_dec_le(v___x_892_, v___x_892_);
if (v___x_898_ == 0)
{
if (v___x_896_ == 0)
{
lean_dec_ref(v___f_897_);
lean_dec_ref(v_vs_891_);
return v___x_893_;
}
else
{
size_t v___x_899_; size_t v___x_900_; lean_object* v___x_901_; 
v___x_899_ = ((size_t)0ULL);
v___x_900_ = lean_usize_of_nat(v___x_892_);
v___x_901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_895_, v___f_897_, v_vs_891_, v___x_899_, v___x_900_, v___x_893_);
return v___x_901_;
}
}
else
{
size_t v___x_902_; size_t v___x_903_; lean_object* v___x_904_; 
v___x_902_ = ((size_t)0ULL);
v___x_903_ = lean_usize_of_nat(v___x_892_);
v___x_904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_895_, v___f_897_, v_vs_891_, v___x_902_, v___x_903_, v___x_893_);
return v___x_904_;
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
