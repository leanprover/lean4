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
static const lean_array_object l_Lake_RBArray_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_RBArray_empty___redArg___closed__0 = (const lean_object*)&l_Lake_RBArray_empty___redArg___closed__0_value;
static const lean_ctor_object l_Lake_RBArray_empty___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lake_RBArray_empty___redArg___closed__0_value)}};
static const lean_object* l_Lake_RBArray_empty___redArg___closed__1 = (const lean_object*)&l_Lake_RBArray_empty___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_RBArray_empty___redArg();
LEAN_EXPORT lean_object* l_Lake_RBArray_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_RBArray_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_RBArray_empty___closed__0;
LEAN_EXPORT lean_object* l_Lake_RBArray_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg();
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
LEAN_EXPORT lean_object* l_Lake_RBArray_empty___redArg(){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = ((lean_object*)(l_Lake_RBArray_empty___redArg___closed__1));
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_empty___redArg___boxed(lean_object* v___dummy_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lake_RBArray_empty___redArg();
return v_res_9_;
}
}
static lean_object* _init_l_Lake_RBArray_empty___closed__0(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lake_RBArray_empty___redArg();
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_empty(lean_object* v_00_u03b1_11_, lean_object* v_00_u03b2_12_, lean_object* v_cmp_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&l_Lake_RBArray_empty___closed__0, &l_Lake_RBArray_empty___closed__0_once, _init_l_Lake_RBArray_empty___closed__0);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_empty___boxed(lean_object* v_00_u03b1_15_, lean_object* v_00_u03b2_16_, lean_object* v_cmp_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lake_RBArray_empty(v_00_u03b1_15_, v_00_u03b2_16_, v_cmp_17_);
lean_dec_ref(v_cmp_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_obj_once(&l_Lake_RBArray_empty___closed__0, &l_Lake_RBArray_empty___closed__0_once, _init_l_Lake_RBArray_empty___closed__0);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg___boxed(lean_object* v___dummy_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg();
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection(lean_object* v_00_u03b1_23_, lean_object* v_00_u03b2_24_, lean_object* v_cmp_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_obj_once(&l_Lake_RBArray_empty___closed__0, &l_Lake_RBArray_empty___closed__0_once, _init_l_Lake_RBArray_empty___closed__0);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___boxed(lean_object* v_00_u03b1_27_, lean_object* v_00_u03b2_28_, lean_object* v_cmp_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection(v_00_u03b1_27_, v_00_u03b2_28_, v_cmp_29_);
lean_dec_ref(v_cmp_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_mkEmpty___redArg(lean_object* v_size_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_32_ = lean_box(1);
v___x_33_ = lean_mk_empty_array_with_capacity(v_size_31_);
v___x_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_32_);
lean_ctor_set(v___x_34_, 1, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_mkEmpty___redArg___boxed(lean_object* v_size_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lake_RBArray_mkEmpty___redArg(v_size_35_);
lean_dec(v_size_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_mkEmpty(lean_object* v_00_u03b1_37_, lean_object* v_00_u03b2_38_, lean_object* v_cmp_39_, lean_object* v_size_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lake_RBArray_mkEmpty___redArg(v_size_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_mkEmpty___boxed(lean_object* v_00_u03b1_42_, lean_object* v_00_u03b2_43_, lean_object* v_cmp_44_, lean_object* v_size_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lake_RBArray_mkEmpty(v_00_u03b1_42_, v_00_u03b2_43_, v_cmp_44_, v_size_45_);
lean_dec(v_size_45_);
lean_dec_ref(v_cmp_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_find_x3f___redArg(lean_object* v_cmp_47_, lean_object* v_self_48_, lean_object* v_a_49_){
_start:
{
lean_object* v_toTreeMap_50_; lean_object* v___x_51_; 
v_toTreeMap_50_ = lean_ctor_get(v_self_48_, 0);
lean_inc(v_toTreeMap_50_);
lean_dec_ref(v_self_48_);
v___x_51_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_47_, v_toTreeMap_50_, v_a_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_find_x3f(lean_object* v_00_u03b1_52_, lean_object* v_00_u03b2_53_, lean_object* v_cmp_54_, lean_object* v_self_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_toTreeMap_57_; lean_object* v___x_58_; 
v_toTreeMap_57_ = lean_ctor_get(v_self_55_, 0);
lean_inc(v_toTreeMap_57_);
lean_dec_ref(v_self_55_);
v___x_58_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_54_, v_toTreeMap_57_, v_a_56_);
return v___x_58_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_contains___redArg(lean_object* v_cmp_59_, lean_object* v_self_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_toTreeMap_62_; uint8_t v___x_63_; 
v_toTreeMap_62_ = lean_ctor_get(v_self_60_, 0);
lean_inc(v_toTreeMap_62_);
lean_dec_ref(v_self_60_);
v___x_63_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_59_, v_a_61_, v_toTreeMap_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_contains___redArg___boxed(lean_object* v_cmp_64_, lean_object* v_self_65_, lean_object* v_a_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l_Lake_RBArray_contains___redArg(v_cmp_64_, v_self_65_, v_a_66_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_contains(lean_object* v_00_u03b1_69_, lean_object* v_00_u03b2_70_, lean_object* v_cmp_71_, lean_object* v_self_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_toTreeMap_74_; uint8_t v___x_75_; 
v_toTreeMap_74_ = lean_ctor_get(v_self_72_, 0);
lean_inc(v_toTreeMap_74_);
lean_dec_ref(v_self_72_);
v___x_75_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_71_, v_a_73_, v_toTreeMap_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_contains___boxed(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_cmp_78_, lean_object* v_self_79_, lean_object* v_a_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Lake_RBArray_contains(v_00_u03b1_76_, v_00_u03b2_77_, v_cmp_78_, v_self_79_, v_a_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(lean_object* v_cmp_83_, lean_object* v_k_84_, lean_object* v_v_85_, lean_object* v_t_86_){
_start:
{
if (lean_obj_tag(v_t_86_) == 0)
{
lean_object* v_size_87_; lean_object* v_k_88_; lean_object* v_v_89_; lean_object* v_l_90_; lean_object* v_r_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_372_; 
v_size_87_ = lean_ctor_get(v_t_86_, 0);
v_k_88_ = lean_ctor_get(v_t_86_, 1);
v_v_89_ = lean_ctor_get(v_t_86_, 2);
v_l_90_ = lean_ctor_get(v_t_86_, 3);
v_r_91_ = lean_ctor_get(v_t_86_, 4);
v_isSharedCheck_372_ = !lean_is_exclusive(v_t_86_);
if (v_isSharedCheck_372_ == 0)
{
v___x_93_ = v_t_86_;
v_isShared_94_ = v_isSharedCheck_372_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_r_91_);
lean_inc(v_l_90_);
lean_inc(v_v_89_);
lean_inc(v_k_88_);
lean_inc(v_size_87_);
lean_dec(v_t_86_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_372_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; uint8_t v___x_96_; 
lean_inc_ref(v_cmp_83_);
lean_inc(v_k_88_);
lean_inc(v_k_84_);
v___x_95_ = lean_apply_2(v_cmp_83_, v_k_84_, v_k_88_);
v___x_96_ = lean_unbox(v___x_95_);
switch(v___x_96_)
{
case 0:
{
lean_object* v_impl_97_; lean_object* v___x_98_; 
lean_dec(v_size_87_);
v_impl_97_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_83_, v_k_84_, v_v_85_, v_l_90_);
v___x_98_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_91_) == 0)
{
lean_object* v_size_99_; lean_object* v_size_100_; lean_object* v_k_101_; lean_object* v_v_102_; lean_object* v_l_103_; lean_object* v_r_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v_size_99_ = lean_ctor_get(v_r_91_, 0);
v_size_100_ = lean_ctor_get(v_impl_97_, 0);
lean_inc(v_size_100_);
v_k_101_ = lean_ctor_get(v_impl_97_, 1);
lean_inc(v_k_101_);
v_v_102_ = lean_ctor_get(v_impl_97_, 2);
lean_inc(v_v_102_);
v_l_103_ = lean_ctor_get(v_impl_97_, 3);
lean_inc(v_l_103_);
v_r_104_ = lean_ctor_get(v_impl_97_, 4);
lean_inc(v_r_104_);
v___x_105_ = lean_unsigned_to_nat(3u);
v___x_106_ = lean_nat_mul(v___x_105_, v_size_99_);
v___x_107_ = lean_nat_dec_lt(v___x_106_, v_size_100_);
lean_dec(v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
lean_dec(v_r_104_);
lean_dec(v_l_103_);
lean_dec(v_v_102_);
lean_dec(v_k_101_);
v___x_108_ = lean_nat_add(v___x_98_, v_size_100_);
lean_dec(v_size_100_);
v___x_109_ = lean_nat_add(v___x_108_, v_size_99_);
lean_dec(v___x_108_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 3, v_impl_97_);
lean_ctor_set(v___x_93_, 0, v___x_109_);
v___x_111_ = v___x_93_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_k_88_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v_v_89_);
lean_ctor_set(v_reuseFailAlloc_112_, 3, v_impl_97_);
lean_ctor_set(v_reuseFailAlloc_112_, 4, v_r_91_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
else
{
lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_178_; 
v_isSharedCheck_178_ = !lean_is_exclusive(v_impl_97_);
if (v_isSharedCheck_178_ == 0)
{
lean_object* v_unused_179_; lean_object* v_unused_180_; lean_object* v_unused_181_; lean_object* v_unused_182_; lean_object* v_unused_183_; 
v_unused_179_ = lean_ctor_get(v_impl_97_, 4);
lean_dec(v_unused_179_);
v_unused_180_ = lean_ctor_get(v_impl_97_, 3);
lean_dec(v_unused_180_);
v_unused_181_ = lean_ctor_get(v_impl_97_, 2);
lean_dec(v_unused_181_);
v_unused_182_ = lean_ctor_get(v_impl_97_, 1);
lean_dec(v_unused_182_);
v_unused_183_ = lean_ctor_get(v_impl_97_, 0);
lean_dec(v_unused_183_);
v___x_114_ = v_impl_97_;
v_isShared_115_ = v_isSharedCheck_178_;
goto v_resetjp_113_;
}
else
{
lean_dec(v_impl_97_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_178_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v_size_116_; lean_object* v_size_117_; lean_object* v_k_118_; lean_object* v_v_119_; lean_object* v_l_120_; lean_object* v_r_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_size_116_ = lean_ctor_get(v_l_103_, 0);
v_size_117_ = lean_ctor_get(v_r_104_, 0);
v_k_118_ = lean_ctor_get(v_r_104_, 1);
v_v_119_ = lean_ctor_get(v_r_104_, 2);
v_l_120_ = lean_ctor_get(v_r_104_, 3);
v_r_121_ = lean_ctor_get(v_r_104_, 4);
v___x_122_ = lean_unsigned_to_nat(2u);
v___x_123_ = lean_nat_mul(v___x_122_, v_size_116_);
v___x_124_ = lean_nat_dec_lt(v_size_117_, v___x_123_);
lean_dec(v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_153_; 
lean_inc(v_r_121_);
lean_inc(v_l_120_);
lean_inc(v_v_119_);
lean_inc(v_k_118_);
v_isSharedCheck_153_ = !lean_is_exclusive(v_r_104_);
if (v_isSharedCheck_153_ == 0)
{
lean_object* v_unused_154_; lean_object* v_unused_155_; lean_object* v_unused_156_; lean_object* v_unused_157_; lean_object* v_unused_158_; 
v_unused_154_ = lean_ctor_get(v_r_104_, 4);
lean_dec(v_unused_154_);
v_unused_155_ = lean_ctor_get(v_r_104_, 3);
lean_dec(v_unused_155_);
v_unused_156_ = lean_ctor_get(v_r_104_, 2);
lean_dec(v_unused_156_);
v_unused_157_ = lean_ctor_get(v_r_104_, 1);
lean_dec(v_unused_157_);
v_unused_158_ = lean_ctor_get(v_r_104_, 0);
lean_dec(v_unused_158_);
v___x_126_ = v_r_104_;
v_isShared_127_ = v_isSharedCheck_153_;
goto v_resetjp_125_;
}
else
{
lean_dec(v_r_104_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_153_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___y_131_; lean_object* v___y_132_; lean_object* v___y_133_; lean_object* v___x_141_; lean_object* v___y_143_; 
v___x_128_ = lean_nat_add(v___x_98_, v_size_100_);
lean_dec(v_size_100_);
v___x_129_ = lean_nat_add(v___x_128_, v_size_99_);
lean_dec(v___x_128_);
v___x_141_ = lean_nat_add(v___x_98_, v_size_116_);
if (lean_obj_tag(v_l_120_) == 0)
{
lean_object* v_size_151_; 
v_size_151_ = lean_ctor_get(v_l_120_, 0);
lean_inc(v_size_151_);
v___y_143_ = v_size_151_;
goto v___jp_142_;
}
else
{
lean_object* v___x_152_; 
v___x_152_ = lean_unsigned_to_nat(0u);
v___y_143_ = v___x_152_;
goto v___jp_142_;
}
v___jp_130_:
{
lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_134_ = lean_nat_add(v___y_132_, v___y_133_);
lean_dec(v___y_133_);
lean_dec(v___y_132_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 4, v_r_91_);
lean_ctor_set(v___x_126_, 3, v_r_121_);
lean_ctor_set(v___x_126_, 2, v_v_89_);
lean_ctor_set(v___x_126_, 1, v_k_88_);
lean_ctor_set(v___x_126_, 0, v___x_134_);
v___x_136_ = v___x_126_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_k_88_);
lean_ctor_set(v_reuseFailAlloc_140_, 2, v_v_89_);
lean_ctor_set(v_reuseFailAlloc_140_, 3, v_r_121_);
lean_ctor_set(v_reuseFailAlloc_140_, 4, v_r_91_);
v___x_136_ = v_reuseFailAlloc_140_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_138_; 
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 4, v___x_136_);
lean_ctor_set(v___x_114_, 3, v___y_131_);
lean_ctor_set(v___x_114_, 2, v_v_119_);
lean_ctor_set(v___x_114_, 1, v_k_118_);
lean_ctor_set(v___x_114_, 0, v___x_129_);
v___x_138_ = v___x_114_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_k_118_);
lean_ctor_set(v_reuseFailAlloc_139_, 2, v_v_119_);
lean_ctor_set(v_reuseFailAlloc_139_, 3, v___y_131_);
lean_ctor_set(v_reuseFailAlloc_139_, 4, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
v___jp_142_:
{
lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_144_ = lean_nat_add(v___x_141_, v___y_143_);
lean_dec(v___y_143_);
lean_dec(v___x_141_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 4, v_l_120_);
lean_ctor_set(v___x_93_, 3, v_l_103_);
lean_ctor_set(v___x_93_, 2, v_v_102_);
lean_ctor_set(v___x_93_, 1, v_k_101_);
lean_ctor_set(v___x_93_, 0, v___x_144_);
v___x_146_ = v___x_93_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_k_101_);
lean_ctor_set(v_reuseFailAlloc_150_, 2, v_v_102_);
lean_ctor_set(v_reuseFailAlloc_150_, 3, v_l_103_);
lean_ctor_set(v_reuseFailAlloc_150_, 4, v_l_120_);
v___x_146_ = v_reuseFailAlloc_150_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; 
v___x_147_ = lean_nat_add(v___x_98_, v_size_99_);
if (lean_obj_tag(v_r_121_) == 0)
{
lean_object* v_size_148_; 
v_size_148_ = lean_ctor_get(v_r_121_, 0);
lean_inc(v_size_148_);
v___y_131_ = v___x_146_;
v___y_132_ = v___x_147_;
v___y_133_ = v_size_148_;
goto v___jp_130_;
}
else
{
lean_object* v___x_149_; 
v___x_149_ = lean_unsigned_to_nat(0u);
v___y_131_ = v___x_146_;
v___y_132_ = v___x_147_;
v___y_133_ = v___x_149_;
goto v___jp_130_;
}
}
}
}
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_164_; 
lean_del_object(v___x_93_);
v___x_159_ = lean_nat_add(v___x_98_, v_size_100_);
lean_dec(v_size_100_);
v___x_160_ = lean_nat_add(v___x_159_, v_size_99_);
lean_dec(v___x_159_);
v___x_161_ = lean_nat_add(v___x_98_, v_size_99_);
v___x_162_ = lean_nat_add(v___x_161_, v_size_117_);
lean_dec(v___x_161_);
lean_inc_ref(v_r_91_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 4, v_r_91_);
lean_ctor_set(v___x_114_, 3, v_r_104_);
lean_ctor_set(v___x_114_, 2, v_v_89_);
lean_ctor_set(v___x_114_, 1, v_k_88_);
lean_ctor_set(v___x_114_, 0, v___x_162_);
v___x_164_ = v___x_114_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_k_88_);
lean_ctor_set(v_reuseFailAlloc_177_, 2, v_v_89_);
lean_ctor_set(v_reuseFailAlloc_177_, 3, v_r_104_);
lean_ctor_set(v_reuseFailAlloc_177_, 4, v_r_91_);
v___x_164_ = v_reuseFailAlloc_177_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
v_isSharedCheck_171_ = !lean_is_exclusive(v_r_91_);
if (v_isSharedCheck_171_ == 0)
{
lean_object* v_unused_172_; lean_object* v_unused_173_; lean_object* v_unused_174_; lean_object* v_unused_175_; lean_object* v_unused_176_; 
v_unused_172_ = lean_ctor_get(v_r_91_, 4);
lean_dec(v_unused_172_);
v_unused_173_ = lean_ctor_get(v_r_91_, 3);
lean_dec(v_unused_173_);
v_unused_174_ = lean_ctor_get(v_r_91_, 2);
lean_dec(v_unused_174_);
v_unused_175_ = lean_ctor_get(v_r_91_, 1);
lean_dec(v_unused_175_);
v_unused_176_ = lean_ctor_get(v_r_91_, 0);
lean_dec(v_unused_176_);
v___x_166_ = v_r_91_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_dec(v_r_91_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 4, v___x_164_);
lean_ctor_set(v___x_166_, 3, v_l_103_);
lean_ctor_set(v___x_166_, 2, v_v_102_);
lean_ctor_set(v___x_166_, 1, v_k_101_);
lean_ctor_set(v___x_166_, 0, v___x_160_);
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_k_101_);
lean_ctor_set(v_reuseFailAlloc_170_, 2, v_v_102_);
lean_ctor_set(v_reuseFailAlloc_170_, 3, v_l_103_);
lean_ctor_set(v_reuseFailAlloc_170_, 4, v___x_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_184_; 
v_l_184_ = lean_ctor_get(v_impl_97_, 3);
lean_inc(v_l_184_);
if (lean_obj_tag(v_l_184_) == 0)
{
lean_object* v_r_185_; lean_object* v_k_186_; lean_object* v_v_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_198_; 
v_r_185_ = lean_ctor_get(v_impl_97_, 4);
v_k_186_ = lean_ctor_get(v_impl_97_, 1);
v_v_187_ = lean_ctor_get(v_impl_97_, 2);
v_isSharedCheck_198_ = !lean_is_exclusive(v_impl_97_);
if (v_isSharedCheck_198_ == 0)
{
lean_object* v_unused_199_; lean_object* v_unused_200_; 
v_unused_199_ = lean_ctor_get(v_impl_97_, 3);
lean_dec(v_unused_199_);
v_unused_200_ = lean_ctor_get(v_impl_97_, 0);
lean_dec(v_unused_200_);
v___x_189_ = v_impl_97_;
v_isShared_190_ = v_isSharedCheck_198_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_r_185_);
lean_inc(v_v_187_);
lean_inc(v_k_186_);
lean_dec(v_impl_97_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_198_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_191_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_185_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 3, v_r_185_);
lean_ctor_set(v___x_189_, 2, v_v_89_);
lean_ctor_set(v___x_189_, 1, v_k_88_);
lean_ctor_set(v___x_189_, 0, v___x_98_);
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_k_88_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v_v_89_);
lean_ctor_set(v_reuseFailAlloc_197_, 3, v_r_185_);
lean_ctor_set(v_reuseFailAlloc_197_, 4, v_r_185_);
v___x_193_ = v_reuseFailAlloc_197_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_195_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 4, v___x_193_);
lean_ctor_set(v___x_93_, 3, v_l_184_);
lean_ctor_set(v___x_93_, 2, v_v_187_);
lean_ctor_set(v___x_93_, 1, v_k_186_);
lean_ctor_set(v___x_93_, 0, v___x_191_);
v___x_195_ = v___x_93_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_k_186_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_v_187_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v_l_184_);
lean_ctor_set(v_reuseFailAlloc_196_, 4, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
else
{
lean_object* v_r_201_; 
v_r_201_ = lean_ctor_get(v_impl_97_, 4);
lean_inc(v_r_201_);
if (lean_obj_tag(v_r_201_) == 0)
{
lean_object* v_k_202_; lean_object* v_v_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_226_; 
v_k_202_ = lean_ctor_get(v_impl_97_, 1);
v_v_203_ = lean_ctor_get(v_impl_97_, 2);
v_isSharedCheck_226_ = !lean_is_exclusive(v_impl_97_);
if (v_isSharedCheck_226_ == 0)
{
lean_object* v_unused_227_; lean_object* v_unused_228_; lean_object* v_unused_229_; 
v_unused_227_ = lean_ctor_get(v_impl_97_, 4);
lean_dec(v_unused_227_);
v_unused_228_ = lean_ctor_get(v_impl_97_, 3);
lean_dec(v_unused_228_);
v_unused_229_ = lean_ctor_get(v_impl_97_, 0);
lean_dec(v_unused_229_);
v___x_205_ = v_impl_97_;
v_isShared_206_ = v_isSharedCheck_226_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_v_203_);
lean_inc(v_k_202_);
lean_dec(v_impl_97_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_226_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v_k_207_; lean_object* v_v_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_222_; 
v_k_207_ = lean_ctor_get(v_r_201_, 1);
v_v_208_ = lean_ctor_get(v_r_201_, 2);
v_isSharedCheck_222_ = !lean_is_exclusive(v_r_201_);
if (v_isSharedCheck_222_ == 0)
{
lean_object* v_unused_223_; lean_object* v_unused_224_; lean_object* v_unused_225_; 
v_unused_223_ = lean_ctor_get(v_r_201_, 4);
lean_dec(v_unused_223_);
v_unused_224_ = lean_ctor_get(v_r_201_, 3);
lean_dec(v_unused_224_);
v_unused_225_ = lean_ctor_get(v_r_201_, 0);
lean_dec(v_unused_225_);
v___x_210_ = v_r_201_;
v_isShared_211_ = v_isSharedCheck_222_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_v_208_);
lean_inc(v_k_207_);
lean_dec(v_r_201_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_222_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_212_ = lean_unsigned_to_nat(3u);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 4, v_l_184_);
lean_ctor_set(v___x_210_, 3, v_l_184_);
lean_ctor_set(v___x_210_, 2, v_v_203_);
lean_ctor_set(v___x_210_, 1, v_k_202_);
lean_ctor_set(v___x_210_, 0, v___x_98_);
v___x_214_ = v___x_210_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_k_202_);
lean_ctor_set(v_reuseFailAlloc_221_, 2, v_v_203_);
lean_ctor_set(v_reuseFailAlloc_221_, 3, v_l_184_);
lean_ctor_set(v_reuseFailAlloc_221_, 4, v_l_184_);
v___x_214_ = v_reuseFailAlloc_221_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_216_; 
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 4, v_l_184_);
lean_ctor_set(v___x_205_, 2, v_v_89_);
lean_ctor_set(v___x_205_, 1, v_k_88_);
lean_ctor_set(v___x_205_, 0, v___x_98_);
v___x_216_ = v___x_205_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_k_88_);
lean_ctor_set(v_reuseFailAlloc_220_, 2, v_v_89_);
lean_ctor_set(v_reuseFailAlloc_220_, 3, v_l_184_);
lean_ctor_set(v_reuseFailAlloc_220_, 4, v_l_184_);
v___x_216_ = v_reuseFailAlloc_220_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_218_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 4, v___x_216_);
lean_ctor_set(v___x_93_, 3, v___x_214_);
lean_ctor_set(v___x_93_, 2, v_v_208_);
lean_ctor_set(v___x_93_, 1, v_k_207_);
lean_ctor_set(v___x_93_, 0, v___x_212_);
v___x_218_ = v___x_93_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_k_207_);
lean_ctor_set(v_reuseFailAlloc_219_, 2, v_v_208_);
lean_ctor_set(v_reuseFailAlloc_219_, 3, v___x_214_);
lean_ctor_set(v_reuseFailAlloc_219_, 4, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
}
}
else
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = lean_unsigned_to_nat(2u);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 4, v_r_201_);
lean_ctor_set(v___x_93_, 3, v_impl_97_);
lean_ctor_set(v___x_93_, 0, v___x_230_);
v___x_232_ = v___x_93_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_k_88_);
lean_ctor_set(v_reuseFailAlloc_233_, 2, v_v_89_);
lean_ctor_set(v_reuseFailAlloc_233_, 3, v_impl_97_);
lean_ctor_set(v_reuseFailAlloc_233_, 4, v_r_201_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
case 1:
{
lean_object* v___x_235_; 
lean_dec(v_v_89_);
lean_dec(v_k_88_);
lean_dec_ref(v_cmp_83_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 2, v_v_85_);
lean_ctor_set(v___x_93_, 1, v_k_84_);
v___x_235_ = v___x_93_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_size_87_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_k_84_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_v_85_);
lean_ctor_set(v_reuseFailAlloc_236_, 3, v_l_90_);
lean_ctor_set(v_reuseFailAlloc_236_, 4, v_r_91_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
default: 
{
lean_object* v_impl_237_; lean_object* v___x_238_; 
lean_dec(v_size_87_);
v_impl_237_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_83_, v_k_84_, v_v_85_, v_r_91_);
v___x_238_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_90_) == 0)
{
lean_object* v_size_239_; lean_object* v_size_240_; lean_object* v_k_241_; lean_object* v_v_242_; lean_object* v_l_243_; lean_object* v_r_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v_size_239_ = lean_ctor_get(v_l_90_, 0);
v_size_240_ = lean_ctor_get(v_impl_237_, 0);
lean_inc(v_size_240_);
v_k_241_ = lean_ctor_get(v_impl_237_, 1);
lean_inc(v_k_241_);
v_v_242_ = lean_ctor_get(v_impl_237_, 2);
lean_inc(v_v_242_);
v_l_243_ = lean_ctor_get(v_impl_237_, 3);
lean_inc(v_l_243_);
v_r_244_ = lean_ctor_get(v_impl_237_, 4);
lean_inc(v_r_244_);
v___x_245_ = lean_unsigned_to_nat(3u);
v___x_246_ = lean_nat_mul(v___x_245_, v_size_239_);
v___x_247_ = lean_nat_dec_lt(v___x_246_, v_size_240_);
lean_dec(v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
lean_dec(v_r_244_);
lean_dec(v_l_243_);
lean_dec(v_v_242_);
lean_dec(v_k_241_);
v___x_248_ = lean_nat_add(v___x_238_, v_size_239_);
v___x_249_ = lean_nat_add(v___x_248_, v_size_240_);
lean_dec(v_size_240_);
lean_dec(v___x_248_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 4, v_impl_237_);
lean_ctor_set(v___x_93_, 0, v___x_249_);
v___x_251_ = v___x_93_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_k_88_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_v_89_);
lean_ctor_set(v_reuseFailAlloc_252_, 3, v_l_90_);
lean_ctor_set(v_reuseFailAlloc_252_, 4, v_impl_237_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
else
{
lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_316_; 
v_isSharedCheck_316_ = !lean_is_exclusive(v_impl_237_);
if (v_isSharedCheck_316_ == 0)
{
lean_object* v_unused_317_; lean_object* v_unused_318_; lean_object* v_unused_319_; lean_object* v_unused_320_; lean_object* v_unused_321_; 
v_unused_317_ = lean_ctor_get(v_impl_237_, 4);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_impl_237_, 3);
lean_dec(v_unused_318_);
v_unused_319_ = lean_ctor_get(v_impl_237_, 2);
lean_dec(v_unused_319_);
v_unused_320_ = lean_ctor_get(v_impl_237_, 1);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_impl_237_, 0);
lean_dec(v_unused_321_);
v___x_254_ = v_impl_237_;
v_isShared_255_ = v_isSharedCheck_316_;
goto v_resetjp_253_;
}
else
{
lean_dec(v_impl_237_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_316_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v_size_256_; lean_object* v_k_257_; lean_object* v_v_258_; lean_object* v_l_259_; lean_object* v_r_260_; lean_object* v_size_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_size_256_ = lean_ctor_get(v_l_243_, 0);
v_k_257_ = lean_ctor_get(v_l_243_, 1);
v_v_258_ = lean_ctor_get(v_l_243_, 2);
v_l_259_ = lean_ctor_get(v_l_243_, 3);
v_r_260_ = lean_ctor_get(v_l_243_, 4);
v_size_261_ = lean_ctor_get(v_r_244_, 0);
v___x_262_ = lean_unsigned_to_nat(2u);
v___x_263_ = lean_nat_mul(v___x_262_, v_size_261_);
v___x_264_ = lean_nat_dec_lt(v_size_256_, v___x_263_);
lean_dec(v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_292_; 
lean_inc(v_r_260_);
lean_inc(v_l_259_);
lean_inc(v_v_258_);
lean_inc(v_k_257_);
v_isSharedCheck_292_ = !lean_is_exclusive(v_l_243_);
if (v_isSharedCheck_292_ == 0)
{
lean_object* v_unused_293_; lean_object* v_unused_294_; lean_object* v_unused_295_; lean_object* v_unused_296_; lean_object* v_unused_297_; 
v_unused_293_ = lean_ctor_get(v_l_243_, 4);
lean_dec(v_unused_293_);
v_unused_294_ = lean_ctor_get(v_l_243_, 3);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v_l_243_, 2);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v_l_243_, 1);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_l_243_, 0);
lean_dec(v_unused_297_);
v___x_266_ = v_l_243_;
v_isShared_267_ = v_isSharedCheck_292_;
goto v_resetjp_265_;
}
else
{
lean_dec(v_l_243_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_292_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_282_; 
v___x_268_ = lean_nat_add(v___x_238_, v_size_239_);
v___x_269_ = lean_nat_add(v___x_268_, v_size_240_);
lean_dec(v_size_240_);
if (lean_obj_tag(v_l_259_) == 0)
{
lean_object* v_size_290_; 
v_size_290_ = lean_ctor_get(v_l_259_, 0);
lean_inc(v_size_290_);
v___y_282_ = v_size_290_;
goto v___jp_281_;
}
else
{
lean_object* v___x_291_; 
v___x_291_ = lean_unsigned_to_nat(0u);
v___y_282_ = v___x_291_;
goto v___jp_281_;
}
v___jp_270_:
{
lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_274_ = lean_nat_add(v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec(v___y_272_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 4, v_r_244_);
lean_ctor_set(v___x_266_, 3, v_r_260_);
lean_ctor_set(v___x_266_, 2, v_v_242_);
lean_ctor_set(v___x_266_, 1, v_k_241_);
lean_ctor_set(v___x_266_, 0, v___x_274_);
v___x_276_ = v___x_266_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_k_241_);
lean_ctor_set(v_reuseFailAlloc_280_, 2, v_v_242_);
lean_ctor_set(v_reuseFailAlloc_280_, 3, v_r_260_);
lean_ctor_set(v_reuseFailAlloc_280_, 4, v_r_244_);
v___x_276_ = v_reuseFailAlloc_280_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_278_; 
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 4, v___x_276_);
lean_ctor_set(v___x_254_, 3, v___y_271_);
lean_ctor_set(v___x_254_, 2, v_v_258_);
lean_ctor_set(v___x_254_, 1, v_k_257_);
lean_ctor_set(v___x_254_, 0, v___x_269_);
v___x_278_ = v___x_254_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_k_257_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_v_258_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v___y_271_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
v___jp_281_:
{
lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_283_ = lean_nat_add(v___x_268_, v___y_282_);
lean_dec(v___y_282_);
lean_dec(v___x_268_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 4, v_l_259_);
lean_ctor_set(v___x_93_, 0, v___x_283_);
v___x_285_ = v___x_93_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_k_88_);
lean_ctor_set(v_reuseFailAlloc_289_, 2, v_v_89_);
lean_ctor_set(v_reuseFailAlloc_289_, 3, v_l_90_);
lean_ctor_set(v_reuseFailAlloc_289_, 4, v_l_259_);
v___x_285_ = v_reuseFailAlloc_289_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_286_; 
v___x_286_ = lean_nat_add(v___x_238_, v_size_261_);
if (lean_obj_tag(v_r_260_) == 0)
{
lean_object* v_size_287_; 
v_size_287_ = lean_ctor_get(v_r_260_, 0);
lean_inc(v_size_287_);
v___y_271_ = v___x_285_;
v___y_272_ = v___x_286_;
v___y_273_ = v_size_287_;
goto v___jp_270_;
}
else
{
lean_object* v___x_288_; 
v___x_288_ = lean_unsigned_to_nat(0u);
v___y_271_ = v___x_285_;
v___y_272_ = v___x_286_;
v___y_273_ = v___x_288_;
goto v___jp_270_;
}
}
}
}
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
lean_del_object(v___x_93_);
v___x_298_ = lean_nat_add(v___x_238_, v_size_239_);
v___x_299_ = lean_nat_add(v___x_298_, v_size_240_);
lean_dec(v_size_240_);
v___x_300_ = lean_nat_add(v___x_298_, v_size_256_);
lean_dec(v___x_298_);
lean_inc_ref(v_l_90_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 4, v_l_243_);
lean_ctor_set(v___x_254_, 3, v_l_90_);
lean_ctor_set(v___x_254_, 2, v_v_89_);
lean_ctor_set(v___x_254_, 1, v_k_88_);
lean_ctor_set(v___x_254_, 0, v___x_300_);
v___x_302_ = v___x_254_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_k_88_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_v_89_);
lean_ctor_set(v_reuseFailAlloc_315_, 3, v_l_90_);
lean_ctor_set(v_reuseFailAlloc_315_, 4, v_l_243_);
v___x_302_ = v_reuseFailAlloc_315_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
v_isSharedCheck_309_ = !lean_is_exclusive(v_l_90_);
if (v_isSharedCheck_309_ == 0)
{
lean_object* v_unused_310_; lean_object* v_unused_311_; lean_object* v_unused_312_; lean_object* v_unused_313_; lean_object* v_unused_314_; 
v_unused_310_ = lean_ctor_get(v_l_90_, 4);
lean_dec(v_unused_310_);
v_unused_311_ = lean_ctor_get(v_l_90_, 3);
lean_dec(v_unused_311_);
v_unused_312_ = lean_ctor_get(v_l_90_, 2);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_l_90_, 1);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_l_90_, 0);
lean_dec(v_unused_314_);
v___x_304_ = v_l_90_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_dec(v_l_90_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 4, v_r_244_);
lean_ctor_set(v___x_304_, 3, v___x_302_);
lean_ctor_set(v___x_304_, 2, v_v_242_);
lean_ctor_set(v___x_304_, 1, v_k_241_);
lean_ctor_set(v___x_304_, 0, v___x_299_);
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_k_241_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v_v_242_);
lean_ctor_set(v_reuseFailAlloc_308_, 3, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_308_, 4, v_r_244_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_322_; 
v_l_322_ = lean_ctor_get(v_impl_237_, 3);
lean_inc(v_l_322_);
if (lean_obj_tag(v_l_322_) == 0)
{
lean_object* v_r_323_; lean_object* v_k_324_; lean_object* v_v_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_348_; 
v_r_323_ = lean_ctor_get(v_impl_237_, 4);
v_k_324_ = lean_ctor_get(v_impl_237_, 1);
v_v_325_ = lean_ctor_get(v_impl_237_, 2);
v_isSharedCheck_348_ = !lean_is_exclusive(v_impl_237_);
if (v_isSharedCheck_348_ == 0)
{
lean_object* v_unused_349_; lean_object* v_unused_350_; 
v_unused_349_ = lean_ctor_get(v_impl_237_, 3);
lean_dec(v_unused_349_);
v_unused_350_ = lean_ctor_get(v_impl_237_, 0);
lean_dec(v_unused_350_);
v___x_327_ = v_impl_237_;
v_isShared_328_ = v_isSharedCheck_348_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_r_323_);
lean_inc(v_v_325_);
lean_inc(v_k_324_);
lean_dec(v_impl_237_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_348_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v_k_329_; lean_object* v_v_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_344_; 
v_k_329_ = lean_ctor_get(v_l_322_, 1);
v_v_330_ = lean_ctor_get(v_l_322_, 2);
v_isSharedCheck_344_ = !lean_is_exclusive(v_l_322_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; lean_object* v_unused_346_; lean_object* v_unused_347_; 
v_unused_345_ = lean_ctor_get(v_l_322_, 4);
lean_dec(v_unused_345_);
v_unused_346_ = lean_ctor_get(v_l_322_, 3);
lean_dec(v_unused_346_);
v_unused_347_ = lean_ctor_get(v_l_322_, 0);
lean_dec(v_unused_347_);
v___x_332_ = v_l_322_;
v_isShared_333_ = v_isSharedCheck_344_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_v_330_);
lean_inc(v_k_329_);
lean_dec(v_l_322_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_344_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_334_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_323_, 2);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 4, v_r_323_);
lean_ctor_set(v___x_332_, 3, v_r_323_);
lean_ctor_set(v___x_332_, 2, v_v_89_);
lean_ctor_set(v___x_332_, 1, v_k_88_);
lean_ctor_set(v___x_332_, 0, v___x_238_);
v___x_336_ = v___x_332_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_k_88_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_v_89_);
lean_ctor_set(v_reuseFailAlloc_343_, 3, v_r_323_);
lean_ctor_set(v_reuseFailAlloc_343_, 4, v_r_323_);
v___x_336_ = v_reuseFailAlloc_343_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_338_; 
lean_inc(v_r_323_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 3, v_r_323_);
lean_ctor_set(v___x_327_, 0, v___x_238_);
v___x_338_ = v___x_327_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_k_324_);
lean_ctor_set(v_reuseFailAlloc_342_, 2, v_v_325_);
lean_ctor_set(v_reuseFailAlloc_342_, 3, v_r_323_);
lean_ctor_set(v_reuseFailAlloc_342_, 4, v_r_323_);
v___x_338_ = v_reuseFailAlloc_342_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_340_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 4, v___x_338_);
lean_ctor_set(v___x_93_, 3, v___x_336_);
lean_ctor_set(v___x_93_, 2, v_v_330_);
lean_ctor_set(v___x_93_, 1, v_k_329_);
lean_ctor_set(v___x_93_, 0, v___x_334_);
v___x_340_ = v___x_93_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_k_329_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_v_330_);
lean_ctor_set(v_reuseFailAlloc_341_, 3, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_341_, 4, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
}
else
{
lean_object* v_r_351_; 
v_r_351_ = lean_ctor_get(v_impl_237_, 4);
lean_inc(v_r_351_);
if (lean_obj_tag(v_r_351_) == 0)
{
lean_object* v_k_352_; lean_object* v_v_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_364_; 
v_k_352_ = lean_ctor_get(v_impl_237_, 1);
v_v_353_ = lean_ctor_get(v_impl_237_, 2);
v_isSharedCheck_364_ = !lean_is_exclusive(v_impl_237_);
if (v_isSharedCheck_364_ == 0)
{
lean_object* v_unused_365_; lean_object* v_unused_366_; lean_object* v_unused_367_; 
v_unused_365_ = lean_ctor_get(v_impl_237_, 4);
lean_dec(v_unused_365_);
v_unused_366_ = lean_ctor_get(v_impl_237_, 3);
lean_dec(v_unused_366_);
v_unused_367_ = lean_ctor_get(v_impl_237_, 0);
lean_dec(v_unused_367_);
v___x_355_ = v_impl_237_;
v_isShared_356_ = v_isSharedCheck_364_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_v_353_);
lean_inc(v_k_352_);
lean_dec(v_impl_237_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_364_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_357_ = lean_unsigned_to_nat(3u);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 4, v_l_322_);
lean_ctor_set(v___x_355_, 2, v_v_89_);
lean_ctor_set(v___x_355_, 1, v_k_88_);
lean_ctor_set(v___x_355_, 0, v___x_238_);
v___x_359_ = v___x_355_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_k_88_);
lean_ctor_set(v_reuseFailAlloc_363_, 2, v_v_89_);
lean_ctor_set(v_reuseFailAlloc_363_, 3, v_l_322_);
lean_ctor_set(v_reuseFailAlloc_363_, 4, v_l_322_);
v___x_359_ = v_reuseFailAlloc_363_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_361_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 4, v_r_351_);
lean_ctor_set(v___x_93_, 3, v___x_359_);
lean_ctor_set(v___x_93_, 2, v_v_353_);
lean_ctor_set(v___x_93_, 1, v_k_352_);
lean_ctor_set(v___x_93_, 0, v___x_357_);
v___x_361_ = v___x_93_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_357_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_k_352_);
lean_ctor_set(v_reuseFailAlloc_362_, 2, v_v_353_);
lean_ctor_set(v_reuseFailAlloc_362_, 3, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_362_, 4, v_r_351_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_368_ = lean_unsigned_to_nat(2u);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 4, v_impl_237_);
lean_ctor_set(v___x_93_, 3, v_r_351_);
lean_ctor_set(v___x_93_, 0, v___x_368_);
v___x_370_ = v___x_93_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_k_88_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_v_89_);
lean_ctor_set(v_reuseFailAlloc_371_, 3, v_r_351_);
lean_ctor_set(v_reuseFailAlloc_371_, 4, v_impl_237_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
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
lean_object* v___x_373_; lean_object* v___x_374_; 
lean_dec_ref(v_cmp_83_);
v___x_373_ = lean_unsigned_to_nat(1u);
v___x_374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v_k_84_);
lean_ctor_set(v___x_374_, 2, v_v_85_);
lean_ctor_set(v___x_374_, 3, v_t_86_);
lean_ctor_set(v___x_374_, 4, v_t_86_);
return v___x_374_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(lean_object* v_cmp_375_, lean_object* v_k_376_, lean_object* v_t_377_){
_start:
{
if (lean_obj_tag(v_t_377_) == 0)
{
lean_object* v_k_378_; lean_object* v_l_379_; lean_object* v_r_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_k_378_ = lean_ctor_get(v_t_377_, 1);
lean_inc(v_k_378_);
v_l_379_ = lean_ctor_get(v_t_377_, 3);
lean_inc(v_l_379_);
v_r_380_ = lean_ctor_get(v_t_377_, 4);
lean_inc(v_r_380_);
lean_dec_ref_known(v_t_377_, 5);
lean_inc_ref(v_cmp_375_);
lean_inc(v_k_376_);
v___x_381_ = lean_apply_2(v_cmp_375_, v_k_376_, v_k_378_);
v___x_382_ = lean_unbox(v___x_381_);
switch(v___x_382_)
{
case 0:
{
lean_dec(v_r_380_);
v_t_377_ = v_l_379_;
goto _start;
}
case 1:
{
uint8_t v___x_384_; 
lean_dec(v_r_380_);
lean_dec(v_l_379_);
lean_dec(v_k_376_);
lean_dec_ref(v_cmp_375_);
v___x_384_ = 1;
return v___x_384_;
}
default: 
{
lean_dec(v_l_379_);
v_t_377_ = v_r_380_;
goto _start;
}
}
}
else
{
uint8_t v___x_386_; 
lean_dec(v_k_376_);
lean_dec_ref(v_cmp_375_);
v___x_386_ = 0;
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg___boxed(lean_object* v_cmp_387_, lean_object* v_k_388_, lean_object* v_t_389_){
_start:
{
uint8_t v_res_390_; lean_object* v_r_391_; 
v_res_390_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(v_cmp_387_, v_k_388_, v_t_389_);
v_r_391_ = lean_box(v_res_390_);
return v_r_391_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_insert___redArg(lean_object* v_cmp_392_, lean_object* v_self_393_, lean_object* v_a_394_, lean_object* v_b_395_){
_start:
{
lean_object* v_toTreeMap_396_; lean_object* v_toArray_397_; uint8_t v___x_398_; 
v_toTreeMap_396_ = lean_ctor_get(v_self_393_, 0);
v_toArray_397_ = lean_ctor_get(v_self_393_, 1);
lean_inc(v_toTreeMap_396_);
lean_inc(v_a_394_);
lean_inc_ref(v_cmp_392_);
v___x_398_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(v_cmp_392_, v_a_394_, v_toTreeMap_396_);
if (v___x_398_ == 0)
{
lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_407_; 
lean_inc_ref(v_toArray_397_);
lean_inc(v_toTreeMap_396_);
v_isSharedCheck_407_ = !lean_is_exclusive(v_self_393_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; lean_object* v_unused_409_; 
v_unused_408_ = lean_ctor_get(v_self_393_, 1);
lean_dec(v_unused_408_);
v_unused_409_ = lean_ctor_get(v_self_393_, 0);
lean_dec(v_unused_409_);
v___x_400_ = v_self_393_;
v_isShared_401_ = v_isSharedCheck_407_;
goto v_resetjp_399_;
}
else
{
lean_dec(v_self_393_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_407_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
lean_inc(v_b_395_);
v___x_402_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_392_, v_a_394_, v_b_395_, v_toTreeMap_396_);
v___x_403_ = lean_array_push(v_toArray_397_, v_b_395_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 1, v___x_403_);
lean_ctor_set(v___x_400_, 0, v___x_402_);
v___x_405_ = v___x_400_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
else
{
lean_dec(v_b_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_cmp_392_);
return v_self_393_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_insert(lean_object* v_00_u03b1_410_, lean_object* v_00_u03b2_411_, lean_object* v_cmp_412_, lean_object* v_self_413_, lean_object* v_a_414_, lean_object* v_b_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lake_RBArray_insert___redArg(v_cmp_412_, v_self_413_, v_a_414_, v_b_415_);
return v___x_416_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0(lean_object* v_00_u03b1_417_, lean_object* v_cmp_418_, lean_object* v_00_u03b2_419_, lean_object* v_k_420_, lean_object* v_t_421_){
_start:
{
uint8_t v___x_422_; 
v___x_422_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(v_cmp_418_, v_k_420_, v_t_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___boxed(lean_object* v_00_u03b1_423_, lean_object* v_cmp_424_, lean_object* v_00_u03b2_425_, lean_object* v_k_426_, lean_object* v_t_427_){
_start:
{
uint8_t v_res_428_; lean_object* v_r_429_; 
v_res_428_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0(v_00_u03b1_423_, v_cmp_424_, v_00_u03b2_425_, v_k_426_, v_t_427_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1(lean_object* v_00_u03b1_430_, lean_object* v_cmp_431_, lean_object* v_00_u03b2_432_, lean_object* v_k_433_, lean_object* v_v_434_, lean_object* v_t_435_, lean_object* v_hl_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_431_, v_k_433_, v_v_434_, v_t_435_);
return v___x_437_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_all___redArg___lam__0(lean_object* v_f_438_, uint8_t v___x_439_, lean_object* v_v_440_){
_start:
{
lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_441_ = lean_apply_1(v_f_438_, v_v_440_);
v___x_442_ = lean_unbox(v___x_441_);
if (v___x_442_ == 0)
{
return v___x_439_;
}
else
{
uint8_t v___x_443_; 
v___x_443_ = 0;
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_all___redArg___lam__0___boxed(lean_object* v_f_444_, lean_object* v___x_445_, lean_object* v_v_446_){
_start:
{
uint8_t v___x_75__boxed_447_; uint8_t v_res_448_; lean_object* v_r_449_; 
v___x_75__boxed_447_ = lean_unbox(v___x_445_);
v_res_448_ = l_Lake_RBArray_all___redArg___lam__0(v_f_444_, v___x_75__boxed_447_, v_v_446_);
v_r_449_ = lean_box(v_res_448_);
return v_r_449_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_all___redArg(lean_object* v_f_469_, lean_object* v_self_470_){
_start:
{
lean_object* v_toArray_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v_toArray_471_ = lean_ctor_get(v_self_470_, 1);
lean_inc_ref(v_toArray_471_);
lean_dec_ref(v_self_470_);
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = lean_array_get_size(v_toArray_471_);
v___x_474_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_475_ = lean_nat_dec_lt(v___x_472_, v___x_473_);
if (v___x_475_ == 0)
{
uint8_t v___x_476_; 
lean_dec_ref(v_toArray_471_);
lean_dec_ref(v_f_469_);
v___x_476_ = 1;
return v___x_476_;
}
else
{
if (v___x_475_ == 0)
{
lean_dec_ref(v_toArray_471_);
lean_dec_ref(v_f_469_);
return v___x_475_;
}
else
{
lean_object* v___x_477_; lean_object* v___f_478_; size_t v___x_479_; size_t v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_477_ = lean_box(v___x_475_);
v___f_478_ = lean_alloc_closure((void*)(l_Lake_RBArray_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_478_, 0, v_f_469_);
lean_closure_set(v___f_478_, 1, v___x_477_);
v___x_479_ = ((size_t)0ULL);
v___x_480_ = lean_usize_of_nat(v___x_473_);
v___x_481_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_474_, v___f_478_, v_toArray_471_, v___x_479_, v___x_480_);
v___x_482_ = lean_unbox(v___x_481_);
lean_dec(v___x_481_);
if (v___x_482_ == 0)
{
return v___x_475_;
}
else
{
uint8_t v___x_483_; 
v___x_483_ = 0;
return v___x_483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_all___redArg___boxed(lean_object* v_f_484_, lean_object* v_self_485_){
_start:
{
uint8_t v_res_486_; lean_object* v_r_487_; 
v_res_486_ = l_Lake_RBArray_all___redArg(v_f_484_, v_self_485_);
v_r_487_ = lean_box(v_res_486_);
return v_r_487_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_all(lean_object* v_00_u03b2_488_, lean_object* v_00_u03b1_489_, lean_object* v_cmp_490_, lean_object* v_f_491_, lean_object* v_self_492_){
_start:
{
lean_object* v_toArray_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v_toArray_493_ = lean_ctor_get(v_self_492_, 1);
lean_inc_ref(v_toArray_493_);
lean_dec_ref(v_self_492_);
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = lean_array_get_size(v_toArray_493_);
v___x_496_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_497_ = lean_nat_dec_lt(v___x_494_, v___x_495_);
if (v___x_497_ == 0)
{
uint8_t v___x_498_; 
lean_dec_ref(v_toArray_493_);
lean_dec_ref(v_f_491_);
v___x_498_ = 1;
return v___x_498_;
}
else
{
if (v___x_497_ == 0)
{
lean_dec_ref(v_toArray_493_);
lean_dec_ref(v_f_491_);
return v___x_497_;
}
else
{
lean_object* v___x_499_; lean_object* v___f_500_; size_t v___x_501_; size_t v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_499_ = lean_box(v___x_497_);
v___f_500_ = lean_alloc_closure((void*)(l_Lake_RBArray_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_500_, 0, v_f_491_);
lean_closure_set(v___f_500_, 1, v___x_499_);
v___x_501_ = ((size_t)0ULL);
v___x_502_ = lean_usize_of_nat(v___x_495_);
v___x_503_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_496_, v___f_500_, v_toArray_493_, v___x_501_, v___x_502_);
v___x_504_ = lean_unbox(v___x_503_);
lean_dec(v___x_503_);
if (v___x_504_ == 0)
{
return v___x_497_;
}
else
{
uint8_t v___x_505_; 
v___x_505_ = 0;
return v___x_505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_all___boxed(lean_object* v_00_u03b2_506_, lean_object* v_00_u03b1_507_, lean_object* v_cmp_508_, lean_object* v_f_509_, lean_object* v_self_510_){
_start:
{
uint8_t v_res_511_; lean_object* v_r_512_; 
v_res_511_ = l_Lake_RBArray_all(v_00_u03b2_506_, v_00_u03b1_507_, v_cmp_508_, v_f_509_, v_self_510_);
lean_dec_ref(v_cmp_508_);
v_r_512_ = lean_box(v_res_511_);
return v_r_512_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_any___redArg___lam__0(lean_object* v_f_513_, lean_object* v_x_514_){
_start:
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_apply_1(v_f_513_, v_x_514_);
v___x_516_ = lean_unbox(v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_any___redArg___lam__0___boxed(lean_object* v_f_517_, lean_object* v_x_518_){
_start:
{
uint8_t v_res_519_; lean_object* v_r_520_; 
v_res_519_ = l_Lake_RBArray_any___redArg___lam__0(v_f_517_, v_x_518_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_any___redArg(lean_object* v_f_521_, lean_object* v_self_522_){
_start:
{
lean_object* v_toArray_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v_toArray_523_ = lean_ctor_get(v_self_522_, 1);
lean_inc_ref(v_toArray_523_);
lean_dec_ref(v_self_522_);
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = lean_array_get_size(v_toArray_523_);
v___x_526_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_527_ = lean_nat_dec_lt(v___x_524_, v___x_525_);
if (v___x_527_ == 0)
{
lean_dec_ref(v_toArray_523_);
lean_dec_ref(v_f_521_);
return v___x_527_;
}
else
{
if (v___x_527_ == 0)
{
lean_dec_ref(v_toArray_523_);
lean_dec_ref(v_f_521_);
return v___x_527_;
}
else
{
lean_object* v___f_528_; size_t v___x_529_; size_t v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___f_528_ = lean_alloc_closure((void*)(l_Lake_RBArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_528_, 0, v_f_521_);
v___x_529_ = ((size_t)0ULL);
v___x_530_ = lean_usize_of_nat(v___x_525_);
v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_526_, v___f_528_, v_toArray_523_, v___x_529_, v___x_530_);
v___x_532_ = lean_unbox(v___x_531_);
lean_dec(v___x_531_);
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_any___redArg___boxed(lean_object* v_f_533_, lean_object* v_self_534_){
_start:
{
uint8_t v_res_535_; lean_object* v_r_536_; 
v_res_535_ = l_Lake_RBArray_any___redArg(v_f_533_, v_self_534_);
v_r_536_ = lean_box(v_res_535_);
return v_r_536_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_any(lean_object* v_00_u03b2_537_, lean_object* v_00_u03b1_538_, lean_object* v_cmp_539_, lean_object* v_f_540_, lean_object* v_self_541_){
_start:
{
lean_object* v_toArray_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v_toArray_542_ = lean_ctor_get(v_self_541_, 1);
lean_inc_ref(v_toArray_542_);
lean_dec_ref(v_self_541_);
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = lean_array_get_size(v_toArray_542_);
v___x_545_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_546_ = lean_nat_dec_lt(v___x_543_, v___x_544_);
if (v___x_546_ == 0)
{
lean_dec_ref(v_toArray_542_);
lean_dec_ref(v_f_540_);
return v___x_546_;
}
else
{
if (v___x_546_ == 0)
{
lean_dec_ref(v_toArray_542_);
lean_dec_ref(v_f_540_);
return v___x_546_;
}
else
{
lean_object* v___f_547_; size_t v___x_548_; size_t v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___f_547_ = lean_alloc_closure((void*)(l_Lake_RBArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_547_, 0, v_f_540_);
v___x_548_ = ((size_t)0ULL);
v___x_549_ = lean_usize_of_nat(v___x_544_);
v___x_550_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_545_, v___f_547_, v_toArray_542_, v___x_548_, v___x_549_);
v___x_551_ = lean_unbox(v___x_550_);
lean_dec(v___x_550_);
return v___x_551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_any___boxed(lean_object* v_00_u03b2_552_, lean_object* v_00_u03b1_553_, lean_object* v_cmp_554_, lean_object* v_f_555_, lean_object* v_self_556_){
_start:
{
uint8_t v_res_557_; lean_object* v_r_558_; 
v_res_557_ = l_Lake_RBArray_any(v_00_u03b2_552_, v_00_u03b1_553_, v_cmp_554_, v_f_555_, v_self_556_);
lean_dec_ref(v_cmp_554_);
v_r_558_ = lean_box(v_res_557_);
return v_r_558_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl___redArg___lam__0(lean_object* v_f_559_, lean_object* v_x1_560_, lean_object* v_x2_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = lean_apply_2(v_f_559_, v_x1_560_, v_x2_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl___redArg(lean_object* v_f_563_, lean_object* v_init_564_, lean_object* v_self_565_){
_start:
{
lean_object* v_toArray_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_toArray_566_ = lean_ctor_get(v_self_565_, 1);
lean_inc_ref(v_toArray_566_);
lean_dec_ref(v_self_565_);
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_array_get_size(v_toArray_566_);
v___x_569_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_570_ = lean_nat_dec_lt(v___x_567_, v___x_568_);
if (v___x_570_ == 0)
{
lean_dec_ref(v_toArray_566_);
lean_dec(v_f_563_);
return v_init_564_;
}
else
{
lean_object* v___f_571_; uint8_t v___x_572_; 
v___f_571_ = lean_alloc_closure((void*)(l_Lake_RBArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_571_, 0, v_f_563_);
v___x_572_ = lean_nat_dec_le(v___x_568_, v___x_568_);
if (v___x_572_ == 0)
{
if (v___x_570_ == 0)
{
lean_dec_ref(v___f_571_);
lean_dec_ref(v_toArray_566_);
return v_init_564_;
}
else
{
size_t v___x_573_; size_t v___x_574_; lean_object* v___x_575_; 
v___x_573_ = ((size_t)0ULL);
v___x_574_ = lean_usize_of_nat(v___x_568_);
v___x_575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_569_, v___f_571_, v_toArray_566_, v___x_573_, v___x_574_, v_init_564_);
return v___x_575_;
}
}
else
{
size_t v___x_576_; size_t v___x_577_; lean_object* v___x_578_; 
v___x_576_ = ((size_t)0ULL);
v___x_577_ = lean_usize_of_nat(v___x_568_);
v___x_578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_569_, v___f_571_, v_toArray_566_, v___x_576_, v___x_577_, v_init_564_);
return v___x_578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl(lean_object* v_00_u03c3_579_, lean_object* v_00_u03b2_580_, lean_object* v_00_u03b1_581_, lean_object* v_cmp_582_, lean_object* v_f_583_, lean_object* v_init_584_, lean_object* v_self_585_){
_start:
{
lean_object* v_toArray_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v_toArray_586_ = lean_ctor_get(v_self_585_, 1);
lean_inc_ref(v_toArray_586_);
lean_dec_ref(v_self_585_);
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = lean_array_get_size(v_toArray_586_);
v___x_589_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_590_ = lean_nat_dec_lt(v___x_587_, v___x_588_);
if (v___x_590_ == 0)
{
lean_dec_ref(v_toArray_586_);
lean_dec(v_f_583_);
return v_init_584_;
}
else
{
lean_object* v___f_591_; uint8_t v___x_592_; 
v___f_591_ = lean_alloc_closure((void*)(l_Lake_RBArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_591_, 0, v_f_583_);
v___x_592_ = lean_nat_dec_le(v___x_588_, v___x_588_);
if (v___x_592_ == 0)
{
if (v___x_590_ == 0)
{
lean_dec_ref(v___f_591_);
lean_dec_ref(v_toArray_586_);
return v_init_584_;
}
else
{
size_t v___x_593_; size_t v___x_594_; lean_object* v___x_595_; 
v___x_593_ = ((size_t)0ULL);
v___x_594_ = lean_usize_of_nat(v___x_588_);
v___x_595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_589_, v___f_591_, v_toArray_586_, v___x_593_, v___x_594_, v_init_584_);
return v___x_595_;
}
}
else
{
size_t v___x_596_; size_t v___x_597_; lean_object* v___x_598_; 
v___x_596_ = ((size_t)0ULL);
v___x_597_ = lean_usize_of_nat(v___x_588_);
v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_589_, v___f_591_, v_toArray_586_, v___x_596_, v___x_597_, v_init_584_);
return v___x_598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl___boxed(lean_object* v_00_u03c3_599_, lean_object* v_00_u03b2_600_, lean_object* v_00_u03b1_601_, lean_object* v_cmp_602_, lean_object* v_f_603_, lean_object* v_init_604_, lean_object* v_self_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lake_RBArray_foldl(v_00_u03c3_599_, v_00_u03b2_600_, v_00_u03b1_601_, v_cmp_602_, v_f_603_, v_init_604_, v_self_605_);
lean_dec_ref(v_cmp_602_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldlM___redArg(lean_object* v_inst_607_, lean_object* v_f_608_, lean_object* v_init_609_, lean_object* v_self_610_){
_start:
{
lean_object* v_toApplicative_611_; lean_object* v_toArray_612_; lean_object* v_toPure_613_; lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_toApplicative_611_ = lean_ctor_get(v_inst_607_, 0);
v_toArray_612_ = lean_ctor_get(v_self_610_, 1);
lean_inc_ref(v_toArray_612_);
lean_dec_ref(v_self_610_);
v_toPure_613_ = lean_ctor_get(v_toApplicative_611_, 1);
v___x_614_ = lean_unsigned_to_nat(0u);
v___x_615_ = lean_array_get_size(v_toArray_612_);
v___x_616_ = lean_nat_dec_lt(v___x_614_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
lean_inc(v_toPure_613_);
lean_dec_ref(v_toArray_612_);
lean_dec(v_f_608_);
lean_dec_ref(v_inst_607_);
v___x_617_ = lean_apply_2(v_toPure_613_, lean_box(0), v_init_609_);
return v___x_617_;
}
else
{
uint8_t v___x_618_; 
v___x_618_ = lean_nat_dec_le(v___x_615_, v___x_615_);
if (v___x_618_ == 0)
{
if (v___x_616_ == 0)
{
lean_object* v___x_619_; 
lean_inc(v_toPure_613_);
lean_dec_ref(v_toArray_612_);
lean_dec(v_f_608_);
lean_dec_ref(v_inst_607_);
v___x_619_ = lean_apply_2(v_toPure_613_, lean_box(0), v_init_609_);
return v___x_619_;
}
else
{
size_t v___x_620_; size_t v___x_621_; lean_object* v___x_622_; 
v___x_620_ = ((size_t)0ULL);
v___x_621_ = lean_usize_of_nat(v___x_615_);
v___x_622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_607_, v_f_608_, v_toArray_612_, v___x_620_, v___x_621_, v_init_609_);
return v___x_622_;
}
}
else
{
size_t v___x_623_; size_t v___x_624_; lean_object* v___x_625_; 
v___x_623_ = ((size_t)0ULL);
v___x_624_ = lean_usize_of_nat(v___x_615_);
v___x_625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_607_, v_f_608_, v_toArray_612_, v___x_623_, v___x_624_, v_init_609_);
return v___x_625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldlM(lean_object* v_m_626_, lean_object* v_00_u03c3_627_, lean_object* v_00_u03b2_628_, lean_object* v_00_u03b1_629_, lean_object* v_cmp_630_, lean_object* v_inst_631_, lean_object* v_f_632_, lean_object* v_init_633_, lean_object* v_self_634_){
_start:
{
lean_object* v_toApplicative_635_; lean_object* v_toArray_636_; lean_object* v_toPure_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_toApplicative_635_ = lean_ctor_get(v_inst_631_, 0);
v_toArray_636_ = lean_ctor_get(v_self_634_, 1);
lean_inc_ref(v_toArray_636_);
lean_dec_ref(v_self_634_);
v_toPure_637_ = lean_ctor_get(v_toApplicative_635_, 1);
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = lean_array_get_size(v_toArray_636_);
v___x_640_ = lean_nat_dec_lt(v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
lean_inc(v_toPure_637_);
lean_dec_ref(v_toArray_636_);
lean_dec(v_f_632_);
lean_dec_ref(v_inst_631_);
v___x_641_ = lean_apply_2(v_toPure_637_, lean_box(0), v_init_633_);
return v___x_641_;
}
else
{
uint8_t v___x_642_; 
v___x_642_ = lean_nat_dec_le(v___x_639_, v___x_639_);
if (v___x_642_ == 0)
{
if (v___x_640_ == 0)
{
lean_object* v___x_643_; 
lean_inc(v_toPure_637_);
lean_dec_ref(v_toArray_636_);
lean_dec(v_f_632_);
lean_dec_ref(v_inst_631_);
v___x_643_ = lean_apply_2(v_toPure_637_, lean_box(0), v_init_633_);
return v___x_643_;
}
else
{
size_t v___x_644_; size_t v___x_645_; lean_object* v___x_646_; 
v___x_644_ = ((size_t)0ULL);
v___x_645_ = lean_usize_of_nat(v___x_639_);
v___x_646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_631_, v_f_632_, v_toArray_636_, v___x_644_, v___x_645_, v_init_633_);
return v___x_646_;
}
}
else
{
size_t v___x_647_; size_t v___x_648_; lean_object* v___x_649_; 
v___x_647_ = ((size_t)0ULL);
v___x_648_ = lean_usize_of_nat(v___x_639_);
v___x_649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_631_, v_f_632_, v_toArray_636_, v___x_647_, v___x_648_, v_init_633_);
return v___x_649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldlM___boxed(lean_object* v_m_650_, lean_object* v_00_u03c3_651_, lean_object* v_00_u03b2_652_, lean_object* v_00_u03b1_653_, lean_object* v_cmp_654_, lean_object* v_inst_655_, lean_object* v_f_656_, lean_object* v_init_657_, lean_object* v_self_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lake_RBArray_foldlM(v_m_650_, v_00_u03c3_651_, v_00_u03b2_652_, v_00_u03b1_653_, v_cmp_654_, v_inst_655_, v_f_656_, v_init_657_, v_self_658_);
lean_dec_ref(v_cmp_654_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldr___redArg(lean_object* v_f_660_, lean_object* v_init_661_, lean_object* v_self_662_){
_start:
{
lean_object* v_toArray_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v_toArray_663_ = lean_ctor_get(v_self_662_, 1);
lean_inc_ref(v_toArray_663_);
lean_dec_ref(v_self_662_);
v___x_664_ = lean_array_get_size(v_toArray_663_);
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_667_ = lean_nat_dec_lt(v___x_665_, v___x_664_);
if (v___x_667_ == 0)
{
lean_dec_ref(v_toArray_663_);
lean_dec(v_f_660_);
return v_init_661_;
}
else
{
lean_object* v___f_668_; size_t v___x_669_; size_t v___x_670_; lean_object* v___x_671_; 
v___f_668_ = lean_alloc_closure((void*)(l_Lake_RBArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_668_, 0, v_f_660_);
v___x_669_ = lean_usize_of_nat(v___x_664_);
v___x_670_ = ((size_t)0ULL);
v___x_671_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_666_, v___f_668_, v_toArray_663_, v___x_669_, v___x_670_, v_init_661_);
return v___x_671_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldr(lean_object* v_00_u03b2_672_, lean_object* v_00_u03c3_673_, lean_object* v_00_u03b1_674_, lean_object* v_cmp_675_, lean_object* v_f_676_, lean_object* v_init_677_, lean_object* v_self_678_){
_start:
{
lean_object* v_toArray_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v_toArray_679_ = lean_ctor_get(v_self_678_, 1);
lean_inc_ref(v_toArray_679_);
lean_dec_ref(v_self_678_);
v___x_680_ = lean_array_get_size(v_toArray_679_);
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_683_ = lean_nat_dec_lt(v___x_681_, v___x_680_);
if (v___x_683_ == 0)
{
lean_dec_ref(v_toArray_679_);
lean_dec(v_f_676_);
return v_init_677_;
}
else
{
lean_object* v___f_684_; size_t v___x_685_; size_t v___x_686_; lean_object* v___x_687_; 
v___f_684_ = lean_alloc_closure((void*)(l_Lake_RBArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_684_, 0, v_f_676_);
v___x_685_ = lean_usize_of_nat(v___x_680_);
v___x_686_ = ((size_t)0ULL);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_682_, v___f_684_, v_toArray_679_, v___x_685_, v___x_686_, v_init_677_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldr___boxed(lean_object* v_00_u03b2_688_, lean_object* v_00_u03c3_689_, lean_object* v_00_u03b1_690_, lean_object* v_cmp_691_, lean_object* v_f_692_, lean_object* v_init_693_, lean_object* v_self_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lake_RBArray_foldr(v_00_u03b2_688_, v_00_u03c3_689_, v_00_u03b1_690_, v_cmp_691_, v_f_692_, v_init_693_, v_self_694_);
lean_dec_ref(v_cmp_691_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldrM___redArg(lean_object* v_inst_696_, lean_object* v_f_697_, lean_object* v_init_698_, lean_object* v_self_699_){
_start:
{
lean_object* v_toApplicative_700_; lean_object* v_toArray_701_; lean_object* v_toPure_702_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v_toApplicative_700_ = lean_ctor_get(v_inst_696_, 0);
v_toArray_701_ = lean_ctor_get(v_self_699_, 1);
lean_inc_ref(v_toArray_701_);
lean_dec_ref(v_self_699_);
v_toPure_702_ = lean_ctor_get(v_toApplicative_700_, 1);
v___x_703_ = lean_array_get_size(v_toArray_701_);
v___x_704_ = lean_unsigned_to_nat(0u);
v___x_705_ = lean_nat_dec_lt(v___x_704_, v___x_703_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; 
lean_inc(v_toPure_702_);
lean_dec_ref(v_toArray_701_);
lean_dec(v_f_697_);
lean_dec_ref(v_inst_696_);
v___x_706_ = lean_apply_2(v_toPure_702_, lean_box(0), v_init_698_);
return v___x_706_;
}
else
{
size_t v___x_707_; size_t v___x_708_; lean_object* v___x_709_; 
v___x_707_ = lean_usize_of_nat(v___x_703_);
v___x_708_ = ((size_t)0ULL);
v___x_709_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_696_, v_f_697_, v_toArray_701_, v___x_707_, v___x_708_, v_init_698_);
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldrM(lean_object* v_m_710_, lean_object* v_00_u03b2_711_, lean_object* v_00_u03c3_712_, lean_object* v_00_u03b1_713_, lean_object* v_cmp_714_, lean_object* v_inst_715_, lean_object* v_f_716_, lean_object* v_init_717_, lean_object* v_self_718_){
_start:
{
lean_object* v_toApplicative_719_; lean_object* v_toArray_720_; lean_object* v_toPure_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_toApplicative_719_ = lean_ctor_get(v_inst_715_, 0);
v_toArray_720_ = lean_ctor_get(v_self_718_, 1);
lean_inc_ref(v_toArray_720_);
lean_dec_ref(v_self_718_);
v_toPure_721_ = lean_ctor_get(v_toApplicative_719_, 1);
v___x_722_ = lean_array_get_size(v_toArray_720_);
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_nat_dec_lt(v___x_723_, v___x_722_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
lean_inc(v_toPure_721_);
lean_dec_ref(v_toArray_720_);
lean_dec(v_f_716_);
lean_dec_ref(v_inst_715_);
v___x_725_ = lean_apply_2(v_toPure_721_, lean_box(0), v_init_717_);
return v___x_725_;
}
else
{
size_t v___x_726_; size_t v___x_727_; lean_object* v___x_728_; 
v___x_726_ = lean_usize_of_nat(v___x_722_);
v___x_727_ = ((size_t)0ULL);
v___x_728_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_715_, v_f_716_, v_toArray_720_, v___x_726_, v___x_727_, v_init_717_);
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldrM___boxed(lean_object* v_m_729_, lean_object* v_00_u03b2_730_, lean_object* v_00_u03c3_731_, lean_object* v_00_u03b1_732_, lean_object* v_cmp_733_, lean_object* v_inst_734_, lean_object* v_f_735_, lean_object* v_init_736_, lean_object* v_self_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lake_RBArray_foldrM(v_m_729_, v_00_u03b2_730_, v_00_u03c3_731_, v_00_u03b1_732_, v_cmp_733_, v_inst_734_, v_f_735_, v_init_736_, v_self_737_);
lean_dec_ref(v_cmp_733_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM___redArg___lam__0(lean_object* v_f_739_, lean_object* v_x_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = lean_apply_1(v_f_739_, v___y_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM___redArg(lean_object* v_inst_743_, lean_object* v_f_744_, lean_object* v_self_745_){
_start:
{
lean_object* v_toApplicative_746_; lean_object* v_toArray_747_; lean_object* v_toPure_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v_toApplicative_746_ = lean_ctor_get(v_inst_743_, 0);
v_toArray_747_ = lean_ctor_get(v_self_745_, 1);
lean_inc_ref(v_toArray_747_);
lean_dec_ref(v_self_745_);
v_toPure_748_ = lean_ctor_get(v_toApplicative_746_, 1);
v___x_749_ = lean_unsigned_to_nat(0u);
v___x_750_ = lean_array_get_size(v_toArray_747_);
v___x_751_ = lean_box(0);
v___x_752_ = lean_nat_dec_lt(v___x_749_, v___x_750_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; 
lean_inc(v_toPure_748_);
lean_dec_ref(v_toArray_747_);
lean_dec(v_f_744_);
lean_dec_ref(v_inst_743_);
v___x_753_ = lean_apply_2(v_toPure_748_, lean_box(0), v___x_751_);
return v___x_753_;
}
else
{
lean_object* v___f_754_; uint8_t v___x_755_; 
v___f_754_ = lean_alloc_closure((void*)(l_Lake_RBArray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_754_, 0, v_f_744_);
v___x_755_ = lean_nat_dec_le(v___x_750_, v___x_750_);
if (v___x_755_ == 0)
{
if (v___x_752_ == 0)
{
lean_object* v___x_756_; 
lean_inc(v_toPure_748_);
lean_dec_ref(v___f_754_);
lean_dec_ref(v_toArray_747_);
lean_dec_ref(v_inst_743_);
v___x_756_ = lean_apply_2(v_toPure_748_, lean_box(0), v___x_751_);
return v___x_756_;
}
else
{
size_t v___x_757_; size_t v___x_758_; lean_object* v___x_759_; 
v___x_757_ = ((size_t)0ULL);
v___x_758_ = lean_usize_of_nat(v___x_750_);
v___x_759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_743_, v___f_754_, v_toArray_747_, v___x_757_, v___x_758_, v___x_751_);
return v___x_759_;
}
}
else
{
size_t v___x_760_; size_t v___x_761_; lean_object* v___x_762_; 
v___x_760_ = ((size_t)0ULL);
v___x_761_ = lean_usize_of_nat(v___x_750_);
v___x_762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_743_, v___f_754_, v_toArray_747_, v___x_760_, v___x_761_, v___x_751_);
return v___x_762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM(lean_object* v_m_763_, lean_object* v_00_u03b2_764_, lean_object* v_00_u03b1_765_, lean_object* v_cmp_766_, lean_object* v_inst_767_, lean_object* v_f_768_, lean_object* v_self_769_){
_start:
{
lean_object* v_toApplicative_770_; lean_object* v_toArray_771_; lean_object* v_toPure_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v_toApplicative_770_ = lean_ctor_get(v_inst_767_, 0);
v_toArray_771_ = lean_ctor_get(v_self_769_, 1);
lean_inc_ref(v_toArray_771_);
lean_dec_ref(v_self_769_);
v_toPure_772_ = lean_ctor_get(v_toApplicative_770_, 1);
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = lean_array_get_size(v_toArray_771_);
v___x_775_ = lean_box(0);
v___x_776_ = lean_nat_dec_lt(v___x_773_, v___x_774_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; 
lean_inc(v_toPure_772_);
lean_dec_ref(v_toArray_771_);
lean_dec(v_f_768_);
lean_dec_ref(v_inst_767_);
v___x_777_ = lean_apply_2(v_toPure_772_, lean_box(0), v___x_775_);
return v___x_777_;
}
else
{
lean_object* v___f_778_; uint8_t v___x_779_; 
v___f_778_ = lean_alloc_closure((void*)(l_Lake_RBArray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_778_, 0, v_f_768_);
v___x_779_ = lean_nat_dec_le(v___x_774_, v___x_774_);
if (v___x_779_ == 0)
{
if (v___x_776_ == 0)
{
lean_object* v___x_780_; 
lean_inc(v_toPure_772_);
lean_dec_ref(v___f_778_);
lean_dec_ref(v_toArray_771_);
lean_dec_ref(v_inst_767_);
v___x_780_ = lean_apply_2(v_toPure_772_, lean_box(0), v___x_775_);
return v___x_780_;
}
else
{
size_t v___x_781_; size_t v___x_782_; lean_object* v___x_783_; 
v___x_781_ = ((size_t)0ULL);
v___x_782_ = lean_usize_of_nat(v___x_774_);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_767_, v___f_778_, v_toArray_771_, v___x_781_, v___x_782_, v___x_775_);
return v___x_783_;
}
}
else
{
size_t v___x_784_; size_t v___x_785_; lean_object* v___x_786_; 
v___x_784_ = ((size_t)0ULL);
v___x_785_ = lean_usize_of_nat(v___x_774_);
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_767_, v___f_778_, v_toArray_771_, v___x_784_, v___x_785_, v___x_775_);
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_RBArray(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
