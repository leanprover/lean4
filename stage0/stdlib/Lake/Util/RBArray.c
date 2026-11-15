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
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lake_RBArray_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_RBArray_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_RBArray_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lake_RBArray_isEmpty___redArg(lean_object* v_self_47_){
_start:
{
lean_object* v_toArray_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v_toArray_48_ = lean_ctor_get(v_self_47_, 1);
v___x_49_ = lean_array_get_size(v_toArray_48_);
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = lean_nat_dec_eq(v___x_49_, v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_isEmpty___redArg___boxed(lean_object* v_self_52_){
_start:
{
uint8_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l_Lake_RBArray_isEmpty___redArg(v_self_52_);
lean_dec_ref(v_self_52_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_isEmpty(lean_object* v_00_u03b1_55_, lean_object* v_00_u03b2_56_, lean_object* v_cmp_57_, lean_object* v_self_58_){
_start:
{
lean_object* v_toArray_59_; lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_toArray_59_ = lean_ctor_get(v_self_58_, 1);
v___x_60_ = lean_array_get_size(v_toArray_59_);
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = lean_nat_dec_eq(v___x_60_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_isEmpty___boxed(lean_object* v_00_u03b1_63_, lean_object* v_00_u03b2_64_, lean_object* v_cmp_65_, lean_object* v_self_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l_Lake_RBArray_isEmpty(v_00_u03b1_63_, v_00_u03b2_64_, v_cmp_65_, v_self_66_);
lean_dec_ref(v_self_66_);
lean_dec_ref(v_cmp_65_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_find_x3f___redArg(lean_object* v_cmp_69_, lean_object* v_self_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_toTreeMap_72_; lean_object* v___x_73_; 
v_toTreeMap_72_ = lean_ctor_get(v_self_70_, 0);
lean_inc(v_toTreeMap_72_);
lean_dec_ref(v_self_70_);
v___x_73_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_69_, v_toTreeMap_72_, v_a_71_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_find_x3f(lean_object* v_00_u03b1_74_, lean_object* v_00_u03b2_75_, lean_object* v_cmp_76_, lean_object* v_self_77_, lean_object* v_a_78_){
_start:
{
lean_object* v_toTreeMap_79_; lean_object* v___x_80_; 
v_toTreeMap_79_ = lean_ctor_get(v_self_77_, 0);
lean_inc(v_toTreeMap_79_);
lean_dec_ref(v_self_77_);
v___x_80_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_76_, v_toTreeMap_79_, v_a_78_);
return v___x_80_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_contains___redArg(lean_object* v_cmp_81_, lean_object* v_self_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_toTreeMap_84_; uint8_t v___x_85_; 
v_toTreeMap_84_ = lean_ctor_get(v_self_82_, 0);
lean_inc(v_toTreeMap_84_);
lean_dec_ref(v_self_82_);
v___x_85_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_81_, v_a_83_, v_toTreeMap_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_contains___redArg___boxed(lean_object* v_cmp_86_, lean_object* v_self_87_, lean_object* v_a_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Lake_RBArray_contains___redArg(v_cmp_86_, v_self_87_, v_a_88_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_contains(lean_object* v_00_u03b1_91_, lean_object* v_00_u03b2_92_, lean_object* v_cmp_93_, lean_object* v_self_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_toTreeMap_96_; uint8_t v___x_97_; 
v_toTreeMap_96_ = lean_ctor_get(v_self_94_, 0);
lean_inc(v_toTreeMap_96_);
lean_dec_ref(v_self_94_);
v___x_97_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_93_, v_a_95_, v_toTreeMap_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_contains___boxed(lean_object* v_00_u03b1_98_, lean_object* v_00_u03b2_99_, lean_object* v_cmp_100_, lean_object* v_self_101_, lean_object* v_a_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Lake_RBArray_contains(v_00_u03b1_98_, v_00_u03b2_99_, v_cmp_100_, v_self_101_, v_a_102_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(lean_object* v_cmp_105_, lean_object* v_k_106_, lean_object* v_v_107_, lean_object* v_t_108_){
_start:
{
if (lean_obj_tag(v_t_108_) == 0)
{
lean_object* v_size_109_; lean_object* v_k_110_; lean_object* v_v_111_; lean_object* v_l_112_; lean_object* v_r_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_394_; 
v_size_109_ = lean_ctor_get(v_t_108_, 0);
v_k_110_ = lean_ctor_get(v_t_108_, 1);
v_v_111_ = lean_ctor_get(v_t_108_, 2);
v_l_112_ = lean_ctor_get(v_t_108_, 3);
v_r_113_ = lean_ctor_get(v_t_108_, 4);
v_isSharedCheck_394_ = !lean_is_exclusive(v_t_108_);
if (v_isSharedCheck_394_ == 0)
{
v___x_115_ = v_t_108_;
v_isShared_116_ = v_isSharedCheck_394_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_r_113_);
lean_inc(v_l_112_);
lean_inc(v_v_111_);
lean_inc(v_k_110_);
lean_inc(v_size_109_);
lean_dec(v_t_108_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_394_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; uint8_t v___x_118_; 
lean_inc_ref(v_cmp_105_);
lean_inc(v_k_110_);
lean_inc(v_k_106_);
v___x_117_ = lean_apply_2(v_cmp_105_, v_k_106_, v_k_110_);
v___x_118_ = lean_unbox(v___x_117_);
switch(v___x_118_)
{
case 0:
{
lean_object* v_impl_119_; lean_object* v___x_120_; 
lean_dec(v_size_109_);
v_impl_119_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_105_, v_k_106_, v_v_107_, v_l_112_);
v___x_120_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_113_) == 0)
{
lean_object* v_size_121_; lean_object* v_size_122_; lean_object* v_k_123_; lean_object* v_v_124_; lean_object* v_l_125_; lean_object* v_r_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v_size_121_ = lean_ctor_get(v_r_113_, 0);
v_size_122_ = lean_ctor_get(v_impl_119_, 0);
v_k_123_ = lean_ctor_get(v_impl_119_, 1);
v_v_124_ = lean_ctor_get(v_impl_119_, 2);
v_l_125_ = lean_ctor_get(v_impl_119_, 3);
v_r_126_ = lean_ctor_get(v_impl_119_, 4);
lean_inc(v_r_126_);
v___x_127_ = lean_unsigned_to_nat(3u);
v___x_128_ = lean_nat_mul(v___x_127_, v_size_121_);
v___x_129_ = lean_nat_dec_lt(v___x_128_, v_size_122_);
lean_dec(v___x_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
lean_dec(v_r_126_);
v___x_130_ = lean_nat_add(v___x_120_, v_size_122_);
v___x_131_ = lean_nat_add(v___x_130_, v_size_121_);
lean_dec(v___x_130_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 3, v_impl_119_);
lean_ctor_set(v___x_115_, 0, v___x_131_);
v___x_133_ = v___x_115_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_k_110_);
lean_ctor_set(v_reuseFailAlloc_134_, 2, v_v_111_);
lean_ctor_set(v_reuseFailAlloc_134_, 3, v_impl_119_);
lean_ctor_set(v_reuseFailAlloc_134_, 4, v_r_113_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
else
{
lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_200_; 
lean_inc(v_l_125_);
lean_inc(v_v_124_);
lean_inc(v_k_123_);
lean_inc(v_size_122_);
v_isSharedCheck_200_ = !lean_is_exclusive(v_impl_119_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; lean_object* v_unused_202_; lean_object* v_unused_203_; lean_object* v_unused_204_; lean_object* v_unused_205_; 
v_unused_201_ = lean_ctor_get(v_impl_119_, 4);
lean_dec(v_unused_201_);
v_unused_202_ = lean_ctor_get(v_impl_119_, 3);
lean_dec(v_unused_202_);
v_unused_203_ = lean_ctor_get(v_impl_119_, 2);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_impl_119_, 1);
lean_dec(v_unused_204_);
v_unused_205_ = lean_ctor_get(v_impl_119_, 0);
lean_dec(v_unused_205_);
v___x_136_ = v_impl_119_;
v_isShared_137_ = v_isSharedCheck_200_;
goto v_resetjp_135_;
}
else
{
lean_dec(v_impl_119_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_200_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v_size_138_; lean_object* v_size_139_; lean_object* v_k_140_; lean_object* v_v_141_; lean_object* v_l_142_; lean_object* v_r_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v_size_138_ = lean_ctor_get(v_l_125_, 0);
v_size_139_ = lean_ctor_get(v_r_126_, 0);
v_k_140_ = lean_ctor_get(v_r_126_, 1);
v_v_141_ = lean_ctor_get(v_r_126_, 2);
v_l_142_ = lean_ctor_get(v_r_126_, 3);
v_r_143_ = lean_ctor_get(v_r_126_, 4);
v___x_144_ = lean_unsigned_to_nat(2u);
v___x_145_ = lean_nat_mul(v___x_144_, v_size_138_);
v___x_146_ = lean_nat_dec_lt(v_size_139_, v___x_145_);
lean_dec(v___x_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_175_; 
lean_inc(v_r_143_);
lean_inc(v_l_142_);
lean_inc(v_v_141_);
lean_inc(v_k_140_);
v_isSharedCheck_175_ = !lean_is_exclusive(v_r_126_);
if (v_isSharedCheck_175_ == 0)
{
lean_object* v_unused_176_; lean_object* v_unused_177_; lean_object* v_unused_178_; lean_object* v_unused_179_; lean_object* v_unused_180_; 
v_unused_176_ = lean_ctor_get(v_r_126_, 4);
lean_dec(v_unused_176_);
v_unused_177_ = lean_ctor_get(v_r_126_, 3);
lean_dec(v_unused_177_);
v_unused_178_ = lean_ctor_get(v_r_126_, 2);
lean_dec(v_unused_178_);
v_unused_179_ = lean_ctor_get(v_r_126_, 1);
lean_dec(v_unused_179_);
v_unused_180_ = lean_ctor_get(v_r_126_, 0);
lean_dec(v_unused_180_);
v___x_148_ = v_r_126_;
v_isShared_149_ = v_isSharedCheck_175_;
goto v_resetjp_147_;
}
else
{
lean_dec(v_r_126_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_175_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___x_163_; lean_object* v___y_165_; 
v___x_150_ = lean_nat_add(v___x_120_, v_size_122_);
lean_dec(v_size_122_);
v___x_151_ = lean_nat_add(v___x_150_, v_size_121_);
lean_dec(v___x_150_);
v___x_163_ = lean_nat_add(v___x_120_, v_size_138_);
if (lean_obj_tag(v_l_142_) == 0)
{
lean_object* v_size_173_; 
v_size_173_ = lean_ctor_get(v_l_142_, 0);
lean_inc(v_size_173_);
v___y_165_ = v_size_173_;
goto v___jp_164_;
}
else
{
lean_object* v___x_174_; 
v___x_174_ = lean_unsigned_to_nat(0u);
v___y_165_ = v___x_174_;
goto v___jp_164_;
}
v___jp_152_:
{
lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_156_ = lean_nat_add(v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec(v___y_154_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 4, v_r_113_);
lean_ctor_set(v___x_148_, 3, v_r_143_);
lean_ctor_set(v___x_148_, 2, v_v_111_);
lean_ctor_set(v___x_148_, 1, v_k_110_);
lean_ctor_set(v___x_148_, 0, v___x_156_);
v___x_158_ = v___x_148_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_k_110_);
lean_ctor_set(v_reuseFailAlloc_162_, 2, v_v_111_);
lean_ctor_set(v_reuseFailAlloc_162_, 3, v_r_143_);
lean_ctor_set(v_reuseFailAlloc_162_, 4, v_r_113_);
v___x_158_ = v_reuseFailAlloc_162_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_160_; 
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 4, v___x_158_);
lean_ctor_set(v___x_136_, 3, v___y_153_);
lean_ctor_set(v___x_136_, 2, v_v_141_);
lean_ctor_set(v___x_136_, 1, v_k_140_);
lean_ctor_set(v___x_136_, 0, v___x_151_);
v___x_160_ = v___x_136_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_k_140_);
lean_ctor_set(v_reuseFailAlloc_161_, 2, v_v_141_);
lean_ctor_set(v_reuseFailAlloc_161_, 3, v___y_153_);
lean_ctor_set(v_reuseFailAlloc_161_, 4, v___x_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
v___jp_164_:
{
lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_166_ = lean_nat_add(v___x_163_, v___y_165_);
lean_dec(v___y_165_);
lean_dec(v___x_163_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 4, v_l_142_);
lean_ctor_set(v___x_115_, 3, v_l_125_);
lean_ctor_set(v___x_115_, 2, v_v_124_);
lean_ctor_set(v___x_115_, 1, v_k_123_);
lean_ctor_set(v___x_115_, 0, v___x_166_);
v___x_168_ = v___x_115_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_k_123_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_v_124_);
lean_ctor_set(v_reuseFailAlloc_172_, 3, v_l_125_);
lean_ctor_set(v_reuseFailAlloc_172_, 4, v_l_142_);
v___x_168_ = v_reuseFailAlloc_172_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_169_; 
v___x_169_ = lean_nat_add(v___x_120_, v_size_121_);
if (lean_obj_tag(v_r_143_) == 0)
{
lean_object* v_size_170_; 
v_size_170_ = lean_ctor_get(v_r_143_, 0);
lean_inc(v_size_170_);
v___y_153_ = v___x_168_;
v___y_154_ = v___x_169_;
v___y_155_ = v_size_170_;
goto v___jp_152_;
}
else
{
lean_object* v___x_171_; 
v___x_171_ = lean_unsigned_to_nat(0u);
v___y_153_ = v___x_168_;
v___y_154_ = v___x_169_;
v___y_155_ = v___x_171_;
goto v___jp_152_;
}
}
}
}
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
lean_del_object(v___x_115_);
v___x_181_ = lean_nat_add(v___x_120_, v_size_122_);
lean_dec(v_size_122_);
v___x_182_ = lean_nat_add(v___x_181_, v_size_121_);
lean_dec(v___x_181_);
v___x_183_ = lean_nat_add(v___x_120_, v_size_121_);
v___x_184_ = lean_nat_add(v___x_183_, v_size_139_);
lean_dec(v___x_183_);
lean_inc_ref(v_r_113_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 4, v_r_113_);
lean_ctor_set(v___x_136_, 3, v_r_126_);
lean_ctor_set(v___x_136_, 2, v_v_111_);
lean_ctor_set(v___x_136_, 1, v_k_110_);
lean_ctor_set(v___x_136_, 0, v___x_184_);
v___x_186_ = v___x_136_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_k_110_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v_v_111_);
lean_ctor_set(v_reuseFailAlloc_199_, 3, v_r_126_);
lean_ctor_set(v_reuseFailAlloc_199_, 4, v_r_113_);
v___x_186_ = v_reuseFailAlloc_199_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
v_isSharedCheck_193_ = !lean_is_exclusive(v_r_113_);
if (v_isSharedCheck_193_ == 0)
{
lean_object* v_unused_194_; lean_object* v_unused_195_; lean_object* v_unused_196_; lean_object* v_unused_197_; lean_object* v_unused_198_; 
v_unused_194_ = lean_ctor_get(v_r_113_, 4);
lean_dec(v_unused_194_);
v_unused_195_ = lean_ctor_get(v_r_113_, 3);
lean_dec(v_unused_195_);
v_unused_196_ = lean_ctor_get(v_r_113_, 2);
lean_dec(v_unused_196_);
v_unused_197_ = lean_ctor_get(v_r_113_, 1);
lean_dec(v_unused_197_);
v_unused_198_ = lean_ctor_get(v_r_113_, 0);
lean_dec(v_unused_198_);
v___x_188_ = v_r_113_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_dec(v_r_113_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 4, v___x_186_);
lean_ctor_set(v___x_188_, 3, v_l_125_);
lean_ctor_set(v___x_188_, 2, v_v_124_);
lean_ctor_set(v___x_188_, 1, v_k_123_);
lean_ctor_set(v___x_188_, 0, v___x_182_);
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_k_123_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v_v_124_);
lean_ctor_set(v_reuseFailAlloc_192_, 3, v_l_125_);
lean_ctor_set(v_reuseFailAlloc_192_, 4, v___x_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_206_; 
v_l_206_ = lean_ctor_get(v_impl_119_, 3);
if (lean_obj_tag(v_l_206_) == 0)
{
lean_object* v_r_207_; lean_object* v_k_208_; lean_object* v_v_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_220_; 
lean_inc_ref(v_l_206_);
v_r_207_ = lean_ctor_get(v_impl_119_, 4);
v_k_208_ = lean_ctor_get(v_impl_119_, 1);
v_v_209_ = lean_ctor_get(v_impl_119_, 2);
v_isSharedCheck_220_ = !lean_is_exclusive(v_impl_119_);
if (v_isSharedCheck_220_ == 0)
{
lean_object* v_unused_221_; lean_object* v_unused_222_; 
v_unused_221_ = lean_ctor_get(v_impl_119_, 3);
lean_dec(v_unused_221_);
v_unused_222_ = lean_ctor_get(v_impl_119_, 0);
lean_dec(v_unused_222_);
v___x_211_ = v_impl_119_;
v_isShared_212_ = v_isSharedCheck_220_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_r_207_);
lean_inc(v_v_209_);
lean_inc(v_k_208_);
lean_dec(v_impl_119_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_220_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_213_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_207_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 3, v_r_207_);
lean_ctor_set(v___x_211_, 2, v_v_111_);
lean_ctor_set(v___x_211_, 1, v_k_110_);
lean_ctor_set(v___x_211_, 0, v___x_120_);
v___x_215_ = v___x_211_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_k_110_);
lean_ctor_set(v_reuseFailAlloc_219_, 2, v_v_111_);
lean_ctor_set(v_reuseFailAlloc_219_, 3, v_r_207_);
lean_ctor_set(v_reuseFailAlloc_219_, 4, v_r_207_);
v___x_215_ = v_reuseFailAlloc_219_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_217_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 4, v___x_215_);
lean_ctor_set(v___x_115_, 3, v_l_206_);
lean_ctor_set(v___x_115_, 2, v_v_209_);
lean_ctor_set(v___x_115_, 1, v_k_208_);
lean_ctor_set(v___x_115_, 0, v___x_213_);
v___x_217_ = v___x_115_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_k_208_);
lean_ctor_set(v_reuseFailAlloc_218_, 2, v_v_209_);
lean_ctor_set(v_reuseFailAlloc_218_, 3, v_l_206_);
lean_ctor_set(v_reuseFailAlloc_218_, 4, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
else
{
lean_object* v_r_223_; 
v_r_223_ = lean_ctor_get(v_impl_119_, 4);
lean_inc(v_r_223_);
if (lean_obj_tag(v_r_223_) == 0)
{
lean_object* v_k_224_; lean_object* v_v_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_248_; 
lean_inc(v_l_206_);
v_k_224_ = lean_ctor_get(v_impl_119_, 1);
v_v_225_ = lean_ctor_get(v_impl_119_, 2);
v_isSharedCheck_248_ = !lean_is_exclusive(v_impl_119_);
if (v_isSharedCheck_248_ == 0)
{
lean_object* v_unused_249_; lean_object* v_unused_250_; lean_object* v_unused_251_; 
v_unused_249_ = lean_ctor_get(v_impl_119_, 4);
lean_dec(v_unused_249_);
v_unused_250_ = lean_ctor_get(v_impl_119_, 3);
lean_dec(v_unused_250_);
v_unused_251_ = lean_ctor_get(v_impl_119_, 0);
lean_dec(v_unused_251_);
v___x_227_ = v_impl_119_;
v_isShared_228_ = v_isSharedCheck_248_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_v_225_);
lean_inc(v_k_224_);
lean_dec(v_impl_119_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_248_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v_k_229_; lean_object* v_v_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_244_; 
v_k_229_ = lean_ctor_get(v_r_223_, 1);
v_v_230_ = lean_ctor_get(v_r_223_, 2);
v_isSharedCheck_244_ = !lean_is_exclusive(v_r_223_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; lean_object* v_unused_246_; lean_object* v_unused_247_; 
v_unused_245_ = lean_ctor_get(v_r_223_, 4);
lean_dec(v_unused_245_);
v_unused_246_ = lean_ctor_get(v_r_223_, 3);
lean_dec(v_unused_246_);
v_unused_247_ = lean_ctor_get(v_r_223_, 0);
lean_dec(v_unused_247_);
v___x_232_ = v_r_223_;
v_isShared_233_ = v_isSharedCheck_244_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_v_230_);
lean_inc(v_k_229_);
lean_dec(v_r_223_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_244_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = lean_unsigned_to_nat(3u);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 4, v_l_206_);
lean_ctor_set(v___x_232_, 3, v_l_206_);
lean_ctor_set(v___x_232_, 2, v_v_225_);
lean_ctor_set(v___x_232_, 1, v_k_224_);
lean_ctor_set(v___x_232_, 0, v___x_120_);
v___x_236_ = v___x_232_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_k_224_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v_v_225_);
lean_ctor_set(v_reuseFailAlloc_243_, 3, v_l_206_);
lean_ctor_set(v_reuseFailAlloc_243_, 4, v_l_206_);
v___x_236_ = v_reuseFailAlloc_243_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 4, v_l_206_);
lean_ctor_set(v___x_227_, 2, v_v_111_);
lean_ctor_set(v___x_227_, 1, v_k_110_);
lean_ctor_set(v___x_227_, 0, v___x_120_);
v___x_238_ = v___x_227_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_k_110_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_v_111_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_l_206_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v_l_206_);
v___x_238_ = v_reuseFailAlloc_242_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_240_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 4, v___x_238_);
lean_ctor_set(v___x_115_, 3, v___x_236_);
lean_ctor_set(v___x_115_, 2, v_v_230_);
lean_ctor_set(v___x_115_, 1, v_k_229_);
lean_ctor_set(v___x_115_, 0, v___x_234_);
v___x_240_ = v___x_115_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_k_229_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_v_230_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
}
else
{
lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_252_ = lean_unsigned_to_nat(2u);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 4, v_r_223_);
lean_ctor_set(v___x_115_, 3, v_impl_119_);
lean_ctor_set(v___x_115_, 0, v___x_252_);
v___x_254_ = v___x_115_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_k_110_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_v_111_);
lean_ctor_set(v_reuseFailAlloc_255_, 3, v_impl_119_);
lean_ctor_set(v_reuseFailAlloc_255_, 4, v_r_223_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
}
case 1:
{
lean_object* v___x_257_; 
lean_dec(v_v_111_);
lean_dec(v_k_110_);
lean_dec_ref(v_cmp_105_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 2, v_v_107_);
lean_ctor_set(v___x_115_, 1, v_k_106_);
v___x_257_ = v___x_115_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_size_109_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_k_106_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_v_107_);
lean_ctor_set(v_reuseFailAlloc_258_, 3, v_l_112_);
lean_ctor_set(v_reuseFailAlloc_258_, 4, v_r_113_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
default: 
{
lean_object* v_impl_259_; lean_object* v___x_260_; 
lean_dec(v_size_109_);
v_impl_259_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_105_, v_k_106_, v_v_107_, v_r_113_);
v___x_260_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_112_) == 0)
{
lean_object* v_size_261_; lean_object* v_size_262_; lean_object* v_k_263_; lean_object* v_v_264_; lean_object* v_l_265_; lean_object* v_r_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v_size_261_ = lean_ctor_get(v_l_112_, 0);
v_size_262_ = lean_ctor_get(v_impl_259_, 0);
v_k_263_ = lean_ctor_get(v_impl_259_, 1);
v_v_264_ = lean_ctor_get(v_impl_259_, 2);
v_l_265_ = lean_ctor_get(v_impl_259_, 3);
lean_inc(v_l_265_);
v_r_266_ = lean_ctor_get(v_impl_259_, 4);
v___x_267_ = lean_unsigned_to_nat(3u);
v___x_268_ = lean_nat_mul(v___x_267_, v_size_261_);
v___x_269_ = lean_nat_dec_lt(v___x_268_, v_size_262_);
lean_dec(v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
lean_dec(v_l_265_);
v___x_270_ = lean_nat_add(v___x_260_, v_size_261_);
v___x_271_ = lean_nat_add(v___x_270_, v_size_262_);
lean_dec(v___x_270_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 4, v_impl_259_);
lean_ctor_set(v___x_115_, 0, v___x_271_);
v___x_273_ = v___x_115_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_k_110_);
lean_ctor_set(v_reuseFailAlloc_274_, 2, v_v_111_);
lean_ctor_set(v_reuseFailAlloc_274_, 3, v_l_112_);
lean_ctor_set(v_reuseFailAlloc_274_, 4, v_impl_259_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
else
{
lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_338_; 
lean_inc(v_r_266_);
lean_inc(v_v_264_);
lean_inc(v_k_263_);
lean_inc(v_size_262_);
v_isSharedCheck_338_ = !lean_is_exclusive(v_impl_259_);
if (v_isSharedCheck_338_ == 0)
{
lean_object* v_unused_339_; lean_object* v_unused_340_; lean_object* v_unused_341_; lean_object* v_unused_342_; lean_object* v_unused_343_; 
v_unused_339_ = lean_ctor_get(v_impl_259_, 4);
lean_dec(v_unused_339_);
v_unused_340_ = lean_ctor_get(v_impl_259_, 3);
lean_dec(v_unused_340_);
v_unused_341_ = lean_ctor_get(v_impl_259_, 2);
lean_dec(v_unused_341_);
v_unused_342_ = lean_ctor_get(v_impl_259_, 1);
lean_dec(v_unused_342_);
v_unused_343_ = lean_ctor_get(v_impl_259_, 0);
lean_dec(v_unused_343_);
v___x_276_ = v_impl_259_;
v_isShared_277_ = v_isSharedCheck_338_;
goto v_resetjp_275_;
}
else
{
lean_dec(v_impl_259_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_338_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v_size_278_; lean_object* v_k_279_; lean_object* v_v_280_; lean_object* v_l_281_; lean_object* v_r_282_; lean_object* v_size_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v_size_278_ = lean_ctor_get(v_l_265_, 0);
v_k_279_ = lean_ctor_get(v_l_265_, 1);
v_v_280_ = lean_ctor_get(v_l_265_, 2);
v_l_281_ = lean_ctor_get(v_l_265_, 3);
v_r_282_ = lean_ctor_get(v_l_265_, 4);
v_size_283_ = lean_ctor_get(v_r_266_, 0);
v___x_284_ = lean_unsigned_to_nat(2u);
v___x_285_ = lean_nat_mul(v___x_284_, v_size_283_);
v___x_286_ = lean_nat_dec_lt(v_size_278_, v___x_285_);
lean_dec(v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_314_; 
lean_inc(v_r_282_);
lean_inc(v_l_281_);
lean_inc(v_v_280_);
lean_inc(v_k_279_);
v_isSharedCheck_314_ = !lean_is_exclusive(v_l_265_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; lean_object* v_unused_316_; lean_object* v_unused_317_; lean_object* v_unused_318_; lean_object* v_unused_319_; 
v_unused_315_ = lean_ctor_get(v_l_265_, 4);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_l_265_, 3);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_l_265_, 2);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_l_265_, 1);
lean_dec(v_unused_318_);
v_unused_319_ = lean_ctor_get(v_l_265_, 0);
lean_dec(v_unused_319_);
v___x_288_ = v_l_265_;
v_isShared_289_ = v_isSharedCheck_314_;
goto v_resetjp_287_;
}
else
{
lean_dec(v_l_265_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_314_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_304_; 
v___x_290_ = lean_nat_add(v___x_260_, v_size_261_);
v___x_291_ = lean_nat_add(v___x_290_, v_size_262_);
lean_dec(v_size_262_);
if (lean_obj_tag(v_l_281_) == 0)
{
lean_object* v_size_312_; 
v_size_312_ = lean_ctor_get(v_l_281_, 0);
lean_inc(v_size_312_);
v___y_304_ = v_size_312_;
goto v___jp_303_;
}
else
{
lean_object* v___x_313_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___y_304_ = v___x_313_;
goto v___jp_303_;
}
v___jp_292_:
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = lean_nat_add(v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec(v___y_294_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 4, v_r_266_);
lean_ctor_set(v___x_288_, 3, v_r_282_);
lean_ctor_set(v___x_288_, 2, v_v_264_);
lean_ctor_set(v___x_288_, 1, v_k_263_);
lean_ctor_set(v___x_288_, 0, v___x_296_);
v___x_298_ = v___x_288_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_k_263_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_v_264_);
lean_ctor_set(v_reuseFailAlloc_302_, 3, v_r_282_);
lean_ctor_set(v_reuseFailAlloc_302_, 4, v_r_266_);
v___x_298_ = v_reuseFailAlloc_302_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_300_; 
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 4, v___x_298_);
lean_ctor_set(v___x_276_, 3, v___y_293_);
lean_ctor_set(v___x_276_, 2, v_v_280_);
lean_ctor_set(v___x_276_, 1, v_k_279_);
lean_ctor_set(v___x_276_, 0, v___x_291_);
v___x_300_ = v___x_276_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v_k_279_);
lean_ctor_set(v_reuseFailAlloc_301_, 2, v_v_280_);
lean_ctor_set(v_reuseFailAlloc_301_, 3, v___y_293_);
lean_ctor_set(v_reuseFailAlloc_301_, 4, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
v___jp_303_:
{
lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_305_ = lean_nat_add(v___x_290_, v___y_304_);
lean_dec(v___y_304_);
lean_dec(v___x_290_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 4, v_l_281_);
lean_ctor_set(v___x_115_, 0, v___x_305_);
v___x_307_ = v___x_115_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_k_110_);
lean_ctor_set(v_reuseFailAlloc_311_, 2, v_v_111_);
lean_ctor_set(v_reuseFailAlloc_311_, 3, v_l_112_);
lean_ctor_set(v_reuseFailAlloc_311_, 4, v_l_281_);
v___x_307_ = v_reuseFailAlloc_311_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; 
v___x_308_ = lean_nat_add(v___x_260_, v_size_283_);
if (lean_obj_tag(v_r_282_) == 0)
{
lean_object* v_size_309_; 
v_size_309_ = lean_ctor_get(v_r_282_, 0);
lean_inc(v_size_309_);
v___y_293_ = v___x_307_;
v___y_294_ = v___x_308_;
v___y_295_ = v_size_309_;
goto v___jp_292_;
}
else
{
lean_object* v___x_310_; 
v___x_310_ = lean_unsigned_to_nat(0u);
v___y_293_ = v___x_307_;
v___y_294_ = v___x_308_;
v___y_295_ = v___x_310_;
goto v___jp_292_;
}
}
}
}
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
lean_del_object(v___x_115_);
v___x_320_ = lean_nat_add(v___x_260_, v_size_261_);
v___x_321_ = lean_nat_add(v___x_320_, v_size_262_);
lean_dec(v_size_262_);
v___x_322_ = lean_nat_add(v___x_320_, v_size_278_);
lean_dec(v___x_320_);
lean_inc_ref(v_l_112_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 4, v_l_265_);
lean_ctor_set(v___x_276_, 3, v_l_112_);
lean_ctor_set(v___x_276_, 2, v_v_111_);
lean_ctor_set(v___x_276_, 1, v_k_110_);
lean_ctor_set(v___x_276_, 0, v___x_322_);
v___x_324_ = v___x_276_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_k_110_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_v_111_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v_l_112_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v_l_265_);
v___x_324_ = v_reuseFailAlloc_337_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
v_isSharedCheck_331_ = !lean_is_exclusive(v_l_112_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; lean_object* v_unused_333_; lean_object* v_unused_334_; lean_object* v_unused_335_; lean_object* v_unused_336_; 
v_unused_332_ = lean_ctor_get(v_l_112_, 4);
lean_dec(v_unused_332_);
v_unused_333_ = lean_ctor_get(v_l_112_, 3);
lean_dec(v_unused_333_);
v_unused_334_ = lean_ctor_get(v_l_112_, 2);
lean_dec(v_unused_334_);
v_unused_335_ = lean_ctor_get(v_l_112_, 1);
lean_dec(v_unused_335_);
v_unused_336_ = lean_ctor_get(v_l_112_, 0);
lean_dec(v_unused_336_);
v___x_326_ = v_l_112_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_dec(v_l_112_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 4, v_r_266_);
lean_ctor_set(v___x_326_, 3, v___x_324_);
lean_ctor_set(v___x_326_, 2, v_v_264_);
lean_ctor_set(v___x_326_, 1, v_k_263_);
lean_ctor_set(v___x_326_, 0, v___x_321_);
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_k_263_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_v_264_);
lean_ctor_set(v_reuseFailAlloc_330_, 3, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_330_, 4, v_r_266_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_344_; 
v_l_344_ = lean_ctor_get(v_impl_259_, 3);
lean_inc(v_l_344_);
if (lean_obj_tag(v_l_344_) == 0)
{
lean_object* v_r_345_; lean_object* v_k_346_; lean_object* v_v_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_370_; 
v_r_345_ = lean_ctor_get(v_impl_259_, 4);
v_k_346_ = lean_ctor_get(v_impl_259_, 1);
v_v_347_ = lean_ctor_get(v_impl_259_, 2);
v_isSharedCheck_370_ = !lean_is_exclusive(v_impl_259_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; lean_object* v_unused_372_; 
v_unused_371_ = lean_ctor_get(v_impl_259_, 3);
lean_dec(v_unused_371_);
v_unused_372_ = lean_ctor_get(v_impl_259_, 0);
lean_dec(v_unused_372_);
v___x_349_ = v_impl_259_;
v_isShared_350_ = v_isSharedCheck_370_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_r_345_);
lean_inc(v_v_347_);
lean_inc(v_k_346_);
lean_dec(v_impl_259_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_370_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v_k_351_; lean_object* v_v_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_366_; 
v_k_351_ = lean_ctor_get(v_l_344_, 1);
v_v_352_ = lean_ctor_get(v_l_344_, 2);
v_isSharedCheck_366_ = !lean_is_exclusive(v_l_344_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; lean_object* v_unused_368_; lean_object* v_unused_369_; 
v_unused_367_ = lean_ctor_get(v_l_344_, 4);
lean_dec(v_unused_367_);
v_unused_368_ = lean_ctor_get(v_l_344_, 3);
lean_dec(v_unused_368_);
v_unused_369_ = lean_ctor_get(v_l_344_, 0);
lean_dec(v_unused_369_);
v___x_354_ = v_l_344_;
v_isShared_355_ = v_isSharedCheck_366_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_v_352_);
lean_inc(v_k_351_);
lean_dec(v_l_344_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_366_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_356_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_345_, 2);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 4, v_r_345_);
lean_ctor_set(v___x_354_, 3, v_r_345_);
lean_ctor_set(v___x_354_, 2, v_v_111_);
lean_ctor_set(v___x_354_, 1, v_k_110_);
lean_ctor_set(v___x_354_, 0, v___x_260_);
v___x_358_ = v___x_354_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_k_110_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_v_111_);
lean_ctor_set(v_reuseFailAlloc_365_, 3, v_r_345_);
lean_ctor_set(v_reuseFailAlloc_365_, 4, v_r_345_);
v___x_358_ = v_reuseFailAlloc_365_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_360_; 
lean_inc(v_r_345_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 3, v_r_345_);
lean_ctor_set(v___x_349_, 0, v___x_260_);
v___x_360_ = v___x_349_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_k_346_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v_v_347_);
lean_ctor_set(v_reuseFailAlloc_364_, 3, v_r_345_);
lean_ctor_set(v_reuseFailAlloc_364_, 4, v_r_345_);
v___x_360_ = v_reuseFailAlloc_364_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_362_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 4, v___x_360_);
lean_ctor_set(v___x_115_, 3, v___x_358_);
lean_ctor_set(v___x_115_, 2, v_v_352_);
lean_ctor_set(v___x_115_, 1, v_k_351_);
lean_ctor_set(v___x_115_, 0, v___x_356_);
v___x_362_ = v___x_115_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_356_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_k_351_);
lean_ctor_set(v_reuseFailAlloc_363_, 2, v_v_352_);
lean_ctor_set(v_reuseFailAlloc_363_, 3, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_363_, 4, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
}
else
{
lean_object* v_r_373_; 
v_r_373_ = lean_ctor_get(v_impl_259_, 4);
lean_inc(v_r_373_);
if (lean_obj_tag(v_r_373_) == 0)
{
lean_object* v_k_374_; lean_object* v_v_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_386_; 
v_k_374_ = lean_ctor_get(v_impl_259_, 1);
v_v_375_ = lean_ctor_get(v_impl_259_, 2);
v_isSharedCheck_386_ = !lean_is_exclusive(v_impl_259_);
if (v_isSharedCheck_386_ == 0)
{
lean_object* v_unused_387_; lean_object* v_unused_388_; lean_object* v_unused_389_; 
v_unused_387_ = lean_ctor_get(v_impl_259_, 4);
lean_dec(v_unused_387_);
v_unused_388_ = lean_ctor_get(v_impl_259_, 3);
lean_dec(v_unused_388_);
v_unused_389_ = lean_ctor_get(v_impl_259_, 0);
lean_dec(v_unused_389_);
v___x_377_ = v_impl_259_;
v_isShared_378_ = v_isSharedCheck_386_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_v_375_);
lean_inc(v_k_374_);
lean_dec(v_impl_259_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_386_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_379_ = lean_unsigned_to_nat(3u);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 4, v_l_344_);
lean_ctor_set(v___x_377_, 2, v_v_111_);
lean_ctor_set(v___x_377_, 1, v_k_110_);
lean_ctor_set(v___x_377_, 0, v___x_260_);
v___x_381_ = v___x_377_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_k_110_);
lean_ctor_set(v_reuseFailAlloc_385_, 2, v_v_111_);
lean_ctor_set(v_reuseFailAlloc_385_, 3, v_l_344_);
lean_ctor_set(v_reuseFailAlloc_385_, 4, v_l_344_);
v___x_381_ = v_reuseFailAlloc_385_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_383_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 4, v_r_373_);
lean_ctor_set(v___x_115_, 3, v___x_381_);
lean_ctor_set(v___x_115_, 2, v_v_375_);
lean_ctor_set(v___x_115_, 1, v_k_374_);
lean_ctor_set(v___x_115_, 0, v___x_379_);
v___x_383_ = v___x_115_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_k_374_);
lean_ctor_set(v_reuseFailAlloc_384_, 2, v_v_375_);
lean_ctor_set(v_reuseFailAlloc_384_, 3, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_384_, 4, v_r_373_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
else
{
lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_390_ = lean_unsigned_to_nat(2u);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 4, v_impl_259_);
lean_ctor_set(v___x_115_, 3, v_r_373_);
lean_ctor_set(v___x_115_, 0, v___x_390_);
v___x_392_ = v___x_115_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_k_110_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v_v_111_);
lean_ctor_set(v_reuseFailAlloc_393_, 3, v_r_373_);
lean_ctor_set(v_reuseFailAlloc_393_, 4, v_impl_259_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
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
lean_object* v___x_395_; lean_object* v___x_396_; 
lean_dec_ref(v_cmp_105_);
v___x_395_ = lean_unsigned_to_nat(1u);
v___x_396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v_k_106_);
lean_ctor_set(v___x_396_, 2, v_v_107_);
lean_ctor_set(v___x_396_, 3, v_t_108_);
lean_ctor_set(v___x_396_, 4, v_t_108_);
return v___x_396_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(lean_object* v_cmp_397_, lean_object* v_k_398_, lean_object* v_t_399_){
_start:
{
if (lean_obj_tag(v_t_399_) == 0)
{
lean_object* v_k_400_; lean_object* v_l_401_; lean_object* v_r_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v_k_400_ = lean_ctor_get(v_t_399_, 1);
lean_inc(v_k_400_);
v_l_401_ = lean_ctor_get(v_t_399_, 3);
lean_inc(v_l_401_);
v_r_402_ = lean_ctor_get(v_t_399_, 4);
lean_inc(v_r_402_);
lean_dec_ref_known(v_t_399_, 5);
lean_inc_ref(v_cmp_397_);
lean_inc(v_k_398_);
v___x_403_ = lean_apply_2(v_cmp_397_, v_k_398_, v_k_400_);
v___x_404_ = lean_unbox(v___x_403_);
switch(v___x_404_)
{
case 0:
{
lean_dec(v_r_402_);
v_t_399_ = v_l_401_;
goto _start;
}
case 1:
{
uint8_t v___x_406_; 
lean_dec(v_r_402_);
lean_dec(v_l_401_);
lean_dec(v_k_398_);
lean_dec_ref(v_cmp_397_);
v___x_406_ = 1;
return v___x_406_;
}
default: 
{
lean_dec(v_l_401_);
v_t_399_ = v_r_402_;
goto _start;
}
}
}
else
{
uint8_t v___x_408_; 
lean_dec(v_k_398_);
lean_dec_ref(v_cmp_397_);
v___x_408_ = 0;
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg___boxed(lean_object* v_cmp_409_, lean_object* v_k_410_, lean_object* v_t_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(v_cmp_409_, v_k_410_, v_t_411_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_insert___redArg(lean_object* v_cmp_414_, lean_object* v_self_415_, lean_object* v_a_416_, lean_object* v_b_417_){
_start:
{
lean_object* v_toTreeMap_418_; lean_object* v_toArray_419_; uint8_t v___x_420_; 
v_toTreeMap_418_ = lean_ctor_get(v_self_415_, 0);
v_toArray_419_ = lean_ctor_get(v_self_415_, 1);
lean_inc(v_toTreeMap_418_);
lean_inc(v_a_416_);
lean_inc_ref(v_cmp_414_);
v___x_420_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(v_cmp_414_, v_a_416_, v_toTreeMap_418_);
if (v___x_420_ == 0)
{
lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_429_; 
lean_inc_ref(v_toArray_419_);
lean_inc(v_toTreeMap_418_);
v_isSharedCheck_429_ = !lean_is_exclusive(v_self_415_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; lean_object* v_unused_431_; 
v_unused_430_ = lean_ctor_get(v_self_415_, 1);
lean_dec(v_unused_430_);
v_unused_431_ = lean_ctor_get(v_self_415_, 0);
lean_dec(v_unused_431_);
v___x_422_ = v_self_415_;
v_isShared_423_ = v_isSharedCheck_429_;
goto v_resetjp_421_;
}
else
{
lean_dec(v_self_415_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_429_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
lean_inc(v_b_417_);
v___x_424_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_414_, v_a_416_, v_b_417_, v_toTreeMap_418_);
v___x_425_ = lean_array_push(v_toArray_419_, v_b_417_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 1, v___x_425_);
lean_ctor_set(v___x_422_, 0, v___x_424_);
v___x_427_ = v___x_422_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
else
{
lean_dec(v_b_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_cmp_414_);
return v_self_415_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_insert(lean_object* v_00_u03b1_432_, lean_object* v_00_u03b2_433_, lean_object* v_cmp_434_, lean_object* v_self_435_, lean_object* v_a_436_, lean_object* v_b_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lake_RBArray_insert___redArg(v_cmp_434_, v_self_435_, v_a_436_, v_b_437_);
return v___x_438_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0(lean_object* v_00_u03b1_439_, lean_object* v_cmp_440_, lean_object* v_00_u03b2_441_, lean_object* v_k_442_, lean_object* v_t_443_){
_start:
{
uint8_t v___x_444_; 
v___x_444_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(v_cmp_440_, v_k_442_, v_t_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___boxed(lean_object* v_00_u03b1_445_, lean_object* v_cmp_446_, lean_object* v_00_u03b2_447_, lean_object* v_k_448_, lean_object* v_t_449_){
_start:
{
uint8_t v_res_450_; lean_object* v_r_451_; 
v_res_450_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0(v_00_u03b1_445_, v_cmp_446_, v_00_u03b2_447_, v_k_448_, v_t_449_);
v_r_451_ = lean_box(v_res_450_);
return v_r_451_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1(lean_object* v_00_u03b1_452_, lean_object* v_cmp_453_, lean_object* v_00_u03b2_454_, lean_object* v_k_455_, lean_object* v_v_456_, lean_object* v_t_457_, lean_object* v_hl_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_453_, v_k_455_, v_v_456_, v_t_457_);
return v___x_459_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_all___redArg___lam__0(lean_object* v_f_460_, uint8_t v___x_461_, lean_object* v_v_462_){
_start:
{
lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_463_ = lean_apply_1(v_f_460_, v_v_462_);
v___x_464_ = lean_unbox(v___x_463_);
if (v___x_464_ == 0)
{
return v___x_461_;
}
else
{
uint8_t v___x_465_; 
v___x_465_ = 0;
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_all___redArg___lam__0___boxed(lean_object* v_f_466_, lean_object* v___x_467_, lean_object* v_v_468_){
_start:
{
uint8_t v___x_75__boxed_469_; uint8_t v_res_470_; lean_object* v_r_471_; 
v___x_75__boxed_469_ = lean_unbox(v___x_467_);
v_res_470_ = l_Lake_RBArray_all___redArg___lam__0(v_f_466_, v___x_75__boxed_469_, v_v_468_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_all___redArg(lean_object* v_f_491_, lean_object* v_self_492_){
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
LEAN_EXPORT lean_object* l_Lake_RBArray_all___redArg___boxed(lean_object* v_f_506_, lean_object* v_self_507_){
_start:
{
uint8_t v_res_508_; lean_object* v_r_509_; 
v_res_508_ = l_Lake_RBArray_all___redArg(v_f_506_, v_self_507_);
v_r_509_ = lean_box(v_res_508_);
return v_r_509_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_all(lean_object* v_00_u03b2_510_, lean_object* v_00_u03b1_511_, lean_object* v_cmp_512_, lean_object* v_f_513_, lean_object* v_self_514_){
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
uint8_t v___x_520_; 
lean_dec_ref(v_toArray_515_);
lean_dec_ref(v_f_513_);
v___x_520_ = 1;
return v___x_520_;
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
lean_object* v___x_521_; lean_object* v___f_522_; size_t v___x_523_; size_t v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_521_ = lean_box(v___x_519_);
v___f_522_ = lean_alloc_closure((void*)(l_Lake_RBArray_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_522_, 0, v_f_513_);
lean_closure_set(v___f_522_, 1, v___x_521_);
v___x_523_ = ((size_t)0ULL);
v___x_524_ = lean_usize_of_nat(v___x_517_);
v___x_525_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_518_, v___f_522_, v_toArray_515_, v___x_523_, v___x_524_);
v___x_526_ = lean_unbox(v___x_525_);
lean_dec(v___x_525_);
if (v___x_526_ == 0)
{
return v___x_519_;
}
else
{
uint8_t v___x_527_; 
v___x_527_ = 0;
return v___x_527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_all___boxed(lean_object* v_00_u03b2_528_, lean_object* v_00_u03b1_529_, lean_object* v_cmp_530_, lean_object* v_f_531_, lean_object* v_self_532_){
_start:
{
uint8_t v_res_533_; lean_object* v_r_534_; 
v_res_533_ = l_Lake_RBArray_all(v_00_u03b2_528_, v_00_u03b1_529_, v_cmp_530_, v_f_531_, v_self_532_);
lean_dec_ref(v_cmp_530_);
v_r_534_ = lean_box(v_res_533_);
return v_r_534_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_any___redArg___lam__0(lean_object* v_f_535_, lean_object* v_x_536_){
_start:
{
lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_537_ = lean_apply_1(v_f_535_, v_x_536_);
v___x_538_ = lean_unbox(v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_any___redArg___lam__0___boxed(lean_object* v_f_539_, lean_object* v_x_540_){
_start:
{
uint8_t v_res_541_; lean_object* v_r_542_; 
v_res_541_ = l_Lake_RBArray_any___redArg___lam__0(v_f_539_, v_x_540_);
v_r_542_ = lean_box(v_res_541_);
return v_r_542_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_any___redArg(lean_object* v_f_543_, lean_object* v_self_544_){
_start:
{
lean_object* v_toArray_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v_toArray_545_ = lean_ctor_get(v_self_544_, 1);
lean_inc_ref(v_toArray_545_);
lean_dec_ref(v_self_544_);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_array_get_size(v_toArray_545_);
v___x_548_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_549_ = lean_nat_dec_lt(v___x_546_, v___x_547_);
if (v___x_549_ == 0)
{
lean_dec_ref(v_toArray_545_);
lean_dec_ref(v_f_543_);
return v___x_549_;
}
else
{
if (v___x_549_ == 0)
{
lean_dec_ref(v_toArray_545_);
lean_dec_ref(v_f_543_);
return v___x_549_;
}
else
{
lean_object* v___f_550_; size_t v___x_551_; size_t v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___f_550_ = lean_alloc_closure((void*)(l_Lake_RBArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_550_, 0, v_f_543_);
v___x_551_ = ((size_t)0ULL);
v___x_552_ = lean_usize_of_nat(v___x_547_);
v___x_553_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_548_, v___f_550_, v_toArray_545_, v___x_551_, v___x_552_);
v___x_554_ = lean_unbox(v___x_553_);
lean_dec(v___x_553_);
return v___x_554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_any___redArg___boxed(lean_object* v_f_555_, lean_object* v_self_556_){
_start:
{
uint8_t v_res_557_; lean_object* v_r_558_; 
v_res_557_ = l_Lake_RBArray_any___redArg(v_f_555_, v_self_556_);
v_r_558_ = lean_box(v_res_557_);
return v_r_558_;
}
}
LEAN_EXPORT uint8_t l_Lake_RBArray_any(lean_object* v_00_u03b2_559_, lean_object* v_00_u03b1_560_, lean_object* v_cmp_561_, lean_object* v_f_562_, lean_object* v_self_563_){
_start:
{
lean_object* v_toArray_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v_toArray_564_ = lean_ctor_get(v_self_563_, 1);
lean_inc_ref(v_toArray_564_);
lean_dec_ref(v_self_563_);
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_array_get_size(v_toArray_564_);
v___x_567_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_568_ = lean_nat_dec_lt(v___x_565_, v___x_566_);
if (v___x_568_ == 0)
{
lean_dec_ref(v_toArray_564_);
lean_dec_ref(v_f_562_);
return v___x_568_;
}
else
{
if (v___x_568_ == 0)
{
lean_dec_ref(v_toArray_564_);
lean_dec_ref(v_f_562_);
return v___x_568_;
}
else
{
lean_object* v___f_569_; size_t v___x_570_; size_t v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___f_569_ = lean_alloc_closure((void*)(l_Lake_RBArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_569_, 0, v_f_562_);
v___x_570_ = ((size_t)0ULL);
v___x_571_ = lean_usize_of_nat(v___x_566_);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_567_, v___f_569_, v_toArray_564_, v___x_570_, v___x_571_);
v___x_573_ = lean_unbox(v___x_572_);
lean_dec(v___x_572_);
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_any___boxed(lean_object* v_00_u03b2_574_, lean_object* v_00_u03b1_575_, lean_object* v_cmp_576_, lean_object* v_f_577_, lean_object* v_self_578_){
_start:
{
uint8_t v_res_579_; lean_object* v_r_580_; 
v_res_579_ = l_Lake_RBArray_any(v_00_u03b2_574_, v_00_u03b1_575_, v_cmp_576_, v_f_577_, v_self_578_);
lean_dec_ref(v_cmp_576_);
v_r_580_ = lean_box(v_res_579_);
return v_r_580_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl___redArg___lam__0(lean_object* v_f_581_, lean_object* v_x1_582_, lean_object* v_x2_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = lean_apply_2(v_f_581_, v_x1_582_, v_x2_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl___redArg(lean_object* v_f_585_, lean_object* v_init_586_, lean_object* v_self_587_){
_start:
{
lean_object* v_toArray_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v_toArray_588_ = lean_ctor_get(v_self_587_, 1);
lean_inc_ref(v_toArray_588_);
lean_dec_ref(v_self_587_);
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = lean_array_get_size(v_toArray_588_);
v___x_591_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_592_ = lean_nat_dec_lt(v___x_589_, v___x_590_);
if (v___x_592_ == 0)
{
lean_dec_ref(v_toArray_588_);
lean_dec(v_f_585_);
return v_init_586_;
}
else
{
lean_object* v___f_593_; size_t v___x_594_; size_t v___x_595_; lean_object* v___x_596_; 
v___f_593_ = lean_alloc_closure((void*)(l_Lake_RBArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_593_, 0, v_f_585_);
v___x_594_ = ((size_t)0ULL);
v___x_595_ = lean_usize_of_nat(v___x_590_);
v___x_596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_591_, v___f_593_, v_toArray_588_, v___x_594_, v___x_595_, v_init_586_);
return v___x_596_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl(lean_object* v_00_u03c3_597_, lean_object* v_00_u03b2_598_, lean_object* v_00_u03b1_599_, lean_object* v_cmp_600_, lean_object* v_f_601_, lean_object* v_init_602_, lean_object* v_self_603_){
_start:
{
lean_object* v_toArray_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_toArray_604_ = lean_ctor_get(v_self_603_, 1);
lean_inc_ref(v_toArray_604_);
lean_dec_ref(v_self_603_);
v___x_605_ = lean_unsigned_to_nat(0u);
v___x_606_ = lean_array_get_size(v_toArray_604_);
v___x_607_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_608_ = lean_nat_dec_lt(v___x_605_, v___x_606_);
if (v___x_608_ == 0)
{
lean_dec_ref(v_toArray_604_);
lean_dec(v_f_601_);
return v_init_602_;
}
else
{
lean_object* v___f_609_; size_t v___x_610_; size_t v___x_611_; lean_object* v___x_612_; 
v___f_609_ = lean_alloc_closure((void*)(l_Lake_RBArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_609_, 0, v_f_601_);
v___x_610_ = ((size_t)0ULL);
v___x_611_ = lean_usize_of_nat(v___x_606_);
v___x_612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_607_, v___f_609_, v_toArray_604_, v___x_610_, v___x_611_, v_init_602_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl___boxed(lean_object* v_00_u03c3_613_, lean_object* v_00_u03b2_614_, lean_object* v_00_u03b1_615_, lean_object* v_cmp_616_, lean_object* v_f_617_, lean_object* v_init_618_, lean_object* v_self_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lake_RBArray_foldl(v_00_u03c3_613_, v_00_u03b2_614_, v_00_u03b1_615_, v_cmp_616_, v_f_617_, v_init_618_, v_self_619_);
lean_dec_ref(v_cmp_616_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldlM___redArg(lean_object* v_inst_621_, lean_object* v_f_622_, lean_object* v_init_623_, lean_object* v_self_624_){
_start:
{
lean_object* v_toApplicative_625_; lean_object* v_toArray_626_; lean_object* v_toPure_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_toApplicative_625_ = lean_ctor_get(v_inst_621_, 0);
v_toArray_626_ = lean_ctor_get(v_self_624_, 1);
lean_inc_ref(v_toArray_626_);
lean_dec_ref(v_self_624_);
v_toPure_627_ = lean_ctor_get(v_toApplicative_625_, 1);
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_array_get_size(v_toArray_626_);
v___x_630_ = lean_nat_dec_lt(v___x_628_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; 
lean_inc(v_toPure_627_);
lean_dec_ref(v_toArray_626_);
lean_dec(v_f_622_);
lean_dec_ref(v_inst_621_);
v___x_631_ = lean_apply_2(v_toPure_627_, lean_box(0), v_init_623_);
return v___x_631_;
}
else
{
size_t v___x_632_; size_t v___x_633_; lean_object* v___x_634_; 
v___x_632_ = ((size_t)0ULL);
v___x_633_ = lean_usize_of_nat(v___x_629_);
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_621_, v_f_622_, v_toArray_626_, v___x_632_, v___x_633_, v_init_623_);
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldlM(lean_object* v_m_635_, lean_object* v_00_u03c3_636_, lean_object* v_00_u03b2_637_, lean_object* v_00_u03b1_638_, lean_object* v_cmp_639_, lean_object* v_inst_640_, lean_object* v_f_641_, lean_object* v_init_642_, lean_object* v_self_643_){
_start:
{
lean_object* v_toApplicative_644_; lean_object* v_toArray_645_; lean_object* v_toPure_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_toApplicative_644_ = lean_ctor_get(v_inst_640_, 0);
v_toArray_645_ = lean_ctor_get(v_self_643_, 1);
lean_inc_ref(v_toArray_645_);
lean_dec_ref(v_self_643_);
v_toPure_646_ = lean_ctor_get(v_toApplicative_644_, 1);
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_array_get_size(v_toArray_645_);
v___x_649_ = lean_nat_dec_lt(v___x_647_, v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; 
lean_inc(v_toPure_646_);
lean_dec_ref(v_toArray_645_);
lean_dec(v_f_641_);
lean_dec_ref(v_inst_640_);
v___x_650_ = lean_apply_2(v_toPure_646_, lean_box(0), v_init_642_);
return v___x_650_;
}
else
{
size_t v___x_651_; size_t v___x_652_; lean_object* v___x_653_; 
v___x_651_ = ((size_t)0ULL);
v___x_652_ = lean_usize_of_nat(v___x_648_);
v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_640_, v_f_641_, v_toArray_645_, v___x_651_, v___x_652_, v_init_642_);
return v___x_653_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldlM___boxed(lean_object* v_m_654_, lean_object* v_00_u03c3_655_, lean_object* v_00_u03b2_656_, lean_object* v_00_u03b1_657_, lean_object* v_cmp_658_, lean_object* v_inst_659_, lean_object* v_f_660_, lean_object* v_init_661_, lean_object* v_self_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lake_RBArray_foldlM(v_m_654_, v_00_u03c3_655_, v_00_u03b2_656_, v_00_u03b1_657_, v_cmp_658_, v_inst_659_, v_f_660_, v_init_661_, v_self_662_);
lean_dec_ref(v_cmp_658_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldr___redArg(lean_object* v_f_664_, lean_object* v_init_665_, lean_object* v_self_666_){
_start:
{
lean_object* v_toArray_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v_toArray_667_ = lean_ctor_get(v_self_666_, 1);
lean_inc_ref(v_toArray_667_);
lean_dec_ref(v_self_666_);
v___x_668_ = lean_array_get_size(v_toArray_667_);
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_671_ = lean_nat_dec_lt(v___x_669_, v___x_668_);
if (v___x_671_ == 0)
{
lean_dec_ref(v_toArray_667_);
lean_dec(v_f_664_);
return v_init_665_;
}
else
{
lean_object* v___f_672_; size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; 
v___f_672_ = lean_alloc_closure((void*)(l_Lake_RBArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_672_, 0, v_f_664_);
v___x_673_ = lean_usize_of_nat(v___x_668_);
v___x_674_ = ((size_t)0ULL);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_670_, v___f_672_, v_toArray_667_, v___x_673_, v___x_674_, v_init_665_);
return v___x_675_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldr(lean_object* v_00_u03b2_676_, lean_object* v_00_u03c3_677_, lean_object* v_00_u03b1_678_, lean_object* v_cmp_679_, lean_object* v_f_680_, lean_object* v_init_681_, lean_object* v_self_682_){
_start:
{
lean_object* v_toArray_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v_toArray_683_ = lean_ctor_get(v_self_682_, 1);
lean_inc_ref(v_toArray_683_);
lean_dec_ref(v_self_682_);
v___x_684_ = lean_array_get_size(v_toArray_683_);
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_687_ = lean_nat_dec_lt(v___x_685_, v___x_684_);
if (v___x_687_ == 0)
{
lean_dec_ref(v_toArray_683_);
lean_dec(v_f_680_);
return v_init_681_;
}
else
{
lean_object* v___f_688_; size_t v___x_689_; size_t v___x_690_; lean_object* v___x_691_; 
v___f_688_ = lean_alloc_closure((void*)(l_Lake_RBArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_688_, 0, v_f_680_);
v___x_689_ = lean_usize_of_nat(v___x_684_);
v___x_690_ = ((size_t)0ULL);
v___x_691_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_686_, v___f_688_, v_toArray_683_, v___x_689_, v___x_690_, v_init_681_);
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldr___boxed(lean_object* v_00_u03b2_692_, lean_object* v_00_u03c3_693_, lean_object* v_00_u03b1_694_, lean_object* v_cmp_695_, lean_object* v_f_696_, lean_object* v_init_697_, lean_object* v_self_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lake_RBArray_foldr(v_00_u03b2_692_, v_00_u03c3_693_, v_00_u03b1_694_, v_cmp_695_, v_f_696_, v_init_697_, v_self_698_);
lean_dec_ref(v_cmp_695_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldrM___redArg(lean_object* v_inst_700_, lean_object* v_f_701_, lean_object* v_init_702_, lean_object* v_self_703_){
_start:
{
lean_object* v_toApplicative_704_; lean_object* v_toArray_705_; lean_object* v_toPure_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v_toApplicative_704_ = lean_ctor_get(v_inst_700_, 0);
v_toArray_705_ = lean_ctor_get(v_self_703_, 1);
lean_inc_ref(v_toArray_705_);
lean_dec_ref(v_self_703_);
v_toPure_706_ = lean_ctor_get(v_toApplicative_704_, 1);
v___x_707_ = lean_array_get_size(v_toArray_705_);
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_nat_dec_lt(v___x_708_, v___x_707_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; 
lean_inc(v_toPure_706_);
lean_dec_ref(v_toArray_705_);
lean_dec(v_f_701_);
lean_dec_ref(v_inst_700_);
v___x_710_ = lean_apply_2(v_toPure_706_, lean_box(0), v_init_702_);
return v___x_710_;
}
else
{
size_t v___x_711_; size_t v___x_712_; lean_object* v___x_713_; 
v___x_711_ = lean_usize_of_nat(v___x_707_);
v___x_712_ = ((size_t)0ULL);
v___x_713_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_700_, v_f_701_, v_toArray_705_, v___x_711_, v___x_712_, v_init_702_);
return v___x_713_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldrM(lean_object* v_m_714_, lean_object* v_00_u03b2_715_, lean_object* v_00_u03c3_716_, lean_object* v_00_u03b1_717_, lean_object* v_cmp_718_, lean_object* v_inst_719_, lean_object* v_f_720_, lean_object* v_init_721_, lean_object* v_self_722_){
_start:
{
lean_object* v_toApplicative_723_; lean_object* v_toArray_724_; lean_object* v_toPure_725_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_toApplicative_723_ = lean_ctor_get(v_inst_719_, 0);
v_toArray_724_ = lean_ctor_get(v_self_722_, 1);
lean_inc_ref(v_toArray_724_);
lean_dec_ref(v_self_722_);
v_toPure_725_ = lean_ctor_get(v_toApplicative_723_, 1);
v___x_726_ = lean_array_get_size(v_toArray_724_);
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = lean_nat_dec_lt(v___x_727_, v___x_726_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
lean_inc(v_toPure_725_);
lean_dec_ref(v_toArray_724_);
lean_dec(v_f_720_);
lean_dec_ref(v_inst_719_);
v___x_729_ = lean_apply_2(v_toPure_725_, lean_box(0), v_init_721_);
return v___x_729_;
}
else
{
size_t v___x_730_; size_t v___x_731_; lean_object* v___x_732_; 
v___x_730_ = lean_usize_of_nat(v___x_726_);
v___x_731_ = ((size_t)0ULL);
v___x_732_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_719_, v_f_720_, v_toArray_724_, v___x_730_, v___x_731_, v_init_721_);
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldrM___boxed(lean_object* v_m_733_, lean_object* v_00_u03b2_734_, lean_object* v_00_u03c3_735_, lean_object* v_00_u03b1_736_, lean_object* v_cmp_737_, lean_object* v_inst_738_, lean_object* v_f_739_, lean_object* v_init_740_, lean_object* v_self_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lake_RBArray_foldrM(v_m_733_, v_00_u03b2_734_, v_00_u03c3_735_, v_00_u03b1_736_, v_cmp_737_, v_inst_738_, v_f_739_, v_init_740_, v_self_741_);
lean_dec_ref(v_cmp_737_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM___redArg___lam__0(lean_object* v_f_743_, lean_object* v_x_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = lean_apply_1(v_f_743_, v___y_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM___redArg(lean_object* v_inst_747_, lean_object* v_f_748_, lean_object* v_self_749_){
_start:
{
lean_object* v_toApplicative_750_; lean_object* v_toArray_751_; lean_object* v_toPure_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v_toApplicative_750_ = lean_ctor_get(v_inst_747_, 0);
v_toArray_751_ = lean_ctor_get(v_self_749_, 1);
lean_inc_ref(v_toArray_751_);
lean_dec_ref(v_self_749_);
v_toPure_752_ = lean_ctor_get(v_toApplicative_750_, 1);
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_array_get_size(v_toArray_751_);
v___x_755_ = lean_box(0);
v___x_756_ = lean_nat_dec_lt(v___x_753_, v___x_754_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
lean_inc(v_toPure_752_);
lean_dec_ref(v_toArray_751_);
lean_dec(v_f_748_);
lean_dec_ref(v_inst_747_);
v___x_757_ = lean_apply_2(v_toPure_752_, lean_box(0), v___x_755_);
return v___x_757_;
}
else
{
lean_object* v___f_758_; size_t v___x_759_; size_t v___x_760_; lean_object* v___x_761_; 
v___f_758_ = lean_alloc_closure((void*)(l_Lake_RBArray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_758_, 0, v_f_748_);
v___x_759_ = ((size_t)0ULL);
v___x_760_ = lean_usize_of_nat(v___x_754_);
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_747_, v___f_758_, v_toArray_751_, v___x_759_, v___x_760_, v___x_755_);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM(lean_object* v_m_762_, lean_object* v_00_u03b2_763_, lean_object* v_00_u03b1_764_, lean_object* v_cmp_765_, lean_object* v_inst_766_, lean_object* v_f_767_, lean_object* v_self_768_){
_start:
{
lean_object* v_toApplicative_769_; lean_object* v_toArray_770_; lean_object* v_toPure_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_toApplicative_769_ = lean_ctor_get(v_inst_766_, 0);
v_toArray_770_ = lean_ctor_get(v_self_768_, 1);
lean_inc_ref(v_toArray_770_);
lean_dec_ref(v_self_768_);
v_toPure_771_ = lean_ctor_get(v_toApplicative_769_, 1);
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = lean_array_get_size(v_toArray_770_);
v___x_774_ = lean_box(0);
v___x_775_ = lean_nat_dec_lt(v___x_772_, v___x_773_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
lean_inc(v_toPure_771_);
lean_dec_ref(v_toArray_770_);
lean_dec(v_f_767_);
lean_dec_ref(v_inst_766_);
v___x_776_ = lean_apply_2(v_toPure_771_, lean_box(0), v___x_774_);
return v___x_776_;
}
else
{
lean_object* v___f_777_; size_t v___x_778_; size_t v___x_779_; lean_object* v___x_780_; 
v___f_777_ = lean_alloc_closure((void*)(l_Lake_RBArray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_777_, 0, v_f_767_);
v___x_778_ = ((size_t)0ULL);
v___x_779_ = lean_usize_of_nat(v___x_773_);
v___x_780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_766_, v___f_777_, v_toArray_770_, v___x_778_, v___x_779_, v___x_774_);
return v___x_780_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM___boxed(lean_object* v_m_781_, lean_object* v_00_u03b2_782_, lean_object* v_00_u03b1_783_, lean_object* v_cmp_784_, lean_object* v_inst_785_, lean_object* v_f_786_, lean_object* v_self_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lake_RBArray_forM(v_m_781_, v_00_u03b2_782_, v_00_u03b1_783_, v_cmp_784_, v_inst_785_, v_f_786_, v_self_787_);
lean_dec_ref(v_cmp_784_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn___redArg___lam__0(lean_object* v_f_789_, lean_object* v_a_790_, lean_object* v_x_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = lean_apply_2(v_f_789_, v_a_790_, v___y_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn___redArg(lean_object* v_inst_794_, lean_object* v_self_795_, lean_object* v_init_796_, lean_object* v_f_797_){
_start:
{
lean_object* v_toArray_798_; lean_object* v___f_799_; size_t v_sz_800_; size_t v___x_801_; lean_object* v___x_802_; 
v_toArray_798_ = lean_ctor_get(v_self_795_, 1);
lean_inc_ref(v_toArray_798_);
lean_dec_ref(v_self_795_);
v___f_799_ = lean_alloc_closure((void*)(l_Lake_RBArray_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_799_, 0, v_f_797_);
v_sz_800_ = lean_array_size(v_toArray_798_);
v___x_801_ = ((size_t)0ULL);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_794_, v_toArray_798_, v___f_799_, v_sz_800_, v___x_801_, v_init_796_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn(lean_object* v_m_803_, lean_object* v_00_u03b1_804_, lean_object* v_00_u03b2_805_, lean_object* v_cmp_806_, lean_object* v_00_u03c3_807_, lean_object* v_inst_808_, lean_object* v_self_809_, lean_object* v_init_810_, lean_object* v_f_811_){
_start:
{
lean_object* v_toArray_812_; lean_object* v___f_813_; size_t v_sz_814_; size_t v___x_815_; lean_object* v___x_816_; 
v_toArray_812_ = lean_ctor_get(v_self_809_, 1);
lean_inc_ref(v_toArray_812_);
lean_dec_ref(v_self_809_);
v___f_813_ = lean_alloc_closure((void*)(l_Lake_RBArray_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_813_, 0, v_f_811_);
v_sz_814_ = lean_array_size(v_toArray_812_);
v___x_815_ = ((size_t)0ULL);
v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_808_, v_toArray_812_, v___f_813_, v_sz_814_, v___x_815_, v_init_810_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn___boxed(lean_object* v_m_817_, lean_object* v_00_u03b1_818_, lean_object* v_00_u03b2_819_, lean_object* v_cmp_820_, lean_object* v_00_u03c3_821_, lean_object* v_inst_822_, lean_object* v_self_823_, lean_object* v_init_824_, lean_object* v_f_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lake_RBArray_forIn(v_m_817_, v_00_u03b1_818_, v_00_u03b2_819_, v_cmp_820_, v_00_u03c3_821_, v_inst_822_, v_self_823_, v_init_824_, v_f_825_);
lean_dec_ref(v_cmp_820_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__0(lean_object* v___y_827_, lean_object* v_a_828_, lean_object* v_x_829_, lean_object* v___y_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = lean_apply_2(v___y_827_, v_a_828_, v___y_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1(lean_object* v_inst_832_, lean_object* v_00_u03b2_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_toArray_837_; lean_object* v___f_838_; size_t v_sz_839_; size_t v___x_840_; lean_object* v___x_841_; 
v_toArray_837_ = lean_ctor_get(v___y_834_, 1);
lean_inc_ref(v_toArray_837_);
lean_dec_ref(v___y_834_);
v___f_838_ = lean_alloc_closure((void*)(l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_838_, 0, v___y_836_);
v_sz_839_ = lean_array_size(v_toArray_837_);
v___x_840_ = ((size_t)0ULL);
v___x_841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_832_, v_toArray_837_, v___f_838_, v_sz_839_, v___x_840_, v___y_835_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg(lean_object* v_inst_842_){
_start:
{
lean_object* v___f_843_; 
v___f_843_ = lean_alloc_closure((void*)(l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_843_, 0, v_inst_842_);
return v___f_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad(lean_object* v_m_844_, lean_object* v_00_u03b1_845_, lean_object* v_00_u03b2_846_, lean_object* v_cmp_847_, lean_object* v_inst_848_){
_start:
{
lean_object* v___f_849_; 
v___f_849_ = lean_alloc_closure((void*)(l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_849_, 0, v_inst_848_);
return v___f_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___boxed(lean_object* v_m_850_, lean_object* v_00_u03b1_851_, lean_object* v_00_u03b2_852_, lean_object* v_cmp_853_, lean_object* v_inst_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad(v_m_850_, v_00_u03b1_851_, v_00_u03b2_852_, v_cmp_853_, v_inst_854_);
lean_dec_ref(v_cmp_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkRBArray___redArg___lam__0(lean_object* v_f_856_, lean_object* v_cmp_857_, lean_object* v_x1_858_, lean_object* v_x2_859_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
lean_inc(v_x2_859_);
v___x_860_ = lean_apply_1(v_f_856_, v_x2_859_);
v___x_861_ = l_Lake_RBArray_insert___redArg(v_cmp_857_, v_x1_858_, v___x_860_, v_x2_859_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkRBArray___redArg(lean_object* v_cmp_862_, lean_object* v_f_863_, lean_object* v_vs_864_){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_865_ = lean_array_get_size(v_vs_864_);
v___x_866_ = l_Lake_RBArray_mkEmpty___redArg(v___x_865_);
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_869_ = lean_nat_dec_lt(v___x_867_, v___x_865_);
if (v___x_869_ == 0)
{
lean_dec_ref(v_vs_864_);
lean_dec(v_f_863_);
lean_dec_ref(v_cmp_862_);
return v___x_866_;
}
else
{
lean_object* v___f_870_; size_t v___x_871_; size_t v___x_872_; lean_object* v___x_873_; 
v___f_870_ = lean_alloc_closure((void*)(l_Lake_mkRBArray___redArg___lam__0), 4, 2);
lean_closure_set(v___f_870_, 0, v_f_863_);
lean_closure_set(v___f_870_, 1, v_cmp_862_);
v___x_871_ = ((size_t)0ULL);
v___x_872_ = lean_usize_of_nat(v___x_865_);
v___x_873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_868_, v___f_870_, v_vs_864_, v___x_871_, v___x_872_, v___x_866_);
return v___x_873_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkRBArray(lean_object* v_00_u03b2_874_, lean_object* v_00_u03b1_875_, lean_object* v_cmp_876_, lean_object* v_f_877_, lean_object* v_vs_878_){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_879_ = lean_array_get_size(v_vs_878_);
v___x_880_ = l_Lake_RBArray_mkEmpty___redArg(v___x_879_);
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_883_ = lean_nat_dec_lt(v___x_881_, v___x_879_);
if (v___x_883_ == 0)
{
lean_dec_ref(v_vs_878_);
lean_dec(v_f_877_);
lean_dec_ref(v_cmp_876_);
return v___x_880_;
}
else
{
lean_object* v___f_884_; size_t v___x_885_; size_t v___x_886_; lean_object* v___x_887_; 
v___f_884_ = lean_alloc_closure((void*)(l_Lake_mkRBArray___redArg___lam__0), 4, 2);
lean_closure_set(v___f_884_, 0, v_f_877_);
lean_closure_set(v___f_884_, 1, v_cmp_876_);
v___x_885_ = ((size_t)0ULL);
v___x_886_ = lean_usize_of_nat(v___x_879_);
v___x_887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_882_, v___f_884_, v_vs_878_, v___x_885_, v___x_886_, v___x_880_);
return v___x_887_;
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
