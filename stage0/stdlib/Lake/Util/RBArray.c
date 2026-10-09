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
lean_object* l_Lake_RBArray_empty___redArg(){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = ((lean_object*)(l_Lake_RBArray_empty___redArg___closed__1));
return v___x_7_;
}
}
LEAN_EXPORT void l_Lake_RBArray_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_8_;
v_res_8_ = l_Lake_RBArray_empty___redArg();
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_Lake_RBArray_empty___redArg___boxed(lean_object* v___dummy_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lake_RBArray_empty___redArg();
return v_res_10_;
}
}
static lean_object* _init_l_Lake_RBArray_empty___closed__0(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Lake_RBArray_empty___redArg();
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_empty(lean_object* v_00_u03b1_12_, lean_object* v_00_u03b2_13_, lean_object* v_cmp_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&l_Lake_RBArray_empty___closed__0, &l_Lake_RBArray_empty___closed__0_once, _init_l_Lake_RBArray_empty___closed__0);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_empty___boxed(lean_object* v_00_u03b1_16_, lean_object* v_00_u03b2_17_, lean_object* v_cmp_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lake_RBArray_empty(v_00_u03b1_16_, v_00_u03b2_17_, v_cmp_18_);
lean_dec_ref(v_cmp_18_);
return v_res_19_;
}
}
lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_obj_once(&l_Lake_RBArray_empty___closed__0, &l_Lake_RBArray_empty___closed__0_once, _init_l_Lake_RBArray_empty___closed__0);
return v___x_21_;
}
}
LEAN_EXPORT void l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_22_;
v_res_22_ = l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg();
stack->m_obj
 = v_res_22_;
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg___boxed(lean_object* v___dummy_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___redArg();
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection(lean_object* v_00_u03b1_25_, lean_object* v_00_u03b2_26_, lean_object* v_cmp_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_obj_once(&l_Lake_RBArray_empty___closed__0, &l_Lake_RBArray_empty___closed__0_once, _init_l_Lake_RBArray_empty___closed__0);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection___boxed(lean_object* v_00_u03b1_29_, lean_object* v_00_u03b2_30_, lean_object* v_cmp_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Lake_Util_RBArray_0__Lake_RBArray_instEmptyCollection(v_00_u03b1_29_, v_00_u03b2_30_, v_cmp_31_);
lean_dec_ref(v_cmp_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_mkEmpty___redArg(lean_object* v_size_33_){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_box(1);
v___x_35_ = lean_mk_empty_array_with_capacity(v_size_33_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_34_);
lean_ctor_set(v___x_36_, 1, v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_mkEmpty___redArg___boxed(lean_object* v_size_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lake_RBArray_mkEmpty___redArg(v_size_37_);
lean_dec(v_size_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_mkEmpty(lean_object* v_00_u03b1_39_, lean_object* v_00_u03b2_40_, lean_object* v_cmp_41_, lean_object* v_size_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lake_RBArray_mkEmpty___redArg(v_size_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_mkEmpty___boxed(lean_object* v_00_u03b1_44_, lean_object* v_00_u03b2_45_, lean_object* v_cmp_46_, lean_object* v_size_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lake_RBArray_mkEmpty(v_00_u03b1_44_, v_00_u03b2_45_, v_cmp_46_, v_size_47_);
lean_dec(v_size_47_);
lean_dec_ref(v_cmp_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_find_x3f___redArg(lean_object* v_cmp_49_, lean_object* v_self_50_, lean_object* v_a_51_){
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
LEAN_EXPORT lean_object* l_Lake_RBArray_find_x3f(lean_object* v_00_u03b1_54_, lean_object* v_00_u03b2_55_, lean_object* v_cmp_56_, lean_object* v_self_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_toTreeMap_59_; lean_object* v___x_60_; 
v_toTreeMap_59_ = lean_ctor_get(v_self_57_, 0);
lean_inc(v_toTreeMap_59_);
lean_dec_ref(v_self_57_);
v___x_60_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_56_, v_toTreeMap_59_, v_a_58_);
return v___x_60_;
}
}
uint8_t l_Lake_RBArray_contains___redArg(lean_object* v_cmp_61_, lean_object* v_self_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_toTreeMap_64_; uint8_t v___x_65_; 
v_toTreeMap_64_ = lean_ctor_get(v_self_62_, 0);
lean_inc(v_toTreeMap_64_);
lean_dec_ref(v_self_62_);
v___x_65_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_61_, v_a_63_, v_toTreeMap_64_);
return v___x_65_;
}
}
LEAN_EXPORT void l_Lake_RBArray_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_61_ = stack[0].m_obj;
lean_object* v_self_62_ = stack[1].m_obj;
lean_object* v_a_63_ = stack[2].m_obj;
uint8_t v_res_66_;
v_res_66_ = l_Lake_RBArray_contains___redArg(v_cmp_61_, v_self_62_, v_a_63_);
stack->m_num = v_res_66_;
}
LEAN_EXPORT lean_object* l_Lake_RBArray_contains___redArg___boxed(lean_object* v_cmp_67_, lean_object* v_self_68_, lean_object* v_a_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_Lake_RBArray_contains___redArg(v_cmp_67_, v_self_68_, v_a_69_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
uint8_t l_Lake_RBArray_contains(lean_object* v_00_u03b1_72_, lean_object* v_00_u03b2_73_, lean_object* v_cmp_74_, lean_object* v_self_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_toTreeMap_77_; uint8_t v___x_78_; 
v_toTreeMap_77_ = lean_ctor_get(v_self_75_, 0);
lean_inc(v_toTreeMap_77_);
lean_dec_ref(v_self_75_);
v___x_78_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_74_, v_a_76_, v_toTreeMap_77_);
return v___x_78_;
}
}
LEAN_EXPORT void l_Lake_RBArray_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_74_ = stack[2].m_obj;
lean_object* v_self_75_ = stack[3].m_obj;
lean_object* v_a_76_ = stack[4].m_obj;
uint8_t v_res_79_;
v_res_79_ = l_Lake_RBArray_contains(lean_box(0), lean_box(0), v_cmp_74_, v_self_75_, v_a_76_);
stack->m_num = v_res_79_;
}
LEAN_EXPORT lean_object* l_Lake_RBArray_contains___boxed(lean_object* v_00_u03b1_80_, lean_object* v_00_u03b2_81_, lean_object* v_cmp_82_, lean_object* v_self_83_, lean_object* v_a_84_){
_start:
{
uint8_t v_res_85_; lean_object* v_r_86_; 
v_res_85_ = l_Lake_RBArray_contains(v_00_u03b1_80_, v_00_u03b2_81_, v_cmp_82_, v_self_83_, v_a_84_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(lean_object* v_cmp_87_, lean_object* v_k_88_, lean_object* v_v_89_, lean_object* v_t_90_){
_start:
{
if (lean_obj_tag(v_t_90_) == 0)
{
lean_object* v_size_91_; lean_object* v_k_92_; lean_object* v_v_93_; lean_object* v_l_94_; lean_object* v_r_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_376_; 
v_size_91_ = lean_ctor_get(v_t_90_, 0);
v_k_92_ = lean_ctor_get(v_t_90_, 1);
v_v_93_ = lean_ctor_get(v_t_90_, 2);
v_l_94_ = lean_ctor_get(v_t_90_, 3);
v_r_95_ = lean_ctor_get(v_t_90_, 4);
v_isSharedCheck_376_ = !lean_is_exclusive(v_t_90_);
if (v_isSharedCheck_376_ == 0)
{
v___x_97_ = v_t_90_;
v_isShared_98_ = v_isSharedCheck_376_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_r_95_);
lean_inc(v_l_94_);
lean_inc(v_v_93_);
lean_inc(v_k_92_);
lean_inc(v_size_91_);
lean_dec(v_t_90_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_376_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_99_; uint8_t v___x_100_; 
lean_inc_ref(v_cmp_87_);
lean_inc(v_k_92_);
lean_inc(v_k_88_);
v___x_99_ = lean_apply_2(v_cmp_87_, v_k_88_, v_k_92_);
v___x_100_ = lean_unbox(v___x_99_);
switch(v___x_100_)
{
case 0:
{
lean_object* v_impl_101_; lean_object* v___x_102_; 
lean_dec(v_size_91_);
v_impl_101_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_87_, v_k_88_, v_v_89_, v_l_94_);
v___x_102_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_95_) == 0)
{
lean_object* v_size_103_; lean_object* v_size_104_; lean_object* v_k_105_; lean_object* v_v_106_; lean_object* v_l_107_; lean_object* v_r_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_size_103_ = lean_ctor_get(v_r_95_, 0);
v_size_104_ = lean_ctor_get(v_impl_101_, 0);
v_k_105_ = lean_ctor_get(v_impl_101_, 1);
v_v_106_ = lean_ctor_get(v_impl_101_, 2);
v_l_107_ = lean_ctor_get(v_impl_101_, 3);
v_r_108_ = lean_ctor_get(v_impl_101_, 4);
lean_inc(v_r_108_);
v___x_109_ = lean_unsigned_to_nat(3u);
v___x_110_ = lean_nat_mul(v___x_109_, v_size_103_);
v___x_111_ = lean_nat_dec_lt(v___x_110_, v_size_104_);
lean_dec(v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_115_; 
lean_dec(v_r_108_);
v___x_112_ = lean_nat_add(v___x_102_, v_size_104_);
v___x_113_ = lean_nat_add(v___x_112_, v_size_103_);
lean_dec(v___x_112_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 3, v_impl_101_);
lean_ctor_set(v___x_97_, 0, v___x_113_);
v___x_115_ = v___x_97_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_k_92_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v_v_93_);
lean_ctor_set(v_reuseFailAlloc_116_, 3, v_impl_101_);
lean_ctor_set(v_reuseFailAlloc_116_, 4, v_r_95_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
else
{
lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_182_; 
lean_inc(v_l_107_);
lean_inc(v_v_106_);
lean_inc(v_k_105_);
lean_inc(v_size_104_);
v_isSharedCheck_182_ = !lean_is_exclusive(v_impl_101_);
if (v_isSharedCheck_182_ == 0)
{
lean_object* v_unused_183_; lean_object* v_unused_184_; lean_object* v_unused_185_; lean_object* v_unused_186_; lean_object* v_unused_187_; 
v_unused_183_ = lean_ctor_get(v_impl_101_, 4);
lean_dec(v_unused_183_);
v_unused_184_ = lean_ctor_get(v_impl_101_, 3);
lean_dec(v_unused_184_);
v_unused_185_ = lean_ctor_get(v_impl_101_, 2);
lean_dec(v_unused_185_);
v_unused_186_ = lean_ctor_get(v_impl_101_, 1);
lean_dec(v_unused_186_);
v_unused_187_ = lean_ctor_get(v_impl_101_, 0);
lean_dec(v_unused_187_);
v___x_118_ = v_impl_101_;
v_isShared_119_ = v_isSharedCheck_182_;
goto v_resetjp_117_;
}
else
{
lean_dec(v_impl_101_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_182_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v_size_120_; lean_object* v_size_121_; lean_object* v_k_122_; lean_object* v_v_123_; lean_object* v_l_124_; lean_object* v_r_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v_size_120_ = lean_ctor_get(v_l_107_, 0);
v_size_121_ = lean_ctor_get(v_r_108_, 0);
v_k_122_ = lean_ctor_get(v_r_108_, 1);
v_v_123_ = lean_ctor_get(v_r_108_, 2);
v_l_124_ = lean_ctor_get(v_r_108_, 3);
v_r_125_ = lean_ctor_get(v_r_108_, 4);
v___x_126_ = lean_unsigned_to_nat(2u);
v___x_127_ = lean_nat_mul(v___x_126_, v_size_120_);
v___x_128_ = lean_nat_dec_lt(v_size_121_, v___x_127_);
lean_dec(v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_157_; 
lean_inc(v_r_125_);
lean_inc(v_l_124_);
lean_inc(v_v_123_);
lean_inc(v_k_122_);
v_isSharedCheck_157_ = !lean_is_exclusive(v_r_108_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; lean_object* v_unused_159_; lean_object* v_unused_160_; lean_object* v_unused_161_; lean_object* v_unused_162_; 
v_unused_158_ = lean_ctor_get(v_r_108_, 4);
lean_dec(v_unused_158_);
v_unused_159_ = lean_ctor_get(v_r_108_, 3);
lean_dec(v_unused_159_);
v_unused_160_ = lean_ctor_get(v_r_108_, 2);
lean_dec(v_unused_160_);
v_unused_161_ = lean_ctor_get(v_r_108_, 1);
lean_dec(v_unused_161_);
v_unused_162_ = lean_ctor_get(v_r_108_, 0);
lean_dec(v_unused_162_);
v___x_130_ = v_r_108_;
v_isShared_131_ = v_isSharedCheck_157_;
goto v_resetjp_129_;
}
else
{
lean_dec(v_r_108_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_157_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___y_135_; lean_object* v___y_136_; lean_object* v___y_137_; lean_object* v___x_145_; lean_object* v___y_147_; 
v___x_132_ = lean_nat_add(v___x_102_, v_size_104_);
lean_dec(v_size_104_);
v___x_133_ = lean_nat_add(v___x_132_, v_size_103_);
lean_dec(v___x_132_);
v___x_145_ = lean_nat_add(v___x_102_, v_size_120_);
if (lean_obj_tag(v_l_124_) == 0)
{
lean_object* v_size_155_; 
v_size_155_ = lean_ctor_get(v_l_124_, 0);
lean_inc(v_size_155_);
v___y_147_ = v_size_155_;
goto v___jp_146_;
}
else
{
lean_object* v___x_156_; 
v___x_156_ = lean_unsigned_to_nat(0u);
v___y_147_ = v___x_156_;
goto v___jp_146_;
}
v___jp_134_:
{
lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_138_ = lean_nat_add(v___y_135_, v___y_137_);
lean_dec(v___y_137_);
lean_dec(v___y_135_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 4, v_r_95_);
lean_ctor_set(v___x_130_, 3, v_r_125_);
lean_ctor_set(v___x_130_, 2, v_v_93_);
lean_ctor_set(v___x_130_, 1, v_k_92_);
lean_ctor_set(v___x_130_, 0, v___x_138_);
v___x_140_ = v___x_130_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_k_92_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v_v_93_);
lean_ctor_set(v_reuseFailAlloc_144_, 3, v_r_125_);
lean_ctor_set(v_reuseFailAlloc_144_, 4, v_r_95_);
v___x_140_ = v_reuseFailAlloc_144_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_142_; 
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 4, v___x_140_);
lean_ctor_set(v___x_118_, 3, v___y_136_);
lean_ctor_set(v___x_118_, 2, v_v_123_);
lean_ctor_set(v___x_118_, 1, v_k_122_);
lean_ctor_set(v___x_118_, 0, v___x_133_);
v___x_142_ = v___x_118_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_k_122_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v_v_123_);
lean_ctor_set(v_reuseFailAlloc_143_, 3, v___y_136_);
lean_ctor_set(v_reuseFailAlloc_143_, 4, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
v___jp_146_:
{
lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_148_ = lean_nat_add(v___x_145_, v___y_147_);
lean_dec(v___y_147_);
lean_dec(v___x_145_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 4, v_l_124_);
lean_ctor_set(v___x_97_, 3, v_l_107_);
lean_ctor_set(v___x_97_, 2, v_v_106_);
lean_ctor_set(v___x_97_, 1, v_k_105_);
lean_ctor_set(v___x_97_, 0, v___x_148_);
v___x_150_ = v___x_97_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_k_105_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_v_106_);
lean_ctor_set(v_reuseFailAlloc_154_, 3, v_l_107_);
lean_ctor_set(v_reuseFailAlloc_154_, 4, v_l_124_);
v___x_150_ = v_reuseFailAlloc_154_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; 
v___x_151_ = lean_nat_add(v___x_102_, v_size_103_);
if (lean_obj_tag(v_r_125_) == 0)
{
lean_object* v_size_152_; 
v_size_152_ = lean_ctor_get(v_r_125_, 0);
lean_inc(v_size_152_);
v___y_135_ = v___x_151_;
v___y_136_ = v___x_150_;
v___y_137_ = v_size_152_;
goto v___jp_134_;
}
else
{
lean_object* v___x_153_; 
v___x_153_ = lean_unsigned_to_nat(0u);
v___y_135_ = v___x_151_;
v___y_136_ = v___x_150_;
v___y_137_ = v___x_153_;
goto v___jp_134_;
}
}
}
}
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
lean_del_object(v___x_97_);
v___x_163_ = lean_nat_add(v___x_102_, v_size_104_);
lean_dec(v_size_104_);
v___x_164_ = lean_nat_add(v___x_163_, v_size_103_);
lean_dec(v___x_163_);
v___x_165_ = lean_nat_add(v___x_102_, v_size_103_);
v___x_166_ = lean_nat_add(v___x_165_, v_size_121_);
lean_dec(v___x_165_);
lean_inc_ref(v_r_95_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 4, v_r_95_);
lean_ctor_set(v___x_118_, 3, v_r_108_);
lean_ctor_set(v___x_118_, 2, v_v_93_);
lean_ctor_set(v___x_118_, 1, v_k_92_);
lean_ctor_set(v___x_118_, 0, v___x_166_);
v___x_168_ = v___x_118_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_k_92_);
lean_ctor_set(v_reuseFailAlloc_181_, 2, v_v_93_);
lean_ctor_set(v_reuseFailAlloc_181_, 3, v_r_108_);
lean_ctor_set(v_reuseFailAlloc_181_, 4, v_r_95_);
v___x_168_ = v_reuseFailAlloc_181_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
v_isSharedCheck_175_ = !lean_is_exclusive(v_r_95_);
if (v_isSharedCheck_175_ == 0)
{
lean_object* v_unused_176_; lean_object* v_unused_177_; lean_object* v_unused_178_; lean_object* v_unused_179_; lean_object* v_unused_180_; 
v_unused_176_ = lean_ctor_get(v_r_95_, 4);
lean_dec(v_unused_176_);
v_unused_177_ = lean_ctor_get(v_r_95_, 3);
lean_dec(v_unused_177_);
v_unused_178_ = lean_ctor_get(v_r_95_, 2);
lean_dec(v_unused_178_);
v_unused_179_ = lean_ctor_get(v_r_95_, 1);
lean_dec(v_unused_179_);
v_unused_180_ = lean_ctor_get(v_r_95_, 0);
lean_dec(v_unused_180_);
v___x_170_ = v_r_95_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_dec(v_r_95_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 4, v___x_168_);
lean_ctor_set(v___x_170_, 3, v_l_107_);
lean_ctor_set(v___x_170_, 2, v_v_106_);
lean_ctor_set(v___x_170_, 1, v_k_105_);
lean_ctor_set(v___x_170_, 0, v___x_164_);
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_k_105_);
lean_ctor_set(v_reuseFailAlloc_174_, 2, v_v_106_);
lean_ctor_set(v_reuseFailAlloc_174_, 3, v_l_107_);
lean_ctor_set(v_reuseFailAlloc_174_, 4, v___x_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_188_; 
v_l_188_ = lean_ctor_get(v_impl_101_, 3);
if (lean_obj_tag(v_l_188_) == 0)
{
lean_object* v_r_189_; lean_object* v_k_190_; lean_object* v_v_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_202_; 
lean_inc_ref(v_l_188_);
v_r_189_ = lean_ctor_get(v_impl_101_, 4);
v_k_190_ = lean_ctor_get(v_impl_101_, 1);
v_v_191_ = lean_ctor_get(v_impl_101_, 2);
v_isSharedCheck_202_ = !lean_is_exclusive(v_impl_101_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; lean_object* v_unused_204_; 
v_unused_203_ = lean_ctor_get(v_impl_101_, 3);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_impl_101_, 0);
lean_dec(v_unused_204_);
v___x_193_ = v_impl_101_;
v_isShared_194_ = v_isSharedCheck_202_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_r_189_);
lean_inc(v_v_191_);
lean_inc(v_k_190_);
lean_dec(v_impl_101_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_202_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_195_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_189_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 3, v_r_189_);
lean_ctor_set(v___x_193_, 2, v_v_93_);
lean_ctor_set(v___x_193_, 1, v_k_92_);
lean_ctor_set(v___x_193_, 0, v___x_102_);
v___x_197_ = v___x_193_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_k_92_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v_v_93_);
lean_ctor_set(v_reuseFailAlloc_201_, 3, v_r_189_);
lean_ctor_set(v_reuseFailAlloc_201_, 4, v_r_189_);
v___x_197_ = v_reuseFailAlloc_201_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_199_; 
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 4, v___x_197_);
lean_ctor_set(v___x_97_, 3, v_l_188_);
lean_ctor_set(v___x_97_, 2, v_v_191_);
lean_ctor_set(v___x_97_, 1, v_k_190_);
lean_ctor_set(v___x_97_, 0, v___x_195_);
v___x_199_ = v___x_97_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_k_190_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_v_191_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v_l_188_);
lean_ctor_set(v_reuseFailAlloc_200_, 4, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
else
{
lean_object* v_r_205_; 
v_r_205_ = lean_ctor_get(v_impl_101_, 4);
lean_inc(v_r_205_);
if (lean_obj_tag(v_r_205_) == 0)
{
lean_object* v_k_206_; lean_object* v_v_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_230_; 
lean_inc(v_l_188_);
v_k_206_ = lean_ctor_get(v_impl_101_, 1);
v_v_207_ = lean_ctor_get(v_impl_101_, 2);
v_isSharedCheck_230_ = !lean_is_exclusive(v_impl_101_);
if (v_isSharedCheck_230_ == 0)
{
lean_object* v_unused_231_; lean_object* v_unused_232_; lean_object* v_unused_233_; 
v_unused_231_ = lean_ctor_get(v_impl_101_, 4);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_impl_101_, 3);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v_impl_101_, 0);
lean_dec(v_unused_233_);
v___x_209_ = v_impl_101_;
v_isShared_210_ = v_isSharedCheck_230_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_v_207_);
lean_inc(v_k_206_);
lean_dec(v_impl_101_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_230_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v_k_211_; lean_object* v_v_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_226_; 
v_k_211_ = lean_ctor_get(v_r_205_, 1);
v_v_212_ = lean_ctor_get(v_r_205_, 2);
v_isSharedCheck_226_ = !lean_is_exclusive(v_r_205_);
if (v_isSharedCheck_226_ == 0)
{
lean_object* v_unused_227_; lean_object* v_unused_228_; lean_object* v_unused_229_; 
v_unused_227_ = lean_ctor_get(v_r_205_, 4);
lean_dec(v_unused_227_);
v_unused_228_ = lean_ctor_get(v_r_205_, 3);
lean_dec(v_unused_228_);
v_unused_229_ = lean_ctor_get(v_r_205_, 0);
lean_dec(v_unused_229_);
v___x_214_ = v_r_205_;
v_isShared_215_ = v_isSharedCheck_226_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_v_212_);
lean_inc(v_k_211_);
lean_dec(v_r_205_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_226_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_216_ = lean_unsigned_to_nat(3u);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 4, v_l_188_);
lean_ctor_set(v___x_214_, 3, v_l_188_);
lean_ctor_set(v___x_214_, 2, v_v_207_);
lean_ctor_set(v___x_214_, 1, v_k_206_);
lean_ctor_set(v___x_214_, 0, v___x_102_);
v___x_218_ = v___x_214_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_k_206_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v_v_207_);
lean_ctor_set(v_reuseFailAlloc_225_, 3, v_l_188_);
lean_ctor_set(v_reuseFailAlloc_225_, 4, v_l_188_);
v___x_218_ = v_reuseFailAlloc_225_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_220_; 
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 4, v_l_188_);
lean_ctor_set(v___x_209_, 2, v_v_93_);
lean_ctor_set(v___x_209_, 1, v_k_92_);
lean_ctor_set(v___x_209_, 0, v___x_102_);
v___x_220_ = v___x_209_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_k_92_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v_v_93_);
lean_ctor_set(v_reuseFailAlloc_224_, 3, v_l_188_);
lean_ctor_set(v_reuseFailAlloc_224_, 4, v_l_188_);
v___x_220_ = v_reuseFailAlloc_224_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_222_; 
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 4, v___x_220_);
lean_ctor_set(v___x_97_, 3, v___x_218_);
lean_ctor_set(v___x_97_, 2, v_v_212_);
lean_ctor_set(v___x_97_, 1, v_k_211_);
lean_ctor_set(v___x_97_, 0, v___x_216_);
v___x_222_ = v___x_97_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_k_211_);
lean_ctor_set(v_reuseFailAlloc_223_, 2, v_v_212_);
lean_ctor_set(v_reuseFailAlloc_223_, 3, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_223_, 4, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
}
}
else
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = lean_unsigned_to_nat(2u);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 4, v_r_205_);
lean_ctor_set(v___x_97_, 3, v_impl_101_);
lean_ctor_set(v___x_97_, 0, v___x_234_);
v___x_236_ = v___x_97_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_k_92_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_v_93_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v_impl_101_);
lean_ctor_set(v_reuseFailAlloc_237_, 4, v_r_205_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
case 1:
{
lean_object* v___x_239_; 
lean_dec(v_v_93_);
lean_dec(v_k_92_);
lean_dec_ref(v_cmp_87_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 2, v_v_89_);
lean_ctor_set(v___x_97_, 1, v_k_88_);
v___x_239_ = v___x_97_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_size_91_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_k_88_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_v_89_);
lean_ctor_set(v_reuseFailAlloc_240_, 3, v_l_94_);
lean_ctor_set(v_reuseFailAlloc_240_, 4, v_r_95_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
default: 
{
lean_object* v_impl_241_; lean_object* v___x_242_; 
lean_dec(v_size_91_);
v_impl_241_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_87_, v_k_88_, v_v_89_, v_r_95_);
v___x_242_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_94_) == 0)
{
lean_object* v_size_243_; lean_object* v_size_244_; lean_object* v_k_245_; lean_object* v_v_246_; lean_object* v_l_247_; lean_object* v_r_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v_size_243_ = lean_ctor_get(v_l_94_, 0);
v_size_244_ = lean_ctor_get(v_impl_241_, 0);
v_k_245_ = lean_ctor_get(v_impl_241_, 1);
v_v_246_ = lean_ctor_get(v_impl_241_, 2);
v_l_247_ = lean_ctor_get(v_impl_241_, 3);
lean_inc(v_l_247_);
v_r_248_ = lean_ctor_get(v_impl_241_, 4);
v___x_249_ = lean_unsigned_to_nat(3u);
v___x_250_ = lean_nat_mul(v___x_249_, v_size_243_);
v___x_251_ = lean_nat_dec_lt(v___x_250_, v_size_244_);
lean_dec(v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_255_; 
lean_dec(v_l_247_);
v___x_252_ = lean_nat_add(v___x_242_, v_size_243_);
v___x_253_ = lean_nat_add(v___x_252_, v_size_244_);
lean_dec(v___x_252_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 4, v_impl_241_);
lean_ctor_set(v___x_97_, 0, v___x_253_);
v___x_255_ = v___x_97_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_k_92_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_v_93_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v_l_94_);
lean_ctor_set(v_reuseFailAlloc_256_, 4, v_impl_241_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
else
{
lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_320_; 
lean_inc(v_r_248_);
lean_inc(v_v_246_);
lean_inc(v_k_245_);
lean_inc(v_size_244_);
v_isSharedCheck_320_ = !lean_is_exclusive(v_impl_241_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; lean_object* v_unused_322_; lean_object* v_unused_323_; lean_object* v_unused_324_; lean_object* v_unused_325_; 
v_unused_321_ = lean_ctor_get(v_impl_241_, 4);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_impl_241_, 3);
lean_dec(v_unused_322_);
v_unused_323_ = lean_ctor_get(v_impl_241_, 2);
lean_dec(v_unused_323_);
v_unused_324_ = lean_ctor_get(v_impl_241_, 1);
lean_dec(v_unused_324_);
v_unused_325_ = lean_ctor_get(v_impl_241_, 0);
lean_dec(v_unused_325_);
v___x_258_ = v_impl_241_;
v_isShared_259_ = v_isSharedCheck_320_;
goto v_resetjp_257_;
}
else
{
lean_dec(v_impl_241_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_320_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v_size_260_; lean_object* v_k_261_; lean_object* v_v_262_; lean_object* v_l_263_; lean_object* v_r_264_; lean_object* v_size_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_size_260_ = lean_ctor_get(v_l_247_, 0);
v_k_261_ = lean_ctor_get(v_l_247_, 1);
v_v_262_ = lean_ctor_get(v_l_247_, 2);
v_l_263_ = lean_ctor_get(v_l_247_, 3);
v_r_264_ = lean_ctor_get(v_l_247_, 4);
v_size_265_ = lean_ctor_get(v_r_248_, 0);
v___x_266_ = lean_unsigned_to_nat(2u);
v___x_267_ = lean_nat_mul(v___x_266_, v_size_265_);
v___x_268_ = lean_nat_dec_lt(v_size_260_, v___x_267_);
lean_dec(v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_296_; 
lean_inc(v_r_264_);
lean_inc(v_l_263_);
lean_inc(v_v_262_);
lean_inc(v_k_261_);
v_isSharedCheck_296_ = !lean_is_exclusive(v_l_247_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; lean_object* v_unused_298_; lean_object* v_unused_299_; lean_object* v_unused_300_; lean_object* v_unused_301_; 
v_unused_297_ = lean_ctor_get(v_l_247_, 4);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_l_247_, 3);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_l_247_, 2);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v_l_247_, 1);
lean_dec(v_unused_300_);
v_unused_301_ = lean_ctor_get(v_l_247_, 0);
lean_dec(v_unused_301_);
v___x_270_ = v_l_247_;
v_isShared_271_ = v_isSharedCheck_296_;
goto v_resetjp_269_;
}
else
{
lean_dec(v_l_247_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_296_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_286_; 
v___x_272_ = lean_nat_add(v___x_242_, v_size_243_);
v___x_273_ = lean_nat_add(v___x_272_, v_size_244_);
lean_dec(v_size_244_);
if (lean_obj_tag(v_l_263_) == 0)
{
lean_object* v_size_294_; 
v_size_294_ = lean_ctor_get(v_l_263_, 0);
lean_inc(v_size_294_);
v___y_286_ = v_size_294_;
goto v___jp_285_;
}
else
{
lean_object* v___x_295_; 
v___x_295_ = lean_unsigned_to_nat(0u);
v___y_286_ = v___x_295_;
goto v___jp_285_;
}
v___jp_274_:
{
lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_278_ = lean_nat_add(v___y_275_, v___y_277_);
lean_dec(v___y_277_);
lean_dec(v___y_275_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 4, v_r_248_);
lean_ctor_set(v___x_270_, 3, v_r_264_);
lean_ctor_set(v___x_270_, 2, v_v_246_);
lean_ctor_set(v___x_270_, 1, v_k_245_);
lean_ctor_set(v___x_270_, 0, v___x_278_);
v___x_280_ = v___x_270_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_k_245_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v_v_246_);
lean_ctor_set(v_reuseFailAlloc_284_, 3, v_r_264_);
lean_ctor_set(v_reuseFailAlloc_284_, 4, v_r_248_);
v___x_280_ = v_reuseFailAlloc_284_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v___x_282_; 
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 4, v___x_280_);
lean_ctor_set(v___x_258_, 3, v___y_276_);
lean_ctor_set(v___x_258_, 2, v_v_262_);
lean_ctor_set(v___x_258_, 1, v_k_261_);
lean_ctor_set(v___x_258_, 0, v___x_273_);
v___x_282_ = v___x_258_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_k_261_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_v_262_);
lean_ctor_set(v_reuseFailAlloc_283_, 3, v___y_276_);
lean_ctor_set(v_reuseFailAlloc_283_, 4, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
v___jp_285_:
{
lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_287_ = lean_nat_add(v___x_272_, v___y_286_);
lean_dec(v___y_286_);
lean_dec(v___x_272_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 4, v_l_263_);
lean_ctor_set(v___x_97_, 0, v___x_287_);
v___x_289_ = v___x_97_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_k_92_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_v_93_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_l_94_);
lean_ctor_set(v_reuseFailAlloc_293_, 4, v_l_263_);
v___x_289_ = v_reuseFailAlloc_293_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; 
v___x_290_ = lean_nat_add(v___x_242_, v_size_265_);
if (lean_obj_tag(v_r_264_) == 0)
{
lean_object* v_size_291_; 
v_size_291_ = lean_ctor_get(v_r_264_, 0);
lean_inc(v_size_291_);
v___y_275_ = v___x_290_;
v___y_276_ = v___x_289_;
v___y_277_ = v_size_291_;
goto v___jp_274_;
}
else
{
lean_object* v___x_292_; 
v___x_292_ = lean_unsigned_to_nat(0u);
v___y_275_ = v___x_290_;
v___y_276_ = v___x_289_;
v___y_277_ = v___x_292_;
goto v___jp_274_;
}
}
}
}
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_306_; 
lean_del_object(v___x_97_);
v___x_302_ = lean_nat_add(v___x_242_, v_size_243_);
v___x_303_ = lean_nat_add(v___x_302_, v_size_244_);
lean_dec(v_size_244_);
v___x_304_ = lean_nat_add(v___x_302_, v_size_260_);
lean_dec(v___x_302_);
lean_inc_ref(v_l_94_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 4, v_l_247_);
lean_ctor_set(v___x_258_, 3, v_l_94_);
lean_ctor_set(v___x_258_, 2, v_v_93_);
lean_ctor_set(v___x_258_, 1, v_k_92_);
lean_ctor_set(v___x_258_, 0, v___x_304_);
v___x_306_ = v___x_258_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_k_92_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v_v_93_);
lean_ctor_set(v_reuseFailAlloc_319_, 3, v_l_94_);
lean_ctor_set(v_reuseFailAlloc_319_, 4, v_l_247_);
v___x_306_ = v_reuseFailAlloc_319_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
v_isSharedCheck_313_ = !lean_is_exclusive(v_l_94_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; lean_object* v_unused_315_; lean_object* v_unused_316_; lean_object* v_unused_317_; lean_object* v_unused_318_; 
v_unused_314_ = lean_ctor_get(v_l_94_, 4);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_l_94_, 3);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_l_94_, 2);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_l_94_, 1);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_l_94_, 0);
lean_dec(v_unused_318_);
v___x_308_ = v_l_94_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_dec(v_l_94_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 4, v_r_248_);
lean_ctor_set(v___x_308_, 3, v___x_306_);
lean_ctor_set(v___x_308_, 2, v_v_246_);
lean_ctor_set(v___x_308_, 1, v_k_245_);
lean_ctor_set(v___x_308_, 0, v___x_303_);
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_k_245_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v_v_246_);
lean_ctor_set(v_reuseFailAlloc_312_, 3, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_312_, 4, v_r_248_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_326_; 
v_l_326_ = lean_ctor_get(v_impl_241_, 3);
lean_inc(v_l_326_);
if (lean_obj_tag(v_l_326_) == 0)
{
lean_object* v_r_327_; lean_object* v_k_328_; lean_object* v_v_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_352_; 
v_r_327_ = lean_ctor_get(v_impl_241_, 4);
v_k_328_ = lean_ctor_get(v_impl_241_, 1);
v_v_329_ = lean_ctor_get(v_impl_241_, 2);
v_isSharedCheck_352_ = !lean_is_exclusive(v_impl_241_);
if (v_isSharedCheck_352_ == 0)
{
lean_object* v_unused_353_; lean_object* v_unused_354_; 
v_unused_353_ = lean_ctor_get(v_impl_241_, 3);
lean_dec(v_unused_353_);
v_unused_354_ = lean_ctor_get(v_impl_241_, 0);
lean_dec(v_unused_354_);
v___x_331_ = v_impl_241_;
v_isShared_332_ = v_isSharedCheck_352_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_r_327_);
lean_inc(v_v_329_);
lean_inc(v_k_328_);
lean_dec(v_impl_241_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_352_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v_k_333_; lean_object* v_v_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_348_; 
v_k_333_ = lean_ctor_get(v_l_326_, 1);
v_v_334_ = lean_ctor_get(v_l_326_, 2);
v_isSharedCheck_348_ = !lean_is_exclusive(v_l_326_);
if (v_isSharedCheck_348_ == 0)
{
lean_object* v_unused_349_; lean_object* v_unused_350_; lean_object* v_unused_351_; 
v_unused_349_ = lean_ctor_get(v_l_326_, 4);
lean_dec(v_unused_349_);
v_unused_350_ = lean_ctor_get(v_l_326_, 3);
lean_dec(v_unused_350_);
v_unused_351_ = lean_ctor_get(v_l_326_, 0);
lean_dec(v_unused_351_);
v___x_336_ = v_l_326_;
v_isShared_337_ = v_isSharedCheck_348_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_v_334_);
lean_inc(v_k_333_);
lean_dec(v_l_326_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_348_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_338_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_327_, 2);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 4, v_r_327_);
lean_ctor_set(v___x_336_, 3, v_r_327_);
lean_ctor_set(v___x_336_, 2, v_v_93_);
lean_ctor_set(v___x_336_, 1, v_k_92_);
lean_ctor_set(v___x_336_, 0, v___x_242_);
v___x_340_ = v___x_336_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_k_92_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_v_93_);
lean_ctor_set(v_reuseFailAlloc_347_, 3, v_r_327_);
lean_ctor_set(v_reuseFailAlloc_347_, 4, v_r_327_);
v___x_340_ = v_reuseFailAlloc_347_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_342_; 
lean_inc(v_r_327_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 3, v_r_327_);
lean_ctor_set(v___x_331_, 0, v___x_242_);
v___x_342_ = v___x_331_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_k_328_);
lean_ctor_set(v_reuseFailAlloc_346_, 2, v_v_329_);
lean_ctor_set(v_reuseFailAlloc_346_, 3, v_r_327_);
lean_ctor_set(v_reuseFailAlloc_346_, 4, v_r_327_);
v___x_342_ = v_reuseFailAlloc_346_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_344_; 
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 4, v___x_342_);
lean_ctor_set(v___x_97_, 3, v___x_340_);
lean_ctor_set(v___x_97_, 2, v_v_334_);
lean_ctor_set(v___x_97_, 1, v_k_333_);
lean_ctor_set(v___x_97_, 0, v___x_338_);
v___x_344_ = v___x_97_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_k_333_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v_v_334_);
lean_ctor_set(v_reuseFailAlloc_345_, 3, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_345_, 4, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
}
else
{
lean_object* v_r_355_; 
v_r_355_ = lean_ctor_get(v_impl_241_, 4);
lean_inc(v_r_355_);
if (lean_obj_tag(v_r_355_) == 0)
{
lean_object* v_k_356_; lean_object* v_v_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_368_; 
v_k_356_ = lean_ctor_get(v_impl_241_, 1);
v_v_357_ = lean_ctor_get(v_impl_241_, 2);
v_isSharedCheck_368_ = !lean_is_exclusive(v_impl_241_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; lean_object* v_unused_370_; lean_object* v_unused_371_; 
v_unused_369_ = lean_ctor_get(v_impl_241_, 4);
lean_dec(v_unused_369_);
v_unused_370_ = lean_ctor_get(v_impl_241_, 3);
lean_dec(v_unused_370_);
v_unused_371_ = lean_ctor_get(v_impl_241_, 0);
lean_dec(v_unused_371_);
v___x_359_ = v_impl_241_;
v_isShared_360_ = v_isSharedCheck_368_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_v_357_);
lean_inc(v_k_356_);
lean_dec(v_impl_241_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_368_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_361_ = lean_unsigned_to_nat(3u);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 4, v_l_326_);
lean_ctor_set(v___x_359_, 2, v_v_93_);
lean_ctor_set(v___x_359_, 1, v_k_92_);
lean_ctor_set(v___x_359_, 0, v___x_242_);
v___x_363_ = v___x_359_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_k_92_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v_v_93_);
lean_ctor_set(v_reuseFailAlloc_367_, 3, v_l_326_);
lean_ctor_set(v_reuseFailAlloc_367_, 4, v_l_326_);
v___x_363_ = v_reuseFailAlloc_367_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_365_; 
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 4, v_r_355_);
lean_ctor_set(v___x_97_, 3, v___x_363_);
lean_ctor_set(v___x_97_, 2, v_v_357_);
lean_ctor_set(v___x_97_, 1, v_k_356_);
lean_ctor_set(v___x_97_, 0, v___x_361_);
v___x_365_ = v___x_97_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_k_356_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v_v_357_);
lean_ctor_set(v_reuseFailAlloc_366_, 3, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_366_, 4, v_r_355_);
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
else
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = lean_unsigned_to_nat(2u);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 4, v_impl_241_);
lean_ctor_set(v___x_97_, 3, v_r_355_);
lean_ctor_set(v___x_97_, 0, v___x_372_);
v___x_374_ = v___x_97_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_k_92_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_v_93_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v_r_355_);
lean_ctor_set(v_reuseFailAlloc_375_, 4, v_impl_241_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
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
lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec_ref(v_cmp_87_);
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v_k_88_);
lean_ctor_set(v___x_378_, 2, v_v_89_);
lean_ctor_set(v___x_378_, 3, v_t_90_);
lean_ctor_set(v___x_378_, 4, v_t_90_);
return v___x_378_;
}
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(lean_object* v_cmp_379_, lean_object* v_k_380_, lean_object* v_t_381_){
_start:
{
if (lean_obj_tag(v_t_381_) == 0)
{
lean_object* v_k_382_; lean_object* v_l_383_; lean_object* v_r_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v_k_382_ = lean_ctor_get(v_t_381_, 1);
lean_inc(v_k_382_);
v_l_383_ = lean_ctor_get(v_t_381_, 3);
lean_inc(v_l_383_);
v_r_384_ = lean_ctor_get(v_t_381_, 4);
lean_inc(v_r_384_);
lean_dec_ref_known(v_t_381_, 5);
lean_inc_ref(v_cmp_379_);
lean_inc(v_k_380_);
v___x_385_ = lean_apply_2(v_cmp_379_, v_k_380_, v_k_382_);
v___x_386_ = lean_unbox(v___x_385_);
switch(v___x_386_)
{
case 0:
{
lean_dec(v_r_384_);
v_t_381_ = v_l_383_;
goto _start;
}
case 1:
{
uint8_t v___x_388_; 
lean_dec(v_r_384_);
lean_dec(v_l_383_);
lean_dec(v_k_380_);
lean_dec_ref(v_cmp_379_);
v___x_388_ = 1;
return v___x_388_;
}
default: 
{
lean_dec(v_l_383_);
v_t_381_ = v_r_384_;
goto _start;
}
}
}
else
{
uint8_t v___x_390_; 
lean_dec(v_k_380_);
lean_dec_ref(v_cmp_379_);
v___x_390_ = 0;
return v___x_390_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_379_ = stack[0].m_obj;
lean_object* v_k_380_ = stack[1].m_obj;
lean_object* v_t_381_ = stack[2].m_obj;
uint8_t v_res_391_;
v_res_391_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(v_cmp_379_, v_k_380_, v_t_381_);
stack->m_num = v_res_391_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg___boxed(lean_object* v_cmp_392_, lean_object* v_k_393_, lean_object* v_t_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(v_cmp_392_, v_k_393_, v_t_394_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_insert___redArg(lean_object* v_cmp_397_, lean_object* v_self_398_, lean_object* v_a_399_, lean_object* v_b_400_){
_start:
{
lean_object* v_toTreeMap_401_; lean_object* v_toArray_402_; uint8_t v___x_403_; 
v_toTreeMap_401_ = lean_ctor_get(v_self_398_, 0);
v_toArray_402_ = lean_ctor_get(v_self_398_, 1);
lean_inc(v_toTreeMap_401_);
lean_inc(v_a_399_);
lean_inc_ref(v_cmp_397_);
v___x_403_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(v_cmp_397_, v_a_399_, v_toTreeMap_401_);
if (v___x_403_ == 0)
{
lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_412_; 
lean_inc_ref(v_toArray_402_);
lean_inc(v_toTreeMap_401_);
v_isSharedCheck_412_ = !lean_is_exclusive(v_self_398_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; lean_object* v_unused_414_; 
v_unused_413_ = lean_ctor_get(v_self_398_, 1);
lean_dec(v_unused_413_);
v_unused_414_ = lean_ctor_get(v_self_398_, 0);
lean_dec(v_unused_414_);
v___x_405_ = v_self_398_;
v_isShared_406_ = v_isSharedCheck_412_;
goto v_resetjp_404_;
}
else
{
lean_dec(v_self_398_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_412_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_410_; 
lean_inc(v_b_400_);
v___x_407_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_397_, v_a_399_, v_b_400_, v_toTreeMap_401_);
v___x_408_ = lean_array_push(v_toArray_402_, v_b_400_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 1, v___x_408_);
lean_ctor_set(v___x_405_, 0, v___x_407_);
v___x_410_ = v___x_405_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
else
{
lean_dec(v_b_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_cmp_397_);
return v_self_398_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_insert(lean_object* v_00_u03b1_415_, lean_object* v_00_u03b2_416_, lean_object* v_cmp_417_, lean_object* v_self_418_, lean_object* v_a_419_, lean_object* v_b_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lake_RBArray_insert___redArg(v_cmp_417_, v_self_418_, v_a_419_, v_b_420_);
return v___x_421_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0(lean_object* v_00_u03b1_422_, lean_object* v_cmp_423_, lean_object* v_00_u03b2_424_, lean_object* v_k_425_, lean_object* v_t_426_){
_start:
{
uint8_t v___x_427_; 
v___x_427_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___redArg(v_cmp_423_, v_k_425_, v_t_426_);
return v___x_427_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_423_ = stack[1].m_obj;
lean_object* v_k_425_ = stack[3].m_obj;
lean_object* v_t_426_ = stack[4].m_obj;
uint8_t v_res_428_;
v_res_428_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0(lean_box(0), v_cmp_423_, lean_box(0), v_k_425_, v_t_426_);
stack->m_num = v_res_428_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0___boxed(lean_object* v_00_u03b1_429_, lean_object* v_cmp_430_, lean_object* v_00_u03b2_431_, lean_object* v_k_432_, lean_object* v_t_433_){
_start:
{
uint8_t v_res_434_; lean_object* v_r_435_; 
v_res_434_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_RBArray_insert_spec__0(v_00_u03b1_429_, v_cmp_430_, v_00_u03b2_431_, v_k_432_, v_t_433_);
v_r_435_ = lean_box(v_res_434_);
return v_r_435_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1(lean_object* v_00_u03b1_436_, lean_object* v_cmp_437_, lean_object* v_00_u03b2_438_, lean_object* v_k_439_, lean_object* v_v_440_, lean_object* v_t_441_, lean_object* v_hl_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_RBArray_insert_spec__1___redArg(v_cmp_437_, v_k_439_, v_v_440_, v_t_441_);
return v___x_443_;
}
}
uint8_t l_Lake_RBArray_all___redArg___lam__0(lean_object* v_f_444_, uint8_t v___x_445_, lean_object* v_v_446_){
_start:
{
lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_447_ = lean_apply_1(v_f_444_, v_v_446_);
v___x_448_ = lean_unbox(v___x_447_);
if (v___x_448_ == 0)
{
return v___x_445_;
}
else
{
uint8_t v___x_449_; 
v___x_449_ = 0;
return v___x_449_;
}
}
}
LEAN_EXPORT void l_Lake_RBArray_all___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_444_ = stack[0].m_obj;
uint8_t v___x_445_ = stack[1].m_num;
lean_object* v_v_446_ = stack[2].m_obj;
uint8_t v_res_450_;
v_res_450_ = l_Lake_RBArray_all___redArg___lam__0(v_f_444_, v___x_445_, v_v_446_);
stack->m_num = v_res_450_;
}
LEAN_EXPORT lean_object* l_Lake_RBArray_all___redArg___lam__0___boxed(lean_object* v_f_451_, lean_object* v___x_452_, lean_object* v_v_453_){
_start:
{
uint8_t v___x_75__boxed_454_; uint8_t v_res_455_; lean_object* v_r_456_; 
v___x_75__boxed_454_ = lean_unbox(v___x_452_);
v_res_455_ = l_Lake_RBArray_all___redArg___lam__0(v_f_451_, v___x_75__boxed_454_, v_v_453_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
uint8_t l_Lake_RBArray_all___redArg(lean_object* v_f_476_, lean_object* v_self_477_){
_start:
{
lean_object* v_toArray_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_toArray_478_ = lean_ctor_get(v_self_477_, 1);
lean_inc_ref(v_toArray_478_);
lean_dec_ref(v_self_477_);
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = lean_array_get_size(v_toArray_478_);
v___x_481_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_482_ = lean_nat_dec_lt(v___x_479_, v___x_480_);
if (v___x_482_ == 0)
{
uint8_t v___x_483_; 
lean_dec_ref(v_toArray_478_);
lean_dec_ref(v_f_476_);
v___x_483_ = 1;
return v___x_483_;
}
else
{
if (v___x_482_ == 0)
{
lean_dec_ref(v_toArray_478_);
lean_dec_ref(v_f_476_);
return v___x_482_;
}
else
{
lean_object* v___x_484_; lean_object* v___f_485_; size_t v___x_486_; size_t v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_484_ = lean_box(v___x_482_);
v___f_485_ = lean_alloc_closure((void*)(l_Lake_RBArray_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_485_, 0, v_f_476_);
lean_closure_set(v___f_485_, 1, v___x_484_);
v___x_486_ = ((size_t)0ULL);
v___x_487_ = lean_usize_of_nat(v___x_480_);
v___x_488_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_481_, v___f_485_, v_toArray_478_, v___x_486_, v___x_487_);
v___x_489_ = lean_unbox(v___x_488_);
lean_dec(v___x_488_);
if (v___x_489_ == 0)
{
return v___x_482_;
}
else
{
uint8_t v___x_490_; 
v___x_490_ = 0;
return v___x_490_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_RBArray_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_476_ = stack[0].m_obj;
lean_object* v_self_477_ = stack[1].m_obj;
uint8_t v_res_491_;
v_res_491_ = l_Lake_RBArray_all___redArg(v_f_476_, v_self_477_);
stack->m_num = v_res_491_;
}
LEAN_EXPORT lean_object* l_Lake_RBArray_all___redArg___boxed(lean_object* v_f_492_, lean_object* v_self_493_){
_start:
{
uint8_t v_res_494_; lean_object* v_r_495_; 
v_res_494_ = l_Lake_RBArray_all___redArg(v_f_492_, v_self_493_);
v_r_495_ = lean_box(v_res_494_);
return v_r_495_;
}
}
uint8_t l_Lake_RBArray_all(lean_object* v_00_u03b2_496_, lean_object* v_00_u03b1_497_, lean_object* v_cmp_498_, lean_object* v_f_499_, lean_object* v_self_500_){
_start:
{
lean_object* v_toArray_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v_toArray_501_ = lean_ctor_get(v_self_500_, 1);
lean_inc_ref(v_toArray_501_);
lean_dec_ref(v_self_500_);
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = lean_array_get_size(v_toArray_501_);
v___x_504_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_505_ = lean_nat_dec_lt(v___x_502_, v___x_503_);
if (v___x_505_ == 0)
{
uint8_t v___x_506_; 
lean_dec_ref(v_toArray_501_);
lean_dec_ref(v_f_499_);
v___x_506_ = 1;
return v___x_506_;
}
else
{
if (v___x_505_ == 0)
{
lean_dec_ref(v_toArray_501_);
lean_dec_ref(v_f_499_);
return v___x_505_;
}
else
{
lean_object* v___x_507_; lean_object* v___f_508_; size_t v___x_509_; size_t v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_507_ = lean_box(v___x_505_);
v___f_508_ = lean_alloc_closure((void*)(l_Lake_RBArray_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_508_, 0, v_f_499_);
lean_closure_set(v___f_508_, 1, v___x_507_);
v___x_509_ = ((size_t)0ULL);
v___x_510_ = lean_usize_of_nat(v___x_503_);
v___x_511_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_504_, v___f_508_, v_toArray_501_, v___x_509_, v___x_510_);
v___x_512_ = lean_unbox(v___x_511_);
lean_dec(v___x_511_);
if (v___x_512_ == 0)
{
return v___x_505_;
}
else
{
uint8_t v___x_513_; 
v___x_513_ = 0;
return v___x_513_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_RBArray_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_498_ = stack[2].m_obj;
lean_object* v_f_499_ = stack[3].m_obj;
lean_object* v_self_500_ = stack[4].m_obj;
uint8_t v_res_514_;
v_res_514_ = l_Lake_RBArray_all(lean_box(0), lean_box(0), v_cmp_498_, v_f_499_, v_self_500_);
stack->m_num = v_res_514_;
}
LEAN_EXPORT lean_object* l_Lake_RBArray_all___boxed(lean_object* v_00_u03b2_515_, lean_object* v_00_u03b1_516_, lean_object* v_cmp_517_, lean_object* v_f_518_, lean_object* v_self_519_){
_start:
{
uint8_t v_res_520_; lean_object* v_r_521_; 
v_res_520_ = l_Lake_RBArray_all(v_00_u03b2_515_, v_00_u03b1_516_, v_cmp_517_, v_f_518_, v_self_519_);
lean_dec_ref(v_cmp_517_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
uint8_t l_Lake_RBArray_any___redArg___lam__0(lean_object* v_f_522_, lean_object* v_x_523_){
_start:
{
lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_524_ = lean_apply_1(v_f_522_, v_x_523_);
v___x_525_ = lean_unbox(v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT void l_Lake_RBArray_any___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_522_ = stack[0].m_obj;
lean_object* v_x_523_ = stack[1].m_obj;
uint8_t v_res_526_;
v_res_526_ = l_Lake_RBArray_any___redArg___lam__0(v_f_522_, v_x_523_);
stack->m_num = v_res_526_;
}
LEAN_EXPORT lean_object* l_Lake_RBArray_any___redArg___lam__0___boxed(lean_object* v_f_527_, lean_object* v_x_528_){
_start:
{
uint8_t v_res_529_; lean_object* v_r_530_; 
v_res_529_ = l_Lake_RBArray_any___redArg___lam__0(v_f_527_, v_x_528_);
v_r_530_ = lean_box(v_res_529_);
return v_r_530_;
}
}
uint8_t l_Lake_RBArray_any___redArg(lean_object* v_f_531_, lean_object* v_self_532_){
_start:
{
lean_object* v_toArray_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v_toArray_533_ = lean_ctor_get(v_self_532_, 1);
lean_inc_ref(v_toArray_533_);
lean_dec_ref(v_self_532_);
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = lean_array_get_size(v_toArray_533_);
v___x_536_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_537_ = lean_nat_dec_lt(v___x_534_, v___x_535_);
if (v___x_537_ == 0)
{
lean_dec_ref(v_toArray_533_);
lean_dec_ref(v_f_531_);
return v___x_537_;
}
else
{
if (v___x_537_ == 0)
{
lean_dec_ref(v_toArray_533_);
lean_dec_ref(v_f_531_);
return v___x_537_;
}
else
{
lean_object* v___f_538_; size_t v___x_539_; size_t v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___f_538_ = lean_alloc_closure((void*)(l_Lake_RBArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_538_, 0, v_f_531_);
v___x_539_ = ((size_t)0ULL);
v___x_540_ = lean_usize_of_nat(v___x_535_);
v___x_541_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_536_, v___f_538_, v_toArray_533_, v___x_539_, v___x_540_);
v___x_542_ = lean_unbox(v___x_541_);
lean_dec(v___x_541_);
return v___x_542_;
}
}
}
}
LEAN_EXPORT void l_Lake_RBArray_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_531_ = stack[0].m_obj;
lean_object* v_self_532_ = stack[1].m_obj;
uint8_t v_res_543_;
v_res_543_ = l_Lake_RBArray_any___redArg(v_f_531_, v_self_532_);
stack->m_num = v_res_543_;
}
LEAN_EXPORT lean_object* l_Lake_RBArray_any___redArg___boxed(lean_object* v_f_544_, lean_object* v_self_545_){
_start:
{
uint8_t v_res_546_; lean_object* v_r_547_; 
v_res_546_ = l_Lake_RBArray_any___redArg(v_f_544_, v_self_545_);
v_r_547_ = lean_box(v_res_546_);
return v_r_547_;
}
}
uint8_t l_Lake_RBArray_any(lean_object* v_00_u03b2_548_, lean_object* v_00_u03b1_549_, lean_object* v_cmp_550_, lean_object* v_f_551_, lean_object* v_self_552_){
_start:
{
lean_object* v_toArray_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v_toArray_553_ = lean_ctor_get(v_self_552_, 1);
lean_inc_ref(v_toArray_553_);
lean_dec_ref(v_self_552_);
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = lean_array_get_size(v_toArray_553_);
v___x_556_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_557_ = lean_nat_dec_lt(v___x_554_, v___x_555_);
if (v___x_557_ == 0)
{
lean_dec_ref(v_toArray_553_);
lean_dec_ref(v_f_551_);
return v___x_557_;
}
else
{
if (v___x_557_ == 0)
{
lean_dec_ref(v_toArray_553_);
lean_dec_ref(v_f_551_);
return v___x_557_;
}
else
{
lean_object* v___f_558_; size_t v___x_559_; size_t v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___f_558_ = lean_alloc_closure((void*)(l_Lake_RBArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_558_, 0, v_f_551_);
v___x_559_ = ((size_t)0ULL);
v___x_560_ = lean_usize_of_nat(v___x_555_);
v___x_561_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_556_, v___f_558_, v_toArray_553_, v___x_559_, v___x_560_);
v___x_562_ = lean_unbox(v___x_561_);
lean_dec(v___x_561_);
return v___x_562_;
}
}
}
}
LEAN_EXPORT void l_Lake_RBArray_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_550_ = stack[2].m_obj;
lean_object* v_f_551_ = stack[3].m_obj;
lean_object* v_self_552_ = stack[4].m_obj;
uint8_t v_res_563_;
v_res_563_ = l_Lake_RBArray_any(lean_box(0), lean_box(0), v_cmp_550_, v_f_551_, v_self_552_);
stack->m_num = v_res_563_;
}
LEAN_EXPORT lean_object* l_Lake_RBArray_any___boxed(lean_object* v_00_u03b2_564_, lean_object* v_00_u03b1_565_, lean_object* v_cmp_566_, lean_object* v_f_567_, lean_object* v_self_568_){
_start:
{
uint8_t v_res_569_; lean_object* v_r_570_; 
v_res_569_ = l_Lake_RBArray_any(v_00_u03b2_564_, v_00_u03b1_565_, v_cmp_566_, v_f_567_, v_self_568_);
lean_dec_ref(v_cmp_566_);
v_r_570_ = lean_box(v_res_569_);
return v_r_570_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl___redArg___lam__0(lean_object* v_f_571_, lean_object* v_x1_572_, lean_object* v_x2_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = lean_apply_2(v_f_571_, v_x1_572_, v_x2_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl___redArg(lean_object* v_f_575_, lean_object* v_init_576_, lean_object* v_self_577_){
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
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl(lean_object* v_00_u03c3_591_, lean_object* v_00_u03b2_592_, lean_object* v_00_u03b1_593_, lean_object* v_cmp_594_, lean_object* v_f_595_, lean_object* v_init_596_, lean_object* v_self_597_){
_start:
{
lean_object* v_toArray_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_toArray_598_ = lean_ctor_get(v_self_597_, 1);
lean_inc_ref(v_toArray_598_);
lean_dec_ref(v_self_597_);
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_array_get_size(v_toArray_598_);
v___x_601_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_602_ = lean_nat_dec_lt(v___x_599_, v___x_600_);
if (v___x_602_ == 0)
{
lean_dec_ref(v_toArray_598_);
lean_dec(v_f_595_);
return v_init_596_;
}
else
{
lean_object* v___f_603_; uint8_t v___x_604_; 
v___f_603_ = lean_alloc_closure((void*)(l_Lake_RBArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_603_, 0, v_f_595_);
v___x_604_ = lean_nat_dec_le(v___x_600_, v___x_600_);
if (v___x_604_ == 0)
{
if (v___x_602_ == 0)
{
lean_dec_ref(v___f_603_);
lean_dec_ref(v_toArray_598_);
return v_init_596_;
}
else
{
size_t v___x_605_; size_t v___x_606_; lean_object* v___x_607_; 
v___x_605_ = ((size_t)0ULL);
v___x_606_ = lean_usize_of_nat(v___x_600_);
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_601_, v___f_603_, v_toArray_598_, v___x_605_, v___x_606_, v_init_596_);
return v___x_607_;
}
}
else
{
size_t v___x_608_; size_t v___x_609_; lean_object* v___x_610_; 
v___x_608_ = ((size_t)0ULL);
v___x_609_ = lean_usize_of_nat(v___x_600_);
v___x_610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_601_, v___f_603_, v_toArray_598_, v___x_608_, v___x_609_, v_init_596_);
return v___x_610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldl___boxed(lean_object* v_00_u03c3_611_, lean_object* v_00_u03b2_612_, lean_object* v_00_u03b1_613_, lean_object* v_cmp_614_, lean_object* v_f_615_, lean_object* v_init_616_, lean_object* v_self_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lake_RBArray_foldl(v_00_u03c3_611_, v_00_u03b2_612_, v_00_u03b1_613_, v_cmp_614_, v_f_615_, v_init_616_, v_self_617_);
lean_dec_ref(v_cmp_614_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldlM___redArg(lean_object* v_inst_619_, lean_object* v_f_620_, lean_object* v_init_621_, lean_object* v_self_622_){
_start:
{
lean_object* v_toApplicative_623_; lean_object* v_toArray_624_; lean_object* v_toPure_625_; lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v_toApplicative_623_ = lean_ctor_get(v_inst_619_, 0);
v_toArray_624_ = lean_ctor_get(v_self_622_, 1);
lean_inc_ref(v_toArray_624_);
lean_dec_ref(v_self_622_);
v_toPure_625_ = lean_ctor_get(v_toApplicative_623_, 1);
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = lean_array_get_size(v_toArray_624_);
v___x_628_ = lean_nat_dec_lt(v___x_626_, v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; 
lean_inc(v_toPure_625_);
lean_dec_ref(v_toArray_624_);
lean_dec(v_f_620_);
lean_dec_ref(v_inst_619_);
v___x_629_ = lean_apply_2(v_toPure_625_, lean_box(0), v_init_621_);
return v___x_629_;
}
else
{
uint8_t v___x_630_; 
v___x_630_ = lean_nat_dec_le(v___x_627_, v___x_627_);
if (v___x_630_ == 0)
{
if (v___x_628_ == 0)
{
lean_object* v___x_631_; 
lean_inc(v_toPure_625_);
lean_dec_ref(v_toArray_624_);
lean_dec(v_f_620_);
lean_dec_ref(v_inst_619_);
v___x_631_ = lean_apply_2(v_toPure_625_, lean_box(0), v_init_621_);
return v___x_631_;
}
else
{
size_t v___x_632_; size_t v___x_633_; lean_object* v___x_634_; 
v___x_632_ = ((size_t)0ULL);
v___x_633_ = lean_usize_of_nat(v___x_627_);
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_619_, v_f_620_, v_toArray_624_, v___x_632_, v___x_633_, v_init_621_);
return v___x_634_;
}
}
else
{
size_t v___x_635_; size_t v___x_636_; lean_object* v___x_637_; 
v___x_635_ = ((size_t)0ULL);
v___x_636_ = lean_usize_of_nat(v___x_627_);
v___x_637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_619_, v_f_620_, v_toArray_624_, v___x_635_, v___x_636_, v_init_621_);
return v___x_637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldlM(lean_object* v_m_638_, lean_object* v_00_u03c3_639_, lean_object* v_00_u03b2_640_, lean_object* v_00_u03b1_641_, lean_object* v_cmp_642_, lean_object* v_inst_643_, lean_object* v_f_644_, lean_object* v_init_645_, lean_object* v_self_646_){
_start:
{
lean_object* v_toApplicative_647_; lean_object* v_toArray_648_; lean_object* v_toPure_649_; lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v_toApplicative_647_ = lean_ctor_get(v_inst_643_, 0);
v_toArray_648_ = lean_ctor_get(v_self_646_, 1);
lean_inc_ref(v_toArray_648_);
lean_dec_ref(v_self_646_);
v_toPure_649_ = lean_ctor_get(v_toApplicative_647_, 1);
v___x_650_ = lean_unsigned_to_nat(0u);
v___x_651_ = lean_array_get_size(v_toArray_648_);
v___x_652_ = lean_nat_dec_lt(v___x_650_, v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
lean_inc(v_toPure_649_);
lean_dec_ref(v_toArray_648_);
lean_dec(v_f_644_);
lean_dec_ref(v_inst_643_);
v___x_653_ = lean_apply_2(v_toPure_649_, lean_box(0), v_init_645_);
return v___x_653_;
}
else
{
uint8_t v___x_654_; 
v___x_654_ = lean_nat_dec_le(v___x_651_, v___x_651_);
if (v___x_654_ == 0)
{
if (v___x_652_ == 0)
{
lean_object* v___x_655_; 
lean_inc(v_toPure_649_);
lean_dec_ref(v_toArray_648_);
lean_dec(v_f_644_);
lean_dec_ref(v_inst_643_);
v___x_655_ = lean_apply_2(v_toPure_649_, lean_box(0), v_init_645_);
return v___x_655_;
}
else
{
size_t v___x_656_; size_t v___x_657_; lean_object* v___x_658_; 
v___x_656_ = ((size_t)0ULL);
v___x_657_ = lean_usize_of_nat(v___x_651_);
v___x_658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_643_, v_f_644_, v_toArray_648_, v___x_656_, v___x_657_, v_init_645_);
return v___x_658_;
}
}
else
{
size_t v___x_659_; size_t v___x_660_; lean_object* v___x_661_; 
v___x_659_ = ((size_t)0ULL);
v___x_660_ = lean_usize_of_nat(v___x_651_);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_643_, v_f_644_, v_toArray_648_, v___x_659_, v___x_660_, v_init_645_);
return v___x_661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldlM___boxed(lean_object* v_m_662_, lean_object* v_00_u03c3_663_, lean_object* v_00_u03b2_664_, lean_object* v_00_u03b1_665_, lean_object* v_cmp_666_, lean_object* v_inst_667_, lean_object* v_f_668_, lean_object* v_init_669_, lean_object* v_self_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lake_RBArray_foldlM(v_m_662_, v_00_u03c3_663_, v_00_u03b2_664_, v_00_u03b1_665_, v_cmp_666_, v_inst_667_, v_f_668_, v_init_669_, v_self_670_);
lean_dec_ref(v_cmp_666_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldr___redArg(lean_object* v_f_672_, lean_object* v_init_673_, lean_object* v_self_674_){
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
LEAN_EXPORT lean_object* l_Lake_RBArray_foldr(lean_object* v_00_u03b2_684_, lean_object* v_00_u03c3_685_, lean_object* v_00_u03b1_686_, lean_object* v_cmp_687_, lean_object* v_f_688_, lean_object* v_init_689_, lean_object* v_self_690_){
_start:
{
lean_object* v_toArray_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v_toArray_691_ = lean_ctor_get(v_self_690_, 1);
lean_inc_ref(v_toArray_691_);
lean_dec_ref(v_self_690_);
v___x_692_ = lean_array_get_size(v_toArray_691_);
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_695_ = lean_nat_dec_lt(v___x_693_, v___x_692_);
if (v___x_695_ == 0)
{
lean_dec_ref(v_toArray_691_);
lean_dec(v_f_688_);
return v_init_689_;
}
else
{
lean_object* v___f_696_; size_t v___x_697_; size_t v___x_698_; lean_object* v___x_699_; 
v___f_696_ = lean_alloc_closure((void*)(l_Lake_RBArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_696_, 0, v_f_688_);
v___x_697_ = lean_usize_of_nat(v___x_692_);
v___x_698_ = ((size_t)0ULL);
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_694_, v___f_696_, v_toArray_691_, v___x_697_, v___x_698_, v_init_689_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldr___boxed(lean_object* v_00_u03b2_700_, lean_object* v_00_u03c3_701_, lean_object* v_00_u03b1_702_, lean_object* v_cmp_703_, lean_object* v_f_704_, lean_object* v_init_705_, lean_object* v_self_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lake_RBArray_foldr(v_00_u03b2_700_, v_00_u03c3_701_, v_00_u03b1_702_, v_cmp_703_, v_f_704_, v_init_705_, v_self_706_);
lean_dec_ref(v_cmp_703_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldrM___redArg(lean_object* v_inst_708_, lean_object* v_f_709_, lean_object* v_init_710_, lean_object* v_self_711_){
_start:
{
lean_object* v_toApplicative_712_; lean_object* v_toArray_713_; lean_object* v_toPure_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v_toApplicative_712_ = lean_ctor_get(v_inst_708_, 0);
v_toArray_713_ = lean_ctor_get(v_self_711_, 1);
lean_inc_ref(v_toArray_713_);
lean_dec_ref(v_self_711_);
v_toPure_714_ = lean_ctor_get(v_toApplicative_712_, 1);
v___x_715_ = lean_array_get_size(v_toArray_713_);
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = lean_nat_dec_lt(v___x_716_, v___x_715_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
lean_inc(v_toPure_714_);
lean_dec_ref(v_toArray_713_);
lean_dec(v_f_709_);
lean_dec_ref(v_inst_708_);
v___x_718_ = lean_apply_2(v_toPure_714_, lean_box(0), v_init_710_);
return v___x_718_;
}
else
{
size_t v___x_719_; size_t v___x_720_; lean_object* v___x_721_; 
v___x_719_ = lean_usize_of_nat(v___x_715_);
v___x_720_ = ((size_t)0ULL);
v___x_721_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_708_, v_f_709_, v_toArray_713_, v___x_719_, v___x_720_, v_init_710_);
return v___x_721_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldrM(lean_object* v_m_722_, lean_object* v_00_u03b2_723_, lean_object* v_00_u03c3_724_, lean_object* v_00_u03b1_725_, lean_object* v_cmp_726_, lean_object* v_inst_727_, lean_object* v_f_728_, lean_object* v_init_729_, lean_object* v_self_730_){
_start:
{
lean_object* v_toApplicative_731_; lean_object* v_toArray_732_; lean_object* v_toPure_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v_toApplicative_731_ = lean_ctor_get(v_inst_727_, 0);
v_toArray_732_ = lean_ctor_get(v_self_730_, 1);
lean_inc_ref(v_toArray_732_);
lean_dec_ref(v_self_730_);
v_toPure_733_ = lean_ctor_get(v_toApplicative_731_, 1);
v___x_734_ = lean_array_get_size(v_toArray_732_);
v___x_735_ = lean_unsigned_to_nat(0u);
v___x_736_ = lean_nat_dec_lt(v___x_735_, v___x_734_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
lean_inc(v_toPure_733_);
lean_dec_ref(v_toArray_732_);
lean_dec(v_f_728_);
lean_dec_ref(v_inst_727_);
v___x_737_ = lean_apply_2(v_toPure_733_, lean_box(0), v_init_729_);
return v___x_737_;
}
else
{
size_t v___x_738_; size_t v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_usize_of_nat(v___x_734_);
v___x_739_ = ((size_t)0ULL);
v___x_740_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_727_, v_f_728_, v_toArray_732_, v___x_738_, v___x_739_, v_init_729_);
return v___x_740_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_foldrM___boxed(lean_object* v_m_741_, lean_object* v_00_u03b2_742_, lean_object* v_00_u03c3_743_, lean_object* v_00_u03b1_744_, lean_object* v_cmp_745_, lean_object* v_inst_746_, lean_object* v_f_747_, lean_object* v_init_748_, lean_object* v_self_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lake_RBArray_foldrM(v_m_741_, v_00_u03b2_742_, v_00_u03c3_743_, v_00_u03b1_744_, v_cmp_745_, v_inst_746_, v_f_747_, v_init_748_, v_self_749_);
lean_dec_ref(v_cmp_745_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM___redArg___lam__0(lean_object* v_f_751_, lean_object* v_x_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = lean_apply_1(v_f_751_, v___y_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM___redArg(lean_object* v_inst_755_, lean_object* v_f_756_, lean_object* v_self_757_){
_start:
{
lean_object* v_toApplicative_758_; lean_object* v_toArray_759_; lean_object* v_toPure_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v_toApplicative_758_ = lean_ctor_get(v_inst_755_, 0);
v_toArray_759_ = lean_ctor_get(v_self_757_, 1);
lean_inc_ref(v_toArray_759_);
lean_dec_ref(v_self_757_);
v_toPure_760_ = lean_ctor_get(v_toApplicative_758_, 1);
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = lean_array_get_size(v_toArray_759_);
v___x_763_ = lean_box(0);
v___x_764_ = lean_nat_dec_lt(v___x_761_, v___x_762_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; 
lean_inc(v_toPure_760_);
lean_dec_ref(v_toArray_759_);
lean_dec(v_f_756_);
lean_dec_ref(v_inst_755_);
v___x_765_ = lean_apply_2(v_toPure_760_, lean_box(0), v___x_763_);
return v___x_765_;
}
else
{
lean_object* v___f_766_; uint8_t v___x_767_; 
v___f_766_ = lean_alloc_closure((void*)(l_Lake_RBArray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_766_, 0, v_f_756_);
v___x_767_ = lean_nat_dec_le(v___x_762_, v___x_762_);
if (v___x_767_ == 0)
{
if (v___x_764_ == 0)
{
lean_object* v___x_768_; 
lean_inc(v_toPure_760_);
lean_dec_ref(v___f_766_);
lean_dec_ref(v_toArray_759_);
lean_dec_ref(v_inst_755_);
v___x_768_ = lean_apply_2(v_toPure_760_, lean_box(0), v___x_763_);
return v___x_768_;
}
else
{
size_t v___x_769_; size_t v___x_770_; lean_object* v___x_771_; 
v___x_769_ = ((size_t)0ULL);
v___x_770_ = lean_usize_of_nat(v___x_762_);
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_755_, v___f_766_, v_toArray_759_, v___x_769_, v___x_770_, v___x_763_);
return v___x_771_;
}
}
else
{
size_t v___x_772_; size_t v___x_773_; lean_object* v___x_774_; 
v___x_772_ = ((size_t)0ULL);
v___x_773_ = lean_usize_of_nat(v___x_762_);
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_755_, v___f_766_, v_toArray_759_, v___x_772_, v___x_773_, v___x_763_);
return v___x_774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM(lean_object* v_m_775_, lean_object* v_00_u03b2_776_, lean_object* v_00_u03b1_777_, lean_object* v_cmp_778_, lean_object* v_inst_779_, lean_object* v_f_780_, lean_object* v_self_781_){
_start:
{
lean_object* v_toApplicative_782_; lean_object* v_toArray_783_; lean_object* v_toPure_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_toApplicative_782_ = lean_ctor_get(v_inst_779_, 0);
v_toArray_783_ = lean_ctor_get(v_self_781_, 1);
lean_inc_ref(v_toArray_783_);
lean_dec_ref(v_self_781_);
v_toPure_784_ = lean_ctor_get(v_toApplicative_782_, 1);
v___x_785_ = lean_unsigned_to_nat(0u);
v___x_786_ = lean_array_get_size(v_toArray_783_);
v___x_787_ = lean_box(0);
v___x_788_ = lean_nat_dec_lt(v___x_785_, v___x_786_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
lean_inc(v_toPure_784_);
lean_dec_ref(v_toArray_783_);
lean_dec(v_f_780_);
lean_dec_ref(v_inst_779_);
v___x_789_ = lean_apply_2(v_toPure_784_, lean_box(0), v___x_787_);
return v___x_789_;
}
else
{
lean_object* v___f_790_; uint8_t v___x_791_; 
v___f_790_ = lean_alloc_closure((void*)(l_Lake_RBArray_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_790_, 0, v_f_780_);
v___x_791_ = lean_nat_dec_le(v___x_786_, v___x_786_);
if (v___x_791_ == 0)
{
if (v___x_788_ == 0)
{
lean_object* v___x_792_; 
lean_inc(v_toPure_784_);
lean_dec_ref(v___f_790_);
lean_dec_ref(v_toArray_783_);
lean_dec_ref(v_inst_779_);
v___x_792_ = lean_apply_2(v_toPure_784_, lean_box(0), v___x_787_);
return v___x_792_;
}
else
{
size_t v___x_793_; size_t v___x_794_; lean_object* v___x_795_; 
v___x_793_ = ((size_t)0ULL);
v___x_794_ = lean_usize_of_nat(v___x_786_);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_779_, v___f_790_, v_toArray_783_, v___x_793_, v___x_794_, v___x_787_);
return v___x_795_;
}
}
else
{
size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; 
v___x_796_ = ((size_t)0ULL);
v___x_797_ = lean_usize_of_nat(v___x_786_);
v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_779_, v___f_790_, v_toArray_783_, v___x_796_, v___x_797_, v___x_787_);
return v___x_798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forM___boxed(lean_object* v_m_799_, lean_object* v_00_u03b2_800_, lean_object* v_00_u03b1_801_, lean_object* v_cmp_802_, lean_object* v_inst_803_, lean_object* v_f_804_, lean_object* v_self_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lake_RBArray_forM(v_m_799_, v_00_u03b2_800_, v_00_u03b1_801_, v_cmp_802_, v_inst_803_, v_f_804_, v_self_805_);
lean_dec_ref(v_cmp_802_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn___redArg___lam__0(lean_object* v_f_807_, lean_object* v_a_808_, lean_object* v_x_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = lean_apply_2(v_f_807_, v_a_808_, v___y_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn___redArg(lean_object* v_inst_812_, lean_object* v_self_813_, lean_object* v_init_814_, lean_object* v_f_815_){
_start:
{
lean_object* v_toArray_816_; lean_object* v___f_817_; size_t v_sz_818_; size_t v___x_819_; lean_object* v___x_820_; 
v_toArray_816_ = lean_ctor_get(v_self_813_, 1);
lean_inc_ref(v_toArray_816_);
lean_dec_ref(v_self_813_);
v___f_817_ = lean_alloc_closure((void*)(l_Lake_RBArray_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_817_, 0, v_f_815_);
v_sz_818_ = lean_array_size(v_toArray_816_);
v___x_819_ = ((size_t)0ULL);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_812_, v_toArray_816_, v___f_817_, v_sz_818_, v___x_819_, v_init_814_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn(lean_object* v_m_821_, lean_object* v_00_u03b1_822_, lean_object* v_00_u03b2_823_, lean_object* v_cmp_824_, lean_object* v_00_u03c3_825_, lean_object* v_inst_826_, lean_object* v_self_827_, lean_object* v_init_828_, lean_object* v_f_829_){
_start:
{
lean_object* v_toArray_830_; lean_object* v___f_831_; size_t v_sz_832_; size_t v___x_833_; lean_object* v___x_834_; 
v_toArray_830_ = lean_ctor_get(v_self_827_, 1);
lean_inc_ref(v_toArray_830_);
lean_dec_ref(v_self_827_);
v___f_831_ = lean_alloc_closure((void*)(l_Lake_RBArray_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_831_, 0, v_f_829_);
v_sz_832_ = lean_array_size(v_toArray_830_);
v___x_833_ = ((size_t)0ULL);
v___x_834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_826_, v_toArray_830_, v___f_831_, v_sz_832_, v___x_833_, v_init_828_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lake_RBArray_forIn___boxed(lean_object* v_m_835_, lean_object* v_00_u03b1_836_, lean_object* v_00_u03b2_837_, lean_object* v_cmp_838_, lean_object* v_00_u03c3_839_, lean_object* v_inst_840_, lean_object* v_self_841_, lean_object* v_init_842_, lean_object* v_f_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lake_RBArray_forIn(v_m_835_, v_00_u03b1_836_, v_00_u03b2_837_, v_cmp_838_, v_00_u03c3_839_, v_inst_840_, v_self_841_, v_init_842_, v_f_843_);
lean_dec_ref(v_cmp_838_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__0(lean_object* v___y_845_, lean_object* v_a_846_, lean_object* v_x_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = lean_apply_2(v___y_845_, v_a_846_, v___y_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1(lean_object* v_inst_850_, lean_object* v_00_u03b2_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_toArray_855_; lean_object* v___f_856_; size_t v_sz_857_; size_t v___x_858_; lean_object* v___x_859_; 
v_toArray_855_ = lean_ctor_get(v___y_852_, 1);
lean_inc_ref(v_toArray_855_);
lean_dec_ref(v___y_852_);
v___f_856_ = lean_alloc_closure((void*)(l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_856_, 0, v___y_854_);
v_sz_857_ = lean_array_size(v_toArray_855_);
v___x_858_ = ((size_t)0ULL);
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_850_, v_toArray_855_, v___f_856_, v_sz_857_, v___x_858_, v___y_853_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg(lean_object* v_inst_860_){
_start:
{
lean_object* v___f_861_; 
v___f_861_ = lean_alloc_closure((void*)(l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_861_, 0, v_inst_860_);
return v___f_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad(lean_object* v_m_862_, lean_object* v_00_u03b1_863_, lean_object* v_00_u03b2_864_, lean_object* v_cmp_865_, lean_object* v_inst_866_){
_start:
{
lean_object* v___f_867_; 
v___f_867_ = lean_alloc_closure((void*)(l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_867_, 0, v_inst_866_);
return v___f_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad___boxed(lean_object* v_m_868_, lean_object* v_00_u03b1_869_, lean_object* v_00_u03b2_870_, lean_object* v_cmp_871_, lean_object* v_inst_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l___private_Lake_Util_RBArray_0__Lake_RBArray_instForInOfMonad(v_m_868_, v_00_u03b1_869_, v_00_u03b2_870_, v_cmp_871_, v_inst_872_);
lean_dec_ref(v_cmp_871_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkRBArray___redArg___lam__0(lean_object* v_f_874_, lean_object* v_cmp_875_, lean_object* v_x1_876_, lean_object* v_x2_877_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
lean_inc(v_x2_877_);
v___x_878_ = lean_apply_1(v_f_874_, v_x2_877_);
v___x_879_ = l_Lake_RBArray_insert___redArg(v_cmp_875_, v_x1_876_, v___x_878_, v_x2_877_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkRBArray___redArg(lean_object* v_cmp_880_, lean_object* v_f_881_, lean_object* v_vs_882_){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_883_ = lean_array_get_size(v_vs_882_);
v___x_884_ = l_Lake_RBArray_mkEmpty___redArg(v___x_883_);
v___x_885_ = lean_unsigned_to_nat(0u);
v___x_886_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_887_ = lean_nat_dec_lt(v___x_885_, v___x_883_);
if (v___x_887_ == 0)
{
lean_dec_ref(v_vs_882_);
lean_dec(v_f_881_);
lean_dec_ref(v_cmp_880_);
return v___x_884_;
}
else
{
lean_object* v___f_888_; uint8_t v___x_889_; 
v___f_888_ = lean_alloc_closure((void*)(l_Lake_mkRBArray___redArg___lam__0), 4, 2);
lean_closure_set(v___f_888_, 0, v_f_881_);
lean_closure_set(v___f_888_, 1, v_cmp_880_);
v___x_889_ = lean_nat_dec_le(v___x_883_, v___x_883_);
if (v___x_889_ == 0)
{
if (v___x_887_ == 0)
{
lean_dec_ref(v___f_888_);
lean_dec_ref(v_vs_882_);
return v___x_884_;
}
else
{
size_t v___x_890_; size_t v___x_891_; lean_object* v___x_892_; 
v___x_890_ = ((size_t)0ULL);
v___x_891_ = lean_usize_of_nat(v___x_883_);
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_886_, v___f_888_, v_vs_882_, v___x_890_, v___x_891_, v___x_884_);
return v___x_892_;
}
}
else
{
size_t v___x_893_; size_t v___x_894_; lean_object* v___x_895_; 
v___x_893_ = ((size_t)0ULL);
v___x_894_ = lean_usize_of_nat(v___x_883_);
v___x_895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_886_, v___f_888_, v_vs_882_, v___x_893_, v___x_894_, v___x_884_);
return v___x_895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkRBArray(lean_object* v_00_u03b2_896_, lean_object* v_00_u03b1_897_, lean_object* v_cmp_898_, lean_object* v_f_899_, lean_object* v_vs_900_){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_901_ = lean_array_get_size(v_vs_900_);
v___x_902_ = l_Lake_RBArray_mkEmpty___redArg(v___x_901_);
v___x_903_ = lean_unsigned_to_nat(0u);
v___x_904_ = ((lean_object*)(l_Lake_RBArray_all___redArg___closed__9));
v___x_905_ = lean_nat_dec_lt(v___x_903_, v___x_901_);
if (v___x_905_ == 0)
{
lean_dec_ref(v_vs_900_);
lean_dec(v_f_899_);
lean_dec_ref(v_cmp_898_);
return v___x_902_;
}
else
{
lean_object* v___f_906_; uint8_t v___x_907_; 
v___f_906_ = lean_alloc_closure((void*)(l_Lake_mkRBArray___redArg___lam__0), 4, 2);
lean_closure_set(v___f_906_, 0, v_f_899_);
lean_closure_set(v___f_906_, 1, v_cmp_898_);
v___x_907_ = lean_nat_dec_le(v___x_901_, v___x_901_);
if (v___x_907_ == 0)
{
if (v___x_905_ == 0)
{
lean_dec_ref(v___f_906_);
lean_dec_ref(v_vs_900_);
return v___x_902_;
}
else
{
size_t v___x_908_; size_t v___x_909_; lean_object* v___x_910_; 
v___x_908_ = ((size_t)0ULL);
v___x_909_ = lean_usize_of_nat(v___x_901_);
v___x_910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_904_, v___f_906_, v_vs_900_, v___x_908_, v___x_909_, v___x_902_);
return v___x_910_;
}
}
else
{
size_t v___x_911_; size_t v___x_912_; lean_object* v___x_913_; 
v___x_911_ = ((size_t)0ULL);
v___x_912_ = lean_usize_of_nat(v___x_901_);
v___x_913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_904_, v___f_906_, v_vs_900_, v___x_911_, v___x_912_, v___x_902_);
return v___x_913_;
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
