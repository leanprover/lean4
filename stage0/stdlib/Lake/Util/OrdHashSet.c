// Lean compiler output
// Module: Lake.Util.OrdHashSet
// Imports: public import Std.Data.HashSet.Basic
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_OrdHashSet_instCoeHashSet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_OrdHashSet_instCoeHashSet___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_OrdHashSet_instCoeHashSet___closed__0 = (const lean_object*)&l_Lake_OrdHashSet_instCoeHashSet___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_OrdHashSet_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdHashSet_empty___closed__0;
static lean_once_cell_t l_Lake_OrdHashSet_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdHashSet_empty___closed__1;
static const lean_array_object l_Lake_OrdHashSet_empty___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_OrdHashSet_empty___closed__2 = (const lean_object*)&l_Lake_OrdHashSet_empty___closed__2_value;
static lean_once_cell_t l_Lake_OrdHashSet_empty___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdHashSet_empty___closed__3;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_OrdHashSet_appendArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_OrdHashSet_appendArray___redArg___closed__0 = (const lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__0_value;
static const lean_closure_object l_Lake_OrdHashSet_appendArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_OrdHashSet_appendArray___redArg___closed__1 = (const lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__1_value;
static const lean_closure_object l_Lake_OrdHashSet_appendArray___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_OrdHashSet_appendArray___redArg___closed__2 = (const lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__2_value;
static const lean_closure_object l_Lake_OrdHashSet_appendArray___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_OrdHashSet_appendArray___redArg___closed__3 = (const lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__3_value;
static const lean_closure_object l_Lake_OrdHashSet_appendArray___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_OrdHashSet_appendArray___redArg___closed__4 = (const lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__4_value;
static const lean_closure_object l_Lake_OrdHashSet_appendArray___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_OrdHashSet_appendArray___redArg___closed__5 = (const lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__5_value;
static const lean_closure_object l_Lake_OrdHashSet_appendArray___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_OrdHashSet_appendArray___redArg___closed__6 = (const lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__6_value;
static const lean_ctor_object l_Lake_OrdHashSet_appendArray___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__0_value),((lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__1_value)}};
static const lean_object* l_Lake_OrdHashSet_appendArray___redArg___closed__7 = (const lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__7_value;
static const lean_ctor_object l_Lake_OrdHashSet_appendArray___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__7_value),((lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__2_value),((lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__3_value),((lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__4_value),((lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__5_value)}};
static const lean_object* l_Lake_OrdHashSet_appendArray___redArg___closed__8 = (const lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__8_value;
static const lean_ctor_object l_Lake_OrdHashSet_appendArray___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__8_value),((lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__6_value)}};
static const lean_object* l_Lake_OrdHashSet_appendArray___redArg___closed__9 = (const lean_object*)&l_Lake_OrdHashSet_appendArray___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instHAppendArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instHAppendArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_append___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_append(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instAppend___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instAppend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_ofArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_any___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet___lam__0(lean_object* v_self_1_){
_start:
{
lean_object* v_toHashSet_2_; 
v_toHashSet_2_ = lean_ctor_get(v_self_1_, 0);
lean_inc_ref(v_toHashSet_2_);
return v_toHashSet_2_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet___lam__0___boxed(lean_object* v_self_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lake_OrdHashSet_instCoeHashSet___lam__0(v_self_3_);
lean_dec_ref(v_self_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet(lean_object* v_00_u03b1_6_, lean_object* v_inst_7_, lean_object* v_inst_8_){
_start:
{
lean_object* v___f_9_; 
v___f_9_ = ((lean_object*)(l_Lake_OrdHashSet_instCoeHashSet___closed__0));
return v___f_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet___boxed(lean_object* v_00_u03b1_10_, lean_object* v_inst_11_, lean_object* v_inst_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lake_OrdHashSet_instCoeHashSet(v_00_u03b1_10_, v_inst_11_, v_inst_12_);
lean_dec_ref(v_inst_12_);
lean_dec_ref(v_inst_11_);
return v_res_13_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___closed__0(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = lean_box(0);
v___x_15_ = lean_unsigned_to_nat(16u);
v___x_16_ = lean_mk_array(v___x_15_, v___x_14_);
return v___x_16_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___closed__1(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_17_ = lean_obj_once(&l_Lake_OrdHashSet_empty___closed__0, &l_Lake_OrdHashSet_empty___closed__0_once, _init_l_Lake_OrdHashSet_empty___closed__0);
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
return v___x_19_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___closed__3(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_22_ = ((lean_object*)(l_Lake_OrdHashSet_empty___closed__2));
v___x_23_ = lean_obj_once(&l_Lake_OrdHashSet_empty___closed__1, &l_Lake_OrdHashSet_empty___closed__1_once, _init_l_Lake_OrdHashSet_empty___closed__1);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
lean_ctor_set(v___x_24_, 1, v___x_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty(lean_object* v_00_u03b1_25_, lean_object* v_inst_26_, lean_object* v_inst_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_obj_once(&l_Lake_OrdHashSet_empty___closed__3, &l_Lake_OrdHashSet_empty___closed__3_once, _init_l_Lake_OrdHashSet_empty___closed__3);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___boxed(lean_object* v_00_u03b1_29_, lean_object* v_inst_30_, lean_object* v_inst_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lake_OrdHashSet_empty(v_00_u03b1_29_, v_inst_30_, v_inst_31_);
lean_dec_ref(v_inst_31_);
lean_dec_ref(v_inst_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection___redArg(lean_object* v_inst_33_, lean_object* v_inst_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lake_OrdHashSet_empty(lean_box(0), v_inst_33_, v_inst_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection___redArg___boxed(lean_object* v_inst_36_, lean_object* v_inst_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lake_OrdHashSet_instEmptyCollection___redArg(v_inst_36_, v_inst_37_);
lean_dec_ref(v_inst_37_);
lean_dec_ref(v_inst_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection(lean_object* v_00_u03b1_39_, lean_object* v_inst_40_, lean_object* v_inst_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lake_OrdHashSet_empty(lean_box(0), v_inst_40_, v_inst_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_43_, lean_object* v_inst_44_, lean_object* v_inst_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lake_OrdHashSet_instEmptyCollection(v_00_u03b1_43_, v_inst_44_, v_inst_45_);
lean_dec_ref(v_inst_45_);
lean_dec_ref(v_inst_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty___redArg(lean_object* v_size_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_obj_once(&l_Lake_OrdHashSet_empty___closed__1, &l_Lake_OrdHashSet_empty___closed__1_once, _init_l_Lake_OrdHashSet_empty___closed__1);
v___x_49_ = lean_mk_empty_array_with_capacity(v_size_47_);
v___x_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_48_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty___redArg___boxed(lean_object* v_size_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lake_OrdHashSet_mkEmpty___redArg(v_size_51_);
lean_dec(v_size_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty(lean_object* v_00_u03b1_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_size_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lake_OrdHashSet_mkEmpty___redArg(v_size_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty___boxed(lean_object* v_00_u03b1_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_size_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lake_OrdHashSet_mkEmpty(v_00_u03b1_58_, v_inst_59_, v_inst_60_, v_size_61_);
lean_dec(v_size_61_);
lean_dec_ref(v_inst_60_);
lean_dec_ref(v_inst_59_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___redArg(lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_self_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_toHashSet_67_; lean_object* v_toArray_68_; uint8_t v___x_69_; 
v_toHashSet_67_ = lean_ctor_get(v_self_65_, 0);
v_toArray_68_ = lean_ctor_get(v_self_65_, 1);
lean_inc(v_a_66_);
lean_inc_ref(v_inst_63_);
lean_inc_ref(v_inst_64_);
v___x_69_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_64_, v_inst_63_, v_toHashSet_67_, v_a_66_);
if (v___x_69_ == 0)
{
lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_79_; 
lean_inc_ref(v_toArray_68_);
lean_inc_ref(v_toHashSet_67_);
v_isSharedCheck_79_ = !lean_is_exclusive(v_self_65_);
if (v_isSharedCheck_79_ == 0)
{
lean_object* v_unused_80_; lean_object* v_unused_81_; 
v_unused_80_ = lean_ctor_get(v_self_65_, 1);
lean_dec(v_unused_80_);
v_unused_81_ = lean_ctor_get(v_self_65_, 0);
lean_dec(v_unused_81_);
v___x_71_ = v_self_65_;
v_isShared_72_ = v_isSharedCheck_79_;
goto v_resetjp_70_;
}
else
{
lean_dec(v_self_65_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_79_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_73_ = lean_box(0);
lean_inc(v_a_66_);
v___x_74_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_64_, v_inst_63_, v_toHashSet_67_, v_a_66_, v___x_73_);
v___x_75_ = lean_array_push(v_toArray_68_, v_a_66_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 1, v___x_75_);
lean_ctor_set(v___x_71_, 0, v___x_74_);
v___x_77_ = v___x_71_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_74_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
else
{
lean_dec(v_a_66_);
lean_dec_ref(v_inst_64_);
lean_dec_ref(v_inst_63_);
return v_self_65_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert(lean_object* v_00_u03b1_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_self_85_, lean_object* v_a_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lake_OrdHashSet_insert___redArg(v_inst_83_, v_inst_84_, v_self_85_, v_a_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___redArg___lam__0(lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_x1_90_, lean_object* v_x2_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lake_OrdHashSet_insert___redArg(v_inst_88_, v_inst_89_, v_x1_90_, v_x2_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___redArg(lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_self_114_, lean_object* v_arr_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_array_get_size(v_arr_115_);
v___x_118_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_119_ = lean_nat_dec_lt(v___x_116_, v___x_117_);
if (v___x_119_ == 0)
{
lean_dec_ref(v_arr_115_);
lean_dec_ref(v_inst_113_);
lean_dec_ref(v_inst_112_);
return v_self_114_;
}
else
{
lean_object* v___f_120_; uint8_t v___x_121_; 
v___f_120_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_appendArray___redArg___lam__0), 4, 2);
lean_closure_set(v___f_120_, 0, v_inst_112_);
lean_closure_set(v___f_120_, 1, v_inst_113_);
v___x_121_ = lean_nat_dec_le(v___x_117_, v___x_117_);
if (v___x_121_ == 0)
{
if (v___x_119_ == 0)
{
lean_dec_ref(v___f_120_);
lean_dec_ref(v_arr_115_);
return v_self_114_;
}
else
{
size_t v___x_122_; size_t v___x_123_; lean_object* v___x_124_; 
v___x_122_ = ((size_t)0ULL);
v___x_123_ = lean_usize_of_nat(v___x_117_);
v___x_124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_118_, v___f_120_, v_arr_115_, v___x_122_, v___x_123_, v_self_114_);
return v___x_124_;
}
}
else
{
size_t v___x_125_; size_t v___x_126_; lean_object* v___x_127_; 
v___x_125_ = ((size_t)0ULL);
v___x_126_ = lean_usize_of_nat(v___x_117_);
v___x_127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_118_, v___f_120_, v_arr_115_, v___x_125_, v___x_126_, v_self_114_);
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray(lean_object* v_00_u03b1_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_self_131_, lean_object* v_arr_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lake_OrdHashSet_appendArray___redArg(v_inst_129_, v_inst_130_, v_self_131_, v_arr_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instHAppendArray___redArg(lean_object* v_inst_134_, lean_object* v_inst_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_appendArray), 5, 3);
lean_closure_set(v___x_136_, 0, lean_box(0));
lean_closure_set(v___x_136_, 1, v_inst_134_);
lean_closure_set(v___x_136_, 2, v_inst_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instHAppendArray(lean_object* v_00_u03b1_137_, lean_object* v_inst_138_, lean_object* v_inst_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_appendArray), 5, 3);
lean_closure_set(v___x_140_, 0, lean_box(0));
lean_closure_set(v___x_140_, 1, v_inst_138_);
lean_closure_set(v___x_140_, 2, v_inst_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_append___redArg(lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_self_143_, lean_object* v_other_144_){
_start:
{
lean_object* v_toArray_145_; lean_object* v___x_146_; 
v_toArray_145_ = lean_ctor_get(v_other_144_, 1);
lean_inc_ref(v_toArray_145_);
lean_dec_ref(v_other_144_);
v___x_146_ = l_Lake_OrdHashSet_appendArray___redArg(v_inst_141_, v_inst_142_, v_self_143_, v_toArray_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_append(lean_object* v_00_u03b1_147_, lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_self_150_, lean_object* v_other_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lake_OrdHashSet_append___redArg(v_inst_148_, v_inst_149_, v_self_150_, v_other_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instAppend___redArg(lean_object* v_inst_153_, lean_object* v_inst_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_append), 5, 3);
lean_closure_set(v___x_155_, 0, lean_box(0));
lean_closure_set(v___x_155_, 1, v_inst_153_);
lean_closure_set(v___x_155_, 2, v_inst_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instAppend(lean_object* v_00_u03b1_156_, lean_object* v_inst_157_, lean_object* v_inst_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_append), 5, 3);
lean_closure_set(v___x_159_, 0, lean_box(0));
lean_closure_set(v___x_159_, 1, v_inst_157_);
lean_closure_set(v___x_159_, 2, v_inst_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_ofArray___redArg(lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_arr_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_array_get_size(v_arr_162_);
v___x_164_ = l_Lake_OrdHashSet_mkEmpty___redArg(v___x_163_);
v___x_165_ = l_Lake_OrdHashSet_appendArray___redArg(v_inst_160_, v_inst_161_, v___x_164_, v_arr_162_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_ofArray(lean_object* v_00_u03b1_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_arr_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lake_OrdHashSet_ofArray___redArg(v_inst_167_, v_inst_168_, v_arr_169_);
return v___x_170_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all___redArg___lam__0(lean_object* v_f_171_, lean_object* v_v_172_){
_start:
{
lean_object* v___x_173_; uint8_t v___x_174_; uint8_t v___x_175_; 
v___x_173_ = lean_apply_1(v_f_171_, v_v_172_);
v___x_174_ = lean_unbox(v___x_173_);
v___x_175_ = lean_bool_not(v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___redArg___lam__0___boxed(lean_object* v_f_176_, lean_object* v_v_177_){
_start:
{
uint8_t v_res_178_; lean_object* v_r_179_; 
v_res_178_ = l_Lake_OrdHashSet_all___redArg___lam__0(v_f_176_, v_v_177_);
v_r_179_ = lean_box(v_res_178_);
return v_r_179_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all___redArg(lean_object* v_f_180_, lean_object* v_self_181_){
_start:
{
lean_object* v_toArray_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_toArray_182_ = lean_ctor_get(v_self_181_, 1);
lean_inc_ref(v_toArray_182_);
lean_dec_ref(v_self_181_);
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_array_get_size(v_toArray_182_);
v___x_185_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_186_ = lean_nat_dec_lt(v___x_183_, v___x_184_);
if (v___x_186_ == 0)
{
uint8_t v___x_187_; 
lean_dec_ref(v_toArray_182_);
lean_dec_ref(v_f_180_);
v___x_187_ = lean_bool_not(v___x_186_);
return v___x_187_;
}
else
{
if (v___x_186_ == 0)
{
uint8_t v___x_188_; 
lean_dec_ref(v_toArray_182_);
lean_dec_ref(v_f_180_);
v___x_188_ = lean_bool_not(v___x_186_);
return v___x_188_;
}
else
{
lean_object* v___f_189_; size_t v___x_190_; size_t v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; uint8_t v___x_194_; 
v___f_189_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_189_, 0, v_f_180_);
v___x_190_ = ((size_t)0ULL);
v___x_191_ = lean_usize_of_nat(v___x_184_);
v___x_192_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_185_, v___f_189_, v_toArray_182_, v___x_190_, v___x_191_);
v___x_193_ = lean_unbox(v___x_192_);
lean_dec(v___x_192_);
v___x_194_ = lean_bool_not(v___x_193_);
return v___x_194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___redArg___boxed(lean_object* v_f_195_, lean_object* v_self_196_){
_start:
{
uint8_t v_res_197_; lean_object* v_r_198_; 
v_res_197_ = l_Lake_OrdHashSet_all___redArg(v_f_195_, v_self_196_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all(lean_object* v_00_u03b1_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_f_202_, lean_object* v_self_203_){
_start:
{
lean_object* v_toArray_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_toArray_204_ = lean_ctor_get(v_self_203_, 1);
lean_inc_ref(v_toArray_204_);
lean_dec_ref(v_self_203_);
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_array_get_size(v_toArray_204_);
v___x_207_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_208_ = lean_nat_dec_lt(v___x_205_, v___x_206_);
if (v___x_208_ == 0)
{
uint8_t v___x_209_; 
lean_dec_ref(v_toArray_204_);
lean_dec_ref(v_f_202_);
v___x_209_ = lean_bool_not(v___x_208_);
return v___x_209_;
}
else
{
if (v___x_208_ == 0)
{
uint8_t v___x_210_; 
lean_dec_ref(v_toArray_204_);
lean_dec_ref(v_f_202_);
v___x_210_ = lean_bool_not(v___x_208_);
return v___x_210_;
}
else
{
lean_object* v___f_211_; size_t v___x_212_; size_t v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; uint8_t v___x_216_; 
v___f_211_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_211_, 0, v_f_202_);
v___x_212_ = ((size_t)0ULL);
v___x_213_ = lean_usize_of_nat(v___x_206_);
v___x_214_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_207_, v___f_211_, v_toArray_204_, v___x_212_, v___x_213_);
v___x_215_ = lean_unbox(v___x_214_);
lean_dec(v___x_214_);
v___x_216_ = lean_bool_not(v___x_215_);
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___boxed(lean_object* v_00_u03b1_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_f_220_, lean_object* v_self_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l_Lake_OrdHashSet_all(v_00_u03b1_217_, v_inst_218_, v_inst_219_, v_f_220_, v_self_221_);
lean_dec_ref(v_inst_219_);
lean_dec_ref(v_inst_218_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_any___redArg___lam__0(lean_object* v_f_224_, lean_object* v_x_225_){
_start:
{
lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_226_ = lean_apply_1(v_f_224_, v_x_225_);
v___x_227_ = lean_unbox(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___redArg___lam__0___boxed(lean_object* v_f_228_, lean_object* v_x_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = l_Lake_OrdHashSet_any___redArg___lam__0(v_f_228_, v_x_229_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_any___redArg(lean_object* v_f_232_, lean_object* v_self_233_){
_start:
{
lean_object* v_toArray_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v_toArray_234_ = lean_ctor_get(v_self_233_, 1);
lean_inc_ref(v_toArray_234_);
lean_dec_ref(v_self_233_);
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = lean_array_get_size(v_toArray_234_);
v___x_237_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_238_ = lean_nat_dec_lt(v___x_235_, v___x_236_);
if (v___x_238_ == 0)
{
lean_dec_ref(v_toArray_234_);
lean_dec_ref(v_f_232_);
return v___x_238_;
}
else
{
if (v___x_238_ == 0)
{
lean_dec_ref(v_toArray_234_);
lean_dec_ref(v_f_232_);
return v___x_238_;
}
else
{
lean_object* v___f_239_; size_t v___x_240_; size_t v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v___f_239_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_239_, 0, v_f_232_);
v___x_240_ = ((size_t)0ULL);
v___x_241_ = lean_usize_of_nat(v___x_236_);
v___x_242_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_237_, v___f_239_, v_toArray_234_, v___x_240_, v___x_241_);
v___x_243_ = lean_unbox(v___x_242_);
lean_dec(v___x_242_);
return v___x_243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___redArg___boxed(lean_object* v_f_244_, lean_object* v_self_245_){
_start:
{
uint8_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_Lake_OrdHashSet_any___redArg(v_f_244_, v_self_245_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_any(lean_object* v_00_u03b1_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_f_251_, lean_object* v_self_252_){
_start:
{
lean_object* v_toArray_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v_toArray_253_ = lean_ctor_get(v_self_252_, 1);
lean_inc_ref(v_toArray_253_);
lean_dec_ref(v_self_252_);
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = lean_array_get_size(v_toArray_253_);
v___x_256_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_257_ = lean_nat_dec_lt(v___x_254_, v___x_255_);
if (v___x_257_ == 0)
{
lean_dec_ref(v_toArray_253_);
lean_dec_ref(v_f_251_);
return v___x_257_;
}
else
{
if (v___x_257_ == 0)
{
lean_dec_ref(v_toArray_253_);
lean_dec_ref(v_f_251_);
return v___x_257_;
}
else
{
lean_object* v___f_258_; size_t v___x_259_; size_t v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v___f_258_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_258_, 0, v_f_251_);
v___x_259_ = ((size_t)0ULL);
v___x_260_ = lean_usize_of_nat(v___x_255_);
v___x_261_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_256_, v___f_258_, v_toArray_253_, v___x_259_, v___x_260_);
v___x_262_ = lean_unbox(v___x_261_);
lean_dec(v___x_261_);
return v___x_262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___boxed(lean_object* v_00_u03b1_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_f_266_, lean_object* v_self_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_Lake_OrdHashSet_any(v_00_u03b1_263_, v_inst_264_, v_inst_265_, v_f_266_, v_self_267_);
lean_dec_ref(v_inst_265_);
lean_dec_ref(v_inst_264_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___redArg___lam__0(lean_object* v_f_270_, lean_object* v_x1_271_, lean_object* v_x2_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lean_apply_2(v_f_270_, v_x1_271_, v_x2_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___redArg(lean_object* v_f_274_, lean_object* v_init_275_, lean_object* v_self_276_){
_start:
{
lean_object* v_toArray_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v_toArray_277_ = lean_ctor_get(v_self_276_, 1);
lean_inc_ref(v_toArray_277_);
lean_dec_ref(v_self_276_);
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = lean_array_get_size(v_toArray_277_);
v___x_280_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_281_ = lean_nat_dec_lt(v___x_278_, v___x_279_);
if (v___x_281_ == 0)
{
lean_dec_ref(v_toArray_277_);
lean_dec(v_f_274_);
return v_init_275_;
}
else
{
lean_object* v___f_282_; uint8_t v___x_283_; 
v___f_282_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_282_, 0, v_f_274_);
v___x_283_ = lean_nat_dec_le(v___x_279_, v___x_279_);
if (v___x_283_ == 0)
{
if (v___x_281_ == 0)
{
lean_dec_ref(v___f_282_);
lean_dec_ref(v_toArray_277_);
return v_init_275_;
}
else
{
size_t v___x_284_; size_t v___x_285_; lean_object* v___x_286_; 
v___x_284_ = ((size_t)0ULL);
v___x_285_ = lean_usize_of_nat(v___x_279_);
v___x_286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_280_, v___f_282_, v_toArray_277_, v___x_284_, v___x_285_, v_init_275_);
return v___x_286_;
}
}
else
{
size_t v___x_287_; size_t v___x_288_; lean_object* v___x_289_; 
v___x_287_ = ((size_t)0ULL);
v___x_288_ = lean_usize_of_nat(v___x_279_);
v___x_289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_280_, v___f_282_, v_toArray_277_, v___x_287_, v___x_288_, v_init_275_);
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl(lean_object* v_00_u03b1_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_00_u03b2_293_, lean_object* v_f_294_, lean_object* v_init_295_, lean_object* v_self_296_){
_start:
{
lean_object* v_toArray_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v_toArray_297_ = lean_ctor_get(v_self_296_, 1);
lean_inc_ref(v_toArray_297_);
lean_dec_ref(v_self_296_);
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_array_get_size(v_toArray_297_);
v___x_300_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_301_ = lean_nat_dec_lt(v___x_298_, v___x_299_);
if (v___x_301_ == 0)
{
lean_dec_ref(v_toArray_297_);
lean_dec(v_f_294_);
return v_init_295_;
}
else
{
lean_object* v___f_302_; uint8_t v___x_303_; 
v___f_302_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_302_, 0, v_f_294_);
v___x_303_ = lean_nat_dec_le(v___x_299_, v___x_299_);
if (v___x_303_ == 0)
{
if (v___x_301_ == 0)
{
lean_dec_ref(v___f_302_);
lean_dec_ref(v_toArray_297_);
return v_init_295_;
}
else
{
size_t v___x_304_; size_t v___x_305_; lean_object* v___x_306_; 
v___x_304_ = ((size_t)0ULL);
v___x_305_ = lean_usize_of_nat(v___x_299_);
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_300_, v___f_302_, v_toArray_297_, v___x_304_, v___x_305_, v_init_295_);
return v___x_306_;
}
}
else
{
size_t v___x_307_; size_t v___x_308_; lean_object* v___x_309_; 
v___x_307_ = ((size_t)0ULL);
v___x_308_ = lean_usize_of_nat(v___x_299_);
v___x_309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_300_, v___f_302_, v_toArray_297_, v___x_307_, v___x_308_, v_init_295_);
return v___x_309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___boxed(lean_object* v_00_u03b1_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_00_u03b2_313_, lean_object* v_f_314_, lean_object* v_init_315_, lean_object* v_self_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lake_OrdHashSet_foldl(v_00_u03b1_310_, v_inst_311_, v_inst_312_, v_00_u03b2_313_, v_f_314_, v_init_315_, v_self_316_);
lean_dec_ref(v_inst_312_);
lean_dec_ref(v_inst_311_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM___redArg(lean_object* v_inst_318_, lean_object* v_f_319_, lean_object* v_init_320_, lean_object* v_self_321_){
_start:
{
lean_object* v_toArray_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_toArray_322_ = lean_ctor_get(v_self_321_, 1);
lean_inc_ref(v_toArray_322_);
lean_dec_ref(v_self_321_);
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = lean_array_get_size(v_toArray_322_);
v___x_325_ = lean_nat_dec_lt(v___x_323_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v_toApplicative_326_; lean_object* v_toPure_327_; lean_object* v___x_328_; 
lean_dec_ref(v_toArray_322_);
lean_dec(v_f_319_);
v_toApplicative_326_ = lean_ctor_get(v_inst_318_, 0);
lean_inc_ref(v_toApplicative_326_);
lean_dec_ref(v_inst_318_);
v_toPure_327_ = lean_ctor_get(v_toApplicative_326_, 1);
lean_inc(v_toPure_327_);
lean_dec_ref(v_toApplicative_326_);
v___x_328_ = lean_apply_2(v_toPure_327_, lean_box(0), v_init_320_);
return v___x_328_;
}
else
{
uint8_t v___x_329_; 
v___x_329_ = lean_nat_dec_le(v___x_324_, v___x_324_);
if (v___x_329_ == 0)
{
if (v___x_325_ == 0)
{
lean_object* v_toApplicative_330_; lean_object* v_toPure_331_; lean_object* v___x_332_; 
lean_dec_ref(v_toArray_322_);
lean_dec(v_f_319_);
v_toApplicative_330_ = lean_ctor_get(v_inst_318_, 0);
lean_inc_ref(v_toApplicative_330_);
lean_dec_ref(v_inst_318_);
v_toPure_331_ = lean_ctor_get(v_toApplicative_330_, 1);
lean_inc(v_toPure_331_);
lean_dec_ref(v_toApplicative_330_);
v___x_332_ = lean_apply_2(v_toPure_331_, lean_box(0), v_init_320_);
return v___x_332_;
}
else
{
size_t v___x_333_; size_t v___x_334_; lean_object* v___x_335_; 
v___x_333_ = ((size_t)0ULL);
v___x_334_ = lean_usize_of_nat(v___x_324_);
v___x_335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_318_, v_f_319_, v_toArray_322_, v___x_333_, v___x_334_, v_init_320_);
return v___x_335_;
}
}
else
{
size_t v___x_336_; size_t v___x_337_; lean_object* v___x_338_; 
v___x_336_ = ((size_t)0ULL);
v___x_337_ = lean_usize_of_nat(v___x_324_);
v___x_338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_318_, v_f_319_, v_toArray_322_, v___x_336_, v___x_337_, v_init_320_);
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM(lean_object* v_00_u03b1_339_, lean_object* v_inst_340_, lean_object* v_inst_341_, lean_object* v_m_342_, lean_object* v_00_u03b2_343_, lean_object* v_inst_344_, lean_object* v_f_345_, lean_object* v_init_346_, lean_object* v_self_347_){
_start:
{
lean_object* v_toArray_348_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v_toArray_348_ = lean_ctor_get(v_self_347_, 1);
lean_inc_ref(v_toArray_348_);
lean_dec_ref(v_self_347_);
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = lean_array_get_size(v_toArray_348_);
v___x_351_ = lean_nat_dec_lt(v___x_349_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v_toApplicative_352_; lean_object* v_toPure_353_; lean_object* v___x_354_; 
lean_dec_ref(v_toArray_348_);
lean_dec(v_f_345_);
v_toApplicative_352_ = lean_ctor_get(v_inst_344_, 0);
lean_inc_ref(v_toApplicative_352_);
lean_dec_ref(v_inst_344_);
v_toPure_353_ = lean_ctor_get(v_toApplicative_352_, 1);
lean_inc(v_toPure_353_);
lean_dec_ref(v_toApplicative_352_);
v___x_354_ = lean_apply_2(v_toPure_353_, lean_box(0), v_init_346_);
return v___x_354_;
}
else
{
uint8_t v___x_355_; 
v___x_355_ = lean_nat_dec_le(v___x_350_, v___x_350_);
if (v___x_355_ == 0)
{
if (v___x_351_ == 0)
{
lean_object* v_toApplicative_356_; lean_object* v_toPure_357_; lean_object* v___x_358_; 
lean_dec_ref(v_toArray_348_);
lean_dec(v_f_345_);
v_toApplicative_356_ = lean_ctor_get(v_inst_344_, 0);
lean_inc_ref(v_toApplicative_356_);
lean_dec_ref(v_inst_344_);
v_toPure_357_ = lean_ctor_get(v_toApplicative_356_, 1);
lean_inc(v_toPure_357_);
lean_dec_ref(v_toApplicative_356_);
v___x_358_ = lean_apply_2(v_toPure_357_, lean_box(0), v_init_346_);
return v___x_358_;
}
else
{
size_t v___x_359_; size_t v___x_360_; lean_object* v___x_361_; 
v___x_359_ = ((size_t)0ULL);
v___x_360_ = lean_usize_of_nat(v___x_350_);
v___x_361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_344_, v_f_345_, v_toArray_348_, v___x_359_, v___x_360_, v_init_346_);
return v___x_361_;
}
}
else
{
size_t v___x_362_; size_t v___x_363_; lean_object* v___x_364_; 
v___x_362_ = ((size_t)0ULL);
v___x_363_ = lean_usize_of_nat(v___x_350_);
v___x_364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_344_, v_f_345_, v_toArray_348_, v___x_362_, v___x_363_, v_init_346_);
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM___boxed(lean_object* v_00_u03b1_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_m_368_, lean_object* v_00_u03b2_369_, lean_object* v_inst_370_, lean_object* v_f_371_, lean_object* v_init_372_, lean_object* v_self_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lake_OrdHashSet_foldlM(v_00_u03b1_365_, v_inst_366_, v_inst_367_, v_m_368_, v_00_u03b2_369_, v_inst_370_, v_f_371_, v_init_372_, v_self_373_);
lean_dec_ref(v_inst_367_);
lean_dec_ref(v_inst_366_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr___redArg(lean_object* v_f_375_, lean_object* v_init_376_, lean_object* v_self_377_){
_start:
{
lean_object* v_toArray_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_toArray_378_ = lean_ctor_get(v_self_377_, 1);
lean_inc_ref(v_toArray_378_);
lean_dec_ref(v_self_377_);
v___x_379_ = lean_array_get_size(v_toArray_378_);
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_382_ = lean_nat_dec_lt(v___x_380_, v___x_379_);
if (v___x_382_ == 0)
{
lean_dec_ref(v_toArray_378_);
lean_dec(v_f_375_);
return v_init_376_;
}
else
{
lean_object* v___f_383_; size_t v___x_384_; size_t v___x_385_; lean_object* v___x_386_; 
v___f_383_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_383_, 0, v_f_375_);
v___x_384_ = lean_usize_of_nat(v___x_379_);
v___x_385_ = ((size_t)0ULL);
v___x_386_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_381_, v___f_383_, v_toArray_378_, v___x_384_, v___x_385_, v_init_376_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr(lean_object* v_00_u03b1_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_00_u03b2_390_, lean_object* v_f_391_, lean_object* v_init_392_, lean_object* v_self_393_){
_start:
{
lean_object* v_toArray_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v_toArray_394_ = lean_ctor_get(v_self_393_, 1);
lean_inc_ref(v_toArray_394_);
lean_dec_ref(v_self_393_);
v___x_395_ = lean_array_get_size(v_toArray_394_);
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_398_ = lean_nat_dec_lt(v___x_396_, v___x_395_);
if (v___x_398_ == 0)
{
lean_dec_ref(v_toArray_394_);
lean_dec(v_f_391_);
return v_init_392_;
}
else
{
lean_object* v___f_399_; size_t v___x_400_; size_t v___x_401_; lean_object* v___x_402_; 
v___f_399_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_399_, 0, v_f_391_);
v___x_400_ = lean_usize_of_nat(v___x_395_);
v___x_401_ = ((size_t)0ULL);
v___x_402_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_397_, v___f_399_, v_toArray_394_, v___x_400_, v___x_401_, v_init_392_);
return v___x_402_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr___boxed(lean_object* v_00_u03b1_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_00_u03b2_406_, lean_object* v_f_407_, lean_object* v_init_408_, lean_object* v_self_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lake_OrdHashSet_foldr(v_00_u03b1_403_, v_inst_404_, v_inst_405_, v_00_u03b2_406_, v_f_407_, v_init_408_, v_self_409_);
lean_dec_ref(v_inst_405_);
lean_dec_ref(v_inst_404_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM___redArg(lean_object* v_inst_411_, lean_object* v_f_412_, lean_object* v_init_413_, lean_object* v_self_414_){
_start:
{
lean_object* v_toArray_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v_toArray_415_ = lean_ctor_get(v_self_414_, 1);
lean_inc_ref(v_toArray_415_);
lean_dec_ref(v_self_414_);
v___x_416_ = lean_array_get_size(v_toArray_415_);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = lean_nat_dec_lt(v___x_417_, v___x_416_);
if (v___x_418_ == 0)
{
lean_object* v_toApplicative_419_; lean_object* v_toPure_420_; lean_object* v___x_421_; 
lean_dec_ref(v_toArray_415_);
lean_dec(v_f_412_);
v_toApplicative_419_ = lean_ctor_get(v_inst_411_, 0);
lean_inc_ref(v_toApplicative_419_);
lean_dec_ref(v_inst_411_);
v_toPure_420_ = lean_ctor_get(v_toApplicative_419_, 1);
lean_inc(v_toPure_420_);
lean_dec_ref(v_toApplicative_419_);
v___x_421_ = lean_apply_2(v_toPure_420_, lean_box(0), v_init_413_);
return v___x_421_;
}
else
{
size_t v___x_422_; size_t v___x_423_; lean_object* v___x_424_; 
v___x_422_ = lean_usize_of_nat(v___x_416_);
v___x_423_ = ((size_t)0ULL);
v___x_424_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_411_, v_f_412_, v_toArray_415_, v___x_422_, v___x_423_, v_init_413_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM(lean_object* v_00_u03b1_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_m_428_, lean_object* v_00_u03b2_429_, lean_object* v_inst_430_, lean_object* v_f_431_, lean_object* v_init_432_, lean_object* v_self_433_){
_start:
{
lean_object* v_toArray_434_; lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v_toArray_434_ = lean_ctor_get(v_self_433_, 1);
lean_inc_ref(v_toArray_434_);
lean_dec_ref(v_self_433_);
v___x_435_ = lean_array_get_size(v_toArray_434_);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_nat_dec_lt(v___x_436_, v___x_435_);
if (v___x_437_ == 0)
{
lean_object* v_toApplicative_438_; lean_object* v_toPure_439_; lean_object* v___x_440_; 
lean_dec_ref(v_toArray_434_);
lean_dec(v_f_431_);
v_toApplicative_438_ = lean_ctor_get(v_inst_430_, 0);
lean_inc_ref(v_toApplicative_438_);
lean_dec_ref(v_inst_430_);
v_toPure_439_ = lean_ctor_get(v_toApplicative_438_, 1);
lean_inc(v_toPure_439_);
lean_dec_ref(v_toApplicative_438_);
v___x_440_ = lean_apply_2(v_toPure_439_, lean_box(0), v_init_432_);
return v___x_440_;
}
else
{
size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; 
v___x_441_ = lean_usize_of_nat(v___x_435_);
v___x_442_ = ((size_t)0ULL);
v___x_443_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_430_, v_f_431_, v_toArray_434_, v___x_441_, v___x_442_, v_init_432_);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM___boxed(lean_object* v_00_u03b1_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_m_447_, lean_object* v_00_u03b2_448_, lean_object* v_inst_449_, lean_object* v_f_450_, lean_object* v_init_451_, lean_object* v_self_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lake_OrdHashSet_foldrM(v_00_u03b1_444_, v_inst_445_, v_inst_446_, v_m_447_, v_00_u03b2_448_, v_inst_449_, v_f_450_, v_init_451_, v_self_452_);
lean_dec_ref(v_inst_446_);
lean_dec_ref(v_inst_445_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___redArg___lam__0(lean_object* v_f_454_, lean_object* v_x_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = lean_apply_1(v_f_454_, v___y_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___redArg(lean_object* v_inst_458_, lean_object* v_f_459_, lean_object* v_self_460_){
_start:
{
lean_object* v_toArray_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v_toArray_461_ = lean_ctor_get(v_self_460_, 1);
lean_inc_ref(v_toArray_461_);
lean_dec_ref(v_self_460_);
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_array_get_size(v_toArray_461_);
v___x_464_ = lean_box(0);
v___x_465_ = lean_nat_dec_lt(v___x_462_, v___x_463_);
if (v___x_465_ == 0)
{
lean_object* v_toApplicative_466_; lean_object* v_toPure_467_; lean_object* v___x_468_; 
lean_dec_ref(v_toArray_461_);
lean_dec(v_f_459_);
v_toApplicative_466_ = lean_ctor_get(v_inst_458_, 0);
lean_inc_ref(v_toApplicative_466_);
lean_dec_ref(v_inst_458_);
v_toPure_467_ = lean_ctor_get(v_toApplicative_466_, 1);
lean_inc(v_toPure_467_);
lean_dec_ref(v_toApplicative_466_);
v___x_468_ = lean_apply_2(v_toPure_467_, lean_box(0), v___x_464_);
return v___x_468_;
}
else
{
lean_object* v___f_469_; uint8_t v___x_470_; 
v___f_469_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_469_, 0, v_f_459_);
v___x_470_ = lean_nat_dec_le(v___x_463_, v___x_463_);
if (v___x_470_ == 0)
{
if (v___x_465_ == 0)
{
lean_object* v_toApplicative_471_; lean_object* v_toPure_472_; lean_object* v___x_473_; 
lean_dec_ref(v___f_469_);
lean_dec_ref(v_toArray_461_);
v_toApplicative_471_ = lean_ctor_get(v_inst_458_, 0);
lean_inc_ref(v_toApplicative_471_);
lean_dec_ref(v_inst_458_);
v_toPure_472_ = lean_ctor_get(v_toApplicative_471_, 1);
lean_inc(v_toPure_472_);
lean_dec_ref(v_toApplicative_471_);
v___x_473_ = lean_apply_2(v_toPure_472_, lean_box(0), v___x_464_);
return v___x_473_;
}
else
{
size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; 
v___x_474_ = ((size_t)0ULL);
v___x_475_ = lean_usize_of_nat(v___x_463_);
v___x_476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_458_, v___f_469_, v_toArray_461_, v___x_474_, v___x_475_, v___x_464_);
return v___x_476_;
}
}
else
{
size_t v___x_477_; size_t v___x_478_; lean_object* v___x_479_; 
v___x_477_ = ((size_t)0ULL);
v___x_478_ = lean_usize_of_nat(v___x_463_);
v___x_479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_458_, v___f_469_, v_toArray_461_, v___x_477_, v___x_478_, v___x_464_);
return v___x_479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM(lean_object* v_00_u03b1_480_, lean_object* v_inst_481_, lean_object* v_inst_482_, lean_object* v_m_483_, lean_object* v_inst_484_, lean_object* v_f_485_, lean_object* v_self_486_){
_start:
{
lean_object* v_toArray_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v_toArray_487_ = lean_ctor_get(v_self_486_, 1);
lean_inc_ref(v_toArray_487_);
lean_dec_ref(v_self_486_);
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = lean_array_get_size(v_toArray_487_);
v___x_490_ = lean_box(0);
v___x_491_ = lean_nat_dec_lt(v___x_488_, v___x_489_);
if (v___x_491_ == 0)
{
lean_object* v_toApplicative_492_; lean_object* v_toPure_493_; lean_object* v___x_494_; 
lean_dec_ref(v_toArray_487_);
lean_dec(v_f_485_);
v_toApplicative_492_ = lean_ctor_get(v_inst_484_, 0);
lean_inc_ref(v_toApplicative_492_);
lean_dec_ref(v_inst_484_);
v_toPure_493_ = lean_ctor_get(v_toApplicative_492_, 1);
lean_inc(v_toPure_493_);
lean_dec_ref(v_toApplicative_492_);
v___x_494_ = lean_apply_2(v_toPure_493_, lean_box(0), v___x_490_);
return v___x_494_;
}
else
{
lean_object* v___f_495_; uint8_t v___x_496_; 
v___f_495_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_495_, 0, v_f_485_);
v___x_496_ = lean_nat_dec_le(v___x_489_, v___x_489_);
if (v___x_496_ == 0)
{
if (v___x_491_ == 0)
{
lean_object* v_toApplicative_497_; lean_object* v_toPure_498_; lean_object* v___x_499_; 
lean_dec_ref(v___f_495_);
lean_dec_ref(v_toArray_487_);
v_toApplicative_497_ = lean_ctor_get(v_inst_484_, 0);
lean_inc_ref(v_toApplicative_497_);
lean_dec_ref(v_inst_484_);
v_toPure_498_ = lean_ctor_get(v_toApplicative_497_, 1);
lean_inc(v_toPure_498_);
lean_dec_ref(v_toApplicative_497_);
v___x_499_ = lean_apply_2(v_toPure_498_, lean_box(0), v___x_490_);
return v___x_499_;
}
else
{
size_t v___x_500_; size_t v___x_501_; lean_object* v___x_502_; 
v___x_500_ = ((size_t)0ULL);
v___x_501_ = lean_usize_of_nat(v___x_489_);
v___x_502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_484_, v___f_495_, v_toArray_487_, v___x_500_, v___x_501_, v___x_490_);
return v___x_502_;
}
}
else
{
size_t v___x_503_; size_t v___x_504_; lean_object* v___x_505_; 
v___x_503_ = ((size_t)0ULL);
v___x_504_ = lean_usize_of_nat(v___x_489_);
v___x_505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_484_, v___f_495_, v_toArray_487_, v___x_503_, v___x_504_, v___x_490_);
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___boxed(lean_object* v_00_u03b1_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_m_509_, lean_object* v_inst_510_, lean_object* v_f_511_, lean_object* v_self_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lake_OrdHashSet_forM(v_00_u03b1_506_, v_inst_507_, v_inst_508_, v_m_509_, v_inst_510_, v_f_511_, v_self_512_);
lean_dec_ref(v_inst_508_);
lean_dec_ref(v_inst_507_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___redArg___lam__0(lean_object* v_f_514_, lean_object* v_a_515_, lean_object* v_x_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = lean_apply_2(v_f_514_, v_a_515_, v___y_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___redArg(lean_object* v_inst_519_, lean_object* v_self_520_, lean_object* v_init_521_, lean_object* v_f_522_){
_start:
{
lean_object* v_toArray_523_; lean_object* v___f_524_; size_t v_sz_525_; size_t v___x_526_; lean_object* v___x_527_; 
v_toArray_523_ = lean_ctor_get(v_self_520_, 1);
lean_inc_ref(v_toArray_523_);
lean_dec_ref(v_self_520_);
v___f_524_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_524_, 0, v_f_522_);
v_sz_525_ = lean_array_size(v_toArray_523_);
v___x_526_ = ((size_t)0ULL);
v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_519_, v_toArray_523_, v___f_524_, v_sz_525_, v___x_526_, v_init_521_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn(lean_object* v_00_u03b1_528_, lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_m_531_, lean_object* v_00_u03b2_532_, lean_object* v_inst_533_, lean_object* v_self_534_, lean_object* v_init_535_, lean_object* v_f_536_){
_start:
{
lean_object* v_toArray_537_; lean_object* v___f_538_; size_t v_sz_539_; size_t v___x_540_; lean_object* v___x_541_; 
v_toArray_537_ = lean_ctor_get(v_self_534_, 1);
lean_inc_ref(v_toArray_537_);
lean_dec_ref(v_self_534_);
v___f_538_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_538_, 0, v_f_536_);
v_sz_539_ = lean_array_size(v_toArray_537_);
v___x_540_ = ((size_t)0ULL);
v___x_541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_533_, v_toArray_537_, v___f_538_, v_sz_539_, v___x_540_, v_init_535_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___boxed(lean_object* v_00_u03b1_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_m_545_, lean_object* v_00_u03b2_546_, lean_object* v_inst_547_, lean_object* v_self_548_, lean_object* v_init_549_, lean_object* v_f_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lake_OrdHashSet_forIn(v_00_u03b1_542_, v_inst_543_, v_inst_544_, v_m_545_, v_00_u03b2_546_, v_inst_547_, v_self_548_, v_init_549_, v_f_550_);
lean_dec_ref(v_inst_544_);
lean_dec_ref(v_inst_543_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0(lean_object* v___y_552_, lean_object* v_a_553_, lean_object* v_x_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = lean_apply_2(v___y_552_, v_a_553_, v___y_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1(lean_object* v_inst_557_, lean_object* v_00_u03b2_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_toArray_562_; lean_object* v___f_563_; size_t v_sz_564_; size_t v___x_565_; lean_object* v___x_566_; 
v_toArray_562_ = lean_ctor_get(v___y_559_, 1);
lean_inc_ref(v_toArray_562_);
lean_dec_ref(v___y_559_);
v___f_563_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_563_, 0, v___y_561_);
v_sz_564_ = lean_array_size(v_toArray_562_);
v___x_565_ = ((size_t)0ULL);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_557_, v_toArray_562_, v___f_563_, v_sz_564_, v___x_565_, v___y_560_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg(lean_object* v_inst_567_){
_start:
{
lean_object* v___f_568_; 
v___f_568_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_568_, 0, v_inst_567_);
return v___f_568_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad(lean_object* v_00_u03b1_569_, lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_m_572_, lean_object* v_inst_573_){
_start:
{
lean_object* v___f_574_; 
v___f_574_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_574_, 0, v_inst_573_);
return v___f_574_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_m_578_, lean_object* v_inst_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lake_OrdHashSet_instForInOfMonad(v_00_u03b1_575_, v_inst_576_, v_inst_577_, v_m_578_, v_inst_579_);
lean_dec_ref(v_inst_577_);
lean_dec_ref(v_inst_576_);
return v_res_580_;
}
}
lean_object* runtime_initialize_Std_Data_HashSet_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_OrdHashSet(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_OrdHashSet(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_OrdHashSet(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_OrdHashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_OrdHashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_OrdHashSet(builtin);
}
#ifdef __cplusplus
}
#endif
