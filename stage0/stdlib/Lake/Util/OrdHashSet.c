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
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all___redArg___lam__0(lean_object* v_f_171_, uint8_t v___x_172_, lean_object* v_v_173_){
_start:
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = lean_apply_1(v_f_171_, v_v_173_);
v___x_175_ = lean_unbox(v___x_174_);
if (v___x_175_ == 0)
{
return v___x_172_;
}
else
{
uint8_t v___x_176_; 
v___x_176_ = 0;
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___redArg___lam__0___boxed(lean_object* v_f_177_, lean_object* v___x_178_, lean_object* v_v_179_){
_start:
{
uint8_t v___x_79__boxed_180_; uint8_t v_res_181_; lean_object* v_r_182_; 
v___x_79__boxed_180_ = lean_unbox(v___x_178_);
v_res_181_ = l_Lake_OrdHashSet_all___redArg___lam__0(v_f_177_, v___x_79__boxed_180_, v_v_179_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all___redArg(lean_object* v_f_183_, lean_object* v_self_184_){
_start:
{
lean_object* v_toArray_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v_toArray_185_ = lean_ctor_get(v_self_184_, 1);
lean_inc_ref(v_toArray_185_);
lean_dec_ref(v_self_184_);
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = lean_array_get_size(v_toArray_185_);
v___x_188_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_189_ = lean_nat_dec_lt(v___x_186_, v___x_187_);
if (v___x_189_ == 0)
{
uint8_t v___x_190_; 
lean_dec_ref(v_toArray_185_);
lean_dec_ref(v_f_183_);
v___x_190_ = 1;
return v___x_190_;
}
else
{
if (v___x_189_ == 0)
{
lean_dec_ref(v_toArray_185_);
lean_dec_ref(v_f_183_);
return v___x_189_;
}
else
{
lean_object* v___x_191_; lean_object* v___f_192_; size_t v___x_193_; size_t v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_191_ = lean_box(v___x_189_);
v___f_192_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_192_, 0, v_f_183_);
lean_closure_set(v___f_192_, 1, v___x_191_);
v___x_193_ = ((size_t)0ULL);
v___x_194_ = lean_usize_of_nat(v___x_187_);
v___x_195_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_188_, v___f_192_, v_toArray_185_, v___x_193_, v___x_194_);
v___x_196_ = lean_unbox(v___x_195_);
lean_dec(v___x_195_);
if (v___x_196_ == 0)
{
return v___x_189_;
}
else
{
uint8_t v___x_197_; 
v___x_197_ = 0;
return v___x_197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___redArg___boxed(lean_object* v_f_198_, lean_object* v_self_199_){
_start:
{
uint8_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_Lake_OrdHashSet_all___redArg(v_f_198_, v_self_199_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all(lean_object* v_00_u03b1_202_, lean_object* v_inst_203_, lean_object* v_inst_204_, lean_object* v_f_205_, lean_object* v_self_206_){
_start:
{
lean_object* v_toArray_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v_toArray_207_ = lean_ctor_get(v_self_206_, 1);
lean_inc_ref(v_toArray_207_);
lean_dec_ref(v_self_206_);
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = lean_array_get_size(v_toArray_207_);
v___x_210_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_211_ = lean_nat_dec_lt(v___x_208_, v___x_209_);
if (v___x_211_ == 0)
{
uint8_t v___x_212_; 
lean_dec_ref(v_toArray_207_);
lean_dec_ref(v_f_205_);
v___x_212_ = 1;
return v___x_212_;
}
else
{
if (v___x_211_ == 0)
{
lean_dec_ref(v_toArray_207_);
lean_dec_ref(v_f_205_);
return v___x_211_;
}
else
{
lean_object* v___x_213_; lean_object* v___f_214_; size_t v___x_215_; size_t v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_213_ = lean_box(v___x_211_);
v___f_214_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_214_, 0, v_f_205_);
lean_closure_set(v___f_214_, 1, v___x_213_);
v___x_215_ = ((size_t)0ULL);
v___x_216_ = lean_usize_of_nat(v___x_209_);
v___x_217_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_210_, v___f_214_, v_toArray_207_, v___x_215_, v___x_216_);
v___x_218_ = lean_unbox(v___x_217_);
lean_dec(v___x_217_);
if (v___x_218_ == 0)
{
return v___x_211_;
}
else
{
uint8_t v___x_219_; 
v___x_219_ = 0;
return v___x_219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___boxed(lean_object* v_00_u03b1_220_, lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_f_223_, lean_object* v_self_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l_Lake_OrdHashSet_all(v_00_u03b1_220_, v_inst_221_, v_inst_222_, v_f_223_, v_self_224_);
lean_dec_ref(v_inst_222_);
lean_dec_ref(v_inst_221_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_any___redArg___lam__0(lean_object* v_f_227_, lean_object* v_x_228_){
_start:
{
lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_229_ = lean_apply_1(v_f_227_, v_x_228_);
v___x_230_ = lean_unbox(v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___redArg___lam__0___boxed(lean_object* v_f_231_, lean_object* v_x_232_){
_start:
{
uint8_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l_Lake_OrdHashSet_any___redArg___lam__0(v_f_231_, v_x_232_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_any___redArg(lean_object* v_f_235_, lean_object* v_self_236_){
_start:
{
lean_object* v_toArray_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v_toArray_237_ = lean_ctor_get(v_self_236_, 1);
lean_inc_ref(v_toArray_237_);
lean_dec_ref(v_self_236_);
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = lean_array_get_size(v_toArray_237_);
v___x_240_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_241_ = lean_nat_dec_lt(v___x_238_, v___x_239_);
if (v___x_241_ == 0)
{
lean_dec_ref(v_toArray_237_);
lean_dec_ref(v_f_235_);
return v___x_241_;
}
else
{
if (v___x_241_ == 0)
{
lean_dec_ref(v_toArray_237_);
lean_dec_ref(v_f_235_);
return v___x_241_;
}
else
{
lean_object* v___f_242_; size_t v___x_243_; size_t v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___f_242_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_242_, 0, v_f_235_);
v___x_243_ = ((size_t)0ULL);
v___x_244_ = lean_usize_of_nat(v___x_239_);
v___x_245_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_240_, v___f_242_, v_toArray_237_, v___x_243_, v___x_244_);
v___x_246_ = lean_unbox(v___x_245_);
lean_dec(v___x_245_);
return v___x_246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___redArg___boxed(lean_object* v_f_247_, lean_object* v_self_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l_Lake_OrdHashSet_any___redArg(v_f_247_, v_self_248_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_any(lean_object* v_00_u03b1_251_, lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_f_254_, lean_object* v_self_255_){
_start:
{
lean_object* v_toArray_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v_toArray_256_ = lean_ctor_get(v_self_255_, 1);
lean_inc_ref(v_toArray_256_);
lean_dec_ref(v_self_255_);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = lean_array_get_size(v_toArray_256_);
v___x_259_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_260_ = lean_nat_dec_lt(v___x_257_, v___x_258_);
if (v___x_260_ == 0)
{
lean_dec_ref(v_toArray_256_);
lean_dec_ref(v_f_254_);
return v___x_260_;
}
else
{
if (v___x_260_ == 0)
{
lean_dec_ref(v_toArray_256_);
lean_dec_ref(v_f_254_);
return v___x_260_;
}
else
{
lean_object* v___f_261_; size_t v___x_262_; size_t v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___f_261_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_261_, 0, v_f_254_);
v___x_262_ = ((size_t)0ULL);
v___x_263_ = lean_usize_of_nat(v___x_258_);
v___x_264_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_259_, v___f_261_, v_toArray_256_, v___x_262_, v___x_263_);
v___x_265_ = lean_unbox(v___x_264_);
lean_dec(v___x_264_);
return v___x_265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___boxed(lean_object* v_00_u03b1_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_f_269_, lean_object* v_self_270_){
_start:
{
uint8_t v_res_271_; lean_object* v_r_272_; 
v_res_271_ = l_Lake_OrdHashSet_any(v_00_u03b1_266_, v_inst_267_, v_inst_268_, v_f_269_, v_self_270_);
lean_dec_ref(v_inst_268_);
lean_dec_ref(v_inst_267_);
v_r_272_ = lean_box(v_res_271_);
return v_r_272_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___redArg___lam__0(lean_object* v_f_273_, lean_object* v_x1_274_, lean_object* v_x2_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = lean_apply_2(v_f_273_, v_x1_274_, v_x2_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___redArg(lean_object* v_f_277_, lean_object* v_init_278_, lean_object* v_self_279_){
_start:
{
lean_object* v_toArray_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v_toArray_280_ = lean_ctor_get(v_self_279_, 1);
lean_inc_ref(v_toArray_280_);
lean_dec_ref(v_self_279_);
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = lean_array_get_size(v_toArray_280_);
v___x_283_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_284_ = lean_nat_dec_lt(v___x_281_, v___x_282_);
if (v___x_284_ == 0)
{
lean_dec_ref(v_toArray_280_);
lean_dec(v_f_277_);
return v_init_278_;
}
else
{
lean_object* v___f_285_; uint8_t v___x_286_; 
v___f_285_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_285_, 0, v_f_277_);
v___x_286_ = lean_nat_dec_le(v___x_282_, v___x_282_);
if (v___x_286_ == 0)
{
if (v___x_284_ == 0)
{
lean_dec_ref(v___f_285_);
lean_dec_ref(v_toArray_280_);
return v_init_278_;
}
else
{
size_t v___x_287_; size_t v___x_288_; lean_object* v___x_289_; 
v___x_287_ = ((size_t)0ULL);
v___x_288_ = lean_usize_of_nat(v___x_282_);
v___x_289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_283_, v___f_285_, v_toArray_280_, v___x_287_, v___x_288_, v_init_278_);
return v___x_289_;
}
}
else
{
size_t v___x_290_; size_t v___x_291_; lean_object* v___x_292_; 
v___x_290_ = ((size_t)0ULL);
v___x_291_ = lean_usize_of_nat(v___x_282_);
v___x_292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_283_, v___f_285_, v_toArray_280_, v___x_290_, v___x_291_, v_init_278_);
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl(lean_object* v_00_u03b1_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_00_u03b2_296_, lean_object* v_f_297_, lean_object* v_init_298_, lean_object* v_self_299_){
_start:
{
lean_object* v_toArray_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_toArray_300_ = lean_ctor_get(v_self_299_, 1);
lean_inc_ref(v_toArray_300_);
lean_dec_ref(v_self_299_);
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = lean_array_get_size(v_toArray_300_);
v___x_303_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_304_ = lean_nat_dec_lt(v___x_301_, v___x_302_);
if (v___x_304_ == 0)
{
lean_dec_ref(v_toArray_300_);
lean_dec(v_f_297_);
return v_init_298_;
}
else
{
lean_object* v___f_305_; uint8_t v___x_306_; 
v___f_305_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_305_, 0, v_f_297_);
v___x_306_ = lean_nat_dec_le(v___x_302_, v___x_302_);
if (v___x_306_ == 0)
{
if (v___x_304_ == 0)
{
lean_dec_ref(v___f_305_);
lean_dec_ref(v_toArray_300_);
return v_init_298_;
}
else
{
size_t v___x_307_; size_t v___x_308_; lean_object* v___x_309_; 
v___x_307_ = ((size_t)0ULL);
v___x_308_ = lean_usize_of_nat(v___x_302_);
v___x_309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_303_, v___f_305_, v_toArray_300_, v___x_307_, v___x_308_, v_init_298_);
return v___x_309_;
}
}
else
{
size_t v___x_310_; size_t v___x_311_; lean_object* v___x_312_; 
v___x_310_ = ((size_t)0ULL);
v___x_311_ = lean_usize_of_nat(v___x_302_);
v___x_312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_303_, v___f_305_, v_toArray_300_, v___x_310_, v___x_311_, v_init_298_);
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___boxed(lean_object* v_00_u03b1_313_, lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_00_u03b2_316_, lean_object* v_f_317_, lean_object* v_init_318_, lean_object* v_self_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lake_OrdHashSet_foldl(v_00_u03b1_313_, v_inst_314_, v_inst_315_, v_00_u03b2_316_, v_f_317_, v_init_318_, v_self_319_);
lean_dec_ref(v_inst_315_);
lean_dec_ref(v_inst_314_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM___redArg(lean_object* v_inst_321_, lean_object* v_f_322_, lean_object* v_init_323_, lean_object* v_self_324_){
_start:
{
lean_object* v_toApplicative_325_; lean_object* v_toArray_326_; lean_object* v_toPure_327_; lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v_toApplicative_325_ = lean_ctor_get(v_inst_321_, 0);
v_toArray_326_ = lean_ctor_get(v_self_324_, 1);
lean_inc_ref(v_toArray_326_);
lean_dec_ref(v_self_324_);
v_toPure_327_ = lean_ctor_get(v_toApplicative_325_, 1);
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_array_get_size(v_toArray_326_);
v___x_330_ = lean_nat_dec_lt(v___x_328_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
lean_inc(v_toPure_327_);
lean_dec_ref(v_toArray_326_);
lean_dec(v_f_322_);
lean_dec_ref(v_inst_321_);
v___x_331_ = lean_apply_2(v_toPure_327_, lean_box(0), v_init_323_);
return v___x_331_;
}
else
{
uint8_t v___x_332_; 
v___x_332_ = lean_nat_dec_le(v___x_329_, v___x_329_);
if (v___x_332_ == 0)
{
if (v___x_330_ == 0)
{
lean_object* v___x_333_; 
lean_inc(v_toPure_327_);
lean_dec_ref(v_toArray_326_);
lean_dec(v_f_322_);
lean_dec_ref(v_inst_321_);
v___x_333_ = lean_apply_2(v_toPure_327_, lean_box(0), v_init_323_);
return v___x_333_;
}
else
{
size_t v___x_334_; size_t v___x_335_; lean_object* v___x_336_; 
v___x_334_ = ((size_t)0ULL);
v___x_335_ = lean_usize_of_nat(v___x_329_);
v___x_336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_321_, v_f_322_, v_toArray_326_, v___x_334_, v___x_335_, v_init_323_);
return v___x_336_;
}
}
else
{
size_t v___x_337_; size_t v___x_338_; lean_object* v___x_339_; 
v___x_337_ = ((size_t)0ULL);
v___x_338_ = lean_usize_of_nat(v___x_329_);
v___x_339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_321_, v_f_322_, v_toArray_326_, v___x_337_, v___x_338_, v_init_323_);
return v___x_339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM(lean_object* v_00_u03b1_340_, lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_m_343_, lean_object* v_00_u03b2_344_, lean_object* v_inst_345_, lean_object* v_f_346_, lean_object* v_init_347_, lean_object* v_self_348_){
_start:
{
lean_object* v_toApplicative_349_; lean_object* v_toArray_350_; lean_object* v_toPure_351_; lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v_toApplicative_349_ = lean_ctor_get(v_inst_345_, 0);
v_toArray_350_ = lean_ctor_get(v_self_348_, 1);
lean_inc_ref(v_toArray_350_);
lean_dec_ref(v_self_348_);
v_toPure_351_ = lean_ctor_get(v_toApplicative_349_, 1);
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = lean_array_get_size(v_toArray_350_);
v___x_354_ = lean_nat_dec_lt(v___x_352_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
lean_inc(v_toPure_351_);
lean_dec_ref(v_toArray_350_);
lean_dec(v_f_346_);
lean_dec_ref(v_inst_345_);
v___x_355_ = lean_apply_2(v_toPure_351_, lean_box(0), v_init_347_);
return v___x_355_;
}
else
{
uint8_t v___x_356_; 
v___x_356_ = lean_nat_dec_le(v___x_353_, v___x_353_);
if (v___x_356_ == 0)
{
if (v___x_354_ == 0)
{
lean_object* v___x_357_; 
lean_inc(v_toPure_351_);
lean_dec_ref(v_toArray_350_);
lean_dec(v_f_346_);
lean_dec_ref(v_inst_345_);
v___x_357_ = lean_apply_2(v_toPure_351_, lean_box(0), v_init_347_);
return v___x_357_;
}
else
{
size_t v___x_358_; size_t v___x_359_; lean_object* v___x_360_; 
v___x_358_ = ((size_t)0ULL);
v___x_359_ = lean_usize_of_nat(v___x_353_);
v___x_360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_345_, v_f_346_, v_toArray_350_, v___x_358_, v___x_359_, v_init_347_);
return v___x_360_;
}
}
else
{
size_t v___x_361_; size_t v___x_362_; lean_object* v___x_363_; 
v___x_361_ = ((size_t)0ULL);
v___x_362_ = lean_usize_of_nat(v___x_353_);
v___x_363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_345_, v_f_346_, v_toArray_350_, v___x_361_, v___x_362_, v_init_347_);
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM___boxed(lean_object* v_00_u03b1_364_, lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_m_367_, lean_object* v_00_u03b2_368_, lean_object* v_inst_369_, lean_object* v_f_370_, lean_object* v_init_371_, lean_object* v_self_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lake_OrdHashSet_foldlM(v_00_u03b1_364_, v_inst_365_, v_inst_366_, v_m_367_, v_00_u03b2_368_, v_inst_369_, v_f_370_, v_init_371_, v_self_372_);
lean_dec_ref(v_inst_366_);
lean_dec_ref(v_inst_365_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr___redArg(lean_object* v_f_374_, lean_object* v_init_375_, lean_object* v_self_376_){
_start:
{
lean_object* v_toArray_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v_toArray_377_ = lean_ctor_get(v_self_376_, 1);
lean_inc_ref(v_toArray_377_);
lean_dec_ref(v_self_376_);
v___x_378_ = lean_array_get_size(v_toArray_377_);
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_381_ = lean_nat_dec_lt(v___x_379_, v___x_378_);
if (v___x_381_ == 0)
{
lean_dec_ref(v_toArray_377_);
lean_dec(v_f_374_);
return v_init_375_;
}
else
{
lean_object* v___f_382_; size_t v___x_383_; size_t v___x_384_; lean_object* v___x_385_; 
v___f_382_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_382_, 0, v_f_374_);
v___x_383_ = lean_usize_of_nat(v___x_378_);
v___x_384_ = ((size_t)0ULL);
v___x_385_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_380_, v___f_382_, v_toArray_377_, v___x_383_, v___x_384_, v_init_375_);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr(lean_object* v_00_u03b1_386_, lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_00_u03b2_389_, lean_object* v_f_390_, lean_object* v_init_391_, lean_object* v_self_392_){
_start:
{
lean_object* v_toArray_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v_toArray_393_ = lean_ctor_get(v_self_392_, 1);
lean_inc_ref(v_toArray_393_);
lean_dec_ref(v_self_392_);
v___x_394_ = lean_array_get_size(v_toArray_393_);
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_397_ = lean_nat_dec_lt(v___x_395_, v___x_394_);
if (v___x_397_ == 0)
{
lean_dec_ref(v_toArray_393_);
lean_dec(v_f_390_);
return v_init_391_;
}
else
{
lean_object* v___f_398_; size_t v___x_399_; size_t v___x_400_; lean_object* v___x_401_; 
v___f_398_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_398_, 0, v_f_390_);
v___x_399_ = lean_usize_of_nat(v___x_394_);
v___x_400_ = ((size_t)0ULL);
v___x_401_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_396_, v___f_398_, v_toArray_393_, v___x_399_, v___x_400_, v_init_391_);
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr___boxed(lean_object* v_00_u03b1_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_00_u03b2_405_, lean_object* v_f_406_, lean_object* v_init_407_, lean_object* v_self_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lake_OrdHashSet_foldr(v_00_u03b1_402_, v_inst_403_, v_inst_404_, v_00_u03b2_405_, v_f_406_, v_init_407_, v_self_408_);
lean_dec_ref(v_inst_404_);
lean_dec_ref(v_inst_403_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM___redArg(lean_object* v_inst_410_, lean_object* v_f_411_, lean_object* v_init_412_, lean_object* v_self_413_){
_start:
{
lean_object* v_toApplicative_414_; lean_object* v_toArray_415_; lean_object* v_toPure_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_toApplicative_414_ = lean_ctor_get(v_inst_410_, 0);
v_toArray_415_ = lean_ctor_get(v_self_413_, 1);
lean_inc_ref(v_toArray_415_);
lean_dec_ref(v_self_413_);
v_toPure_416_ = lean_ctor_get(v_toApplicative_414_, 1);
v___x_417_ = lean_array_get_size(v_toArray_415_);
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_nat_dec_lt(v___x_418_, v___x_417_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; 
lean_inc(v_toPure_416_);
lean_dec_ref(v_toArray_415_);
lean_dec(v_f_411_);
lean_dec_ref(v_inst_410_);
v___x_420_ = lean_apply_2(v_toPure_416_, lean_box(0), v_init_412_);
return v___x_420_;
}
else
{
size_t v___x_421_; size_t v___x_422_; lean_object* v___x_423_; 
v___x_421_ = lean_usize_of_nat(v___x_417_);
v___x_422_ = ((size_t)0ULL);
v___x_423_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_410_, v_f_411_, v_toArray_415_, v___x_421_, v___x_422_, v_init_412_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM(lean_object* v_00_u03b1_424_, lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_m_427_, lean_object* v_00_u03b2_428_, lean_object* v_inst_429_, lean_object* v_f_430_, lean_object* v_init_431_, lean_object* v_self_432_){
_start:
{
lean_object* v_toApplicative_433_; lean_object* v_toArray_434_; lean_object* v_toPure_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v_toApplicative_433_ = lean_ctor_get(v_inst_429_, 0);
v_toArray_434_ = lean_ctor_get(v_self_432_, 1);
lean_inc_ref(v_toArray_434_);
lean_dec_ref(v_self_432_);
v_toPure_435_ = lean_ctor_get(v_toApplicative_433_, 1);
v___x_436_ = lean_array_get_size(v_toArray_434_);
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = lean_nat_dec_lt(v___x_437_, v___x_436_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
lean_inc(v_toPure_435_);
lean_dec_ref(v_toArray_434_);
lean_dec(v_f_430_);
lean_dec_ref(v_inst_429_);
v___x_439_ = lean_apply_2(v_toPure_435_, lean_box(0), v_init_431_);
return v___x_439_;
}
else
{
size_t v___x_440_; size_t v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_usize_of_nat(v___x_436_);
v___x_441_ = ((size_t)0ULL);
v___x_442_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_429_, v_f_430_, v_toArray_434_, v___x_440_, v___x_441_, v_init_431_);
return v___x_442_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM___boxed(lean_object* v_00_u03b1_443_, lean_object* v_inst_444_, lean_object* v_inst_445_, lean_object* v_m_446_, lean_object* v_00_u03b2_447_, lean_object* v_inst_448_, lean_object* v_f_449_, lean_object* v_init_450_, lean_object* v_self_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lake_OrdHashSet_foldrM(v_00_u03b1_443_, v_inst_444_, v_inst_445_, v_m_446_, v_00_u03b2_447_, v_inst_448_, v_f_449_, v_init_450_, v_self_451_);
lean_dec_ref(v_inst_445_);
lean_dec_ref(v_inst_444_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___redArg___lam__0(lean_object* v_f_453_, lean_object* v_x_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = lean_apply_1(v_f_453_, v___y_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___redArg(lean_object* v_inst_457_, lean_object* v_f_458_, lean_object* v_self_459_){
_start:
{
lean_object* v_toApplicative_460_; lean_object* v_toArray_461_; lean_object* v_toPure_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v_toApplicative_460_ = lean_ctor_get(v_inst_457_, 0);
v_toArray_461_ = lean_ctor_get(v_self_459_, 1);
lean_inc_ref(v_toArray_461_);
lean_dec_ref(v_self_459_);
v_toPure_462_ = lean_ctor_get(v_toApplicative_460_, 1);
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_464_ = lean_array_get_size(v_toArray_461_);
v___x_465_ = lean_box(0);
v___x_466_ = lean_nat_dec_lt(v___x_463_, v___x_464_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
lean_inc(v_toPure_462_);
lean_dec_ref(v_toArray_461_);
lean_dec(v_f_458_);
lean_dec_ref(v_inst_457_);
v___x_467_ = lean_apply_2(v_toPure_462_, lean_box(0), v___x_465_);
return v___x_467_;
}
else
{
lean_object* v___f_468_; uint8_t v___x_469_; 
v___f_468_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_468_, 0, v_f_458_);
v___x_469_ = lean_nat_dec_le(v___x_464_, v___x_464_);
if (v___x_469_ == 0)
{
if (v___x_466_ == 0)
{
lean_object* v___x_470_; 
lean_inc(v_toPure_462_);
lean_dec_ref(v___f_468_);
lean_dec_ref(v_toArray_461_);
lean_dec_ref(v_inst_457_);
v___x_470_ = lean_apply_2(v_toPure_462_, lean_box(0), v___x_465_);
return v___x_470_;
}
else
{
size_t v___x_471_; size_t v___x_472_; lean_object* v___x_473_; 
v___x_471_ = ((size_t)0ULL);
v___x_472_ = lean_usize_of_nat(v___x_464_);
v___x_473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_457_, v___f_468_, v_toArray_461_, v___x_471_, v___x_472_, v___x_465_);
return v___x_473_;
}
}
else
{
size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; 
v___x_474_ = ((size_t)0ULL);
v___x_475_ = lean_usize_of_nat(v___x_464_);
v___x_476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_457_, v___f_468_, v_toArray_461_, v___x_474_, v___x_475_, v___x_465_);
return v___x_476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM(lean_object* v_00_u03b1_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_m_480_, lean_object* v_inst_481_, lean_object* v_f_482_, lean_object* v_self_483_){
_start:
{
lean_object* v_toApplicative_484_; lean_object* v_toArray_485_; lean_object* v_toPure_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v_toApplicative_484_ = lean_ctor_get(v_inst_481_, 0);
v_toArray_485_ = lean_ctor_get(v_self_483_, 1);
lean_inc_ref(v_toArray_485_);
lean_dec_ref(v_self_483_);
v_toPure_486_ = lean_ctor_get(v_toApplicative_484_, 1);
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = lean_array_get_size(v_toArray_485_);
v___x_489_ = lean_box(0);
v___x_490_ = lean_nat_dec_lt(v___x_487_, v___x_488_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
lean_inc(v_toPure_486_);
lean_dec_ref(v_toArray_485_);
lean_dec(v_f_482_);
lean_dec_ref(v_inst_481_);
v___x_491_ = lean_apply_2(v_toPure_486_, lean_box(0), v___x_489_);
return v___x_491_;
}
else
{
lean_object* v___f_492_; uint8_t v___x_493_; 
v___f_492_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_492_, 0, v_f_482_);
v___x_493_ = lean_nat_dec_le(v___x_488_, v___x_488_);
if (v___x_493_ == 0)
{
if (v___x_490_ == 0)
{
lean_object* v___x_494_; 
lean_inc(v_toPure_486_);
lean_dec_ref(v___f_492_);
lean_dec_ref(v_toArray_485_);
lean_dec_ref(v_inst_481_);
v___x_494_ = lean_apply_2(v_toPure_486_, lean_box(0), v___x_489_);
return v___x_494_;
}
else
{
size_t v___x_495_; size_t v___x_496_; lean_object* v___x_497_; 
v___x_495_ = ((size_t)0ULL);
v___x_496_ = lean_usize_of_nat(v___x_488_);
v___x_497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_481_, v___f_492_, v_toArray_485_, v___x_495_, v___x_496_, v___x_489_);
return v___x_497_;
}
}
else
{
size_t v___x_498_; size_t v___x_499_; lean_object* v___x_500_; 
v___x_498_ = ((size_t)0ULL);
v___x_499_ = lean_usize_of_nat(v___x_488_);
v___x_500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_481_, v___f_492_, v_toArray_485_, v___x_498_, v___x_499_, v___x_489_);
return v___x_500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___boxed(lean_object* v_00_u03b1_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_m_504_, lean_object* v_inst_505_, lean_object* v_f_506_, lean_object* v_self_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lake_OrdHashSet_forM(v_00_u03b1_501_, v_inst_502_, v_inst_503_, v_m_504_, v_inst_505_, v_f_506_, v_self_507_);
lean_dec_ref(v_inst_503_);
lean_dec_ref(v_inst_502_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___redArg___lam__0(lean_object* v_f_509_, lean_object* v_a_510_, lean_object* v_x_511_, lean_object* v___y_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = lean_apply_2(v_f_509_, v_a_510_, v___y_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___redArg(lean_object* v_inst_514_, lean_object* v_self_515_, lean_object* v_init_516_, lean_object* v_f_517_){
_start:
{
lean_object* v_toArray_518_; lean_object* v___f_519_; size_t v_sz_520_; size_t v___x_521_; lean_object* v___x_522_; 
v_toArray_518_ = lean_ctor_get(v_self_515_, 1);
lean_inc_ref(v_toArray_518_);
lean_dec_ref(v_self_515_);
v___f_519_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_519_, 0, v_f_517_);
v_sz_520_ = lean_array_size(v_toArray_518_);
v___x_521_ = ((size_t)0ULL);
v___x_522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_514_, v_toArray_518_, v___f_519_, v_sz_520_, v___x_521_, v_init_516_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn(lean_object* v_00_u03b1_523_, lean_object* v_inst_524_, lean_object* v_inst_525_, lean_object* v_m_526_, lean_object* v_00_u03b2_527_, lean_object* v_inst_528_, lean_object* v_self_529_, lean_object* v_init_530_, lean_object* v_f_531_){
_start:
{
lean_object* v_toArray_532_; lean_object* v___f_533_; size_t v_sz_534_; size_t v___x_535_; lean_object* v___x_536_; 
v_toArray_532_ = lean_ctor_get(v_self_529_, 1);
lean_inc_ref(v_toArray_532_);
lean_dec_ref(v_self_529_);
v___f_533_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_533_, 0, v_f_531_);
v_sz_534_ = lean_array_size(v_toArray_532_);
v___x_535_ = ((size_t)0ULL);
v___x_536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_528_, v_toArray_532_, v___f_533_, v_sz_534_, v___x_535_, v_init_530_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___boxed(lean_object* v_00_u03b1_537_, lean_object* v_inst_538_, lean_object* v_inst_539_, lean_object* v_m_540_, lean_object* v_00_u03b2_541_, lean_object* v_inst_542_, lean_object* v_self_543_, lean_object* v_init_544_, lean_object* v_f_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lake_OrdHashSet_forIn(v_00_u03b1_537_, v_inst_538_, v_inst_539_, v_m_540_, v_00_u03b2_541_, v_inst_542_, v_self_543_, v_init_544_, v_f_545_);
lean_dec_ref(v_inst_539_);
lean_dec_ref(v_inst_538_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0(lean_object* v___y_547_, lean_object* v_a_548_, lean_object* v_x_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = lean_apply_2(v___y_547_, v_a_548_, v___y_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1(lean_object* v_inst_552_, lean_object* v_00_u03b2_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_toArray_557_; lean_object* v___f_558_; size_t v_sz_559_; size_t v___x_560_; lean_object* v___x_561_; 
v_toArray_557_ = lean_ctor_get(v___y_554_, 1);
lean_inc_ref(v_toArray_557_);
lean_dec_ref(v___y_554_);
v___f_558_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_558_, 0, v___y_556_);
v_sz_559_ = lean_array_size(v_toArray_557_);
v___x_560_ = ((size_t)0ULL);
v___x_561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_552_, v_toArray_557_, v___f_558_, v_sz_559_, v___x_560_, v___y_555_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg(lean_object* v_inst_562_){
_start:
{
lean_object* v___f_563_; 
v___f_563_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_563_, 0, v_inst_562_);
return v___f_563_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad(lean_object* v_00_u03b1_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_m_567_, lean_object* v_inst_568_){
_start:
{
lean_object* v___f_569_; 
v___f_569_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_569_, 0, v_inst_568_);
return v___f_569_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_m_573_, lean_object* v_inst_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lake_OrdHashSet_instForInOfMonad(v_00_u03b1_570_, v_inst_571_, v_inst_572_, v_m_573_, v_inst_574_);
lean_dec_ref(v_inst_572_);
lean_dec_ref(v_inst_571_);
return v_res_575_;
}
}
lean_object* runtime_initialize_Std_Data_HashSet_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_OrdHashSet(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
