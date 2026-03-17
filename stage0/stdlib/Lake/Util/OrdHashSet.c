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
uint8_t v___x_83__boxed_180_; uint8_t v_res_181_; lean_object* v_r_182_; 
v___x_83__boxed_180_ = lean_unbox(v___x_178_);
v_res_181_ = l_Lake_OrdHashSet_all___redArg___lam__0(v_f_177_, v___x_83__boxed_180_, v_v_179_);
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
lean_object* v_toArray_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v_toArray_325_ = lean_ctor_get(v_self_324_, 1);
lean_inc_ref(v_toArray_325_);
lean_dec_ref(v_self_324_);
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = lean_array_get_size(v_toArray_325_);
v___x_328_ = lean_nat_dec_lt(v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v_toApplicative_329_; lean_object* v_toPure_330_; lean_object* v___x_331_; 
lean_dec_ref(v_toArray_325_);
lean_dec(v_f_322_);
v_toApplicative_329_ = lean_ctor_get(v_inst_321_, 0);
lean_inc_ref(v_toApplicative_329_);
lean_dec_ref(v_inst_321_);
v_toPure_330_ = lean_ctor_get(v_toApplicative_329_, 1);
lean_inc(v_toPure_330_);
lean_dec_ref(v_toApplicative_329_);
v___x_331_ = lean_apply_2(v_toPure_330_, lean_box(0), v_init_323_);
return v___x_331_;
}
else
{
uint8_t v___x_332_; 
v___x_332_ = lean_nat_dec_le(v___x_327_, v___x_327_);
if (v___x_332_ == 0)
{
if (v___x_328_ == 0)
{
lean_object* v_toApplicative_333_; lean_object* v_toPure_334_; lean_object* v___x_335_; 
lean_dec_ref(v_toArray_325_);
lean_dec(v_f_322_);
v_toApplicative_333_ = lean_ctor_get(v_inst_321_, 0);
lean_inc_ref(v_toApplicative_333_);
lean_dec_ref(v_inst_321_);
v_toPure_334_ = lean_ctor_get(v_toApplicative_333_, 1);
lean_inc(v_toPure_334_);
lean_dec_ref(v_toApplicative_333_);
v___x_335_ = lean_apply_2(v_toPure_334_, lean_box(0), v_init_323_);
return v___x_335_;
}
else
{
size_t v___x_336_; size_t v___x_337_; lean_object* v___x_338_; 
v___x_336_ = ((size_t)0ULL);
v___x_337_ = lean_usize_of_nat(v___x_327_);
v___x_338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_321_, v_f_322_, v_toArray_325_, v___x_336_, v___x_337_, v_init_323_);
return v___x_338_;
}
}
else
{
size_t v___x_339_; size_t v___x_340_; lean_object* v___x_341_; 
v___x_339_ = ((size_t)0ULL);
v___x_340_ = lean_usize_of_nat(v___x_327_);
v___x_341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_321_, v_f_322_, v_toArray_325_, v___x_339_, v___x_340_, v_init_323_);
return v___x_341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM(lean_object* v_00_u03b1_342_, lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_m_345_, lean_object* v_00_u03b2_346_, lean_object* v_inst_347_, lean_object* v_f_348_, lean_object* v_init_349_, lean_object* v_self_350_){
_start:
{
lean_object* v_toArray_351_; lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v_toArray_351_ = lean_ctor_get(v_self_350_, 1);
lean_inc_ref(v_toArray_351_);
lean_dec_ref(v_self_350_);
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = lean_array_get_size(v_toArray_351_);
v___x_354_ = lean_nat_dec_lt(v___x_352_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v_toApplicative_355_; lean_object* v_toPure_356_; lean_object* v___x_357_; 
lean_dec_ref(v_toArray_351_);
lean_dec(v_f_348_);
v_toApplicative_355_ = lean_ctor_get(v_inst_347_, 0);
lean_inc_ref(v_toApplicative_355_);
lean_dec_ref(v_inst_347_);
v_toPure_356_ = lean_ctor_get(v_toApplicative_355_, 1);
lean_inc(v_toPure_356_);
lean_dec_ref(v_toApplicative_355_);
v___x_357_ = lean_apply_2(v_toPure_356_, lean_box(0), v_init_349_);
return v___x_357_;
}
else
{
uint8_t v___x_358_; 
v___x_358_ = lean_nat_dec_le(v___x_353_, v___x_353_);
if (v___x_358_ == 0)
{
if (v___x_354_ == 0)
{
lean_object* v_toApplicative_359_; lean_object* v_toPure_360_; lean_object* v___x_361_; 
lean_dec_ref(v_toArray_351_);
lean_dec(v_f_348_);
v_toApplicative_359_ = lean_ctor_get(v_inst_347_, 0);
lean_inc_ref(v_toApplicative_359_);
lean_dec_ref(v_inst_347_);
v_toPure_360_ = lean_ctor_get(v_toApplicative_359_, 1);
lean_inc(v_toPure_360_);
lean_dec_ref(v_toApplicative_359_);
v___x_361_ = lean_apply_2(v_toPure_360_, lean_box(0), v_init_349_);
return v___x_361_;
}
else
{
size_t v___x_362_; size_t v___x_363_; lean_object* v___x_364_; 
v___x_362_ = ((size_t)0ULL);
v___x_363_ = lean_usize_of_nat(v___x_353_);
v___x_364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_347_, v_f_348_, v_toArray_351_, v___x_362_, v___x_363_, v_init_349_);
return v___x_364_;
}
}
else
{
size_t v___x_365_; size_t v___x_366_; lean_object* v___x_367_; 
v___x_365_ = ((size_t)0ULL);
v___x_366_ = lean_usize_of_nat(v___x_353_);
v___x_367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_347_, v_f_348_, v_toArray_351_, v___x_365_, v___x_366_, v_init_349_);
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM___boxed(lean_object* v_00_u03b1_368_, lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_m_371_, lean_object* v_00_u03b2_372_, lean_object* v_inst_373_, lean_object* v_f_374_, lean_object* v_init_375_, lean_object* v_self_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lake_OrdHashSet_foldlM(v_00_u03b1_368_, v_inst_369_, v_inst_370_, v_m_371_, v_00_u03b2_372_, v_inst_373_, v_f_374_, v_init_375_, v_self_376_);
lean_dec_ref(v_inst_370_);
lean_dec_ref(v_inst_369_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr___redArg(lean_object* v_f_378_, lean_object* v_init_379_, lean_object* v_self_380_){
_start:
{
lean_object* v_toArray_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v_toArray_381_ = lean_ctor_get(v_self_380_, 1);
lean_inc_ref(v_toArray_381_);
lean_dec_ref(v_self_380_);
v___x_382_ = lean_array_get_size(v_toArray_381_);
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_385_ = lean_nat_dec_lt(v___x_383_, v___x_382_);
if (v___x_385_ == 0)
{
lean_dec_ref(v_toArray_381_);
lean_dec(v_f_378_);
return v_init_379_;
}
else
{
lean_object* v___f_386_; size_t v___x_387_; size_t v___x_388_; lean_object* v___x_389_; 
v___f_386_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_386_, 0, v_f_378_);
v___x_387_ = lean_usize_of_nat(v___x_382_);
v___x_388_ = ((size_t)0ULL);
v___x_389_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_384_, v___f_386_, v_toArray_381_, v___x_387_, v___x_388_, v_init_379_);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr(lean_object* v_00_u03b1_390_, lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_00_u03b2_393_, lean_object* v_f_394_, lean_object* v_init_395_, lean_object* v_self_396_){
_start:
{
lean_object* v_toArray_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_toArray_397_ = lean_ctor_get(v_self_396_, 1);
lean_inc_ref(v_toArray_397_);
lean_dec_ref(v_self_396_);
v___x_398_ = lean_array_get_size(v_toArray_397_);
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_401_ = lean_nat_dec_lt(v___x_399_, v___x_398_);
if (v___x_401_ == 0)
{
lean_dec_ref(v_toArray_397_);
lean_dec(v_f_394_);
return v_init_395_;
}
else
{
lean_object* v___f_402_; size_t v___x_403_; size_t v___x_404_; lean_object* v___x_405_; 
v___f_402_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_402_, 0, v_f_394_);
v___x_403_ = lean_usize_of_nat(v___x_398_);
v___x_404_ = ((size_t)0ULL);
v___x_405_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_400_, v___f_402_, v_toArray_397_, v___x_403_, v___x_404_, v_init_395_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr___boxed(lean_object* v_00_u03b1_406_, lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_00_u03b2_409_, lean_object* v_f_410_, lean_object* v_init_411_, lean_object* v_self_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lake_OrdHashSet_foldr(v_00_u03b1_406_, v_inst_407_, v_inst_408_, v_00_u03b2_409_, v_f_410_, v_init_411_, v_self_412_);
lean_dec_ref(v_inst_408_);
lean_dec_ref(v_inst_407_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM___redArg(lean_object* v_inst_414_, lean_object* v_f_415_, lean_object* v_init_416_, lean_object* v_self_417_){
_start:
{
lean_object* v_toArray_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v_toArray_418_ = lean_ctor_get(v_self_417_, 1);
lean_inc_ref(v_toArray_418_);
lean_dec_ref(v_self_417_);
v___x_419_ = lean_array_get_size(v_toArray_418_);
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = lean_nat_dec_lt(v___x_420_, v___x_419_);
if (v___x_421_ == 0)
{
lean_object* v_toApplicative_422_; lean_object* v_toPure_423_; lean_object* v___x_424_; 
lean_dec_ref(v_toArray_418_);
lean_dec(v_f_415_);
v_toApplicative_422_ = lean_ctor_get(v_inst_414_, 0);
lean_inc_ref(v_toApplicative_422_);
lean_dec_ref(v_inst_414_);
v_toPure_423_ = lean_ctor_get(v_toApplicative_422_, 1);
lean_inc(v_toPure_423_);
lean_dec_ref(v_toApplicative_422_);
v___x_424_ = lean_apply_2(v_toPure_423_, lean_box(0), v_init_416_);
return v___x_424_;
}
else
{
size_t v___x_425_; size_t v___x_426_; lean_object* v___x_427_; 
v___x_425_ = lean_usize_of_nat(v___x_419_);
v___x_426_ = ((size_t)0ULL);
v___x_427_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_414_, v_f_415_, v_toArray_418_, v___x_425_, v___x_426_, v_init_416_);
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM(lean_object* v_00_u03b1_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_m_431_, lean_object* v_00_u03b2_432_, lean_object* v_inst_433_, lean_object* v_f_434_, lean_object* v_init_435_, lean_object* v_self_436_){
_start:
{
lean_object* v_toArray_437_; lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v_toArray_437_ = lean_ctor_get(v_self_436_, 1);
lean_inc_ref(v_toArray_437_);
lean_dec_ref(v_self_436_);
v___x_438_ = lean_array_get_size(v_toArray_437_);
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_nat_dec_lt(v___x_439_, v___x_438_);
if (v___x_440_ == 0)
{
lean_object* v_toApplicative_441_; lean_object* v_toPure_442_; lean_object* v___x_443_; 
lean_dec_ref(v_toArray_437_);
lean_dec(v_f_434_);
v_toApplicative_441_ = lean_ctor_get(v_inst_433_, 0);
lean_inc_ref(v_toApplicative_441_);
lean_dec_ref(v_inst_433_);
v_toPure_442_ = lean_ctor_get(v_toApplicative_441_, 1);
lean_inc(v_toPure_442_);
lean_dec_ref(v_toApplicative_441_);
v___x_443_ = lean_apply_2(v_toPure_442_, lean_box(0), v_init_435_);
return v___x_443_;
}
else
{
size_t v___x_444_; size_t v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_usize_of_nat(v___x_438_);
v___x_445_ = ((size_t)0ULL);
v___x_446_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_433_, v_f_434_, v_toArray_437_, v___x_444_, v___x_445_, v_init_435_);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM___boxed(lean_object* v_00_u03b1_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_m_450_, lean_object* v_00_u03b2_451_, lean_object* v_inst_452_, lean_object* v_f_453_, lean_object* v_init_454_, lean_object* v_self_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lake_OrdHashSet_foldrM(v_00_u03b1_447_, v_inst_448_, v_inst_449_, v_m_450_, v_00_u03b2_451_, v_inst_452_, v_f_453_, v_init_454_, v_self_455_);
lean_dec_ref(v_inst_449_);
lean_dec_ref(v_inst_448_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___redArg___lam__0(lean_object* v_f_457_, lean_object* v_x_458_, lean_object* v___y_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = lean_apply_1(v_f_457_, v___y_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___redArg(lean_object* v_inst_461_, lean_object* v_f_462_, lean_object* v_self_463_){
_start:
{
lean_object* v_toArray_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v_toArray_464_ = lean_ctor_get(v_self_463_, 1);
lean_inc_ref(v_toArray_464_);
lean_dec_ref(v_self_463_);
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_array_get_size(v_toArray_464_);
v___x_467_ = lean_box(0);
v___x_468_ = lean_nat_dec_lt(v___x_465_, v___x_466_);
if (v___x_468_ == 0)
{
lean_object* v_toApplicative_469_; lean_object* v_toPure_470_; lean_object* v___x_471_; 
lean_dec_ref(v_toArray_464_);
lean_dec(v_f_462_);
v_toApplicative_469_ = lean_ctor_get(v_inst_461_, 0);
lean_inc_ref(v_toApplicative_469_);
lean_dec_ref(v_inst_461_);
v_toPure_470_ = lean_ctor_get(v_toApplicative_469_, 1);
lean_inc(v_toPure_470_);
lean_dec_ref(v_toApplicative_469_);
v___x_471_ = lean_apply_2(v_toPure_470_, lean_box(0), v___x_467_);
return v___x_471_;
}
else
{
lean_object* v___f_472_; uint8_t v___x_473_; 
v___f_472_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_472_, 0, v_f_462_);
v___x_473_ = lean_nat_dec_le(v___x_466_, v___x_466_);
if (v___x_473_ == 0)
{
if (v___x_468_ == 0)
{
lean_object* v_toApplicative_474_; lean_object* v_toPure_475_; lean_object* v___x_476_; 
lean_dec_ref(v___f_472_);
lean_dec_ref(v_toArray_464_);
v_toApplicative_474_ = lean_ctor_get(v_inst_461_, 0);
lean_inc_ref(v_toApplicative_474_);
lean_dec_ref(v_inst_461_);
v_toPure_475_ = lean_ctor_get(v_toApplicative_474_, 1);
lean_inc(v_toPure_475_);
lean_dec_ref(v_toApplicative_474_);
v___x_476_ = lean_apply_2(v_toPure_475_, lean_box(0), v___x_467_);
return v___x_476_;
}
else
{
size_t v___x_477_; size_t v___x_478_; lean_object* v___x_479_; 
v___x_477_ = ((size_t)0ULL);
v___x_478_ = lean_usize_of_nat(v___x_466_);
v___x_479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_461_, v___f_472_, v_toArray_464_, v___x_477_, v___x_478_, v___x_467_);
return v___x_479_;
}
}
else
{
size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; 
v___x_480_ = ((size_t)0ULL);
v___x_481_ = lean_usize_of_nat(v___x_466_);
v___x_482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_461_, v___f_472_, v_toArray_464_, v___x_480_, v___x_481_, v___x_467_);
return v___x_482_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM(lean_object* v_00_u03b1_483_, lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_m_486_, lean_object* v_inst_487_, lean_object* v_f_488_, lean_object* v_self_489_){
_start:
{
lean_object* v_toArray_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v_toArray_490_ = lean_ctor_get(v_self_489_, 1);
lean_inc_ref(v_toArray_490_);
lean_dec_ref(v_self_489_);
v___x_491_ = lean_unsigned_to_nat(0u);
v___x_492_ = lean_array_get_size(v_toArray_490_);
v___x_493_ = lean_box(0);
v___x_494_ = lean_nat_dec_lt(v___x_491_, v___x_492_);
if (v___x_494_ == 0)
{
lean_object* v_toApplicative_495_; lean_object* v_toPure_496_; lean_object* v___x_497_; 
lean_dec_ref(v_toArray_490_);
lean_dec(v_f_488_);
v_toApplicative_495_ = lean_ctor_get(v_inst_487_, 0);
lean_inc_ref(v_toApplicative_495_);
lean_dec_ref(v_inst_487_);
v_toPure_496_ = lean_ctor_get(v_toApplicative_495_, 1);
lean_inc(v_toPure_496_);
lean_dec_ref(v_toApplicative_495_);
v___x_497_ = lean_apply_2(v_toPure_496_, lean_box(0), v___x_493_);
return v___x_497_;
}
else
{
lean_object* v___f_498_; uint8_t v___x_499_; 
v___f_498_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_498_, 0, v_f_488_);
v___x_499_ = lean_nat_dec_le(v___x_492_, v___x_492_);
if (v___x_499_ == 0)
{
if (v___x_494_ == 0)
{
lean_object* v_toApplicative_500_; lean_object* v_toPure_501_; lean_object* v___x_502_; 
lean_dec_ref(v___f_498_);
lean_dec_ref(v_toArray_490_);
v_toApplicative_500_ = lean_ctor_get(v_inst_487_, 0);
lean_inc_ref(v_toApplicative_500_);
lean_dec_ref(v_inst_487_);
v_toPure_501_ = lean_ctor_get(v_toApplicative_500_, 1);
lean_inc(v_toPure_501_);
lean_dec_ref(v_toApplicative_500_);
v___x_502_ = lean_apply_2(v_toPure_501_, lean_box(0), v___x_493_);
return v___x_502_;
}
else
{
size_t v___x_503_; size_t v___x_504_; lean_object* v___x_505_; 
v___x_503_ = ((size_t)0ULL);
v___x_504_ = lean_usize_of_nat(v___x_492_);
v___x_505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_487_, v___f_498_, v_toArray_490_, v___x_503_, v___x_504_, v___x_493_);
return v___x_505_;
}
}
else
{
size_t v___x_506_; size_t v___x_507_; lean_object* v___x_508_; 
v___x_506_ = ((size_t)0ULL);
v___x_507_ = lean_usize_of_nat(v___x_492_);
v___x_508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_487_, v___f_498_, v_toArray_490_, v___x_506_, v___x_507_, v___x_493_);
return v___x_508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___boxed(lean_object* v_00_u03b1_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_m_512_, lean_object* v_inst_513_, lean_object* v_f_514_, lean_object* v_self_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lake_OrdHashSet_forM(v_00_u03b1_509_, v_inst_510_, v_inst_511_, v_m_512_, v_inst_513_, v_f_514_, v_self_515_);
lean_dec_ref(v_inst_511_);
lean_dec_ref(v_inst_510_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___redArg___lam__0(lean_object* v_f_517_, lean_object* v_a_518_, lean_object* v_x_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = lean_apply_2(v_f_517_, v_a_518_, v___y_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___redArg(lean_object* v_inst_522_, lean_object* v_self_523_, lean_object* v_init_524_, lean_object* v_f_525_){
_start:
{
lean_object* v_toArray_526_; lean_object* v___f_527_; size_t v_sz_528_; size_t v___x_529_; lean_object* v___x_530_; 
v_toArray_526_ = lean_ctor_get(v_self_523_, 1);
lean_inc_ref(v_toArray_526_);
lean_dec_ref(v_self_523_);
v___f_527_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_527_, 0, v_f_525_);
v_sz_528_ = lean_array_size(v_toArray_526_);
v___x_529_ = ((size_t)0ULL);
v___x_530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_522_, v_toArray_526_, v___f_527_, v_sz_528_, v___x_529_, v_init_524_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn(lean_object* v_00_u03b1_531_, lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_m_534_, lean_object* v_00_u03b2_535_, lean_object* v_inst_536_, lean_object* v_self_537_, lean_object* v_init_538_, lean_object* v_f_539_){
_start:
{
lean_object* v_toArray_540_; lean_object* v___f_541_; size_t v_sz_542_; size_t v___x_543_; lean_object* v___x_544_; 
v_toArray_540_ = lean_ctor_get(v_self_537_, 1);
lean_inc_ref(v_toArray_540_);
lean_dec_ref(v_self_537_);
v___f_541_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_541_, 0, v_f_539_);
v_sz_542_ = lean_array_size(v_toArray_540_);
v___x_543_ = ((size_t)0ULL);
v___x_544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_536_, v_toArray_540_, v___f_541_, v_sz_542_, v___x_543_, v_init_538_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___boxed(lean_object* v_00_u03b1_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_m_548_, lean_object* v_00_u03b2_549_, lean_object* v_inst_550_, lean_object* v_self_551_, lean_object* v_init_552_, lean_object* v_f_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lake_OrdHashSet_forIn(v_00_u03b1_545_, v_inst_546_, v_inst_547_, v_m_548_, v_00_u03b2_549_, v_inst_550_, v_self_551_, v_init_552_, v_f_553_);
lean_dec_ref(v_inst_547_);
lean_dec_ref(v_inst_546_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0(lean_object* v___y_555_, lean_object* v_a_556_, lean_object* v_x_557_, lean_object* v___y_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = lean_apply_2(v___y_555_, v_a_556_, v___y_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1(lean_object* v_inst_560_, lean_object* v_00_u03b2_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_toArray_565_; lean_object* v___f_566_; size_t v_sz_567_; size_t v___x_568_; lean_object* v___x_569_; 
v_toArray_565_ = lean_ctor_get(v___y_562_, 1);
lean_inc_ref(v_toArray_565_);
lean_dec_ref(v___y_562_);
v___f_566_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_566_, 0, v___y_564_);
v_sz_567_ = lean_array_size(v_toArray_565_);
v___x_568_ = ((size_t)0ULL);
v___x_569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_560_, v_toArray_565_, v___f_566_, v_sz_567_, v___x_568_, v___y_563_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg(lean_object* v_inst_570_){
_start:
{
lean_object* v___f_571_; 
v___f_571_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_571_, 0, v_inst_570_);
return v___f_571_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad(lean_object* v_00_u03b1_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_m_575_, lean_object* v_inst_576_){
_start:
{
lean_object* v___f_577_; 
v___f_577_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_577_, 0, v_inst_576_);
return v___f_577_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_578_, lean_object* v_inst_579_, lean_object* v_inst_580_, lean_object* v_m_581_, lean_object* v_inst_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lake_OrdHashSet_instForInOfMonad(v_00_u03b1_578_, v_inst_579_, v_inst_580_, v_m_581_, v_inst_582_);
lean_dec_ref(v_inst_580_);
lean_dec_ref(v_inst_579_);
return v_res_583_;
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
