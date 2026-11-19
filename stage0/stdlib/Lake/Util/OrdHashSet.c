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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_OrdHashSet_instCoeHashSet___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_OrdHashSet_instCoeHashSet___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_OrdHashSet_instCoeHashSet___redArg___closed__0 = (const lean_object*)&l_Lake_OrdHashSet_instCoeHashSet___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet___redArg();
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_OrdHashSet_empty___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdHashSet_empty___redArg___closed__0;
static lean_once_cell_t l_Lake_OrdHashSet_empty___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdHashSet_empty___redArg___closed__1;
static const lean_array_object l_Lake_OrdHashSet_empty___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_OrdHashSet_empty___redArg___closed__2 = (const lean_object*)&l_Lake_OrdHashSet_empty___redArg___closed__2_value;
static lean_once_cell_t l_Lake_OrdHashSet_empty___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdHashSet_empty___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___redArg();
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_OrdHashSet_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdHashSet_empty___closed__0;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet___redArg___lam__0(lean_object* v_self_1_){
_start:
{
lean_object* v_toHashSet_2_; 
v_toHashSet_2_ = lean_ctor_get(v_self_1_, 0);
lean_inc_ref(v_toHashSet_2_);
return v_toHashSet_2_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet___redArg___lam__0___boxed(lean_object* v_self_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lake_OrdHashSet_instCoeHashSet___redArg___lam__0(v_self_3_);
lean_dec_ref(v_self_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet___redArg(){
_start:
{
lean_object* v___f_7_; 
v___f_7_ = ((lean_object*)(l_Lake_OrdHashSet_instCoeHashSet___redArg___closed__0));
return v___f_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet___redArg___boxed(lean_object* v___dummy_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lake_OrdHashSet_instCoeHashSet___redArg();
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet(lean_object* v_00_u03b1_10_, lean_object* v_inst_11_, lean_object* v_inst_12_){
_start:
{
lean_object* v___f_13_; 
v___f_13_ = ((lean_object*)(l_Lake_OrdHashSet_instCoeHashSet___redArg___closed__0));
return v___f_13_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet___boxed(lean_object* v_00_u03b1_14_, lean_object* v_inst_15_, lean_object* v_inst_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lake_OrdHashSet_instCoeHashSet(v_00_u03b1_14_, v_inst_15_, v_inst_16_);
lean_dec_ref(v_inst_16_);
lean_dec_ref(v_inst_15_);
return v_res_17_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_18_ = lean_box(0);
v___x_19_ = lean_unsigned_to_nat(16u);
v___x_20_ = lean_mk_array(v___x_19_, v___x_18_);
return v___x_20_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___redArg___closed__1(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_21_ = lean_obj_once(&l_Lake_OrdHashSet_empty___redArg___closed__0, &l_Lake_OrdHashSet_empty___redArg___closed__0_once, _init_l_Lake_OrdHashSet_empty___redArg___closed__0);
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
lean_ctor_set(v___x_23_, 1, v___x_21_);
return v___x_23_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___redArg___closed__3(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_26_ = ((lean_object*)(l_Lake_OrdHashSet_empty___redArg___closed__2));
v___x_27_ = lean_obj_once(&l_Lake_OrdHashSet_empty___redArg___closed__1, &l_Lake_OrdHashSet_empty___redArg___closed__1_once, _init_l_Lake_OrdHashSet_empty___redArg___closed__1);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
lean_ctor_set(v___x_28_, 1, v___x_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___redArg(){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_obj_once(&l_Lake_OrdHashSet_empty___redArg___closed__3, &l_Lake_OrdHashSet_empty___redArg___closed__3_once, _init_l_Lake_OrdHashSet_empty___redArg___closed__3);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___redArg___boxed(lean_object* v___dummy_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lake_OrdHashSet_empty___redArg();
return v_res_32_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___closed__0(void){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lake_OrdHashSet_empty___redArg();
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty(lean_object* v_00_u03b1_34_, lean_object* v_inst_35_, lean_object* v_inst_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_obj_once(&l_Lake_OrdHashSet_empty___closed__0, &l_Lake_OrdHashSet_empty___closed__0_once, _init_l_Lake_OrdHashSet_empty___closed__0);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___boxed(lean_object* v_00_u03b1_38_, lean_object* v_inst_39_, lean_object* v_inst_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lake_OrdHashSet_empty(v_00_u03b1_38_, v_inst_39_, v_inst_40_);
lean_dec_ref(v_inst_40_);
lean_dec_ref(v_inst_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_obj_once(&l_Lake_OrdHashSet_empty___closed__0, &l_Lake_OrdHashSet_empty___closed__0_once, _init_l_Lake_OrdHashSet_empty___closed__0);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection___redArg___boxed(lean_object* v___dummy_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lake_OrdHashSet_instEmptyCollection___redArg();
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection(lean_object* v_00_u03b1_46_, lean_object* v_inst_47_, lean_object* v_inst_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_obj_once(&l_Lake_OrdHashSet_empty___closed__0, &l_Lake_OrdHashSet_empty___closed__0_once, _init_l_Lake_OrdHashSet_empty___closed__0);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_50_, lean_object* v_inst_51_, lean_object* v_inst_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lake_OrdHashSet_instEmptyCollection(v_00_u03b1_50_, v_inst_51_, v_inst_52_);
lean_dec_ref(v_inst_52_);
lean_dec_ref(v_inst_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty___redArg(lean_object* v_size_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_obj_once(&l_Lake_OrdHashSet_empty___redArg___closed__1, &l_Lake_OrdHashSet_empty___redArg___closed__1_once, _init_l_Lake_OrdHashSet_empty___redArg___closed__1);
v___x_56_ = lean_mk_empty_array_with_capacity(v_size_54_);
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty___redArg___boxed(lean_object* v_size_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lake_OrdHashSet_mkEmpty___redArg(v_size_58_);
lean_dec(v_size_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty(lean_object* v_00_u03b1_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_size_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lake_OrdHashSet_mkEmpty___redArg(v_size_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty___boxed(lean_object* v_00_u03b1_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_size_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lake_OrdHashSet_mkEmpty(v_00_u03b1_65_, v_inst_66_, v_inst_67_, v_size_68_);
lean_dec(v_size_68_);
lean_dec_ref(v_inst_67_);
lean_dec_ref(v_inst_66_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___redArg(lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_self_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_toHashSet_74_; lean_object* v_toArray_75_; uint8_t v___x_76_; 
v_toHashSet_74_ = lean_ctor_get(v_self_72_, 0);
v_toArray_75_ = lean_ctor_get(v_self_72_, 1);
lean_inc(v_a_73_);
lean_inc_ref(v_inst_70_);
lean_inc_ref(v_inst_71_);
v___x_76_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_71_, v_inst_70_, v_toHashSet_74_, v_a_73_);
if (v___x_76_ == 0)
{
lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_86_; 
lean_inc_ref(v_toArray_75_);
lean_inc_ref(v_toHashSet_74_);
v_isSharedCheck_86_ = !lean_is_exclusive(v_self_72_);
if (v_isSharedCheck_86_ == 0)
{
lean_object* v_unused_87_; lean_object* v_unused_88_; 
v_unused_87_ = lean_ctor_get(v_self_72_, 1);
lean_dec(v_unused_87_);
v_unused_88_ = lean_ctor_get(v_self_72_, 0);
lean_dec(v_unused_88_);
v___x_78_ = v_self_72_;
v_isShared_79_ = v_isSharedCheck_86_;
goto v_resetjp_77_;
}
else
{
lean_dec(v_self_72_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_86_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
v___x_80_ = lean_box(0);
lean_inc(v_a_73_);
v___x_81_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_71_, v_inst_70_, v_toHashSet_74_, v_a_73_, v___x_80_);
v___x_82_ = lean_array_push(v_toArray_75_, v_a_73_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v___x_82_);
lean_ctor_set(v___x_78_, 0, v___x_81_);
v___x_84_ = v___x_78_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v___x_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
else
{
lean_dec(v_a_73_);
lean_dec_ref(v_inst_71_);
lean_dec_ref(v_inst_70_);
return v_self_72_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert(lean_object* v_00_u03b1_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_self_92_, lean_object* v_a_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Lake_OrdHashSet_insert___redArg(v_inst_90_, v_inst_91_, v_self_92_, v_a_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___redArg___lam__0(lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_x1_97_, lean_object* v_x2_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lake_OrdHashSet_insert___redArg(v_inst_95_, v_inst_96_, v_x1_97_, v_x2_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___redArg(lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_self_121_, lean_object* v_arr_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_array_get_size(v_arr_122_);
v___x_125_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_126_ = lean_nat_dec_lt(v___x_123_, v___x_124_);
if (v___x_126_ == 0)
{
lean_dec_ref(v_arr_122_);
lean_dec_ref(v_inst_120_);
lean_dec_ref(v_inst_119_);
return v_self_121_;
}
else
{
lean_object* v___f_127_; size_t v___x_128_; size_t v___x_129_; lean_object* v___x_130_; 
v___f_127_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_appendArray___redArg___lam__0), 4, 2);
lean_closure_set(v___f_127_, 0, v_inst_119_);
lean_closure_set(v___f_127_, 1, v_inst_120_);
v___x_128_ = ((size_t)0ULL);
v___x_129_ = lean_usize_of_nat(v___x_124_);
v___x_130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_125_, v___f_127_, v_arr_122_, v___x_128_, v___x_129_, v_self_121_);
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray(lean_object* v_00_u03b1_131_, lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_self_134_, lean_object* v_arr_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lake_OrdHashSet_appendArray___redArg(v_inst_132_, v_inst_133_, v_self_134_, v_arr_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instHAppendArray___redArg(lean_object* v_inst_137_, lean_object* v_inst_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_appendArray), 5, 3);
lean_closure_set(v___x_139_, 0, lean_box(0));
lean_closure_set(v___x_139_, 1, v_inst_137_);
lean_closure_set(v___x_139_, 2, v_inst_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instHAppendArray(lean_object* v_00_u03b1_140_, lean_object* v_inst_141_, lean_object* v_inst_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_appendArray), 5, 3);
lean_closure_set(v___x_143_, 0, lean_box(0));
lean_closure_set(v___x_143_, 1, v_inst_141_);
lean_closure_set(v___x_143_, 2, v_inst_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_append___redArg(lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_self_146_, lean_object* v_other_147_){
_start:
{
lean_object* v_toArray_148_; lean_object* v___x_149_; 
v_toArray_148_ = lean_ctor_get(v_other_147_, 1);
lean_inc_ref(v_toArray_148_);
lean_dec_ref(v_other_147_);
v___x_149_ = l_Lake_OrdHashSet_appendArray___redArg(v_inst_144_, v_inst_145_, v_self_146_, v_toArray_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_append(lean_object* v_00_u03b1_150_, lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_self_153_, lean_object* v_other_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lake_OrdHashSet_append___redArg(v_inst_151_, v_inst_152_, v_self_153_, v_other_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instAppend___redArg(lean_object* v_inst_156_, lean_object* v_inst_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_append), 5, 3);
lean_closure_set(v___x_158_, 0, lean_box(0));
lean_closure_set(v___x_158_, 1, v_inst_156_);
lean_closure_set(v___x_158_, 2, v_inst_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instAppend(lean_object* v_00_u03b1_159_, lean_object* v_inst_160_, lean_object* v_inst_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_append), 5, 3);
lean_closure_set(v___x_162_, 0, lean_box(0));
lean_closure_set(v___x_162_, 1, v_inst_160_);
lean_closure_set(v___x_162_, 2, v_inst_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_ofArray___redArg(lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_arr_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_array_get_size(v_arr_165_);
v___x_167_ = l_Lake_OrdHashSet_mkEmpty___redArg(v___x_166_);
v___x_168_ = l_Lake_OrdHashSet_appendArray___redArg(v_inst_163_, v_inst_164_, v___x_167_, v_arr_165_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_ofArray(lean_object* v_00_u03b1_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_arr_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lake_OrdHashSet_ofArray___redArg(v_inst_170_, v_inst_171_, v_arr_172_);
return v___x_173_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all___redArg___lam__0(lean_object* v_f_174_, uint8_t v___x_175_, lean_object* v_v_176_){
_start:
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = lean_apply_1(v_f_174_, v_v_176_);
v___x_178_ = lean_unbox(v___x_177_);
if (v___x_178_ == 0)
{
return v___x_175_;
}
else
{
uint8_t v___x_179_; 
v___x_179_ = 0;
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___redArg___lam__0___boxed(lean_object* v_f_180_, lean_object* v___x_181_, lean_object* v_v_182_){
_start:
{
uint8_t v___x_79__boxed_183_; uint8_t v_res_184_; lean_object* v_r_185_; 
v___x_79__boxed_183_ = lean_unbox(v___x_181_);
v_res_184_ = l_Lake_OrdHashSet_all___redArg___lam__0(v_f_180_, v___x_79__boxed_183_, v_v_182_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all___redArg(lean_object* v_f_186_, lean_object* v_self_187_){
_start:
{
lean_object* v_toArray_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_toArray_188_ = lean_ctor_get(v_self_187_, 1);
lean_inc_ref(v_toArray_188_);
lean_dec_ref(v_self_187_);
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = lean_array_get_size(v_toArray_188_);
v___x_191_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_192_ = lean_nat_dec_lt(v___x_189_, v___x_190_);
if (v___x_192_ == 0)
{
uint8_t v___x_193_; 
lean_dec_ref(v_toArray_188_);
lean_dec_ref(v_f_186_);
v___x_193_ = 1;
return v___x_193_;
}
else
{
if (v___x_192_ == 0)
{
lean_dec_ref(v_toArray_188_);
lean_dec_ref(v_f_186_);
return v___x_192_;
}
else
{
lean_object* v___x_194_; lean_object* v___f_195_; size_t v___x_196_; size_t v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_194_ = lean_box(v___x_192_);
v___f_195_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_195_, 0, v_f_186_);
lean_closure_set(v___f_195_, 1, v___x_194_);
v___x_196_ = ((size_t)0ULL);
v___x_197_ = lean_usize_of_nat(v___x_190_);
v___x_198_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_191_, v___f_195_, v_toArray_188_, v___x_196_, v___x_197_);
v___x_199_ = lean_unbox(v___x_198_);
lean_dec(v___x_198_);
if (v___x_199_ == 0)
{
return v___x_192_;
}
else
{
uint8_t v___x_200_; 
v___x_200_ = 0;
return v___x_200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___redArg___boxed(lean_object* v_f_201_, lean_object* v_self_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Lake_OrdHashSet_all___redArg(v_f_201_, v_self_202_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all(lean_object* v_00_u03b1_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_f_208_, lean_object* v_self_209_){
_start:
{
lean_object* v_toArray_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_toArray_210_ = lean_ctor_get(v_self_209_, 1);
lean_inc_ref(v_toArray_210_);
lean_dec_ref(v_self_209_);
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = lean_array_get_size(v_toArray_210_);
v___x_213_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_214_ = lean_nat_dec_lt(v___x_211_, v___x_212_);
if (v___x_214_ == 0)
{
uint8_t v___x_215_; 
lean_dec_ref(v_toArray_210_);
lean_dec_ref(v_f_208_);
v___x_215_ = 1;
return v___x_215_;
}
else
{
if (v___x_214_ == 0)
{
lean_dec_ref(v_toArray_210_);
lean_dec_ref(v_f_208_);
return v___x_214_;
}
else
{
lean_object* v___x_216_; lean_object* v___f_217_; size_t v___x_218_; size_t v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_216_ = lean_box(v___x_214_);
v___f_217_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_217_, 0, v_f_208_);
lean_closure_set(v___f_217_, 1, v___x_216_);
v___x_218_ = ((size_t)0ULL);
v___x_219_ = lean_usize_of_nat(v___x_212_);
v___x_220_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_213_, v___f_217_, v_toArray_210_, v___x_218_, v___x_219_);
v___x_221_ = lean_unbox(v___x_220_);
lean_dec(v___x_220_);
if (v___x_221_ == 0)
{
return v___x_214_;
}
else
{
uint8_t v___x_222_; 
v___x_222_ = 0;
return v___x_222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___boxed(lean_object* v_00_u03b1_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_f_226_, lean_object* v_self_227_){
_start:
{
uint8_t v_res_228_; lean_object* v_r_229_; 
v_res_228_ = l_Lake_OrdHashSet_all(v_00_u03b1_223_, v_inst_224_, v_inst_225_, v_f_226_, v_self_227_);
lean_dec_ref(v_inst_225_);
lean_dec_ref(v_inst_224_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_any___redArg___lam__0(lean_object* v_f_230_, lean_object* v_x_231_){
_start:
{
lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_232_ = lean_apply_1(v_f_230_, v_x_231_);
v___x_233_ = lean_unbox(v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___redArg___lam__0___boxed(lean_object* v_f_234_, lean_object* v_x_235_){
_start:
{
uint8_t v_res_236_; lean_object* v_r_237_; 
v_res_236_ = l_Lake_OrdHashSet_any___redArg___lam__0(v_f_234_, v_x_235_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_any___redArg(lean_object* v_f_238_, lean_object* v_self_239_){
_start:
{
lean_object* v_toArray_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v_toArray_240_ = lean_ctor_get(v_self_239_, 1);
lean_inc_ref(v_toArray_240_);
lean_dec_ref(v_self_239_);
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_array_get_size(v_toArray_240_);
v___x_243_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_244_ = lean_nat_dec_lt(v___x_241_, v___x_242_);
if (v___x_244_ == 0)
{
lean_dec_ref(v_toArray_240_);
lean_dec_ref(v_f_238_);
return v___x_244_;
}
else
{
if (v___x_244_ == 0)
{
lean_dec_ref(v_toArray_240_);
lean_dec_ref(v_f_238_);
return v___x_244_;
}
else
{
lean_object* v___f_245_; size_t v___x_246_; size_t v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___f_245_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_245_, 0, v_f_238_);
v___x_246_ = ((size_t)0ULL);
v___x_247_ = lean_usize_of_nat(v___x_242_);
v___x_248_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_243_, v___f_245_, v_toArray_240_, v___x_246_, v___x_247_);
v___x_249_ = lean_unbox(v___x_248_);
lean_dec(v___x_248_);
return v___x_249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___redArg___boxed(lean_object* v_f_250_, lean_object* v_self_251_){
_start:
{
uint8_t v_res_252_; lean_object* v_r_253_; 
v_res_252_ = l_Lake_OrdHashSet_any___redArg(v_f_250_, v_self_251_);
v_r_253_ = lean_box(v_res_252_);
return v_r_253_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_any(lean_object* v_00_u03b1_254_, lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_f_257_, lean_object* v_self_258_){
_start:
{
lean_object* v_toArray_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_toArray_259_ = lean_ctor_get(v_self_258_, 1);
lean_inc_ref(v_toArray_259_);
lean_dec_ref(v_self_258_);
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = lean_array_get_size(v_toArray_259_);
v___x_262_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_263_ = lean_nat_dec_lt(v___x_260_, v___x_261_);
if (v___x_263_ == 0)
{
lean_dec_ref(v_toArray_259_);
lean_dec_ref(v_f_257_);
return v___x_263_;
}
else
{
if (v___x_263_ == 0)
{
lean_dec_ref(v_toArray_259_);
lean_dec_ref(v_f_257_);
return v___x_263_;
}
else
{
lean_object* v___f_264_; size_t v___x_265_; size_t v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___f_264_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_264_, 0, v_f_257_);
v___x_265_ = ((size_t)0ULL);
v___x_266_ = lean_usize_of_nat(v___x_261_);
v___x_267_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_262_, v___f_264_, v_toArray_259_, v___x_265_, v___x_266_);
v___x_268_ = lean_unbox(v___x_267_);
lean_dec(v___x_267_);
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___boxed(lean_object* v_00_u03b1_269_, lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_f_272_, lean_object* v_self_273_){
_start:
{
uint8_t v_res_274_; lean_object* v_r_275_; 
v_res_274_ = l_Lake_OrdHashSet_any(v_00_u03b1_269_, v_inst_270_, v_inst_271_, v_f_272_, v_self_273_);
lean_dec_ref(v_inst_271_);
lean_dec_ref(v_inst_270_);
v_r_275_ = lean_box(v_res_274_);
return v_r_275_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___redArg___lam__0(lean_object* v_f_276_, lean_object* v_x1_277_, lean_object* v_x2_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = lean_apply_2(v_f_276_, v_x1_277_, v_x2_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___redArg(lean_object* v_f_280_, lean_object* v_init_281_, lean_object* v_self_282_){
_start:
{
lean_object* v_toArray_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v_toArray_283_ = lean_ctor_get(v_self_282_, 1);
lean_inc_ref(v_toArray_283_);
lean_dec_ref(v_self_282_);
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = lean_array_get_size(v_toArray_283_);
v___x_286_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_287_ = lean_nat_dec_lt(v___x_284_, v___x_285_);
if (v___x_287_ == 0)
{
lean_dec_ref(v_toArray_283_);
lean_dec(v_f_280_);
return v_init_281_;
}
else
{
lean_object* v___f_288_; size_t v___x_289_; size_t v___x_290_; lean_object* v___x_291_; 
v___f_288_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_288_, 0, v_f_280_);
v___x_289_ = ((size_t)0ULL);
v___x_290_ = lean_usize_of_nat(v___x_285_);
v___x_291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_286_, v___f_288_, v_toArray_283_, v___x_289_, v___x_290_, v_init_281_);
return v___x_291_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl(lean_object* v_00_u03b1_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_00_u03b2_295_, lean_object* v_f_296_, lean_object* v_init_297_, lean_object* v_self_298_){
_start:
{
lean_object* v_toArray_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v_toArray_299_ = lean_ctor_get(v_self_298_, 1);
lean_inc_ref(v_toArray_299_);
lean_dec_ref(v_self_298_);
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = lean_array_get_size(v_toArray_299_);
v___x_302_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_303_ = lean_nat_dec_lt(v___x_300_, v___x_301_);
if (v___x_303_ == 0)
{
lean_dec_ref(v_toArray_299_);
lean_dec(v_f_296_);
return v_init_297_;
}
else
{
lean_object* v___f_304_; size_t v___x_305_; size_t v___x_306_; lean_object* v___x_307_; 
v___f_304_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_304_, 0, v_f_296_);
v___x_305_ = ((size_t)0ULL);
v___x_306_ = lean_usize_of_nat(v___x_301_);
v___x_307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_302_, v___f_304_, v_toArray_299_, v___x_305_, v___x_306_, v_init_297_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___boxed(lean_object* v_00_u03b1_308_, lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_00_u03b2_311_, lean_object* v_f_312_, lean_object* v_init_313_, lean_object* v_self_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lake_OrdHashSet_foldl(v_00_u03b1_308_, v_inst_309_, v_inst_310_, v_00_u03b2_311_, v_f_312_, v_init_313_, v_self_314_);
lean_dec_ref(v_inst_310_);
lean_dec_ref(v_inst_309_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM___redArg(lean_object* v_inst_316_, lean_object* v_f_317_, lean_object* v_init_318_, lean_object* v_self_319_){
_start:
{
lean_object* v_toApplicative_320_; lean_object* v_toArray_321_; lean_object* v_toPure_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_toApplicative_320_ = lean_ctor_get(v_inst_316_, 0);
v_toArray_321_ = lean_ctor_get(v_self_319_, 1);
lean_inc_ref(v_toArray_321_);
lean_dec_ref(v_self_319_);
v_toPure_322_ = lean_ctor_get(v_toApplicative_320_, 1);
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = lean_array_get_size(v_toArray_321_);
v___x_325_ = lean_nat_dec_lt(v___x_323_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
lean_inc(v_toPure_322_);
lean_dec_ref(v_toArray_321_);
lean_dec(v_f_317_);
lean_dec_ref(v_inst_316_);
v___x_326_ = lean_apply_2(v_toPure_322_, lean_box(0), v_init_318_);
return v___x_326_;
}
else
{
size_t v___x_327_; size_t v___x_328_; lean_object* v___x_329_; 
v___x_327_ = ((size_t)0ULL);
v___x_328_ = lean_usize_of_nat(v___x_324_);
v___x_329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_316_, v_f_317_, v_toArray_321_, v___x_327_, v___x_328_, v_init_318_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM(lean_object* v_00_u03b1_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_m_333_, lean_object* v_00_u03b2_334_, lean_object* v_inst_335_, lean_object* v_f_336_, lean_object* v_init_337_, lean_object* v_self_338_){
_start:
{
lean_object* v_toApplicative_339_; lean_object* v_toArray_340_; lean_object* v_toPure_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v_toApplicative_339_ = lean_ctor_get(v_inst_335_, 0);
v_toArray_340_ = lean_ctor_get(v_self_338_, 1);
lean_inc_ref(v_toArray_340_);
lean_dec_ref(v_self_338_);
v_toPure_341_ = lean_ctor_get(v_toApplicative_339_, 1);
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = lean_array_get_size(v_toArray_340_);
v___x_344_ = lean_nat_dec_lt(v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
lean_inc(v_toPure_341_);
lean_dec_ref(v_toArray_340_);
lean_dec(v_f_336_);
lean_dec_ref(v_inst_335_);
v___x_345_ = lean_apply_2(v_toPure_341_, lean_box(0), v_init_337_);
return v___x_345_;
}
else
{
size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; 
v___x_346_ = ((size_t)0ULL);
v___x_347_ = lean_usize_of_nat(v___x_343_);
v___x_348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_335_, v_f_336_, v_toArray_340_, v___x_346_, v___x_347_, v_init_337_);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM___boxed(lean_object* v_00_u03b1_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_m_352_, lean_object* v_00_u03b2_353_, lean_object* v_inst_354_, lean_object* v_f_355_, lean_object* v_init_356_, lean_object* v_self_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lake_OrdHashSet_foldlM(v_00_u03b1_349_, v_inst_350_, v_inst_351_, v_m_352_, v_00_u03b2_353_, v_inst_354_, v_f_355_, v_init_356_, v_self_357_);
lean_dec_ref(v_inst_351_);
lean_dec_ref(v_inst_350_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr___redArg(lean_object* v_f_359_, lean_object* v_init_360_, lean_object* v_self_361_){
_start:
{
lean_object* v_toArray_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v_toArray_362_ = lean_ctor_get(v_self_361_, 1);
lean_inc_ref(v_toArray_362_);
lean_dec_ref(v_self_361_);
v___x_363_ = lean_array_get_size(v_toArray_362_);
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_366_ = lean_nat_dec_lt(v___x_364_, v___x_363_);
if (v___x_366_ == 0)
{
lean_dec_ref(v_toArray_362_);
lean_dec(v_f_359_);
return v_init_360_;
}
else
{
lean_object* v___f_367_; size_t v___x_368_; size_t v___x_369_; lean_object* v___x_370_; 
v___f_367_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_367_, 0, v_f_359_);
v___x_368_ = lean_usize_of_nat(v___x_363_);
v___x_369_ = ((size_t)0ULL);
v___x_370_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_365_, v___f_367_, v_toArray_362_, v___x_368_, v___x_369_, v_init_360_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr(lean_object* v_00_u03b1_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_00_u03b2_374_, lean_object* v_f_375_, lean_object* v_init_376_, lean_object* v_self_377_){
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
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr___boxed(lean_object* v_00_u03b1_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_00_u03b2_390_, lean_object* v_f_391_, lean_object* v_init_392_, lean_object* v_self_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lake_OrdHashSet_foldr(v_00_u03b1_387_, v_inst_388_, v_inst_389_, v_00_u03b2_390_, v_f_391_, v_init_392_, v_self_393_);
lean_dec_ref(v_inst_389_);
lean_dec_ref(v_inst_388_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM___redArg(lean_object* v_inst_395_, lean_object* v_f_396_, lean_object* v_init_397_, lean_object* v_self_398_){
_start:
{
lean_object* v_toApplicative_399_; lean_object* v_toArray_400_; lean_object* v_toPure_401_; lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v_toApplicative_399_ = lean_ctor_get(v_inst_395_, 0);
v_toArray_400_ = lean_ctor_get(v_self_398_, 1);
lean_inc_ref(v_toArray_400_);
lean_dec_ref(v_self_398_);
v_toPure_401_ = lean_ctor_get(v_toApplicative_399_, 1);
v___x_402_ = lean_array_get_size(v_toArray_400_);
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_nat_dec_lt(v___x_403_, v___x_402_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
lean_inc(v_toPure_401_);
lean_dec_ref(v_toArray_400_);
lean_dec(v_f_396_);
lean_dec_ref(v_inst_395_);
v___x_405_ = lean_apply_2(v_toPure_401_, lean_box(0), v_init_397_);
return v___x_405_;
}
else
{
size_t v___x_406_; size_t v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_usize_of_nat(v___x_402_);
v___x_407_ = ((size_t)0ULL);
v___x_408_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_395_, v_f_396_, v_toArray_400_, v___x_406_, v___x_407_, v_init_397_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM(lean_object* v_00_u03b1_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_m_412_, lean_object* v_00_u03b2_413_, lean_object* v_inst_414_, lean_object* v_f_415_, lean_object* v_init_416_, lean_object* v_self_417_){
_start:
{
lean_object* v_toApplicative_418_; lean_object* v_toArray_419_; lean_object* v_toPure_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v_toApplicative_418_ = lean_ctor_get(v_inst_414_, 0);
v_toArray_419_ = lean_ctor_get(v_self_417_, 1);
lean_inc_ref(v_toArray_419_);
lean_dec_ref(v_self_417_);
v_toPure_420_ = lean_ctor_get(v_toApplicative_418_, 1);
v___x_421_ = lean_array_get_size(v_toArray_419_);
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_nat_dec_lt(v___x_422_, v___x_421_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; 
lean_inc(v_toPure_420_);
lean_dec_ref(v_toArray_419_);
lean_dec(v_f_415_);
lean_dec_ref(v_inst_414_);
v___x_424_ = lean_apply_2(v_toPure_420_, lean_box(0), v_init_416_);
return v___x_424_;
}
else
{
size_t v___x_425_; size_t v___x_426_; lean_object* v___x_427_; 
v___x_425_ = lean_usize_of_nat(v___x_421_);
v___x_426_ = ((size_t)0ULL);
v___x_427_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_414_, v_f_415_, v_toArray_419_, v___x_425_, v___x_426_, v_init_416_);
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM___boxed(lean_object* v_00_u03b1_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_m_431_, lean_object* v_00_u03b2_432_, lean_object* v_inst_433_, lean_object* v_f_434_, lean_object* v_init_435_, lean_object* v_self_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lake_OrdHashSet_foldrM(v_00_u03b1_428_, v_inst_429_, v_inst_430_, v_m_431_, v_00_u03b2_432_, v_inst_433_, v_f_434_, v_init_435_, v_self_436_);
lean_dec_ref(v_inst_430_);
lean_dec_ref(v_inst_429_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___redArg___lam__0(lean_object* v_f_438_, lean_object* v_x_439_, lean_object* v___y_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = lean_apply_1(v_f_438_, v___y_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___redArg(lean_object* v_inst_442_, lean_object* v_f_443_, lean_object* v_self_444_){
_start:
{
lean_object* v_toApplicative_445_; lean_object* v_toArray_446_; lean_object* v_toPure_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v_toApplicative_445_ = lean_ctor_get(v_inst_442_, 0);
v_toArray_446_ = lean_ctor_get(v_self_444_, 1);
lean_inc_ref(v_toArray_446_);
lean_dec_ref(v_self_444_);
v_toPure_447_ = lean_ctor_get(v_toApplicative_445_, 1);
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_array_get_size(v_toArray_446_);
v___x_450_ = lean_box(0);
v___x_451_ = lean_nat_dec_lt(v___x_448_, v___x_449_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
lean_inc(v_toPure_447_);
lean_dec_ref(v_toArray_446_);
lean_dec(v_f_443_);
lean_dec_ref(v_inst_442_);
v___x_452_ = lean_apply_2(v_toPure_447_, lean_box(0), v___x_450_);
return v___x_452_;
}
else
{
lean_object* v___f_453_; size_t v___x_454_; size_t v___x_455_; lean_object* v___x_456_; 
v___f_453_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_453_, 0, v_f_443_);
v___x_454_ = ((size_t)0ULL);
v___x_455_ = lean_usize_of_nat(v___x_449_);
v___x_456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_442_, v___f_453_, v_toArray_446_, v___x_454_, v___x_455_, v___x_450_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM(lean_object* v_00_u03b1_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_m_460_, lean_object* v_inst_461_, lean_object* v_f_462_, lean_object* v_self_463_){
_start:
{
lean_object* v_toApplicative_464_; lean_object* v_toArray_465_; lean_object* v_toPure_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v_toApplicative_464_ = lean_ctor_get(v_inst_461_, 0);
v_toArray_465_ = lean_ctor_get(v_self_463_, 1);
lean_inc_ref(v_toArray_465_);
lean_dec_ref(v_self_463_);
v_toPure_466_ = lean_ctor_get(v_toApplicative_464_, 1);
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = lean_array_get_size(v_toArray_465_);
v___x_469_ = lean_box(0);
v___x_470_ = lean_nat_dec_lt(v___x_467_, v___x_468_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; 
lean_inc(v_toPure_466_);
lean_dec_ref(v_toArray_465_);
lean_dec(v_f_462_);
lean_dec_ref(v_inst_461_);
v___x_471_ = lean_apply_2(v_toPure_466_, lean_box(0), v___x_469_);
return v___x_471_;
}
else
{
lean_object* v___f_472_; size_t v___x_473_; size_t v___x_474_; lean_object* v___x_475_; 
v___f_472_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_472_, 0, v_f_462_);
v___x_473_ = ((size_t)0ULL);
v___x_474_ = lean_usize_of_nat(v___x_468_);
v___x_475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_461_, v___f_472_, v_toArray_465_, v___x_473_, v___x_474_, v___x_469_);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___boxed(lean_object* v_00_u03b1_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_m_479_, lean_object* v_inst_480_, lean_object* v_f_481_, lean_object* v_self_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lake_OrdHashSet_forM(v_00_u03b1_476_, v_inst_477_, v_inst_478_, v_m_479_, v_inst_480_, v_f_481_, v_self_482_);
lean_dec_ref(v_inst_478_);
lean_dec_ref(v_inst_477_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___redArg___lam__0(lean_object* v_f_484_, lean_object* v_a_485_, lean_object* v_x_486_, lean_object* v___y_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = lean_apply_2(v_f_484_, v_a_485_, v___y_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___redArg(lean_object* v_inst_489_, lean_object* v_self_490_, lean_object* v_init_491_, lean_object* v_f_492_){
_start:
{
lean_object* v_toArray_493_; lean_object* v___f_494_; size_t v_sz_495_; size_t v___x_496_; lean_object* v___x_497_; 
v_toArray_493_ = lean_ctor_get(v_self_490_, 1);
lean_inc_ref(v_toArray_493_);
lean_dec_ref(v_self_490_);
v___f_494_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_494_, 0, v_f_492_);
v_sz_495_ = lean_array_size(v_toArray_493_);
v___x_496_ = ((size_t)0ULL);
v___x_497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_489_, v_toArray_493_, v___f_494_, v_sz_495_, v___x_496_, v_init_491_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn(lean_object* v_00_u03b1_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_m_501_, lean_object* v_00_u03b2_502_, lean_object* v_inst_503_, lean_object* v_self_504_, lean_object* v_init_505_, lean_object* v_f_506_){
_start:
{
lean_object* v_toArray_507_; lean_object* v___f_508_; size_t v_sz_509_; size_t v___x_510_; lean_object* v___x_511_; 
v_toArray_507_ = lean_ctor_get(v_self_504_, 1);
lean_inc_ref(v_toArray_507_);
lean_dec_ref(v_self_504_);
v___f_508_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_508_, 0, v_f_506_);
v_sz_509_ = lean_array_size(v_toArray_507_);
v___x_510_ = ((size_t)0ULL);
v___x_511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_503_, v_toArray_507_, v___f_508_, v_sz_509_, v___x_510_, v_init_505_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___boxed(lean_object* v_00_u03b1_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_m_515_, lean_object* v_00_u03b2_516_, lean_object* v_inst_517_, lean_object* v_self_518_, lean_object* v_init_519_, lean_object* v_f_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lake_OrdHashSet_forIn(v_00_u03b1_512_, v_inst_513_, v_inst_514_, v_m_515_, v_00_u03b2_516_, v_inst_517_, v_self_518_, v_init_519_, v_f_520_);
lean_dec_ref(v_inst_514_);
lean_dec_ref(v_inst_513_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0(lean_object* v___y_522_, lean_object* v_a_523_, lean_object* v_x_524_, lean_object* v___y_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = lean_apply_2(v___y_522_, v_a_523_, v___y_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1(lean_object* v_inst_527_, lean_object* v_00_u03b2_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_toArray_532_; lean_object* v___f_533_; size_t v_sz_534_; size_t v___x_535_; lean_object* v___x_536_; 
v_toArray_532_ = lean_ctor_get(v___y_529_, 1);
lean_inc_ref(v_toArray_532_);
lean_dec_ref(v___y_529_);
v___f_533_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_533_, 0, v___y_531_);
v_sz_534_ = lean_array_size(v_toArray_532_);
v___x_535_ = ((size_t)0ULL);
v___x_536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_527_, v_toArray_532_, v___f_533_, v_sz_534_, v___x_535_, v___y_530_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg(lean_object* v_inst_537_){
_start:
{
lean_object* v___f_538_; 
v___f_538_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_538_, 0, v_inst_537_);
return v___f_538_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad(lean_object* v_00_u03b1_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_m_542_, lean_object* v_inst_543_){
_start:
{
lean_object* v___f_544_; 
v___f_544_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_544_, 0, v_inst_543_);
return v___f_544_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_m_548_, lean_object* v_inst_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lake_OrdHashSet_instForInOfMonad(v_00_u03b1_545_, v_inst_546_, v_inst_547_, v_m_548_, v_inst_549_);
lean_dec_ref(v_inst_547_);
lean_dec_ref(v_inst_546_);
return v_res_550_;
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
