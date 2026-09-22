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
lean_object* v___f_127_; uint8_t v___x_128_; 
v___f_127_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_appendArray___redArg___lam__0), 4, 2);
lean_closure_set(v___f_127_, 0, v_inst_119_);
lean_closure_set(v___f_127_, 1, v_inst_120_);
v___x_128_ = lean_nat_dec_le(v___x_124_, v___x_124_);
if (v___x_128_ == 0)
{
if (v___x_126_ == 0)
{
lean_dec_ref(v___f_127_);
lean_dec_ref(v_arr_122_);
return v_self_121_;
}
else
{
size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; 
v___x_129_ = ((size_t)0ULL);
v___x_130_ = lean_usize_of_nat(v___x_124_);
v___x_131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_125_, v___f_127_, v_arr_122_, v___x_129_, v___x_130_, v_self_121_);
return v___x_131_;
}
}
else
{
size_t v___x_132_; size_t v___x_133_; lean_object* v___x_134_; 
v___x_132_ = ((size_t)0ULL);
v___x_133_ = lean_usize_of_nat(v___x_124_);
v___x_134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_125_, v___f_127_, v_arr_122_, v___x_132_, v___x_133_, v_self_121_);
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray(lean_object* v_00_u03b1_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_self_138_, lean_object* v_arr_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lake_OrdHashSet_appendArray___redArg(v_inst_136_, v_inst_137_, v_self_138_, v_arr_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instHAppendArray___redArg(lean_object* v_inst_141_, lean_object* v_inst_142_){
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
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instHAppendArray(lean_object* v_00_u03b1_144_, lean_object* v_inst_145_, lean_object* v_inst_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_appendArray), 5, 3);
lean_closure_set(v___x_147_, 0, lean_box(0));
lean_closure_set(v___x_147_, 1, v_inst_145_);
lean_closure_set(v___x_147_, 2, v_inst_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_append___redArg(lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_self_150_, lean_object* v_other_151_){
_start:
{
lean_object* v_toArray_152_; lean_object* v___x_153_; 
v_toArray_152_ = lean_ctor_get(v_other_151_, 1);
lean_inc_ref(v_toArray_152_);
lean_dec_ref(v_other_151_);
v___x_153_ = l_Lake_OrdHashSet_appendArray___redArg(v_inst_148_, v_inst_149_, v_self_150_, v_toArray_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_append(lean_object* v_00_u03b1_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_self_157_, lean_object* v_other_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lake_OrdHashSet_append___redArg(v_inst_155_, v_inst_156_, v_self_157_, v_other_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instAppend___redArg(lean_object* v_inst_160_, lean_object* v_inst_161_){
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
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instAppend(lean_object* v_00_u03b1_163_, lean_object* v_inst_164_, lean_object* v_inst_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_append), 5, 3);
lean_closure_set(v___x_166_, 0, lean_box(0));
lean_closure_set(v___x_166_, 1, v_inst_164_);
lean_closure_set(v___x_166_, 2, v_inst_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_ofArray___redArg(lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_arr_169_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_array_get_size(v_arr_169_);
v___x_171_ = l_Lake_OrdHashSet_mkEmpty___redArg(v___x_170_);
v___x_172_ = l_Lake_OrdHashSet_appendArray___redArg(v_inst_167_, v_inst_168_, v___x_171_, v_arr_169_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_ofArray(lean_object* v_00_u03b1_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_arr_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lake_OrdHashSet_ofArray___redArg(v_inst_174_, v_inst_175_, v_arr_176_);
return v___x_177_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all___redArg___lam__0(lean_object* v_f_178_, uint8_t v___x_179_, lean_object* v_v_180_){
_start:
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = lean_apply_1(v_f_178_, v_v_180_);
v___x_182_ = lean_unbox(v___x_181_);
if (v___x_182_ == 0)
{
return v___x_179_;
}
else
{
uint8_t v___x_183_; 
v___x_183_ = 0;
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___redArg___lam__0___boxed(lean_object* v_f_184_, lean_object* v___x_185_, lean_object* v_v_186_){
_start:
{
uint8_t v___x_79__boxed_187_; uint8_t v_res_188_; lean_object* v_r_189_; 
v___x_79__boxed_187_ = lean_unbox(v___x_185_);
v_res_188_ = l_Lake_OrdHashSet_all___redArg___lam__0(v_f_184_, v___x_79__boxed_187_, v_v_186_);
v_r_189_ = lean_box(v_res_188_);
return v_r_189_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all___redArg(lean_object* v_f_190_, lean_object* v_self_191_){
_start:
{
lean_object* v_toArray_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_toArray_192_ = lean_ctor_get(v_self_191_, 1);
lean_inc_ref(v_toArray_192_);
lean_dec_ref(v_self_191_);
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_array_get_size(v_toArray_192_);
v___x_195_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_196_ = lean_nat_dec_lt(v___x_193_, v___x_194_);
if (v___x_196_ == 0)
{
uint8_t v___x_197_; 
lean_dec_ref(v_toArray_192_);
lean_dec_ref(v_f_190_);
v___x_197_ = 1;
return v___x_197_;
}
else
{
if (v___x_196_ == 0)
{
lean_dec_ref(v_toArray_192_);
lean_dec_ref(v_f_190_);
return v___x_196_;
}
else
{
lean_object* v___x_198_; lean_object* v___f_199_; size_t v___x_200_; size_t v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_198_ = lean_box(v___x_196_);
v___f_199_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_199_, 0, v_f_190_);
lean_closure_set(v___f_199_, 1, v___x_198_);
v___x_200_ = ((size_t)0ULL);
v___x_201_ = lean_usize_of_nat(v___x_194_);
v___x_202_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_195_, v___f_199_, v_toArray_192_, v___x_200_, v___x_201_);
v___x_203_ = lean_unbox(v___x_202_);
lean_dec(v___x_202_);
if (v___x_203_ == 0)
{
return v___x_196_;
}
else
{
uint8_t v___x_204_; 
v___x_204_ = 0;
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___redArg___boxed(lean_object* v_f_205_, lean_object* v_self_206_){
_start:
{
uint8_t v_res_207_; lean_object* v_r_208_; 
v_res_207_ = l_Lake_OrdHashSet_all___redArg(v_f_205_, v_self_206_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all(lean_object* v_00_u03b1_209_, lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_f_212_, lean_object* v_self_213_){
_start:
{
lean_object* v_toArray_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v_toArray_214_ = lean_ctor_get(v_self_213_, 1);
lean_inc_ref(v_toArray_214_);
lean_dec_ref(v_self_213_);
v___x_215_ = lean_unsigned_to_nat(0u);
v___x_216_ = lean_array_get_size(v_toArray_214_);
v___x_217_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_218_ = lean_nat_dec_lt(v___x_215_, v___x_216_);
if (v___x_218_ == 0)
{
uint8_t v___x_219_; 
lean_dec_ref(v_toArray_214_);
lean_dec_ref(v_f_212_);
v___x_219_ = 1;
return v___x_219_;
}
else
{
if (v___x_218_ == 0)
{
lean_dec_ref(v_toArray_214_);
lean_dec_ref(v_f_212_);
return v___x_218_;
}
else
{
lean_object* v___x_220_; lean_object* v___f_221_; size_t v___x_222_; size_t v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_220_ = lean_box(v___x_218_);
v___f_221_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_221_, 0, v_f_212_);
lean_closure_set(v___f_221_, 1, v___x_220_);
v___x_222_ = ((size_t)0ULL);
v___x_223_ = lean_usize_of_nat(v___x_216_);
v___x_224_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_217_, v___f_221_, v_toArray_214_, v___x_222_, v___x_223_);
v___x_225_ = lean_unbox(v___x_224_);
lean_dec(v___x_224_);
if (v___x_225_ == 0)
{
return v___x_218_;
}
else
{
uint8_t v___x_226_; 
v___x_226_ = 0;
return v___x_226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___boxed(lean_object* v_00_u03b1_227_, lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_f_230_, lean_object* v_self_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_Lake_OrdHashSet_all(v_00_u03b1_227_, v_inst_228_, v_inst_229_, v_f_230_, v_self_231_);
lean_dec_ref(v_inst_229_);
lean_dec_ref(v_inst_228_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_any___redArg___lam__0(lean_object* v_f_234_, lean_object* v_x_235_){
_start:
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = lean_apply_1(v_f_234_, v_x_235_);
v___x_237_ = lean_unbox(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___redArg___lam__0___boxed(lean_object* v_f_238_, lean_object* v_x_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_Lake_OrdHashSet_any___redArg___lam__0(v_f_238_, v_x_239_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_any___redArg(lean_object* v_f_242_, lean_object* v_self_243_){
_start:
{
lean_object* v_toArray_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_toArray_244_ = lean_ctor_get(v_self_243_, 1);
lean_inc_ref(v_toArray_244_);
lean_dec_ref(v_self_243_);
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_array_get_size(v_toArray_244_);
v___x_247_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_248_ = lean_nat_dec_lt(v___x_245_, v___x_246_);
if (v___x_248_ == 0)
{
lean_dec_ref(v_toArray_244_);
lean_dec_ref(v_f_242_);
return v___x_248_;
}
else
{
if (v___x_248_ == 0)
{
lean_dec_ref(v_toArray_244_);
lean_dec_ref(v_f_242_);
return v___x_248_;
}
else
{
lean_object* v___f_249_; size_t v___x_250_; size_t v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___f_249_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_249_, 0, v_f_242_);
v___x_250_ = ((size_t)0ULL);
v___x_251_ = lean_usize_of_nat(v___x_246_);
v___x_252_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_247_, v___f_249_, v_toArray_244_, v___x_250_, v___x_251_);
v___x_253_ = lean_unbox(v___x_252_);
lean_dec(v___x_252_);
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___redArg___boxed(lean_object* v_f_254_, lean_object* v_self_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_Lake_OrdHashSet_any___redArg(v_f_254_, v_self_255_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_any(lean_object* v_00_u03b1_258_, lean_object* v_inst_259_, lean_object* v_inst_260_, lean_object* v_f_261_, lean_object* v_self_262_){
_start:
{
lean_object* v_toArray_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_toArray_263_ = lean_ctor_get(v_self_262_, 1);
lean_inc_ref(v_toArray_263_);
lean_dec_ref(v_self_262_);
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_array_get_size(v_toArray_263_);
v___x_266_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_267_ = lean_nat_dec_lt(v___x_264_, v___x_265_);
if (v___x_267_ == 0)
{
lean_dec_ref(v_toArray_263_);
lean_dec_ref(v_f_261_);
return v___x_267_;
}
else
{
if (v___x_267_ == 0)
{
lean_dec_ref(v_toArray_263_);
lean_dec_ref(v_f_261_);
return v___x_267_;
}
else
{
lean_object* v___f_268_; size_t v___x_269_; size_t v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___f_268_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_268_, 0, v_f_261_);
v___x_269_ = ((size_t)0ULL);
v___x_270_ = lean_usize_of_nat(v___x_265_);
v___x_271_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_266_, v___f_268_, v_toArray_263_, v___x_269_, v___x_270_);
v___x_272_ = lean_unbox(v___x_271_);
lean_dec(v___x_271_);
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___boxed(lean_object* v_00_u03b1_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_f_276_, lean_object* v_self_277_){
_start:
{
uint8_t v_res_278_; lean_object* v_r_279_; 
v_res_278_ = l_Lake_OrdHashSet_any(v_00_u03b1_273_, v_inst_274_, v_inst_275_, v_f_276_, v_self_277_);
lean_dec_ref(v_inst_275_);
lean_dec_ref(v_inst_274_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___redArg___lam__0(lean_object* v_f_280_, lean_object* v_x1_281_, lean_object* v_x2_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_apply_2(v_f_280_, v_x1_281_, v_x2_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___redArg(lean_object* v_f_284_, lean_object* v_init_285_, lean_object* v_self_286_){
_start:
{
lean_object* v_toArray_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_toArray_287_ = lean_ctor_get(v_self_286_, 1);
lean_inc_ref(v_toArray_287_);
lean_dec_ref(v_self_286_);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = lean_array_get_size(v_toArray_287_);
v___x_290_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_291_ = lean_nat_dec_lt(v___x_288_, v___x_289_);
if (v___x_291_ == 0)
{
lean_dec_ref(v_toArray_287_);
lean_dec(v_f_284_);
return v_init_285_;
}
else
{
lean_object* v___f_292_; uint8_t v___x_293_; 
v___f_292_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_292_, 0, v_f_284_);
v___x_293_ = lean_nat_dec_le(v___x_289_, v___x_289_);
if (v___x_293_ == 0)
{
if (v___x_291_ == 0)
{
lean_dec_ref(v___f_292_);
lean_dec_ref(v_toArray_287_);
return v_init_285_;
}
else
{
size_t v___x_294_; size_t v___x_295_; lean_object* v___x_296_; 
v___x_294_ = ((size_t)0ULL);
v___x_295_ = lean_usize_of_nat(v___x_289_);
v___x_296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_290_, v___f_292_, v_toArray_287_, v___x_294_, v___x_295_, v_init_285_);
return v___x_296_;
}
}
else
{
size_t v___x_297_; size_t v___x_298_; lean_object* v___x_299_; 
v___x_297_ = ((size_t)0ULL);
v___x_298_ = lean_usize_of_nat(v___x_289_);
v___x_299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_290_, v___f_292_, v_toArray_287_, v___x_297_, v___x_298_, v_init_285_);
return v___x_299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl(lean_object* v_00_u03b1_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_00_u03b2_303_, lean_object* v_f_304_, lean_object* v_init_305_, lean_object* v_self_306_){
_start:
{
lean_object* v_toArray_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v_toArray_307_ = lean_ctor_get(v_self_306_, 1);
lean_inc_ref(v_toArray_307_);
lean_dec_ref(v_self_306_);
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_array_get_size(v_toArray_307_);
v___x_310_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_311_ = lean_nat_dec_lt(v___x_308_, v___x_309_);
if (v___x_311_ == 0)
{
lean_dec_ref(v_toArray_307_);
lean_dec(v_f_304_);
return v_init_305_;
}
else
{
lean_object* v___f_312_; uint8_t v___x_313_; 
v___f_312_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_312_, 0, v_f_304_);
v___x_313_ = lean_nat_dec_le(v___x_309_, v___x_309_);
if (v___x_313_ == 0)
{
if (v___x_311_ == 0)
{
lean_dec_ref(v___f_312_);
lean_dec_ref(v_toArray_307_);
return v_init_305_;
}
else
{
size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; 
v___x_314_ = ((size_t)0ULL);
v___x_315_ = lean_usize_of_nat(v___x_309_);
v___x_316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_310_, v___f_312_, v_toArray_307_, v___x_314_, v___x_315_, v_init_305_);
return v___x_316_;
}
}
else
{
size_t v___x_317_; size_t v___x_318_; lean_object* v___x_319_; 
v___x_317_ = ((size_t)0ULL);
v___x_318_ = lean_usize_of_nat(v___x_309_);
v___x_319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_310_, v___f_312_, v_toArray_307_, v___x_317_, v___x_318_, v_init_305_);
return v___x_319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___boxed(lean_object* v_00_u03b1_320_, lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_00_u03b2_323_, lean_object* v_f_324_, lean_object* v_init_325_, lean_object* v_self_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lake_OrdHashSet_foldl(v_00_u03b1_320_, v_inst_321_, v_inst_322_, v_00_u03b2_323_, v_f_324_, v_init_325_, v_self_326_);
lean_dec_ref(v_inst_322_);
lean_dec_ref(v_inst_321_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM___redArg(lean_object* v_inst_328_, lean_object* v_f_329_, lean_object* v_init_330_, lean_object* v_self_331_){
_start:
{
lean_object* v_toApplicative_332_; lean_object* v_toArray_333_; lean_object* v_toPure_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v_toApplicative_332_ = lean_ctor_get(v_inst_328_, 0);
v_toArray_333_ = lean_ctor_get(v_self_331_, 1);
lean_inc_ref(v_toArray_333_);
lean_dec_ref(v_self_331_);
v_toPure_334_ = lean_ctor_get(v_toApplicative_332_, 1);
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = lean_array_get_size(v_toArray_333_);
v___x_337_ = lean_nat_dec_lt(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; 
lean_inc(v_toPure_334_);
lean_dec_ref(v_toArray_333_);
lean_dec(v_f_329_);
lean_dec_ref(v_inst_328_);
v___x_338_ = lean_apply_2(v_toPure_334_, lean_box(0), v_init_330_);
return v___x_338_;
}
else
{
uint8_t v___x_339_; 
v___x_339_ = lean_nat_dec_le(v___x_336_, v___x_336_);
if (v___x_339_ == 0)
{
if (v___x_337_ == 0)
{
lean_object* v___x_340_; 
lean_inc(v_toPure_334_);
lean_dec_ref(v_toArray_333_);
lean_dec(v_f_329_);
lean_dec_ref(v_inst_328_);
v___x_340_ = lean_apply_2(v_toPure_334_, lean_box(0), v_init_330_);
return v___x_340_;
}
else
{
size_t v___x_341_; size_t v___x_342_; lean_object* v___x_343_; 
v___x_341_ = ((size_t)0ULL);
v___x_342_ = lean_usize_of_nat(v___x_336_);
v___x_343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_328_, v_f_329_, v_toArray_333_, v___x_341_, v___x_342_, v_init_330_);
return v___x_343_;
}
}
else
{
size_t v___x_344_; size_t v___x_345_; lean_object* v___x_346_; 
v___x_344_ = ((size_t)0ULL);
v___x_345_ = lean_usize_of_nat(v___x_336_);
v___x_346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_328_, v_f_329_, v_toArray_333_, v___x_344_, v___x_345_, v_init_330_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM(lean_object* v_00_u03b1_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_m_350_, lean_object* v_00_u03b2_351_, lean_object* v_inst_352_, lean_object* v_f_353_, lean_object* v_init_354_, lean_object* v_self_355_){
_start:
{
lean_object* v_toApplicative_356_; lean_object* v_toArray_357_; lean_object* v_toPure_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v_toApplicative_356_ = lean_ctor_get(v_inst_352_, 0);
v_toArray_357_ = lean_ctor_get(v_self_355_, 1);
lean_inc_ref(v_toArray_357_);
lean_dec_ref(v_self_355_);
v_toPure_358_ = lean_ctor_get(v_toApplicative_356_, 1);
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = lean_array_get_size(v_toArray_357_);
v___x_361_ = lean_nat_dec_lt(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
lean_inc(v_toPure_358_);
lean_dec_ref(v_toArray_357_);
lean_dec(v_f_353_);
lean_dec_ref(v_inst_352_);
v___x_362_ = lean_apply_2(v_toPure_358_, lean_box(0), v_init_354_);
return v___x_362_;
}
else
{
uint8_t v___x_363_; 
v___x_363_ = lean_nat_dec_le(v___x_360_, v___x_360_);
if (v___x_363_ == 0)
{
if (v___x_361_ == 0)
{
lean_object* v___x_364_; 
lean_inc(v_toPure_358_);
lean_dec_ref(v_toArray_357_);
lean_dec(v_f_353_);
lean_dec_ref(v_inst_352_);
v___x_364_ = lean_apply_2(v_toPure_358_, lean_box(0), v_init_354_);
return v___x_364_;
}
else
{
size_t v___x_365_; size_t v___x_366_; lean_object* v___x_367_; 
v___x_365_ = ((size_t)0ULL);
v___x_366_ = lean_usize_of_nat(v___x_360_);
v___x_367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_352_, v_f_353_, v_toArray_357_, v___x_365_, v___x_366_, v_init_354_);
return v___x_367_;
}
}
else
{
size_t v___x_368_; size_t v___x_369_; lean_object* v___x_370_; 
v___x_368_ = ((size_t)0ULL);
v___x_369_ = lean_usize_of_nat(v___x_360_);
v___x_370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_352_, v_f_353_, v_toArray_357_, v___x_368_, v___x_369_, v_init_354_);
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM___boxed(lean_object* v_00_u03b1_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_m_374_, lean_object* v_00_u03b2_375_, lean_object* v_inst_376_, lean_object* v_f_377_, lean_object* v_init_378_, lean_object* v_self_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lake_OrdHashSet_foldlM(v_00_u03b1_371_, v_inst_372_, v_inst_373_, v_m_374_, v_00_u03b2_375_, v_inst_376_, v_f_377_, v_init_378_, v_self_379_);
lean_dec_ref(v_inst_373_);
lean_dec_ref(v_inst_372_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr___redArg(lean_object* v_f_381_, lean_object* v_init_382_, lean_object* v_self_383_){
_start:
{
lean_object* v_toArray_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v_toArray_384_ = lean_ctor_get(v_self_383_, 1);
lean_inc_ref(v_toArray_384_);
lean_dec_ref(v_self_383_);
v___x_385_ = lean_array_get_size(v_toArray_384_);
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_388_ = lean_nat_dec_lt(v___x_386_, v___x_385_);
if (v___x_388_ == 0)
{
lean_dec_ref(v_toArray_384_);
lean_dec(v_f_381_);
return v_init_382_;
}
else
{
lean_object* v___f_389_; size_t v___x_390_; size_t v___x_391_; lean_object* v___x_392_; 
v___f_389_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_389_, 0, v_f_381_);
v___x_390_ = lean_usize_of_nat(v___x_385_);
v___x_391_ = ((size_t)0ULL);
v___x_392_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_387_, v___f_389_, v_toArray_384_, v___x_390_, v___x_391_, v_init_382_);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr(lean_object* v_00_u03b1_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_00_u03b2_396_, lean_object* v_f_397_, lean_object* v_init_398_, lean_object* v_self_399_){
_start:
{
lean_object* v_toArray_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v_toArray_400_ = lean_ctor_get(v_self_399_, 1);
lean_inc_ref(v_toArray_400_);
lean_dec_ref(v_self_399_);
v___x_401_ = lean_array_get_size(v_toArray_400_);
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_404_ = lean_nat_dec_lt(v___x_402_, v___x_401_);
if (v___x_404_ == 0)
{
lean_dec_ref(v_toArray_400_);
lean_dec(v_f_397_);
return v_init_398_;
}
else
{
lean_object* v___f_405_; size_t v___x_406_; size_t v___x_407_; lean_object* v___x_408_; 
v___f_405_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_405_, 0, v_f_397_);
v___x_406_ = lean_usize_of_nat(v___x_401_);
v___x_407_ = ((size_t)0ULL);
v___x_408_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_403_, v___f_405_, v_toArray_400_, v___x_406_, v___x_407_, v_init_398_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr___boxed(lean_object* v_00_u03b1_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_00_u03b2_412_, lean_object* v_f_413_, lean_object* v_init_414_, lean_object* v_self_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lake_OrdHashSet_foldr(v_00_u03b1_409_, v_inst_410_, v_inst_411_, v_00_u03b2_412_, v_f_413_, v_init_414_, v_self_415_);
lean_dec_ref(v_inst_411_);
lean_dec_ref(v_inst_410_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM___redArg(lean_object* v_inst_417_, lean_object* v_f_418_, lean_object* v_init_419_, lean_object* v_self_420_){
_start:
{
lean_object* v_toApplicative_421_; lean_object* v_toArray_422_; lean_object* v_toPure_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v_toApplicative_421_ = lean_ctor_get(v_inst_417_, 0);
v_toArray_422_ = lean_ctor_get(v_self_420_, 1);
lean_inc_ref(v_toArray_422_);
lean_dec_ref(v_self_420_);
v_toPure_423_ = lean_ctor_get(v_toApplicative_421_, 1);
v___x_424_ = lean_array_get_size(v_toArray_422_);
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = lean_nat_dec_lt(v___x_425_, v___x_424_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; 
lean_inc(v_toPure_423_);
lean_dec_ref(v_toArray_422_);
lean_dec(v_f_418_);
lean_dec_ref(v_inst_417_);
v___x_427_ = lean_apply_2(v_toPure_423_, lean_box(0), v_init_419_);
return v___x_427_;
}
else
{
size_t v___x_428_; size_t v___x_429_; lean_object* v___x_430_; 
v___x_428_ = lean_usize_of_nat(v___x_424_);
v___x_429_ = ((size_t)0ULL);
v___x_430_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_417_, v_f_418_, v_toArray_422_, v___x_428_, v___x_429_, v_init_419_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM(lean_object* v_00_u03b1_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_m_434_, lean_object* v_00_u03b2_435_, lean_object* v_inst_436_, lean_object* v_f_437_, lean_object* v_init_438_, lean_object* v_self_439_){
_start:
{
lean_object* v_toApplicative_440_; lean_object* v_toArray_441_; lean_object* v_toPure_442_; lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v_toApplicative_440_ = lean_ctor_get(v_inst_436_, 0);
v_toArray_441_ = lean_ctor_get(v_self_439_, 1);
lean_inc_ref(v_toArray_441_);
lean_dec_ref(v_self_439_);
v_toPure_442_ = lean_ctor_get(v_toApplicative_440_, 1);
v___x_443_ = lean_array_get_size(v_toArray_441_);
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = lean_nat_dec_lt(v___x_444_, v___x_443_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; 
lean_inc(v_toPure_442_);
lean_dec_ref(v_toArray_441_);
lean_dec(v_f_437_);
lean_dec_ref(v_inst_436_);
v___x_446_ = lean_apply_2(v_toPure_442_, lean_box(0), v_init_438_);
return v___x_446_;
}
else
{
size_t v___x_447_; size_t v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_usize_of_nat(v___x_443_);
v___x_448_ = ((size_t)0ULL);
v___x_449_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_436_, v_f_437_, v_toArray_441_, v___x_447_, v___x_448_, v_init_438_);
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM___boxed(lean_object* v_00_u03b1_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_m_453_, lean_object* v_00_u03b2_454_, lean_object* v_inst_455_, lean_object* v_f_456_, lean_object* v_init_457_, lean_object* v_self_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lake_OrdHashSet_foldrM(v_00_u03b1_450_, v_inst_451_, v_inst_452_, v_m_453_, v_00_u03b2_454_, v_inst_455_, v_f_456_, v_init_457_, v_self_458_);
lean_dec_ref(v_inst_452_);
lean_dec_ref(v_inst_451_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___redArg___lam__0(lean_object* v_f_460_, lean_object* v_x_461_, lean_object* v___y_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = lean_apply_1(v_f_460_, v___y_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___redArg(lean_object* v_inst_464_, lean_object* v_f_465_, lean_object* v_self_466_){
_start:
{
lean_object* v_toApplicative_467_; lean_object* v_toArray_468_; lean_object* v_toPure_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v_toApplicative_467_ = lean_ctor_get(v_inst_464_, 0);
v_toArray_468_ = lean_ctor_get(v_self_466_, 1);
lean_inc_ref(v_toArray_468_);
lean_dec_ref(v_self_466_);
v_toPure_469_ = lean_ctor_get(v_toApplicative_467_, 1);
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_array_get_size(v_toArray_468_);
v___x_472_ = lean_box(0);
v___x_473_ = lean_nat_dec_lt(v___x_470_, v___x_471_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
lean_inc(v_toPure_469_);
lean_dec_ref(v_toArray_468_);
lean_dec(v_f_465_);
lean_dec_ref(v_inst_464_);
v___x_474_ = lean_apply_2(v_toPure_469_, lean_box(0), v___x_472_);
return v___x_474_;
}
else
{
lean_object* v___f_475_; uint8_t v___x_476_; 
v___f_475_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_475_, 0, v_f_465_);
v___x_476_ = lean_nat_dec_le(v___x_471_, v___x_471_);
if (v___x_476_ == 0)
{
if (v___x_473_ == 0)
{
lean_object* v___x_477_; 
lean_inc(v_toPure_469_);
lean_dec_ref(v___f_475_);
lean_dec_ref(v_toArray_468_);
lean_dec_ref(v_inst_464_);
v___x_477_ = lean_apply_2(v_toPure_469_, lean_box(0), v___x_472_);
return v___x_477_;
}
else
{
size_t v___x_478_; size_t v___x_479_; lean_object* v___x_480_; 
v___x_478_ = ((size_t)0ULL);
v___x_479_ = lean_usize_of_nat(v___x_471_);
v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_464_, v___f_475_, v_toArray_468_, v___x_478_, v___x_479_, v___x_472_);
return v___x_480_;
}
}
else
{
size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; 
v___x_481_ = ((size_t)0ULL);
v___x_482_ = lean_usize_of_nat(v___x_471_);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_464_, v___f_475_, v_toArray_468_, v___x_481_, v___x_482_, v___x_472_);
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM(lean_object* v_00_u03b1_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_m_487_, lean_object* v_inst_488_, lean_object* v_f_489_, lean_object* v_self_490_){
_start:
{
lean_object* v_toApplicative_491_; lean_object* v_toArray_492_; lean_object* v_toPure_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v_toApplicative_491_ = lean_ctor_get(v_inst_488_, 0);
v_toArray_492_ = lean_ctor_get(v_self_490_, 1);
lean_inc_ref(v_toArray_492_);
lean_dec_ref(v_self_490_);
v_toPure_493_ = lean_ctor_get(v_toApplicative_491_, 1);
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = lean_array_get_size(v_toArray_492_);
v___x_496_ = lean_box(0);
v___x_497_ = lean_nat_dec_lt(v___x_494_, v___x_495_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; 
lean_inc(v_toPure_493_);
lean_dec_ref(v_toArray_492_);
lean_dec(v_f_489_);
lean_dec_ref(v_inst_488_);
v___x_498_ = lean_apply_2(v_toPure_493_, lean_box(0), v___x_496_);
return v___x_498_;
}
else
{
lean_object* v___f_499_; uint8_t v___x_500_; 
v___f_499_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_499_, 0, v_f_489_);
v___x_500_ = lean_nat_dec_le(v___x_495_, v___x_495_);
if (v___x_500_ == 0)
{
if (v___x_497_ == 0)
{
lean_object* v___x_501_; 
lean_inc(v_toPure_493_);
lean_dec_ref(v___f_499_);
lean_dec_ref(v_toArray_492_);
lean_dec_ref(v_inst_488_);
v___x_501_ = lean_apply_2(v_toPure_493_, lean_box(0), v___x_496_);
return v___x_501_;
}
else
{
size_t v___x_502_; size_t v___x_503_; lean_object* v___x_504_; 
v___x_502_ = ((size_t)0ULL);
v___x_503_ = lean_usize_of_nat(v___x_495_);
v___x_504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_488_, v___f_499_, v_toArray_492_, v___x_502_, v___x_503_, v___x_496_);
return v___x_504_;
}
}
else
{
size_t v___x_505_; size_t v___x_506_; lean_object* v___x_507_; 
v___x_505_ = ((size_t)0ULL);
v___x_506_ = lean_usize_of_nat(v___x_495_);
v___x_507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_488_, v___f_499_, v_toArray_492_, v___x_505_, v___x_506_, v___x_496_);
return v___x_507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___boxed(lean_object* v_00_u03b1_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_m_511_, lean_object* v_inst_512_, lean_object* v_f_513_, lean_object* v_self_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lake_OrdHashSet_forM(v_00_u03b1_508_, v_inst_509_, v_inst_510_, v_m_511_, v_inst_512_, v_f_513_, v_self_514_);
lean_dec_ref(v_inst_510_);
lean_dec_ref(v_inst_509_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___redArg___lam__0(lean_object* v_f_516_, lean_object* v_a_517_, lean_object* v_x_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = lean_apply_2(v_f_516_, v_a_517_, v___y_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___redArg(lean_object* v_inst_521_, lean_object* v_self_522_, lean_object* v_init_523_, lean_object* v_f_524_){
_start:
{
lean_object* v_toArray_525_; lean_object* v___f_526_; size_t v_sz_527_; size_t v___x_528_; lean_object* v___x_529_; 
v_toArray_525_ = lean_ctor_get(v_self_522_, 1);
lean_inc_ref(v_toArray_525_);
lean_dec_ref(v_self_522_);
v___f_526_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_526_, 0, v_f_524_);
v_sz_527_ = lean_array_size(v_toArray_525_);
v___x_528_ = ((size_t)0ULL);
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_521_, v_toArray_525_, v___f_526_, v_sz_527_, v___x_528_, v_init_523_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn(lean_object* v_00_u03b1_530_, lean_object* v_inst_531_, lean_object* v_inst_532_, lean_object* v_m_533_, lean_object* v_00_u03b2_534_, lean_object* v_inst_535_, lean_object* v_self_536_, lean_object* v_init_537_, lean_object* v_f_538_){
_start:
{
lean_object* v_toArray_539_; lean_object* v___f_540_; size_t v_sz_541_; size_t v___x_542_; lean_object* v___x_543_; 
v_toArray_539_ = lean_ctor_get(v_self_536_, 1);
lean_inc_ref(v_toArray_539_);
lean_dec_ref(v_self_536_);
v___f_540_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_540_, 0, v_f_538_);
v_sz_541_ = lean_array_size(v_toArray_539_);
v___x_542_ = ((size_t)0ULL);
v___x_543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_535_, v_toArray_539_, v___f_540_, v_sz_541_, v___x_542_, v_init_537_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___boxed(lean_object* v_00_u03b1_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_m_547_, lean_object* v_00_u03b2_548_, lean_object* v_inst_549_, lean_object* v_self_550_, lean_object* v_init_551_, lean_object* v_f_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lake_OrdHashSet_forIn(v_00_u03b1_544_, v_inst_545_, v_inst_546_, v_m_547_, v_00_u03b2_548_, v_inst_549_, v_self_550_, v_init_551_, v_f_552_);
lean_dec_ref(v_inst_546_);
lean_dec_ref(v_inst_545_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0(lean_object* v___y_554_, lean_object* v_a_555_, lean_object* v_x_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = lean_apply_2(v___y_554_, v_a_555_, v___y_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1(lean_object* v_inst_559_, lean_object* v_00_u03b2_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_toArray_564_; lean_object* v___f_565_; size_t v_sz_566_; size_t v___x_567_; lean_object* v___x_568_; 
v_toArray_564_ = lean_ctor_get(v___y_561_, 1);
lean_inc_ref(v_toArray_564_);
lean_dec_ref(v___y_561_);
v___f_565_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_565_, 0, v___y_563_);
v_sz_566_ = lean_array_size(v_toArray_564_);
v___x_567_ = ((size_t)0ULL);
v___x_568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_559_, v_toArray_564_, v___f_565_, v_sz_566_, v___x_567_, v___y_562_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg(lean_object* v_inst_569_){
_start:
{
lean_object* v___f_570_; 
v___f_570_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_570_, 0, v_inst_569_);
return v___f_570_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad(lean_object* v_00_u03b1_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_m_574_, lean_object* v_inst_575_){
_start:
{
lean_object* v___f_576_; 
v___f_576_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_576_, 0, v_inst_575_);
return v___f_576_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_m_580_, lean_object* v_inst_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lake_OrdHashSet_instForInOfMonad(v_00_u03b1_577_, v_inst_578_, v_inst_579_, v_m_580_, v_inst_581_);
lean_dec_ref(v_inst_579_);
lean_dec_ref(v_inst_578_);
return v_res_582_;
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
