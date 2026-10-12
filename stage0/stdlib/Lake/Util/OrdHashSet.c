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
lean_object* l_Lake_OrdHashSet_instCoeHashSet___redArg(){
_start:
{
lean_object* v___f_7_; 
v___f_7_ = ((lean_object*)(l_Lake_OrdHashSet_instCoeHashSet___redArg___closed__0));
return v___f_7_;
}
}
LEAN_EXPORT void l_Lake_OrdHashSet_instCoeHashSet___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_8_;
v_res_8_ = l_Lake_OrdHashSet_instCoeHashSet___redArg();
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet___redArg___boxed(lean_object* v___dummy_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lake_OrdHashSet_instCoeHashSet___redArg();
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet(lean_object* v_00_u03b1_11_, lean_object* v_inst_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v___f_14_; 
v___f_14_ = ((lean_object*)(l_Lake_OrdHashSet_instCoeHashSet___redArg___closed__0));
return v___f_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instCoeHashSet___boxed(lean_object* v_00_u03b1_15_, lean_object* v_inst_16_, lean_object* v_inst_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lake_OrdHashSet_instCoeHashSet(v_00_u03b1_15_, v_inst_16_, v_inst_17_);
lean_dec_ref(v_inst_17_);
lean_dec_ref(v_inst_16_);
return v_res_18_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_19_ = lean_box(0);
v___x_20_ = lean_unsigned_to_nat(16u);
v___x_21_ = lean_mk_array(v___x_20_, v___x_19_);
return v___x_21_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___redArg___closed__1(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_22_ = lean_obj_once(&l_Lake_OrdHashSet_empty___redArg___closed__0, &l_Lake_OrdHashSet_empty___redArg___closed__0_once, _init_l_Lake_OrdHashSet_empty___redArg___closed__0);
v___x_23_ = lean_unsigned_to_nat(0u);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
lean_ctor_set(v___x_24_, 1, v___x_22_);
return v___x_24_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___redArg___closed__3(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = ((lean_object*)(l_Lake_OrdHashSet_empty___redArg___closed__2));
v___x_28_ = lean_obj_once(&l_Lake_OrdHashSet_empty___redArg___closed__1, &l_Lake_OrdHashSet_empty___redArg___closed__1_once, _init_l_Lake_OrdHashSet_empty___redArg___closed__1);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___x_27_);
return v___x_29_;
}
}
lean_object* l_Lake_OrdHashSet_empty___redArg(){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_obj_once(&l_Lake_OrdHashSet_empty___redArg___closed__3, &l_Lake_OrdHashSet_empty___redArg___closed__3_once, _init_l_Lake_OrdHashSet_empty___redArg___closed__3);
return v___x_31_;
}
}
LEAN_EXPORT void l_Lake_OrdHashSet_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_32_;
v_res_32_ = l_Lake_OrdHashSet_empty___redArg();
stack->m_obj
 = v_res_32_;
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___redArg___boxed(lean_object* v___dummy_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lake_OrdHashSet_empty___redArg();
return v_res_34_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___closed__0(void){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lake_OrdHashSet_empty___redArg();
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty(lean_object* v_00_u03b1_36_, lean_object* v_inst_37_, lean_object* v_inst_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_obj_once(&l_Lake_OrdHashSet_empty___closed__0, &l_Lake_OrdHashSet_empty___closed__0_once, _init_l_Lake_OrdHashSet_empty___closed__0);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___boxed(lean_object* v_00_u03b1_40_, lean_object* v_inst_41_, lean_object* v_inst_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lake_OrdHashSet_empty(v_00_u03b1_40_, v_inst_41_, v_inst_42_);
lean_dec_ref(v_inst_42_);
lean_dec_ref(v_inst_41_);
return v_res_43_;
}
}
lean_object* l_Lake_OrdHashSet_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_obj_once(&l_Lake_OrdHashSet_empty___closed__0, &l_Lake_OrdHashSet_empty___closed__0_once, _init_l_Lake_OrdHashSet_empty___closed__0);
return v___x_45_;
}
}
LEAN_EXPORT void l_Lake_OrdHashSet_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_46_;
v_res_46_ = l_Lake_OrdHashSet_instEmptyCollection___redArg();
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection___redArg___boxed(lean_object* v___dummy_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lake_OrdHashSet_instEmptyCollection___redArg();
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection(lean_object* v_00_u03b1_49_, lean_object* v_inst_50_, lean_object* v_inst_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_obj_once(&l_Lake_OrdHashSet_empty___closed__0, &l_Lake_OrdHashSet_empty___closed__0_once, _init_l_Lake_OrdHashSet_empty___closed__0);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_53_, lean_object* v_inst_54_, lean_object* v_inst_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lake_OrdHashSet_instEmptyCollection(v_00_u03b1_53_, v_inst_54_, v_inst_55_);
lean_dec_ref(v_inst_55_);
lean_dec_ref(v_inst_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty___redArg(lean_object* v_size_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_obj_once(&l_Lake_OrdHashSet_empty___redArg___closed__1, &l_Lake_OrdHashSet_empty___redArg___closed__1_once, _init_l_Lake_OrdHashSet_empty___redArg___closed__1);
v___x_59_ = lean_mk_empty_array_with_capacity(v_size_57_);
v___x_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty___redArg___boxed(lean_object* v_size_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lake_OrdHashSet_mkEmpty___redArg(v_size_61_);
lean_dec(v_size_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty(lean_object* v_00_u03b1_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_size_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lake_OrdHashSet_mkEmpty___redArg(v_size_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty___boxed(lean_object* v_00_u03b1_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_size_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lake_OrdHashSet_mkEmpty(v_00_u03b1_68_, v_inst_69_, v_inst_70_, v_size_71_);
lean_dec(v_size_71_);
lean_dec_ref(v_inst_70_);
lean_dec_ref(v_inst_69_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___redArg(lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_self_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_toHashSet_77_; lean_object* v_toArray_78_; uint8_t v___x_79_; 
v_toHashSet_77_ = lean_ctor_get(v_self_75_, 0);
v_toArray_78_ = lean_ctor_get(v_self_75_, 1);
lean_inc(v_a_76_);
lean_inc_ref(v_inst_73_);
lean_inc_ref(v_inst_74_);
v___x_79_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_74_, v_inst_73_, v_toHashSet_77_, v_a_76_);
if (v___x_79_ == 0)
{
lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_89_; 
lean_inc_ref(v_toArray_78_);
lean_inc_ref(v_toHashSet_77_);
v_isSharedCheck_89_ = !lean_is_exclusive(v_self_75_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; lean_object* v_unused_91_; 
v_unused_90_ = lean_ctor_get(v_self_75_, 1);
lean_dec(v_unused_90_);
v_unused_91_ = lean_ctor_get(v_self_75_, 0);
lean_dec(v_unused_91_);
v___x_81_ = v_self_75_;
v_isShared_82_ = v_isSharedCheck_89_;
goto v_resetjp_80_;
}
else
{
lean_dec(v_self_75_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_89_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_83_ = lean_box(0);
lean_inc(v_a_76_);
v___x_84_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_74_, v_inst_73_, v_toHashSet_77_, v_a_76_, v___x_83_);
v___x_85_ = lean_array_push(v_toArray_78_, v_a_76_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v___x_85_);
lean_ctor_set(v___x_81_, 0, v___x_84_);
v___x_87_ = v___x_81_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
else
{
lean_dec(v_a_76_);
lean_dec_ref(v_inst_74_);
lean_dec_ref(v_inst_73_);
return v_self_75_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert(lean_object* v_00_u03b1_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_self_95_, lean_object* v_a_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lake_OrdHashSet_insert___redArg(v_inst_93_, v_inst_94_, v_self_95_, v_a_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___redArg___lam__0(lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_x1_100_, lean_object* v_x2_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lake_OrdHashSet_insert___redArg(v_inst_98_, v_inst_99_, v_x1_100_, v_x2_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___redArg(lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_self_124_, lean_object* v_arr_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_array_get_size(v_arr_125_);
v___x_128_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_129_ = lean_nat_dec_lt(v___x_126_, v___x_127_);
if (v___x_129_ == 0)
{
lean_dec_ref(v_arr_125_);
lean_dec_ref(v_inst_123_);
lean_dec_ref(v_inst_122_);
return v_self_124_;
}
else
{
lean_object* v___f_130_; uint8_t v___x_131_; 
v___f_130_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_appendArray___redArg___lam__0), 4, 2);
lean_closure_set(v___f_130_, 0, v_inst_122_);
lean_closure_set(v___f_130_, 1, v_inst_123_);
v___x_131_ = lean_nat_dec_le(v___x_127_, v___x_127_);
if (v___x_131_ == 0)
{
if (v___x_129_ == 0)
{
lean_dec_ref(v___f_130_);
lean_dec_ref(v_arr_125_);
return v_self_124_;
}
else
{
size_t v___x_132_; size_t v___x_133_; lean_object* v___x_134_; 
v___x_132_ = ((size_t)0ULL);
v___x_133_ = lean_usize_of_nat(v___x_127_);
v___x_134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_128_, v___f_130_, v_arr_125_, v___x_132_, v___x_133_, v_self_124_);
return v___x_134_;
}
}
else
{
size_t v___x_135_; size_t v___x_136_; lean_object* v___x_137_; 
v___x_135_ = ((size_t)0ULL);
v___x_136_ = lean_usize_of_nat(v___x_127_);
v___x_137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_128_, v___f_130_, v_arr_125_, v___x_135_, v___x_136_, v_self_124_);
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray(lean_object* v_00_u03b1_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_self_141_, lean_object* v_arr_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lake_OrdHashSet_appendArray___redArg(v_inst_139_, v_inst_140_, v_self_141_, v_arr_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instHAppendArray___redArg(lean_object* v_inst_144_, lean_object* v_inst_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_appendArray), 5, 3);
lean_closure_set(v___x_146_, 0, lean_box(0));
lean_closure_set(v___x_146_, 1, v_inst_144_);
lean_closure_set(v___x_146_, 2, v_inst_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instHAppendArray(lean_object* v_00_u03b1_147_, lean_object* v_inst_148_, lean_object* v_inst_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_appendArray), 5, 3);
lean_closure_set(v___x_150_, 0, lean_box(0));
lean_closure_set(v___x_150_, 1, v_inst_148_);
lean_closure_set(v___x_150_, 2, v_inst_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_append___redArg(lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_self_153_, lean_object* v_other_154_){
_start:
{
lean_object* v_toArray_155_; lean_object* v___x_156_; 
v_toArray_155_ = lean_ctor_get(v_other_154_, 1);
lean_inc_ref(v_toArray_155_);
lean_dec_ref(v_other_154_);
v___x_156_ = l_Lake_OrdHashSet_appendArray___redArg(v_inst_151_, v_inst_152_, v_self_153_, v_toArray_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_append(lean_object* v_00_u03b1_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_self_160_, lean_object* v_other_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lake_OrdHashSet_append___redArg(v_inst_158_, v_inst_159_, v_self_160_, v_other_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instAppend___redArg(lean_object* v_inst_163_, lean_object* v_inst_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_append), 5, 3);
lean_closure_set(v___x_165_, 0, lean_box(0));
lean_closure_set(v___x_165_, 1, v_inst_163_);
lean_closure_set(v___x_165_, 2, v_inst_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instAppend(lean_object* v_00_u03b1_166_, lean_object* v_inst_167_, lean_object* v_inst_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_append), 5, 3);
lean_closure_set(v___x_169_, 0, lean_box(0));
lean_closure_set(v___x_169_, 1, v_inst_167_);
lean_closure_set(v___x_169_, 2, v_inst_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_ofArray___redArg(lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_arr_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_array_get_size(v_arr_172_);
v___x_174_ = l_Lake_OrdHashSet_mkEmpty___redArg(v___x_173_);
v___x_175_ = l_Lake_OrdHashSet_appendArray___redArg(v_inst_170_, v_inst_171_, v___x_174_, v_arr_172_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_ofArray(lean_object* v_00_u03b1_176_, lean_object* v_inst_177_, lean_object* v_inst_178_, lean_object* v_arr_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lake_OrdHashSet_ofArray___redArg(v_inst_177_, v_inst_178_, v_arr_179_);
return v___x_180_;
}
}
uint8_t l_Lake_OrdHashSet_all___redArg___lam__0(lean_object* v_f_181_, uint8_t v___x_182_, lean_object* v_v_183_){
_start:
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = lean_apply_1(v_f_181_, v_v_183_);
v___x_185_ = lean_unbox(v___x_184_);
if (v___x_185_ == 0)
{
return v___x_182_;
}
else
{
uint8_t v___x_186_; 
v___x_186_ = 0;
return v___x_186_;
}
}
}
LEAN_EXPORT void l_Lake_OrdHashSet_all___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_181_ = stack[0].m_obj;
uint8_t v___x_182_ = stack[1].m_num;
lean_object* v_v_183_ = stack[2].m_obj;
uint8_t v_res_187_;
v_res_187_ = l_Lake_OrdHashSet_all___redArg___lam__0(v_f_181_, v___x_182_, v_v_183_);
stack->m_num = v_res_187_;
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___redArg___lam__0___boxed(lean_object* v_f_188_, lean_object* v___x_189_, lean_object* v_v_190_){
_start:
{
uint8_t v___x_79__boxed_191_; uint8_t v_res_192_; lean_object* v_r_193_; 
v___x_79__boxed_191_ = lean_unbox(v___x_189_);
v_res_192_ = l_Lake_OrdHashSet_all___redArg___lam__0(v_f_188_, v___x_79__boxed_191_, v_v_190_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
uint8_t l_Lake_OrdHashSet_all___redArg(lean_object* v_f_194_, lean_object* v_self_195_){
_start:
{
lean_object* v_toArray_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_toArray_196_ = lean_ctor_get(v_self_195_, 1);
lean_inc_ref(v_toArray_196_);
lean_dec_ref(v_self_195_);
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_array_get_size(v_toArray_196_);
v___x_199_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_200_ = lean_nat_dec_lt(v___x_197_, v___x_198_);
if (v___x_200_ == 0)
{
uint8_t v___x_201_; 
lean_dec_ref(v_toArray_196_);
lean_dec_ref(v_f_194_);
v___x_201_ = 1;
return v___x_201_;
}
else
{
if (v___x_200_ == 0)
{
lean_dec_ref(v_toArray_196_);
lean_dec_ref(v_f_194_);
return v___x_200_;
}
else
{
lean_object* v___x_202_; lean_object* v___f_203_; size_t v___x_204_; size_t v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_202_ = lean_box(v___x_200_);
v___f_203_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_203_, 0, v_f_194_);
lean_closure_set(v___f_203_, 1, v___x_202_);
v___x_204_ = ((size_t)0ULL);
v___x_205_ = lean_usize_of_nat(v___x_198_);
v___x_206_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_199_, v___f_203_, v_toArray_196_, v___x_204_, v___x_205_);
v___x_207_ = lean_unbox(v___x_206_);
lean_dec(v___x_206_);
if (v___x_207_ == 0)
{
return v___x_200_;
}
else
{
uint8_t v___x_208_; 
v___x_208_ = 0;
return v___x_208_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_OrdHashSet_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_194_ = stack[0].m_obj;
lean_object* v_self_195_ = stack[1].m_obj;
uint8_t v_res_209_;
v_res_209_ = l_Lake_OrdHashSet_all___redArg(v_f_194_, v_self_195_);
stack->m_num = v_res_209_;
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___redArg___boxed(lean_object* v_f_210_, lean_object* v_self_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_Lake_OrdHashSet_all___redArg(v_f_210_, v_self_211_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
uint8_t l_Lake_OrdHashSet_all(lean_object* v_00_u03b1_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_f_217_, lean_object* v_self_218_){
_start:
{
lean_object* v_toArray_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v_toArray_219_ = lean_ctor_get(v_self_218_, 1);
lean_inc_ref(v_toArray_219_);
lean_dec_ref(v_self_218_);
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_array_get_size(v_toArray_219_);
v___x_222_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_223_ = lean_nat_dec_lt(v___x_220_, v___x_221_);
if (v___x_223_ == 0)
{
uint8_t v___x_224_; 
lean_dec_ref(v_toArray_219_);
lean_dec_ref(v_f_217_);
v___x_224_ = 1;
return v___x_224_;
}
else
{
if (v___x_223_ == 0)
{
lean_dec_ref(v_toArray_219_);
lean_dec_ref(v_f_217_);
return v___x_223_;
}
else
{
lean_object* v___x_225_; lean_object* v___f_226_; size_t v___x_227_; size_t v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_225_ = lean_box(v___x_223_);
v___f_226_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_226_, 0, v_f_217_);
lean_closure_set(v___f_226_, 1, v___x_225_);
v___x_227_ = ((size_t)0ULL);
v___x_228_ = lean_usize_of_nat(v___x_221_);
v___x_229_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_222_, v___f_226_, v_toArray_219_, v___x_227_, v___x_228_);
v___x_230_ = lean_unbox(v___x_229_);
lean_dec(v___x_229_);
if (v___x_230_ == 0)
{
return v___x_223_;
}
else
{
uint8_t v___x_231_; 
v___x_231_ = 0;
return v___x_231_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_OrdHashSet_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_215_ = stack[1].m_obj;
lean_object* v_inst_216_ = stack[2].m_obj;
lean_object* v_f_217_ = stack[3].m_obj;
lean_object* v_self_218_ = stack[4].m_obj;
uint8_t v_res_232_;
v_res_232_ = l_Lake_OrdHashSet_all(lean_box(0), v_inst_215_, v_inst_216_, v_f_217_, v_self_218_);
stack->m_num = v_res_232_;
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___boxed(lean_object* v_00_u03b1_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_f_236_, lean_object* v_self_237_){
_start:
{
uint8_t v_res_238_; lean_object* v_r_239_; 
v_res_238_ = l_Lake_OrdHashSet_all(v_00_u03b1_233_, v_inst_234_, v_inst_235_, v_f_236_, v_self_237_);
lean_dec_ref(v_inst_235_);
lean_dec_ref(v_inst_234_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
uint8_t l_Lake_OrdHashSet_any___redArg___lam__0(lean_object* v_f_240_, lean_object* v_x_241_){
_start:
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_apply_1(v_f_240_, v_x_241_);
v___x_243_ = lean_unbox(v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT void l_Lake_OrdHashSet_any___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_240_ = stack[0].m_obj;
lean_object* v_x_241_ = stack[1].m_obj;
uint8_t v_res_244_;
v_res_244_ = l_Lake_OrdHashSet_any___redArg___lam__0(v_f_240_, v_x_241_);
stack->m_num = v_res_244_;
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___redArg___lam__0___boxed(lean_object* v_f_245_, lean_object* v_x_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_Lake_OrdHashSet_any___redArg___lam__0(v_f_245_, v_x_246_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
uint8_t l_Lake_OrdHashSet_any___redArg(lean_object* v_f_249_, lean_object* v_self_250_){
_start:
{
lean_object* v_toArray_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v_toArray_251_ = lean_ctor_get(v_self_250_, 1);
lean_inc_ref(v_toArray_251_);
lean_dec_ref(v_self_250_);
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = lean_array_get_size(v_toArray_251_);
v___x_254_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_255_ = lean_nat_dec_lt(v___x_252_, v___x_253_);
if (v___x_255_ == 0)
{
lean_dec_ref(v_toArray_251_);
lean_dec_ref(v_f_249_);
return v___x_255_;
}
else
{
if (v___x_255_ == 0)
{
lean_dec_ref(v_toArray_251_);
lean_dec_ref(v_f_249_);
return v___x_255_;
}
else
{
lean_object* v___f_256_; size_t v___x_257_; size_t v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___f_256_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_256_, 0, v_f_249_);
v___x_257_ = ((size_t)0ULL);
v___x_258_ = lean_usize_of_nat(v___x_253_);
v___x_259_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_254_, v___f_256_, v_toArray_251_, v___x_257_, v___x_258_);
v___x_260_ = lean_unbox(v___x_259_);
lean_dec(v___x_259_);
return v___x_260_;
}
}
}
}
LEAN_EXPORT void l_Lake_OrdHashSet_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_249_ = stack[0].m_obj;
lean_object* v_self_250_ = stack[1].m_obj;
uint8_t v_res_261_;
v_res_261_ = l_Lake_OrdHashSet_any___redArg(v_f_249_, v_self_250_);
stack->m_num = v_res_261_;
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___redArg___boxed(lean_object* v_f_262_, lean_object* v_self_263_){
_start:
{
uint8_t v_res_264_; lean_object* v_r_265_; 
v_res_264_ = l_Lake_OrdHashSet_any___redArg(v_f_262_, v_self_263_);
v_r_265_ = lean_box(v_res_264_);
return v_r_265_;
}
}
uint8_t l_Lake_OrdHashSet_any(lean_object* v_00_u03b1_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_f_269_, lean_object* v_self_270_){
_start:
{
lean_object* v_toArray_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v_toArray_271_ = lean_ctor_get(v_self_270_, 1);
lean_inc_ref(v_toArray_271_);
lean_dec_ref(v_self_270_);
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_array_get_size(v_toArray_271_);
v___x_274_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_275_ = lean_nat_dec_lt(v___x_272_, v___x_273_);
if (v___x_275_ == 0)
{
lean_dec_ref(v_toArray_271_);
lean_dec_ref(v_f_269_);
return v___x_275_;
}
else
{
if (v___x_275_ == 0)
{
lean_dec_ref(v_toArray_271_);
lean_dec_ref(v_f_269_);
return v___x_275_;
}
else
{
lean_object* v___f_276_; size_t v___x_277_; size_t v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v___f_276_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_276_, 0, v_f_269_);
v___x_277_ = ((size_t)0ULL);
v___x_278_ = lean_usize_of_nat(v___x_273_);
v___x_279_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_274_, v___f_276_, v_toArray_271_, v___x_277_, v___x_278_);
v___x_280_ = lean_unbox(v___x_279_);
lean_dec(v___x_279_);
return v___x_280_;
}
}
}
}
LEAN_EXPORT void l_Lake_OrdHashSet_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_267_ = stack[1].m_obj;
lean_object* v_inst_268_ = stack[2].m_obj;
lean_object* v_f_269_ = stack[3].m_obj;
lean_object* v_self_270_ = stack[4].m_obj;
uint8_t v_res_281_;
v_res_281_ = l_Lake_OrdHashSet_any(lean_box(0), v_inst_267_, v_inst_268_, v_f_269_, v_self_270_);
stack->m_num = v_res_281_;
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___boxed(lean_object* v_00_u03b1_282_, lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_f_285_, lean_object* v_self_286_){
_start:
{
uint8_t v_res_287_; lean_object* v_r_288_; 
v_res_287_ = l_Lake_OrdHashSet_any(v_00_u03b1_282_, v_inst_283_, v_inst_284_, v_f_285_, v_self_286_);
lean_dec_ref(v_inst_284_);
lean_dec_ref(v_inst_283_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___redArg___lam__0(lean_object* v_f_289_, lean_object* v_x1_290_, lean_object* v_x2_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = lean_apply_2(v_f_289_, v_x1_290_, v_x2_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___redArg(lean_object* v_f_293_, lean_object* v_init_294_, lean_object* v_self_295_){
_start:
{
lean_object* v_toArray_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_toArray_296_ = lean_ctor_get(v_self_295_, 1);
lean_inc_ref(v_toArray_296_);
lean_dec_ref(v_self_295_);
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = lean_array_get_size(v_toArray_296_);
v___x_299_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_300_ = lean_nat_dec_lt(v___x_297_, v___x_298_);
if (v___x_300_ == 0)
{
lean_dec_ref(v_toArray_296_);
lean_dec(v_f_293_);
return v_init_294_;
}
else
{
lean_object* v___f_301_; uint8_t v___x_302_; 
v___f_301_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_301_, 0, v_f_293_);
v___x_302_ = lean_nat_dec_le(v___x_298_, v___x_298_);
if (v___x_302_ == 0)
{
if (v___x_300_ == 0)
{
lean_dec_ref(v___f_301_);
lean_dec_ref(v_toArray_296_);
return v_init_294_;
}
else
{
size_t v___x_303_; size_t v___x_304_; lean_object* v___x_305_; 
v___x_303_ = ((size_t)0ULL);
v___x_304_ = lean_usize_of_nat(v___x_298_);
v___x_305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_299_, v___f_301_, v_toArray_296_, v___x_303_, v___x_304_, v_init_294_);
return v___x_305_;
}
}
else
{
size_t v___x_306_; size_t v___x_307_; lean_object* v___x_308_; 
v___x_306_ = ((size_t)0ULL);
v___x_307_ = lean_usize_of_nat(v___x_298_);
v___x_308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_299_, v___f_301_, v_toArray_296_, v___x_306_, v___x_307_, v_init_294_);
return v___x_308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl(lean_object* v_00_u03b1_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_00_u03b2_312_, lean_object* v_f_313_, lean_object* v_init_314_, lean_object* v_self_315_){
_start:
{
lean_object* v_toArray_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v_toArray_316_ = lean_ctor_get(v_self_315_, 1);
lean_inc_ref(v_toArray_316_);
lean_dec_ref(v_self_315_);
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = lean_array_get_size(v_toArray_316_);
v___x_319_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_320_ = lean_nat_dec_lt(v___x_317_, v___x_318_);
if (v___x_320_ == 0)
{
lean_dec_ref(v_toArray_316_);
lean_dec(v_f_313_);
return v_init_314_;
}
else
{
lean_object* v___f_321_; uint8_t v___x_322_; 
v___f_321_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_321_, 0, v_f_313_);
v___x_322_ = lean_nat_dec_le(v___x_318_, v___x_318_);
if (v___x_322_ == 0)
{
if (v___x_320_ == 0)
{
lean_dec_ref(v___f_321_);
lean_dec_ref(v_toArray_316_);
return v_init_314_;
}
else
{
size_t v___x_323_; size_t v___x_324_; lean_object* v___x_325_; 
v___x_323_ = ((size_t)0ULL);
v___x_324_ = lean_usize_of_nat(v___x_318_);
v___x_325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_319_, v___f_321_, v_toArray_316_, v___x_323_, v___x_324_, v_init_314_);
return v___x_325_;
}
}
else
{
size_t v___x_326_; size_t v___x_327_; lean_object* v___x_328_; 
v___x_326_ = ((size_t)0ULL);
v___x_327_ = lean_usize_of_nat(v___x_318_);
v___x_328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_319_, v___f_321_, v_toArray_316_, v___x_326_, v___x_327_, v_init_314_);
return v___x_328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___boxed(lean_object* v_00_u03b1_329_, lean_object* v_inst_330_, lean_object* v_inst_331_, lean_object* v_00_u03b2_332_, lean_object* v_f_333_, lean_object* v_init_334_, lean_object* v_self_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lake_OrdHashSet_foldl(v_00_u03b1_329_, v_inst_330_, v_inst_331_, v_00_u03b2_332_, v_f_333_, v_init_334_, v_self_335_);
lean_dec_ref(v_inst_331_);
lean_dec_ref(v_inst_330_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM___redArg(lean_object* v_inst_337_, lean_object* v_f_338_, lean_object* v_init_339_, lean_object* v_self_340_){
_start:
{
lean_object* v_toApplicative_341_; lean_object* v_toArray_342_; lean_object* v_toPure_343_; lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v_toApplicative_341_ = lean_ctor_get(v_inst_337_, 0);
v_toArray_342_ = lean_ctor_get(v_self_340_, 1);
lean_inc_ref(v_toArray_342_);
lean_dec_ref(v_self_340_);
v_toPure_343_ = lean_ctor_get(v_toApplicative_341_, 1);
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_345_ = lean_array_get_size(v_toArray_342_);
v___x_346_ = lean_nat_dec_lt(v___x_344_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
lean_inc(v_toPure_343_);
lean_dec_ref(v_toArray_342_);
lean_dec(v_f_338_);
lean_dec_ref(v_inst_337_);
v___x_347_ = lean_apply_2(v_toPure_343_, lean_box(0), v_init_339_);
return v___x_347_;
}
else
{
uint8_t v___x_348_; 
v___x_348_ = lean_nat_dec_le(v___x_345_, v___x_345_);
if (v___x_348_ == 0)
{
if (v___x_346_ == 0)
{
lean_object* v___x_349_; 
lean_inc(v_toPure_343_);
lean_dec_ref(v_toArray_342_);
lean_dec(v_f_338_);
lean_dec_ref(v_inst_337_);
v___x_349_ = lean_apply_2(v_toPure_343_, lean_box(0), v_init_339_);
return v___x_349_;
}
else
{
size_t v___x_350_; size_t v___x_351_; lean_object* v___x_352_; 
v___x_350_ = ((size_t)0ULL);
v___x_351_ = lean_usize_of_nat(v___x_345_);
v___x_352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_337_, v_f_338_, v_toArray_342_, v___x_350_, v___x_351_, v_init_339_);
return v___x_352_;
}
}
else
{
size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; 
v___x_353_ = ((size_t)0ULL);
v___x_354_ = lean_usize_of_nat(v___x_345_);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_337_, v_f_338_, v_toArray_342_, v___x_353_, v___x_354_, v_init_339_);
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM(lean_object* v_00_u03b1_356_, lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_m_359_, lean_object* v_00_u03b2_360_, lean_object* v_inst_361_, lean_object* v_f_362_, lean_object* v_init_363_, lean_object* v_self_364_){
_start:
{
lean_object* v_toApplicative_365_; lean_object* v_toArray_366_; lean_object* v_toPure_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_toApplicative_365_ = lean_ctor_get(v_inst_361_, 0);
v_toArray_366_ = lean_ctor_get(v_self_364_, 1);
lean_inc_ref(v_toArray_366_);
lean_dec_ref(v_self_364_);
v_toPure_367_ = lean_ctor_get(v_toApplicative_365_, 1);
v___x_368_ = lean_unsigned_to_nat(0u);
v___x_369_ = lean_array_get_size(v_toArray_366_);
v___x_370_ = lean_nat_dec_lt(v___x_368_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_inc(v_toPure_367_);
lean_dec_ref(v_toArray_366_);
lean_dec(v_f_362_);
lean_dec_ref(v_inst_361_);
v___x_371_ = lean_apply_2(v_toPure_367_, lean_box(0), v_init_363_);
return v___x_371_;
}
else
{
uint8_t v___x_372_; 
v___x_372_ = lean_nat_dec_le(v___x_369_, v___x_369_);
if (v___x_372_ == 0)
{
if (v___x_370_ == 0)
{
lean_object* v___x_373_; 
lean_inc(v_toPure_367_);
lean_dec_ref(v_toArray_366_);
lean_dec(v_f_362_);
lean_dec_ref(v_inst_361_);
v___x_373_ = lean_apply_2(v_toPure_367_, lean_box(0), v_init_363_);
return v___x_373_;
}
else
{
size_t v___x_374_; size_t v___x_375_; lean_object* v___x_376_; 
v___x_374_ = ((size_t)0ULL);
v___x_375_ = lean_usize_of_nat(v___x_369_);
v___x_376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_361_, v_f_362_, v_toArray_366_, v___x_374_, v___x_375_, v_init_363_);
return v___x_376_;
}
}
else
{
size_t v___x_377_; size_t v___x_378_; lean_object* v___x_379_; 
v___x_377_ = ((size_t)0ULL);
v___x_378_ = lean_usize_of_nat(v___x_369_);
v___x_379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_361_, v_f_362_, v_toArray_366_, v___x_377_, v___x_378_, v_init_363_);
return v___x_379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM___boxed(lean_object* v_00_u03b1_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_m_383_, lean_object* v_00_u03b2_384_, lean_object* v_inst_385_, lean_object* v_f_386_, lean_object* v_init_387_, lean_object* v_self_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lake_OrdHashSet_foldlM(v_00_u03b1_380_, v_inst_381_, v_inst_382_, v_m_383_, v_00_u03b2_384_, v_inst_385_, v_f_386_, v_init_387_, v_self_388_);
lean_dec_ref(v_inst_382_);
lean_dec_ref(v_inst_381_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr___redArg(lean_object* v_f_390_, lean_object* v_init_391_, lean_object* v_self_392_){
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
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr(lean_object* v_00_u03b1_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_00_u03b2_405_, lean_object* v_f_406_, lean_object* v_init_407_, lean_object* v_self_408_){
_start:
{
lean_object* v_toArray_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_toArray_409_ = lean_ctor_get(v_self_408_, 1);
lean_inc_ref(v_toArray_409_);
lean_dec_ref(v_self_408_);
v___x_410_ = lean_array_get_size(v_toArray_409_);
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_413_ = lean_nat_dec_lt(v___x_411_, v___x_410_);
if (v___x_413_ == 0)
{
lean_dec_ref(v_toArray_409_);
lean_dec(v_f_406_);
return v_init_407_;
}
else
{
lean_object* v___f_414_; size_t v___x_415_; size_t v___x_416_; lean_object* v___x_417_; 
v___f_414_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_414_, 0, v_f_406_);
v___x_415_ = lean_usize_of_nat(v___x_410_);
v___x_416_ = ((size_t)0ULL);
v___x_417_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_412_, v___f_414_, v_toArray_409_, v___x_415_, v___x_416_, v_init_407_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr___boxed(lean_object* v_00_u03b1_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_00_u03b2_421_, lean_object* v_f_422_, lean_object* v_init_423_, lean_object* v_self_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lake_OrdHashSet_foldr(v_00_u03b1_418_, v_inst_419_, v_inst_420_, v_00_u03b2_421_, v_f_422_, v_init_423_, v_self_424_);
lean_dec_ref(v_inst_420_);
lean_dec_ref(v_inst_419_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM___redArg(lean_object* v_inst_426_, lean_object* v_f_427_, lean_object* v_init_428_, lean_object* v_self_429_){
_start:
{
lean_object* v_toApplicative_430_; lean_object* v_toArray_431_; lean_object* v_toPure_432_; lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v_toApplicative_430_ = lean_ctor_get(v_inst_426_, 0);
v_toArray_431_ = lean_ctor_get(v_self_429_, 1);
lean_inc_ref(v_toArray_431_);
lean_dec_ref(v_self_429_);
v_toPure_432_ = lean_ctor_get(v_toApplicative_430_, 1);
v___x_433_ = lean_array_get_size(v_toArray_431_);
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = lean_nat_dec_lt(v___x_434_, v___x_433_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
lean_inc(v_toPure_432_);
lean_dec_ref(v_toArray_431_);
lean_dec(v_f_427_);
lean_dec_ref(v_inst_426_);
v___x_436_ = lean_apply_2(v_toPure_432_, lean_box(0), v_init_428_);
return v___x_436_;
}
else
{
size_t v___x_437_; size_t v___x_438_; lean_object* v___x_439_; 
v___x_437_ = lean_usize_of_nat(v___x_433_);
v___x_438_ = ((size_t)0ULL);
v___x_439_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_426_, v_f_427_, v_toArray_431_, v___x_437_, v___x_438_, v_init_428_);
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM(lean_object* v_00_u03b1_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_m_443_, lean_object* v_00_u03b2_444_, lean_object* v_inst_445_, lean_object* v_f_446_, lean_object* v_init_447_, lean_object* v_self_448_){
_start:
{
lean_object* v_toApplicative_449_; lean_object* v_toArray_450_; lean_object* v_toPure_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v_toApplicative_449_ = lean_ctor_get(v_inst_445_, 0);
v_toArray_450_ = lean_ctor_get(v_self_448_, 1);
lean_inc_ref(v_toArray_450_);
lean_dec_ref(v_self_448_);
v_toPure_451_ = lean_ctor_get(v_toApplicative_449_, 1);
v___x_452_ = lean_array_get_size(v_toArray_450_);
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = lean_nat_dec_lt(v___x_453_, v___x_452_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
lean_inc(v_toPure_451_);
lean_dec_ref(v_toArray_450_);
lean_dec(v_f_446_);
lean_dec_ref(v_inst_445_);
v___x_455_ = lean_apply_2(v_toPure_451_, lean_box(0), v_init_447_);
return v___x_455_;
}
else
{
size_t v___x_456_; size_t v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_usize_of_nat(v___x_452_);
v___x_457_ = ((size_t)0ULL);
v___x_458_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_445_, v_f_446_, v_toArray_450_, v___x_456_, v___x_457_, v_init_447_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM___boxed(lean_object* v_00_u03b1_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_m_462_, lean_object* v_00_u03b2_463_, lean_object* v_inst_464_, lean_object* v_f_465_, lean_object* v_init_466_, lean_object* v_self_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lake_OrdHashSet_foldrM(v_00_u03b1_459_, v_inst_460_, v_inst_461_, v_m_462_, v_00_u03b2_463_, v_inst_464_, v_f_465_, v_init_466_, v_self_467_);
lean_dec_ref(v_inst_461_);
lean_dec_ref(v_inst_460_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___redArg___lam__0(lean_object* v_f_469_, lean_object* v_x_470_, lean_object* v___y_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = lean_apply_1(v_f_469_, v___y_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___redArg(lean_object* v_inst_473_, lean_object* v_f_474_, lean_object* v_self_475_){
_start:
{
lean_object* v_toApplicative_476_; lean_object* v_toArray_477_; lean_object* v_toPure_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_toApplicative_476_ = lean_ctor_get(v_inst_473_, 0);
v_toArray_477_ = lean_ctor_get(v_self_475_, 1);
lean_inc_ref(v_toArray_477_);
lean_dec_ref(v_self_475_);
v_toPure_478_ = lean_ctor_get(v_toApplicative_476_, 1);
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = lean_array_get_size(v_toArray_477_);
v___x_481_ = lean_box(0);
v___x_482_ = lean_nat_dec_lt(v___x_479_, v___x_480_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; 
lean_inc(v_toPure_478_);
lean_dec_ref(v_toArray_477_);
lean_dec(v_f_474_);
lean_dec_ref(v_inst_473_);
v___x_483_ = lean_apply_2(v_toPure_478_, lean_box(0), v___x_481_);
return v___x_483_;
}
else
{
lean_object* v___f_484_; uint8_t v___x_485_; 
v___f_484_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_484_, 0, v_f_474_);
v___x_485_ = lean_nat_dec_le(v___x_480_, v___x_480_);
if (v___x_485_ == 0)
{
if (v___x_482_ == 0)
{
lean_object* v___x_486_; 
lean_inc(v_toPure_478_);
lean_dec_ref(v___f_484_);
lean_dec_ref(v_toArray_477_);
lean_dec_ref(v_inst_473_);
v___x_486_ = lean_apply_2(v_toPure_478_, lean_box(0), v___x_481_);
return v___x_486_;
}
else
{
size_t v___x_487_; size_t v___x_488_; lean_object* v___x_489_; 
v___x_487_ = ((size_t)0ULL);
v___x_488_ = lean_usize_of_nat(v___x_480_);
v___x_489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_473_, v___f_484_, v_toArray_477_, v___x_487_, v___x_488_, v___x_481_);
return v___x_489_;
}
}
else
{
size_t v___x_490_; size_t v___x_491_; lean_object* v___x_492_; 
v___x_490_ = ((size_t)0ULL);
v___x_491_ = lean_usize_of_nat(v___x_480_);
v___x_492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_473_, v___f_484_, v_toArray_477_, v___x_490_, v___x_491_, v___x_481_);
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM(lean_object* v_00_u03b1_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_m_496_, lean_object* v_inst_497_, lean_object* v_f_498_, lean_object* v_self_499_){
_start:
{
lean_object* v_toApplicative_500_; lean_object* v_toArray_501_; lean_object* v_toPure_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v_toApplicative_500_ = lean_ctor_get(v_inst_497_, 0);
v_toArray_501_ = lean_ctor_get(v_self_499_, 1);
lean_inc_ref(v_toArray_501_);
lean_dec_ref(v_self_499_);
v_toPure_502_ = lean_ctor_get(v_toApplicative_500_, 1);
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = lean_array_get_size(v_toArray_501_);
v___x_505_ = lean_box(0);
v___x_506_ = lean_nat_dec_lt(v___x_503_, v___x_504_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; 
lean_inc(v_toPure_502_);
lean_dec_ref(v_toArray_501_);
lean_dec(v_f_498_);
lean_dec_ref(v_inst_497_);
v___x_507_ = lean_apply_2(v_toPure_502_, lean_box(0), v___x_505_);
return v___x_507_;
}
else
{
lean_object* v___f_508_; uint8_t v___x_509_; 
v___f_508_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_508_, 0, v_f_498_);
v___x_509_ = lean_nat_dec_le(v___x_504_, v___x_504_);
if (v___x_509_ == 0)
{
if (v___x_506_ == 0)
{
lean_object* v___x_510_; 
lean_inc(v_toPure_502_);
lean_dec_ref(v___f_508_);
lean_dec_ref(v_toArray_501_);
lean_dec_ref(v_inst_497_);
v___x_510_ = lean_apply_2(v_toPure_502_, lean_box(0), v___x_505_);
return v___x_510_;
}
else
{
size_t v___x_511_; size_t v___x_512_; lean_object* v___x_513_; 
v___x_511_ = ((size_t)0ULL);
v___x_512_ = lean_usize_of_nat(v___x_504_);
v___x_513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_497_, v___f_508_, v_toArray_501_, v___x_511_, v___x_512_, v___x_505_);
return v___x_513_;
}
}
else
{
size_t v___x_514_; size_t v___x_515_; lean_object* v___x_516_; 
v___x_514_ = ((size_t)0ULL);
v___x_515_ = lean_usize_of_nat(v___x_504_);
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_497_, v___f_508_, v_toArray_501_, v___x_514_, v___x_515_, v___x_505_);
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___boxed(lean_object* v_00_u03b1_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_m_520_, lean_object* v_inst_521_, lean_object* v_f_522_, lean_object* v_self_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lake_OrdHashSet_forM(v_00_u03b1_517_, v_inst_518_, v_inst_519_, v_m_520_, v_inst_521_, v_f_522_, v_self_523_);
lean_dec_ref(v_inst_519_);
lean_dec_ref(v_inst_518_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___redArg___lam__0(lean_object* v_f_525_, lean_object* v_a_526_, lean_object* v_x_527_, lean_object* v___y_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = lean_apply_2(v_f_525_, v_a_526_, v___y_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___redArg(lean_object* v_inst_530_, lean_object* v_self_531_, lean_object* v_init_532_, lean_object* v_f_533_){
_start:
{
lean_object* v_toArray_534_; lean_object* v___f_535_; size_t v_sz_536_; size_t v___x_537_; lean_object* v___x_538_; 
v_toArray_534_ = lean_ctor_get(v_self_531_, 1);
lean_inc_ref(v_toArray_534_);
lean_dec_ref(v_self_531_);
v___f_535_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_535_, 0, v_f_533_);
v_sz_536_ = lean_array_size(v_toArray_534_);
v___x_537_ = ((size_t)0ULL);
v___x_538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_530_, v_toArray_534_, v___f_535_, v_sz_536_, v___x_537_, v_init_532_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn(lean_object* v_00_u03b1_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_m_542_, lean_object* v_00_u03b2_543_, lean_object* v_inst_544_, lean_object* v_self_545_, lean_object* v_init_546_, lean_object* v_f_547_){
_start:
{
lean_object* v_toArray_548_; lean_object* v___f_549_; size_t v_sz_550_; size_t v___x_551_; lean_object* v___x_552_; 
v_toArray_548_ = lean_ctor_get(v_self_545_, 1);
lean_inc_ref(v_toArray_548_);
lean_dec_ref(v_self_545_);
v___f_549_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_549_, 0, v_f_547_);
v_sz_550_ = lean_array_size(v_toArray_548_);
v___x_551_ = ((size_t)0ULL);
v___x_552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_544_, v_toArray_548_, v___f_549_, v_sz_550_, v___x_551_, v_init_546_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___boxed(lean_object* v_00_u03b1_553_, lean_object* v_inst_554_, lean_object* v_inst_555_, lean_object* v_m_556_, lean_object* v_00_u03b2_557_, lean_object* v_inst_558_, lean_object* v_self_559_, lean_object* v_init_560_, lean_object* v_f_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lake_OrdHashSet_forIn(v_00_u03b1_553_, v_inst_554_, v_inst_555_, v_m_556_, v_00_u03b2_557_, v_inst_558_, v_self_559_, v_init_560_, v_f_561_);
lean_dec_ref(v_inst_555_);
lean_dec_ref(v_inst_554_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0(lean_object* v___y_563_, lean_object* v_a_564_, lean_object* v_x_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = lean_apply_2(v___y_563_, v_a_564_, v___y_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1(lean_object* v_inst_568_, lean_object* v_00_u03b2_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_toArray_573_; lean_object* v___f_574_; size_t v_sz_575_; size_t v___x_576_; lean_object* v___x_577_; 
v_toArray_573_ = lean_ctor_get(v___y_570_, 1);
lean_inc_ref(v_toArray_573_);
lean_dec_ref(v___y_570_);
v___f_574_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_574_, 0, v___y_572_);
v_sz_575_ = lean_array_size(v_toArray_573_);
v___x_576_ = ((size_t)0ULL);
v___x_577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_568_, v_toArray_573_, v___f_574_, v_sz_575_, v___x_576_, v___y_571_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg(lean_object* v_inst_578_){
_start:
{
lean_object* v___f_579_; 
v___f_579_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_579_, 0, v_inst_578_);
return v___f_579_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad(lean_object* v_00_u03b1_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_m_583_, lean_object* v_inst_584_){
_start:
{
lean_object* v___f_585_; 
v___f_585_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_585_, 0, v_inst_584_);
return v___f_585_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_m_589_, lean_object* v_inst_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lake_OrdHashSet_instForInOfMonad(v_00_u03b1_586_, v_inst_587_, v_inst_588_, v_m_589_, v_inst_590_);
lean_dec_ref(v_inst_588_);
lean_dec_ref(v_inst_587_);
return v_res_591_;
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
