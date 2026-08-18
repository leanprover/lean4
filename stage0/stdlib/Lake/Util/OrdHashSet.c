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
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
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
static lean_once_cell_t l_Lake_OrdHashSet_empty___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdHashSet_empty___closed__2;
static const lean_array_object l_Lake_OrdHashSet_empty___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_OrdHashSet_empty___closed__3 = (const lean_object*)&l_Lake_OrdHashSet_empty___closed__3_value;
static lean_once_cell_t l_Lake_OrdHashSet_empty___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdHashSet_empty___closed__4;
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
lean_object* v_cellCount_14_; lean_object* v___x_15_; 
v_cellCount_14_ = lean_unsigned_to_nat(16u);
v___x_15_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_14_);
return v___x_15_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___closed__1(void){
_start:
{
lean_object* v_cellCount_16_; lean_object* v___x_17_; 
v_cellCount_16_ = lean_unsigned_to_nat(16u);
v___x_17_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___closed__2(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_18_ = lean_obj_once(&l_Lake_OrdHashSet_empty___closed__1, &l_Lake_OrdHashSet_empty___closed__1_once, _init_l_Lake_OrdHashSet_empty___closed__1);
v___x_19_ = lean_obj_once(&l_Lake_OrdHashSet_empty___closed__0, &l_Lake_OrdHashSet_empty___closed__0_once, _init_l_Lake_OrdHashSet_empty___closed__0);
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
lean_ctor_set(v___x_21_, 1, v___x_19_);
lean_ctor_set(v___x_21_, 2, v___x_18_);
return v___x_21_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___closed__4(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = ((lean_object*)(l_Lake_OrdHashSet_empty___closed__3));
v___x_25_ = lean_obj_once(&l_Lake_OrdHashSet_empty___closed__2, &l_Lake_OrdHashSet_empty___closed__2_once, _init_l_Lake_OrdHashSet_empty___closed__2);
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
lean_ctor_set(v___x_26_, 1, v___x_24_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty(lean_object* v_00_u03b1_27_, lean_object* v_inst_28_, lean_object* v_inst_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_obj_once(&l_Lake_OrdHashSet_empty___closed__4, &l_Lake_OrdHashSet_empty___closed__4_once, _init_l_Lake_OrdHashSet_empty___closed__4);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___boxed(lean_object* v_00_u03b1_31_, lean_object* v_inst_32_, lean_object* v_inst_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lake_OrdHashSet_empty(v_00_u03b1_31_, v_inst_32_, v_inst_33_);
lean_dec_ref(v_inst_33_);
lean_dec_ref(v_inst_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection___redArg(lean_object* v_inst_35_, lean_object* v_inst_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lake_OrdHashSet_empty(lean_box(0), v_inst_35_, v_inst_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection___redArg___boxed(lean_object* v_inst_38_, lean_object* v_inst_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lake_OrdHashSet_instEmptyCollection___redArg(v_inst_38_, v_inst_39_);
lean_dec_ref(v_inst_39_);
lean_dec_ref(v_inst_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection(lean_object* v_00_u03b1_41_, lean_object* v_inst_42_, lean_object* v_inst_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lake_OrdHashSet_empty(lean_box(0), v_inst_42_, v_inst_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_45_, lean_object* v_inst_46_, lean_object* v_inst_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lake_OrdHashSet_instEmptyCollection(v_00_u03b1_45_, v_inst_46_, v_inst_47_);
lean_dec_ref(v_inst_47_);
lean_dec_ref(v_inst_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty___redArg(lean_object* v_size_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_obj_once(&l_Lake_OrdHashSet_empty___closed__2, &l_Lake_OrdHashSet_empty___closed__2_once, _init_l_Lake_OrdHashSet_empty___closed__2);
v___x_51_ = lean_mk_empty_array_with_capacity(v_size_49_);
v___x_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_50_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty___redArg___boxed(lean_object* v_size_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lake_OrdHashSet_mkEmpty___redArg(v_size_53_);
lean_dec(v_size_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty(lean_object* v_00_u03b1_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_size_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lake_OrdHashSet_mkEmpty___redArg(v_size_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_mkEmpty___boxed(lean_object* v_00_u03b1_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_size_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lake_OrdHashSet_mkEmpty(v_00_u03b1_60_, v_inst_61_, v_inst_62_, v_size_63_);
lean_dec(v_size_63_);
lean_dec_ref(v_inst_62_);
lean_dec_ref(v_inst_61_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___redArg(lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_self_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_toHashSet_69_; lean_object* v_toArray_70_; lean_object* v___y_72_; uint8_t v___x_75_; 
v_toHashSet_69_ = lean_ctor_get(v_self_67_, 0);
v_toArray_70_ = lean_ctor_get(v_self_67_, 1);
lean_inc(v_a_68_);
lean_inc_ref(v_inst_65_);
lean_inc_ref(v_inst_66_);
v___x_75_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_66_, v_inst_65_, v_toHashSet_69_, v_a_68_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___y_78_; lean_object* v_i_79_; lean_object* v___y_85_; lean_object* v___y_95_; lean_object* v_i_96_; lean_object* v___x_111_; 
lean_inc_ref(v_toArray_70_);
lean_inc_ref(v_toHashSet_69_);
lean_dec_ref(v_self_67_);
v___x_76_ = lean_box(0);
lean_inc(v_a_68_);
lean_inc_ref(v_inst_65_);
lean_inc_ref(v_inst_66_);
v___x_111_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_66_, v_inst_65_, v_toHashSet_69_, v_a_68_);
switch(lean_obj_tag(v___x_111_))
{
case 0:
{
lean_dec_ref_known(v___x_111_, 3);
lean_dec_ref(v_inst_66_);
lean_dec_ref(v_inst_65_);
v___y_72_ = v_toHashSet_69_;
goto v___jp_71_;
}
case 1:
{
lean_object* v_index_112_; lean_object* v_size_113_; lean_object* v_keyArray_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v_index_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_index_112_);
lean_dec_ref_known(v___x_111_, 1);
v_size_113_ = lean_ctor_get(v_toHashSet_69_, 0);
v_keyArray_114_ = lean_ctor_get(v_toHashSet_69_, 1);
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_116_ = lean_nat_add(v_size_113_, v___x_115_);
v___x_117_ = lean_array_get_size(v_keyArray_114_);
v___x_118_ = lean_nat_dec_lt(v___x_116_, v___x_117_);
if (v___x_118_ == 0)
{
lean_dec(v___x_116_);
lean_dec(v_index_112_);
goto v___jp_101_;
}
else
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_119_ = lean_unsigned_to_nat(4u);
v___x_120_ = lean_nat_mul(v___x_116_, v___x_119_);
v___x_121_ = lean_unsigned_to_nat(3u);
v___x_122_ = lean_nat_mul(v___x_117_, v___x_121_);
v___x_123_ = lean_nat_dec_le(v___x_120_, v___x_122_);
lean_dec(v___x_122_);
lean_dec(v___x_120_);
if (v___x_123_ == 0)
{
lean_dec(v___x_116_);
lean_dec(v_index_112_);
goto v___jp_101_;
}
else
{
lean_object* v___x_124_; 
lean_dec_ref(v_inst_66_);
lean_dec_ref(v_inst_65_);
lean_inc(v_a_68_);
v___x_124_ = l_Std_DHashMap_Raw_setEntry___redArg(v_toHashSet_69_, v___x_116_, v_index_112_, v_a_68_, v___x_76_);
lean_dec(v_index_112_);
v___y_72_ = v___x_124_;
goto v___jp_71_;
}
}
}
default: 
{
lean_object* v_size_125_; lean_object* v_keyArray_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v_size_125_ = lean_ctor_get(v_toHashSet_69_, 0);
v_keyArray_126_ = lean_ctor_get(v_toHashSet_69_, 1);
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = lean_nat_add(v_size_125_, v___x_127_);
v___x_129_ = lean_array_get_size(v_keyArray_126_);
v___x_130_ = lean_nat_dec_lt(v___x_128_, v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
lean_dec(v___x_128_);
lean_inc_ref(v_inst_65_);
lean_inc_ref(v_inst_66_);
v___x_131_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_66_, v_inst_65_, v_toHashSet_69_);
v___y_85_ = v___x_131_;
goto v___jp_84_;
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_132_ = lean_unsigned_to_nat(4u);
v___x_133_ = lean_nat_mul(v___x_128_, v___x_132_);
lean_dec(v___x_128_);
v___x_134_ = lean_unsigned_to_nat(3u);
v___x_135_ = lean_nat_mul(v___x_129_, v___x_134_);
v___x_136_ = lean_nat_dec_le(v___x_133_, v___x_135_);
lean_dec(v___x_135_);
lean_dec(v___x_133_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; 
lean_inc_ref(v_inst_65_);
lean_inc_ref(v_inst_66_);
v___x_137_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_66_, v_inst_65_, v_toHashSet_69_);
v___y_85_ = v___x_137_;
goto v___jp_84_;
}
else
{
v___y_85_ = v_toHashSet_69_;
goto v___jp_84_;
}
}
}
}
v___jp_77_:
{
lean_object* v_size_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_size_80_ = lean_ctor_get(v___y_78_, 0);
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_add(v_size_80_, v___x_81_);
lean_inc(v_a_68_);
v___x_83_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_78_, v___x_82_, v_i_79_, v_a_68_, v___x_76_);
lean_dec(v_i_79_);
v___y_72_ = v___x_83_;
goto v___jp_71_;
}
v___jp_84_:
{
lean_object* v___x_86_; 
lean_inc(v_a_68_);
v___x_86_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_66_, v_inst_65_, v___y_85_, v_a_68_);
switch(lean_obj_tag(v___x_86_))
{
case 0:
{
lean_object* v_index_87_; lean_object* v_size_88_; lean_object* v___x_89_; 
v_index_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_index_87_);
lean_dec_ref_known(v___x_86_, 3);
v_size_88_ = lean_ctor_get(v___y_85_, 0);
lean_inc(v_size_88_);
lean_inc(v_a_68_);
v___x_89_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_85_, v_size_88_, v_index_87_, v_a_68_, v___x_76_);
lean_dec(v_index_87_);
v___y_72_ = v___x_89_;
goto v___jp_71_;
}
case 1:
{
lean_object* v_index_90_; 
v_index_90_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_index_90_);
lean_dec_ref_known(v___x_86_, 1);
v___y_78_ = v___y_85_;
v_i_79_ = v_index_90_;
goto v___jp_77_;
}
default: 
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_85_, v___x_91_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_index_93_; 
v_index_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc(v_index_93_);
lean_dec_ref_known(v___x_92_, 1);
v___y_78_ = v___y_85_;
v_i_79_ = v_index_93_;
goto v___jp_77_;
}
else
{
v___y_72_ = v___y_85_;
goto v___jp_71_;
}
}
}
}
v___jp_94_:
{
lean_object* v_size_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_size_97_ = lean_ctor_get(v___y_95_, 0);
v___x_98_ = lean_unsigned_to_nat(1u);
v___x_99_ = lean_nat_add(v_size_97_, v___x_98_);
lean_inc(v_a_68_);
v___x_100_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_95_, v___x_99_, v_i_96_, v_a_68_, v___x_76_);
lean_dec(v_i_96_);
v___y_72_ = v___x_100_;
goto v___jp_71_;
}
v___jp_101_:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_inc_ref(v_inst_65_);
lean_inc_ref(v_inst_66_);
v___x_102_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_66_, v_inst_65_, v_toHashSet_69_);
lean_inc(v_a_68_);
v___x_103_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_66_, v_inst_65_, v___x_102_, v_a_68_);
switch(lean_obj_tag(v___x_103_))
{
case 0:
{
lean_object* v_index_104_; lean_object* v_size_105_; lean_object* v___x_106_; 
v_index_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_index_104_);
lean_dec_ref_known(v___x_103_, 3);
v_size_105_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_size_105_);
lean_inc(v_a_68_);
v___x_106_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_102_, v_size_105_, v_index_104_, v_a_68_, v___x_76_);
lean_dec(v_index_104_);
v___y_72_ = v___x_106_;
goto v___jp_71_;
}
case 1:
{
lean_object* v_index_107_; 
v_index_107_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_index_107_);
lean_dec_ref_known(v___x_103_, 1);
v___y_95_ = v___x_102_;
v_i_96_ = v_index_107_;
goto v___jp_94_;
}
default: 
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_102_, v___x_108_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_index_110_; 
v_index_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_index_110_);
lean_dec_ref_known(v___x_109_, 1);
v___y_95_ = v___x_102_;
v_i_96_ = v_index_110_;
goto v___jp_94_;
}
else
{
v___y_72_ = v___x_102_;
goto v___jp_71_;
}
}
}
}
}
else
{
lean_dec(v_a_68_);
lean_dec_ref(v_inst_66_);
lean_dec_ref(v_inst_65_);
return v_self_67_;
}
v___jp_71_:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_array_push(v_toArray_70_, v_a_68_);
v___x_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_74_, 0, v___y_72_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert(lean_object* v_00_u03b1_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_self_141_, lean_object* v_a_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lake_OrdHashSet_insert___redArg(v_inst_139_, v_inst_140_, v_self_141_, v_a_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___redArg___lam__0(lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_x1_146_, lean_object* v_x2_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lake_OrdHashSet_insert___redArg(v_inst_144_, v_inst_145_, v_x1_146_, v_x2_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___redArg(lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_self_170_, lean_object* v_arr_171_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_array_get_size(v_arr_171_);
v___x_174_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_175_ = lean_nat_dec_lt(v___x_172_, v___x_173_);
if (v___x_175_ == 0)
{
lean_dec_ref(v_arr_171_);
lean_dec_ref(v_inst_169_);
lean_dec_ref(v_inst_168_);
return v_self_170_;
}
else
{
lean_object* v___f_176_; uint8_t v___x_177_; 
v___f_176_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_appendArray___redArg___lam__0), 4, 2);
lean_closure_set(v___f_176_, 0, v_inst_168_);
lean_closure_set(v___f_176_, 1, v_inst_169_);
v___x_177_ = lean_nat_dec_le(v___x_173_, v___x_173_);
if (v___x_177_ == 0)
{
if (v___x_175_ == 0)
{
lean_dec_ref(v___f_176_);
lean_dec_ref(v_arr_171_);
return v_self_170_;
}
else
{
size_t v___x_178_; size_t v___x_179_; lean_object* v___x_180_; 
v___x_178_ = ((size_t)0ULL);
v___x_179_ = lean_usize_of_nat(v___x_173_);
v___x_180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_174_, v___f_176_, v_arr_171_, v___x_178_, v___x_179_, v_self_170_);
return v___x_180_;
}
}
else
{
size_t v___x_181_; size_t v___x_182_; lean_object* v___x_183_; 
v___x_181_ = ((size_t)0ULL);
v___x_182_ = lean_usize_of_nat(v___x_173_);
v___x_183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_174_, v___f_176_, v_arr_171_, v___x_181_, v___x_182_, v_self_170_);
return v___x_183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray(lean_object* v_00_u03b1_184_, lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_self_187_, lean_object* v_arr_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lake_OrdHashSet_appendArray___redArg(v_inst_185_, v_inst_186_, v_self_187_, v_arr_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instHAppendArray___redArg(lean_object* v_inst_190_, lean_object* v_inst_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_appendArray), 5, 3);
lean_closure_set(v___x_192_, 0, lean_box(0));
lean_closure_set(v___x_192_, 1, v_inst_190_);
lean_closure_set(v___x_192_, 2, v_inst_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instHAppendArray(lean_object* v_00_u03b1_193_, lean_object* v_inst_194_, lean_object* v_inst_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_appendArray), 5, 3);
lean_closure_set(v___x_196_, 0, lean_box(0));
lean_closure_set(v___x_196_, 1, v_inst_194_);
lean_closure_set(v___x_196_, 2, v_inst_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_append___redArg(lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_self_199_, lean_object* v_other_200_){
_start:
{
lean_object* v_toArray_201_; lean_object* v___x_202_; 
v_toArray_201_ = lean_ctor_get(v_other_200_, 1);
lean_inc_ref(v_toArray_201_);
lean_dec_ref(v_other_200_);
v___x_202_ = l_Lake_OrdHashSet_appendArray___redArg(v_inst_197_, v_inst_198_, v_self_199_, v_toArray_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_append(lean_object* v_00_u03b1_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_self_206_, lean_object* v_other_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lake_OrdHashSet_append___redArg(v_inst_204_, v_inst_205_, v_self_206_, v_other_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instAppend___redArg(lean_object* v_inst_209_, lean_object* v_inst_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_append), 5, 3);
lean_closure_set(v___x_211_, 0, lean_box(0));
lean_closure_set(v___x_211_, 1, v_inst_209_);
lean_closure_set(v___x_211_, 2, v_inst_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instAppend(lean_object* v_00_u03b1_212_, lean_object* v_inst_213_, lean_object* v_inst_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_append), 5, 3);
lean_closure_set(v___x_215_, 0, lean_box(0));
lean_closure_set(v___x_215_, 1, v_inst_213_);
lean_closure_set(v___x_215_, 2, v_inst_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_ofArray___redArg(lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_arr_218_){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_array_get_size(v_arr_218_);
v___x_220_ = l_Lake_OrdHashSet_mkEmpty___redArg(v___x_219_);
v___x_221_ = l_Lake_OrdHashSet_appendArray___redArg(v_inst_216_, v_inst_217_, v___x_220_, v_arr_218_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_ofArray(lean_object* v_00_u03b1_222_, lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_arr_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lake_OrdHashSet_ofArray___redArg(v_inst_223_, v_inst_224_, v_arr_225_);
return v___x_226_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all___redArg___lam__0(lean_object* v_f_227_, uint8_t v___x_228_, lean_object* v_v_229_){
_start:
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = lean_apply_1(v_f_227_, v_v_229_);
v___x_231_ = lean_unbox(v___x_230_);
if (v___x_231_ == 0)
{
return v___x_228_;
}
else
{
uint8_t v___x_232_; 
v___x_232_ = 0;
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___redArg___lam__0___boxed(lean_object* v_f_233_, lean_object* v___x_234_, lean_object* v_v_235_){
_start:
{
uint8_t v___x_83__boxed_236_; uint8_t v_res_237_; lean_object* v_r_238_; 
v___x_83__boxed_236_ = lean_unbox(v___x_234_);
v_res_237_ = l_Lake_OrdHashSet_all___redArg___lam__0(v_f_233_, v___x_83__boxed_236_, v_v_235_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all___redArg(lean_object* v_f_239_, lean_object* v_self_240_){
_start:
{
lean_object* v_toArray_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v_toArray_241_ = lean_ctor_get(v_self_240_, 1);
lean_inc_ref(v_toArray_241_);
lean_dec_ref(v_self_240_);
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = lean_array_get_size(v_toArray_241_);
v___x_244_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_245_ = lean_nat_dec_lt(v___x_242_, v___x_243_);
if (v___x_245_ == 0)
{
uint8_t v___x_246_; 
lean_dec_ref(v_toArray_241_);
lean_dec_ref(v_f_239_);
v___x_246_ = 1;
return v___x_246_;
}
else
{
if (v___x_245_ == 0)
{
lean_dec_ref(v_toArray_241_);
lean_dec_ref(v_f_239_);
return v___x_245_;
}
else
{
lean_object* v___x_247_; lean_object* v___f_248_; size_t v___x_249_; size_t v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_247_ = lean_box(v___x_245_);
v___f_248_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_248_, 0, v_f_239_);
lean_closure_set(v___f_248_, 1, v___x_247_);
v___x_249_ = ((size_t)0ULL);
v___x_250_ = lean_usize_of_nat(v___x_243_);
v___x_251_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_244_, v___f_248_, v_toArray_241_, v___x_249_, v___x_250_);
v___x_252_ = lean_unbox(v___x_251_);
lean_dec(v___x_251_);
if (v___x_252_ == 0)
{
return v___x_245_;
}
else
{
uint8_t v___x_253_; 
v___x_253_ = 0;
return v___x_253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___redArg___boxed(lean_object* v_f_254_, lean_object* v_self_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_Lake_OrdHashSet_all___redArg(v_f_254_, v_self_255_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_all(lean_object* v_00_u03b1_258_, lean_object* v_inst_259_, lean_object* v_inst_260_, lean_object* v_f_261_, lean_object* v_self_262_){
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
uint8_t v___x_268_; 
lean_dec_ref(v_toArray_263_);
lean_dec_ref(v_f_261_);
v___x_268_ = 1;
return v___x_268_;
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
lean_object* v___x_269_; lean_object* v___f_270_; size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_269_ = lean_box(v___x_267_);
v___f_270_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_270_, 0, v_f_261_);
lean_closure_set(v___f_270_, 1, v___x_269_);
v___x_271_ = ((size_t)0ULL);
v___x_272_ = lean_usize_of_nat(v___x_265_);
v___x_273_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_266_, v___f_270_, v_toArray_263_, v___x_271_, v___x_272_);
v___x_274_ = lean_unbox(v___x_273_);
lean_dec(v___x_273_);
if (v___x_274_ == 0)
{
return v___x_267_;
}
else
{
uint8_t v___x_275_; 
v___x_275_ = 0;
return v___x_275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_all___boxed(lean_object* v_00_u03b1_276_, lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_f_279_, lean_object* v_self_280_){
_start:
{
uint8_t v_res_281_; lean_object* v_r_282_; 
v_res_281_ = l_Lake_OrdHashSet_all(v_00_u03b1_276_, v_inst_277_, v_inst_278_, v_f_279_, v_self_280_);
lean_dec_ref(v_inst_278_);
lean_dec_ref(v_inst_277_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_any___redArg___lam__0(lean_object* v_f_283_, lean_object* v_x_284_){
_start:
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_apply_1(v_f_283_, v_x_284_);
v___x_286_ = lean_unbox(v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___redArg___lam__0___boxed(lean_object* v_f_287_, lean_object* v_x_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Lake_OrdHashSet_any___redArg___lam__0(v_f_287_, v_x_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_any___redArg(lean_object* v_f_291_, lean_object* v_self_292_){
_start:
{
lean_object* v_toArray_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_toArray_293_ = lean_ctor_get(v_self_292_, 1);
lean_inc_ref(v_toArray_293_);
lean_dec_ref(v_self_292_);
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = lean_array_get_size(v_toArray_293_);
v___x_296_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_297_ = lean_nat_dec_lt(v___x_294_, v___x_295_);
if (v___x_297_ == 0)
{
lean_dec_ref(v_toArray_293_);
lean_dec_ref(v_f_291_);
return v___x_297_;
}
else
{
if (v___x_297_ == 0)
{
lean_dec_ref(v_toArray_293_);
lean_dec_ref(v_f_291_);
return v___x_297_;
}
else
{
lean_object* v___f_298_; size_t v___x_299_; size_t v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___f_298_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_298_, 0, v_f_291_);
v___x_299_ = ((size_t)0ULL);
v___x_300_ = lean_usize_of_nat(v___x_295_);
v___x_301_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_296_, v___f_298_, v_toArray_293_, v___x_299_, v___x_300_);
v___x_302_ = lean_unbox(v___x_301_);
lean_dec(v___x_301_);
return v___x_302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___redArg___boxed(lean_object* v_f_303_, lean_object* v_self_304_){
_start:
{
uint8_t v_res_305_; lean_object* v_r_306_; 
v_res_305_ = l_Lake_OrdHashSet_any___redArg(v_f_303_, v_self_304_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT uint8_t l_Lake_OrdHashSet_any(lean_object* v_00_u03b1_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_f_310_, lean_object* v_self_311_){
_start:
{
lean_object* v_toArray_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v_toArray_312_ = lean_ctor_get(v_self_311_, 1);
lean_inc_ref(v_toArray_312_);
lean_dec_ref(v_self_311_);
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_array_get_size(v_toArray_312_);
v___x_315_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_316_ = lean_nat_dec_lt(v___x_313_, v___x_314_);
if (v___x_316_ == 0)
{
lean_dec_ref(v_toArray_312_);
lean_dec_ref(v_f_310_);
return v___x_316_;
}
else
{
if (v___x_316_ == 0)
{
lean_dec_ref(v_toArray_312_);
lean_dec_ref(v_f_310_);
return v___x_316_;
}
else
{
lean_object* v___f_317_; size_t v___x_318_; size_t v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___f_317_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_317_, 0, v_f_310_);
v___x_318_ = ((size_t)0ULL);
v___x_319_ = lean_usize_of_nat(v___x_314_);
v___x_320_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_315_, v___f_317_, v_toArray_312_, v___x_318_, v___x_319_);
v___x_321_ = lean_unbox(v___x_320_);
lean_dec(v___x_320_);
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_any___boxed(lean_object* v_00_u03b1_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_f_325_, lean_object* v_self_326_){
_start:
{
uint8_t v_res_327_; lean_object* v_r_328_; 
v_res_327_ = l_Lake_OrdHashSet_any(v_00_u03b1_322_, v_inst_323_, v_inst_324_, v_f_325_, v_self_326_);
lean_dec_ref(v_inst_324_);
lean_dec_ref(v_inst_323_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___redArg___lam__0(lean_object* v_f_329_, lean_object* v_x1_330_, lean_object* v_x2_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = lean_apply_2(v_f_329_, v_x1_330_, v_x2_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___redArg(lean_object* v_f_333_, lean_object* v_init_334_, lean_object* v_self_335_){
_start:
{
lean_object* v_toArray_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v_toArray_336_ = lean_ctor_get(v_self_335_, 1);
lean_inc_ref(v_toArray_336_);
lean_dec_ref(v_self_335_);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_array_get_size(v_toArray_336_);
v___x_339_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_340_ = lean_nat_dec_lt(v___x_337_, v___x_338_);
if (v___x_340_ == 0)
{
lean_dec_ref(v_toArray_336_);
lean_dec(v_f_333_);
return v_init_334_;
}
else
{
lean_object* v___f_341_; uint8_t v___x_342_; 
v___f_341_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_341_, 0, v_f_333_);
v___x_342_ = lean_nat_dec_le(v___x_338_, v___x_338_);
if (v___x_342_ == 0)
{
if (v___x_340_ == 0)
{
lean_dec_ref(v___f_341_);
lean_dec_ref(v_toArray_336_);
return v_init_334_;
}
else
{
size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v___x_343_ = ((size_t)0ULL);
v___x_344_ = lean_usize_of_nat(v___x_338_);
v___x_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_339_, v___f_341_, v_toArray_336_, v___x_343_, v___x_344_, v_init_334_);
return v___x_345_;
}
}
else
{
size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; 
v___x_346_ = ((size_t)0ULL);
v___x_347_ = lean_usize_of_nat(v___x_338_);
v___x_348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_339_, v___f_341_, v_toArray_336_, v___x_346_, v___x_347_, v_init_334_);
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl(lean_object* v_00_u03b1_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_00_u03b2_352_, lean_object* v_f_353_, lean_object* v_init_354_, lean_object* v_self_355_){
_start:
{
lean_object* v_toArray_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v_toArray_356_ = lean_ctor_get(v_self_355_, 1);
lean_inc_ref(v_toArray_356_);
lean_dec_ref(v_self_355_);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_array_get_size(v_toArray_356_);
v___x_359_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_360_ = lean_nat_dec_lt(v___x_357_, v___x_358_);
if (v___x_360_ == 0)
{
lean_dec_ref(v_toArray_356_);
lean_dec(v_f_353_);
return v_init_354_;
}
else
{
lean_object* v___f_361_; uint8_t v___x_362_; 
v___f_361_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_361_, 0, v_f_353_);
v___x_362_ = lean_nat_dec_le(v___x_358_, v___x_358_);
if (v___x_362_ == 0)
{
if (v___x_360_ == 0)
{
lean_dec_ref(v___f_361_);
lean_dec_ref(v_toArray_356_);
return v_init_354_;
}
else
{
size_t v___x_363_; size_t v___x_364_; lean_object* v___x_365_; 
v___x_363_ = ((size_t)0ULL);
v___x_364_ = lean_usize_of_nat(v___x_358_);
v___x_365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_359_, v___f_361_, v_toArray_356_, v___x_363_, v___x_364_, v_init_354_);
return v___x_365_;
}
}
else
{
size_t v___x_366_; size_t v___x_367_; lean_object* v___x_368_; 
v___x_366_ = ((size_t)0ULL);
v___x_367_ = lean_usize_of_nat(v___x_358_);
v___x_368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_359_, v___f_361_, v_toArray_356_, v___x_366_, v___x_367_, v_init_354_);
return v___x_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldl___boxed(lean_object* v_00_u03b1_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_00_u03b2_372_, lean_object* v_f_373_, lean_object* v_init_374_, lean_object* v_self_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lake_OrdHashSet_foldl(v_00_u03b1_369_, v_inst_370_, v_inst_371_, v_00_u03b2_372_, v_f_373_, v_init_374_, v_self_375_);
lean_dec_ref(v_inst_371_);
lean_dec_ref(v_inst_370_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM___redArg(lean_object* v_inst_377_, lean_object* v_f_378_, lean_object* v_init_379_, lean_object* v_self_380_){
_start:
{
lean_object* v_toArray_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v_toArray_381_ = lean_ctor_get(v_self_380_, 1);
lean_inc_ref(v_toArray_381_);
lean_dec_ref(v_self_380_);
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = lean_array_get_size(v_toArray_381_);
v___x_384_ = lean_nat_dec_lt(v___x_382_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v_toApplicative_385_; lean_object* v_toPure_386_; lean_object* v___x_387_; 
lean_dec_ref(v_toArray_381_);
lean_dec(v_f_378_);
v_toApplicative_385_ = lean_ctor_get(v_inst_377_, 0);
lean_inc_ref(v_toApplicative_385_);
lean_dec_ref(v_inst_377_);
v_toPure_386_ = lean_ctor_get(v_toApplicative_385_, 1);
lean_inc(v_toPure_386_);
lean_dec_ref(v_toApplicative_385_);
v___x_387_ = lean_apply_2(v_toPure_386_, lean_box(0), v_init_379_);
return v___x_387_;
}
else
{
uint8_t v___x_388_; 
v___x_388_ = lean_nat_dec_le(v___x_383_, v___x_383_);
if (v___x_388_ == 0)
{
if (v___x_384_ == 0)
{
lean_object* v_toApplicative_389_; lean_object* v_toPure_390_; lean_object* v___x_391_; 
lean_dec_ref(v_toArray_381_);
lean_dec(v_f_378_);
v_toApplicative_389_ = lean_ctor_get(v_inst_377_, 0);
lean_inc_ref(v_toApplicative_389_);
lean_dec_ref(v_inst_377_);
v_toPure_390_ = lean_ctor_get(v_toApplicative_389_, 1);
lean_inc(v_toPure_390_);
lean_dec_ref(v_toApplicative_389_);
v___x_391_ = lean_apply_2(v_toPure_390_, lean_box(0), v_init_379_);
return v___x_391_;
}
else
{
size_t v___x_392_; size_t v___x_393_; lean_object* v___x_394_; 
v___x_392_ = ((size_t)0ULL);
v___x_393_ = lean_usize_of_nat(v___x_383_);
v___x_394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_377_, v_f_378_, v_toArray_381_, v___x_392_, v___x_393_, v_init_379_);
return v___x_394_;
}
}
else
{
size_t v___x_395_; size_t v___x_396_; lean_object* v___x_397_; 
v___x_395_ = ((size_t)0ULL);
v___x_396_ = lean_usize_of_nat(v___x_383_);
v___x_397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_377_, v_f_378_, v_toArray_381_, v___x_395_, v___x_396_, v_init_379_);
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM(lean_object* v_00_u03b1_398_, lean_object* v_inst_399_, lean_object* v_inst_400_, lean_object* v_m_401_, lean_object* v_00_u03b2_402_, lean_object* v_inst_403_, lean_object* v_f_404_, lean_object* v_init_405_, lean_object* v_self_406_){
_start:
{
lean_object* v_toArray_407_; lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v_toArray_407_ = lean_ctor_get(v_self_406_, 1);
lean_inc_ref(v_toArray_407_);
lean_dec_ref(v_self_406_);
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = lean_array_get_size(v_toArray_407_);
v___x_410_ = lean_nat_dec_lt(v___x_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v_toApplicative_411_; lean_object* v_toPure_412_; lean_object* v___x_413_; 
lean_dec_ref(v_toArray_407_);
lean_dec(v_f_404_);
v_toApplicative_411_ = lean_ctor_get(v_inst_403_, 0);
lean_inc_ref(v_toApplicative_411_);
lean_dec_ref(v_inst_403_);
v_toPure_412_ = lean_ctor_get(v_toApplicative_411_, 1);
lean_inc(v_toPure_412_);
lean_dec_ref(v_toApplicative_411_);
v___x_413_ = lean_apply_2(v_toPure_412_, lean_box(0), v_init_405_);
return v___x_413_;
}
else
{
uint8_t v___x_414_; 
v___x_414_ = lean_nat_dec_le(v___x_409_, v___x_409_);
if (v___x_414_ == 0)
{
if (v___x_410_ == 0)
{
lean_object* v_toApplicative_415_; lean_object* v_toPure_416_; lean_object* v___x_417_; 
lean_dec_ref(v_toArray_407_);
lean_dec(v_f_404_);
v_toApplicative_415_ = lean_ctor_get(v_inst_403_, 0);
lean_inc_ref(v_toApplicative_415_);
lean_dec_ref(v_inst_403_);
v_toPure_416_ = lean_ctor_get(v_toApplicative_415_, 1);
lean_inc(v_toPure_416_);
lean_dec_ref(v_toApplicative_415_);
v___x_417_ = lean_apply_2(v_toPure_416_, lean_box(0), v_init_405_);
return v___x_417_;
}
else
{
size_t v___x_418_; size_t v___x_419_; lean_object* v___x_420_; 
v___x_418_ = ((size_t)0ULL);
v___x_419_ = lean_usize_of_nat(v___x_409_);
v___x_420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_403_, v_f_404_, v_toArray_407_, v___x_418_, v___x_419_, v_init_405_);
return v___x_420_;
}
}
else
{
size_t v___x_421_; size_t v___x_422_; lean_object* v___x_423_; 
v___x_421_ = ((size_t)0ULL);
v___x_422_ = lean_usize_of_nat(v___x_409_);
v___x_423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_403_, v_f_404_, v_toArray_407_, v___x_421_, v___x_422_, v_init_405_);
return v___x_423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldlM___boxed(lean_object* v_00_u03b1_424_, lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_m_427_, lean_object* v_00_u03b2_428_, lean_object* v_inst_429_, lean_object* v_f_430_, lean_object* v_init_431_, lean_object* v_self_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lake_OrdHashSet_foldlM(v_00_u03b1_424_, v_inst_425_, v_inst_426_, v_m_427_, v_00_u03b2_428_, v_inst_429_, v_f_430_, v_init_431_, v_self_432_);
lean_dec_ref(v_inst_426_);
lean_dec_ref(v_inst_425_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr___redArg(lean_object* v_f_434_, lean_object* v_init_435_, lean_object* v_self_436_){
_start:
{
lean_object* v_toArray_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v_toArray_437_ = lean_ctor_get(v_self_436_, 1);
lean_inc_ref(v_toArray_437_);
lean_dec_ref(v_self_436_);
v___x_438_ = lean_array_get_size(v_toArray_437_);
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_441_ = lean_nat_dec_lt(v___x_439_, v___x_438_);
if (v___x_441_ == 0)
{
lean_dec_ref(v_toArray_437_);
lean_dec(v_f_434_);
return v_init_435_;
}
else
{
lean_object* v___f_442_; size_t v___x_443_; size_t v___x_444_; lean_object* v___x_445_; 
v___f_442_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_442_, 0, v_f_434_);
v___x_443_ = lean_usize_of_nat(v___x_438_);
v___x_444_ = ((size_t)0ULL);
v___x_445_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_440_, v___f_442_, v_toArray_437_, v___x_443_, v___x_444_, v_init_435_);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr(lean_object* v_00_u03b1_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_00_u03b2_449_, lean_object* v_f_450_, lean_object* v_init_451_, lean_object* v_self_452_){
_start:
{
lean_object* v_toArray_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v_toArray_453_ = lean_ctor_get(v_self_452_, 1);
lean_inc_ref(v_toArray_453_);
lean_dec_ref(v_self_452_);
v___x_454_ = lean_array_get_size(v_toArray_453_);
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = ((lean_object*)(l_Lake_OrdHashSet_appendArray___redArg___closed__9));
v___x_457_ = lean_nat_dec_lt(v___x_455_, v___x_454_);
if (v___x_457_ == 0)
{
lean_dec_ref(v_toArray_453_);
lean_dec(v_f_450_);
return v_init_451_;
}
else
{
lean_object* v___f_458_; size_t v___x_459_; size_t v___x_460_; lean_object* v___x_461_; 
v___f_458_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_458_, 0, v_f_450_);
v___x_459_ = lean_usize_of_nat(v___x_454_);
v___x_460_ = ((size_t)0ULL);
v___x_461_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_456_, v___f_458_, v_toArray_453_, v___x_459_, v___x_460_, v_init_451_);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldr___boxed(lean_object* v_00_u03b1_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_00_u03b2_465_, lean_object* v_f_466_, lean_object* v_init_467_, lean_object* v_self_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lake_OrdHashSet_foldr(v_00_u03b1_462_, v_inst_463_, v_inst_464_, v_00_u03b2_465_, v_f_466_, v_init_467_, v_self_468_);
lean_dec_ref(v_inst_464_);
lean_dec_ref(v_inst_463_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM___redArg(lean_object* v_inst_470_, lean_object* v_f_471_, lean_object* v_init_472_, lean_object* v_self_473_){
_start:
{
lean_object* v_toArray_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v_toArray_474_ = lean_ctor_get(v_self_473_, 1);
lean_inc_ref(v_toArray_474_);
lean_dec_ref(v_self_473_);
v___x_475_ = lean_array_get_size(v_toArray_474_);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_nat_dec_lt(v___x_476_, v___x_475_);
if (v___x_477_ == 0)
{
lean_object* v_toApplicative_478_; lean_object* v_toPure_479_; lean_object* v___x_480_; 
lean_dec_ref(v_toArray_474_);
lean_dec(v_f_471_);
v_toApplicative_478_ = lean_ctor_get(v_inst_470_, 0);
lean_inc_ref(v_toApplicative_478_);
lean_dec_ref(v_inst_470_);
v_toPure_479_ = lean_ctor_get(v_toApplicative_478_, 1);
lean_inc(v_toPure_479_);
lean_dec_ref(v_toApplicative_478_);
v___x_480_ = lean_apply_2(v_toPure_479_, lean_box(0), v_init_472_);
return v___x_480_;
}
else
{
size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; 
v___x_481_ = lean_usize_of_nat(v___x_475_);
v___x_482_ = ((size_t)0ULL);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_470_, v_f_471_, v_toArray_474_, v___x_481_, v___x_482_, v_init_472_);
return v___x_483_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM(lean_object* v_00_u03b1_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_m_487_, lean_object* v_00_u03b2_488_, lean_object* v_inst_489_, lean_object* v_f_490_, lean_object* v_init_491_, lean_object* v_self_492_){
_start:
{
lean_object* v_toArray_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_toArray_493_ = lean_ctor_get(v_self_492_, 1);
lean_inc_ref(v_toArray_493_);
lean_dec_ref(v_self_492_);
v___x_494_ = lean_array_get_size(v_toArray_493_);
v___x_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = lean_nat_dec_lt(v___x_495_, v___x_494_);
if (v___x_496_ == 0)
{
lean_object* v_toApplicative_497_; lean_object* v_toPure_498_; lean_object* v___x_499_; 
lean_dec_ref(v_toArray_493_);
lean_dec(v_f_490_);
v_toApplicative_497_ = lean_ctor_get(v_inst_489_, 0);
lean_inc_ref(v_toApplicative_497_);
lean_dec_ref(v_inst_489_);
v_toPure_498_ = lean_ctor_get(v_toApplicative_497_, 1);
lean_inc(v_toPure_498_);
lean_dec_ref(v_toApplicative_497_);
v___x_499_ = lean_apply_2(v_toPure_498_, lean_box(0), v_init_491_);
return v___x_499_;
}
else
{
size_t v___x_500_; size_t v___x_501_; lean_object* v___x_502_; 
v___x_500_ = lean_usize_of_nat(v___x_494_);
v___x_501_ = ((size_t)0ULL);
v___x_502_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_489_, v_f_490_, v_toArray_493_, v___x_500_, v___x_501_, v_init_491_);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_foldrM___boxed(lean_object* v_00_u03b1_503_, lean_object* v_inst_504_, lean_object* v_inst_505_, lean_object* v_m_506_, lean_object* v_00_u03b2_507_, lean_object* v_inst_508_, lean_object* v_f_509_, lean_object* v_init_510_, lean_object* v_self_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lake_OrdHashSet_foldrM(v_00_u03b1_503_, v_inst_504_, v_inst_505_, v_m_506_, v_00_u03b2_507_, v_inst_508_, v_f_509_, v_init_510_, v_self_511_);
lean_dec_ref(v_inst_505_);
lean_dec_ref(v_inst_504_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___redArg___lam__0(lean_object* v_f_513_, lean_object* v_x_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = lean_apply_1(v_f_513_, v___y_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___redArg(lean_object* v_inst_517_, lean_object* v_f_518_, lean_object* v_self_519_){
_start:
{
lean_object* v_toArray_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v_toArray_520_ = lean_ctor_get(v_self_519_, 1);
lean_inc_ref(v_toArray_520_);
lean_dec_ref(v_self_519_);
v___x_521_ = lean_unsigned_to_nat(0u);
v___x_522_ = lean_array_get_size(v_toArray_520_);
v___x_523_ = lean_box(0);
v___x_524_ = lean_nat_dec_lt(v___x_521_, v___x_522_);
if (v___x_524_ == 0)
{
lean_object* v_toApplicative_525_; lean_object* v_toPure_526_; lean_object* v___x_527_; 
lean_dec_ref(v_toArray_520_);
lean_dec(v_f_518_);
v_toApplicative_525_ = lean_ctor_get(v_inst_517_, 0);
lean_inc_ref(v_toApplicative_525_);
lean_dec_ref(v_inst_517_);
v_toPure_526_ = lean_ctor_get(v_toApplicative_525_, 1);
lean_inc(v_toPure_526_);
lean_dec_ref(v_toApplicative_525_);
v___x_527_ = lean_apply_2(v_toPure_526_, lean_box(0), v___x_523_);
return v___x_527_;
}
else
{
lean_object* v___f_528_; uint8_t v___x_529_; 
v___f_528_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_528_, 0, v_f_518_);
v___x_529_ = lean_nat_dec_le(v___x_522_, v___x_522_);
if (v___x_529_ == 0)
{
if (v___x_524_ == 0)
{
lean_object* v_toApplicative_530_; lean_object* v_toPure_531_; lean_object* v___x_532_; 
lean_dec_ref(v___f_528_);
lean_dec_ref(v_toArray_520_);
v_toApplicative_530_ = lean_ctor_get(v_inst_517_, 0);
lean_inc_ref(v_toApplicative_530_);
lean_dec_ref(v_inst_517_);
v_toPure_531_ = lean_ctor_get(v_toApplicative_530_, 1);
lean_inc(v_toPure_531_);
lean_dec_ref(v_toApplicative_530_);
v___x_532_ = lean_apply_2(v_toPure_531_, lean_box(0), v___x_523_);
return v___x_532_;
}
else
{
size_t v___x_533_; size_t v___x_534_; lean_object* v___x_535_; 
v___x_533_ = ((size_t)0ULL);
v___x_534_ = lean_usize_of_nat(v___x_522_);
v___x_535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_517_, v___f_528_, v_toArray_520_, v___x_533_, v___x_534_, v___x_523_);
return v___x_535_;
}
}
else
{
size_t v___x_536_; size_t v___x_537_; lean_object* v___x_538_; 
v___x_536_ = ((size_t)0ULL);
v___x_537_ = lean_usize_of_nat(v___x_522_);
v___x_538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_517_, v___f_528_, v_toArray_520_, v___x_536_, v___x_537_, v___x_523_);
return v___x_538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM(lean_object* v_00_u03b1_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_m_542_, lean_object* v_inst_543_, lean_object* v_f_544_, lean_object* v_self_545_){
_start:
{
lean_object* v_toArray_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v_toArray_546_ = lean_ctor_get(v_self_545_, 1);
lean_inc_ref(v_toArray_546_);
lean_dec_ref(v_self_545_);
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_array_get_size(v_toArray_546_);
v___x_549_ = lean_box(0);
v___x_550_ = lean_nat_dec_lt(v___x_547_, v___x_548_);
if (v___x_550_ == 0)
{
lean_object* v_toApplicative_551_; lean_object* v_toPure_552_; lean_object* v___x_553_; 
lean_dec_ref(v_toArray_546_);
lean_dec(v_f_544_);
v_toApplicative_551_ = lean_ctor_get(v_inst_543_, 0);
lean_inc_ref(v_toApplicative_551_);
lean_dec_ref(v_inst_543_);
v_toPure_552_ = lean_ctor_get(v_toApplicative_551_, 1);
lean_inc(v_toPure_552_);
lean_dec_ref(v_toApplicative_551_);
v___x_553_ = lean_apply_2(v_toPure_552_, lean_box(0), v___x_549_);
return v___x_553_;
}
else
{
lean_object* v___f_554_; uint8_t v___x_555_; 
v___f_554_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_554_, 0, v_f_544_);
v___x_555_ = lean_nat_dec_le(v___x_548_, v___x_548_);
if (v___x_555_ == 0)
{
if (v___x_550_ == 0)
{
lean_object* v_toApplicative_556_; lean_object* v_toPure_557_; lean_object* v___x_558_; 
lean_dec_ref(v___f_554_);
lean_dec_ref(v_toArray_546_);
v_toApplicative_556_ = lean_ctor_get(v_inst_543_, 0);
lean_inc_ref(v_toApplicative_556_);
lean_dec_ref(v_inst_543_);
v_toPure_557_ = lean_ctor_get(v_toApplicative_556_, 1);
lean_inc(v_toPure_557_);
lean_dec_ref(v_toApplicative_556_);
v___x_558_ = lean_apply_2(v_toPure_557_, lean_box(0), v___x_549_);
return v___x_558_;
}
else
{
size_t v___x_559_; size_t v___x_560_; lean_object* v___x_561_; 
v___x_559_ = ((size_t)0ULL);
v___x_560_ = lean_usize_of_nat(v___x_548_);
v___x_561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_543_, v___f_554_, v_toArray_546_, v___x_559_, v___x_560_, v___x_549_);
return v___x_561_;
}
}
else
{
size_t v___x_562_; size_t v___x_563_; lean_object* v___x_564_; 
v___x_562_ = ((size_t)0ULL);
v___x_563_ = lean_usize_of_nat(v___x_548_);
v___x_564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_543_, v___f_554_, v_toArray_546_, v___x_562_, v___x_563_, v___x_549_);
return v___x_564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forM___boxed(lean_object* v_00_u03b1_565_, lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_m_568_, lean_object* v_inst_569_, lean_object* v_f_570_, lean_object* v_self_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lake_OrdHashSet_forM(v_00_u03b1_565_, v_inst_566_, v_inst_567_, v_m_568_, v_inst_569_, v_f_570_, v_self_571_);
lean_dec_ref(v_inst_567_);
lean_dec_ref(v_inst_566_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___redArg___lam__0(lean_object* v_f_573_, lean_object* v_a_574_, lean_object* v_x_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = lean_apply_2(v_f_573_, v_a_574_, v___y_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___redArg(lean_object* v_inst_578_, lean_object* v_self_579_, lean_object* v_init_580_, lean_object* v_f_581_){
_start:
{
lean_object* v_toArray_582_; lean_object* v___f_583_; size_t v_sz_584_; size_t v___x_585_; lean_object* v___x_586_; 
v_toArray_582_ = lean_ctor_get(v_self_579_, 1);
lean_inc_ref(v_toArray_582_);
lean_dec_ref(v_self_579_);
v___f_583_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_583_, 0, v_f_581_);
v_sz_584_ = lean_array_size(v_toArray_582_);
v___x_585_ = ((size_t)0ULL);
v___x_586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_578_, v_toArray_582_, v___f_583_, v_sz_584_, v___x_585_, v_init_580_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn(lean_object* v_00_u03b1_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_m_590_, lean_object* v_00_u03b2_591_, lean_object* v_inst_592_, lean_object* v_self_593_, lean_object* v_init_594_, lean_object* v_f_595_){
_start:
{
lean_object* v_toArray_596_; lean_object* v___f_597_; size_t v_sz_598_; size_t v___x_599_; lean_object* v___x_600_; 
v_toArray_596_ = lean_ctor_get(v_self_593_, 1);
lean_inc_ref(v_toArray_596_);
lean_dec_ref(v_self_593_);
v___f_597_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_597_, 0, v_f_595_);
v_sz_598_ = lean_array_size(v_toArray_596_);
v___x_599_ = ((size_t)0ULL);
v___x_600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_592_, v_toArray_596_, v___f_597_, v_sz_598_, v___x_599_, v_init_594_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_forIn___boxed(lean_object* v_00_u03b1_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_m_604_, lean_object* v_00_u03b2_605_, lean_object* v_inst_606_, lean_object* v_self_607_, lean_object* v_init_608_, lean_object* v_f_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lake_OrdHashSet_forIn(v_00_u03b1_601_, v_inst_602_, v_inst_603_, v_m_604_, v_00_u03b2_605_, v_inst_606_, v_self_607_, v_init_608_, v_f_609_);
lean_dec_ref(v_inst_603_);
lean_dec_ref(v_inst_602_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0(lean_object* v___y_611_, lean_object* v_a_612_, lean_object* v_x_613_, lean_object* v___y_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_apply_2(v___y_611_, v_a_612_, v___y_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1(lean_object* v_inst_616_, lean_object* v_00_u03b2_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_toArray_621_; lean_object* v___f_622_; size_t v_sz_623_; size_t v___x_624_; lean_object* v___x_625_; 
v_toArray_621_ = lean_ctor_get(v___y_618_, 1);
lean_inc_ref(v_toArray_621_);
lean_dec_ref(v___y_618_);
v___f_622_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_622_, 0, v___y_620_);
v_sz_623_ = lean_array_size(v_toArray_621_);
v___x_624_ = ((size_t)0ULL);
v___x_625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_616_, v_toArray_621_, v___f_622_, v_sz_623_, v___x_624_, v___y_619_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___redArg(lean_object* v_inst_626_){
_start:
{
lean_object* v___f_627_; 
v___f_627_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_627_, 0, v_inst_626_);
return v___f_627_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad(lean_object* v_00_u03b1_628_, lean_object* v_inst_629_, lean_object* v_inst_630_, lean_object* v_m_631_, lean_object* v_inst_632_){
_start:
{
lean_object* v___f_633_; 
v___f_633_ = lean_alloc_closure((void*)(l_Lake_OrdHashSet_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_633_, 0, v_inst_632_);
return v___f_633_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_634_, lean_object* v_inst_635_, lean_object* v_inst_636_, lean_object* v_m_637_, lean_object* v_inst_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lake_OrdHashSet_instForInOfMonad(v_00_u03b1_634_, v_inst_635_, v_inst_636_, v_m_637_, v_inst_638_);
lean_dec_ref(v_inst_636_);
lean_dec_ref(v_inst_635_);
return v_res_639_;
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
