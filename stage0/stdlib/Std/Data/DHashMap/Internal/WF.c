// Lean compiler output
// Module: Std.Data.DHashMap.Internal.WF
// Imports: import all Std.Data.Internal.List.Associative import all Std.Data.DHashMap.Raw import all Std.Data.DHashMap.Internal.Defs public import Std.Data.DHashMap.Internal.Model import all Std.Data.DHashMap.Internal.AssocList.Basic import all Std.Data.DHashMap.RawDef import Init.Data.Array.Bootstrap import Init.Data.List.Nat.TakeDrop import Init.Data.List.TakeDrop
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_replicate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_replicate_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_replicate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_replicate_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_insertList_u2098_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_insertList_u2098_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_getEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_eraseList_u2098_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_eraseList_u2098_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__1_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__2_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__3 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__3_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__4 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__4_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__5 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__5_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__6 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__6_value;
static const lean_ctor_object l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__0_value),((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__1_value)}};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__7 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__7_value;
static const lean_ctor_object l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__7_value),((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__2_value),((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__3_value),((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__4_value),((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__5_value)}};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__8 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__8_value;
static const lean_ctor_object l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__8_value),((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__6_value)}};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__9 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__9_value;
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10;
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_replicate_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_){
_start:
{
lean_object* v_zero_5_; uint8_t v_isZero_6_; 
v_zero_5_ = lean_unsigned_to_nat(0u);
v_isZero_6_ = lean_nat_dec_eq(v_x_1_, v_zero_5_);
if (v_isZero_6_ == 1)
{
lean_object* v___x_7_; 
lean_dec(v_h__2_4_);
v___x_7_ = lean_apply_1(v_h__1_3_, v_x_2_);
return v___x_7_;
}
else
{
lean_object* v_one_8_; lean_object* v_n_9_; lean_object* v___x_10_; 
lean_dec(v_h__1_3_);
v_one_8_ = lean_unsigned_to_nat(1u);
v_n_9_ = lean_nat_sub(v_x_1_, v_one_8_);
v___x_10_ = lean_apply_2(v_h__2_4_, v_n_9_, v_x_2_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_replicate_match__1_splitter___redArg___boxed(lean_object* v_x_11_, lean_object* v_x_12_, lean_object* v_h__1_13_, lean_object* v_h__2_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l___private_Std_Data_DHashMap_Internal_WF_0__List_replicate_match__1_splitter___redArg(v_x_11_, v_x_12_, v_h__1_13_, v_h__2_14_);
lean_dec(v_x_11_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_replicate_match__1_splitter(lean_object* v_00_u03b1_16_, lean_object* v_motive_17_, lean_object* v_x_18_, lean_object* v_x_19_, lean_object* v_h__1_20_, lean_object* v_h__2_21_){
_start:
{
lean_object* v_zero_22_; uint8_t v_isZero_23_; 
v_zero_22_ = lean_unsigned_to_nat(0u);
v_isZero_23_ = lean_nat_dec_eq(v_x_18_, v_zero_22_);
if (v_isZero_23_ == 1)
{
lean_object* v___x_24_; 
lean_dec(v_h__2_21_);
v___x_24_ = lean_apply_1(v_h__1_20_, v_x_19_);
return v___x_24_;
}
else
{
lean_object* v_one_25_; lean_object* v_n_26_; lean_object* v___x_27_; 
lean_dec(v_h__1_20_);
v_one_25_ = lean_unsigned_to_nat(1u);
v_n_26_ = lean_nat_sub(v_x_18_, v_one_25_);
v___x_27_ = lean_apply_2(v_h__2_21_, v_n_26_, v_x_19_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_replicate_match__1_splitter___boxed(lean_object* v_00_u03b1_28_, lean_object* v_motive_29_, lean_object* v_x_30_, lean_object* v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l___private_Std_Data_DHashMap_Internal_WF_0__List_replicate_match__1_splitter(v_00_u03b1_28_, v_motive_29_, v_x_30_, v_x_31_, v_h__1_32_, v_h__2_33_);
lean_dec(v_x_30_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter___redArg(lean_object* v_x_35_, lean_object* v_x_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_){
_start:
{
if (lean_obj_tag(v_x_36_) == 0)
{
lean_object* v___x_39_; 
lean_dec(v_h__2_38_);
v___x_39_ = lean_apply_1(v_h__1_37_, v_x_35_);
return v___x_39_;
}
else
{
lean_object* v_key_40_; lean_object* v_value_41_; lean_object* v_tail_42_; lean_object* v___x_43_; 
lean_dec(v_h__1_37_);
v_key_40_ = lean_ctor_get(v_x_36_, 0);
lean_inc(v_key_40_);
v_value_41_ = lean_ctor_get(v_x_36_, 1);
lean_inc(v_value_41_);
v_tail_42_ = lean_ctor_get(v_x_36_, 2);
lean_inc(v_tail_42_);
lean_dec_ref_known(v_x_36_, 3);
v___x_43_ = lean_apply_4(v_h__2_38_, v_x_35_, v_key_40_, v_value_41_, v_tail_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter(lean_object* v_00_u03b1_44_, lean_object* v_00_u03b2_45_, lean_object* v_00_u03b4_46_, lean_object* v_motive_47_, lean_object* v_x_48_, lean_object* v_x_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
lean_object* v___x_52_; 
lean_dec(v_h__2_51_);
v___x_52_ = lean_apply_1(v_h__1_50_, v_x_48_);
return v___x_52_;
}
else
{
lean_object* v_key_53_; lean_object* v_value_54_; lean_object* v_tail_55_; lean_object* v___x_56_; 
lean_dec(v_h__1_50_);
v_key_53_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_key_53_);
v_value_54_ = lean_ctor_get(v_x_49_, 1);
lean_inc(v_value_54_);
v_tail_55_ = lean_ctor_get(v_x_49_, 2);
lean_inc(v_tail_55_);
lean_dec_ref_known(v_x_49_, 3);
v___x_56_ = lean_apply_4(v_h__2_51_, v_x_48_, v_key_53_, v_value_54_, v_tail_55_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__3_splitter___redArg(lean_object* v_x_57_, lean_object* v_x_58_, lean_object* v_h__1_59_, lean_object* v_h__2_60_){
_start:
{
if (lean_obj_tag(v_x_57_) == 0)
{
lean_object* v___x_61_; 
lean_dec(v_h__2_60_);
v___x_61_ = lean_apply_1(v_h__1_59_, v_x_58_);
return v___x_61_;
}
else
{
lean_object* v_key_62_; lean_object* v_value_63_; lean_object* v_tail_64_; lean_object* v___x_65_; 
lean_dec(v_h__1_59_);
v_key_62_ = lean_ctor_get(v_x_57_, 0);
lean_inc(v_key_62_);
v_value_63_ = lean_ctor_get(v_x_57_, 1);
lean_inc(v_value_63_);
v_tail_64_ = lean_ctor_get(v_x_57_, 2);
lean_inc(v_tail_64_);
lean_dec_ref_known(v_x_57_, 3);
v___x_65_ = lean_apply_4(v_h__2_60_, v_key_62_, v_value_63_, v_tail_64_, v_x_58_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__3_splitter(lean_object* v_00_u03b1_66_, lean_object* v_00_u03b2_67_, lean_object* v_00_u03b4_68_, lean_object* v_motive_69_, lean_object* v_x_70_, lean_object* v_x_71_, lean_object* v_h__1_72_, lean_object* v_h__2_73_){
_start:
{
if (lean_obj_tag(v_x_70_) == 0)
{
lean_object* v___x_74_; 
lean_dec(v_h__2_73_);
v___x_74_ = lean_apply_1(v_h__1_72_, v_x_71_);
return v___x_74_;
}
else
{
lean_object* v_key_75_; lean_object* v_value_76_; lean_object* v_tail_77_; lean_object* v___x_78_; 
lean_dec(v_h__1_72_);
v_key_75_ = lean_ctor_get(v_x_70_, 0);
lean_inc(v_key_75_);
v_value_76_ = lean_ctor_get(v_x_70_, 1);
lean_inc(v_value_76_);
v_tail_77_ = lean_ctor_get(v_x_70_, 2);
lean_inc(v_tail_77_);
lean_dec_ref_known(v_x_70_, 3);
v___x_78_ = lean_apply_4(v_h__2_73_, v_key_75_, v_value_76_, v_tail_77_, v_x_71_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__1_splitter___redArg(lean_object* v_____do__lift_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_){
_start:
{
if (lean_obj_tag(v_____do__lift_79_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_83_; 
lean_dec(v_h__2_81_);
v_a_82_ = lean_ctor_get(v_____do__lift_79_, 0);
lean_inc(v_a_82_);
lean_dec_ref_known(v_____do__lift_79_, 1);
v___x_83_ = lean_apply_1(v_h__1_80_, v_a_82_);
return v___x_83_;
}
else
{
lean_object* v_a_84_; lean_object* v___x_85_; 
lean_dec(v_h__1_80_);
v_a_84_ = lean_ctor_get(v_____do__lift_79_, 0);
lean_inc(v_a_84_);
lean_dec_ref_known(v_____do__lift_79_, 1);
v___x_85_ = lean_apply_1(v_h__2_81_, v_a_84_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__1_splitter(lean_object* v_00_u03b4_86_, lean_object* v_motive_87_, lean_object* v_____do__lift_88_, lean_object* v_h__1_89_, lean_object* v_h__2_90_){
_start:
{
if (lean_obj_tag(v_____do__lift_88_) == 0)
{
lean_object* v_a_91_; lean_object* v___x_92_; 
lean_dec(v_h__2_90_);
v_a_91_ = lean_ctor_get(v_____do__lift_88_, 0);
lean_inc(v_a_91_);
lean_dec_ref_known(v_____do__lift_88_, 1);
v___x_92_ = lean_apply_1(v_h__1_89_, v_a_91_);
return v___x_92_;
}
else
{
lean_object* v_a_93_; lean_object* v___x_94_; 
lean_dec(v_h__1_89_);
v_a_93_ = lean_ctor_get(v_____do__lift_88_, 0);
lean_inc(v_a_93_);
lean_dec_ref_known(v_____do__lift_88_, 1);
v___x_94_ = lean_apply_1(v_h__2_90_, v_a_93_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_95_, lean_object* v_h__1_96_, lean_object* v_h__2_97_){
_start:
{
if (lean_obj_tag(v_x_95_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_99_; 
lean_dec(v_h__2_97_);
v_a_98_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_a_98_);
lean_dec_ref_known(v_x_95_, 1);
v___x_99_ = lean_apply_1(v_h__1_96_, v_a_98_);
return v___x_99_;
}
else
{
lean_object* v_a_100_; lean_object* v___x_101_; 
lean_dec(v_h__1_96_);
v_a_100_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_a_100_);
lean_dec_ref_known(v_x_95_, 1);
v___x_101_ = lean_apply_1(v_h__2_97_, v_a_100_);
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_102_, lean_object* v_motive_103_, lean_object* v_x_104_, lean_object* v_h__1_105_, lean_object* v_h__2_106_){
_start:
{
if (lean_obj_tag(v_x_104_) == 0)
{
lean_object* v_a_107_; lean_object* v___x_108_; 
lean_dec(v_h__2_106_);
v_a_107_ = lean_ctor_get(v_x_104_, 0);
lean_inc(v_a_107_);
lean_dec_ref_known(v_x_104_, 1);
v___x_108_ = lean_apply_1(v_h__1_105_, v_a_107_);
return v___x_108_;
}
else
{
lean_object* v_a_109_; lean_object* v___x_110_; 
lean_dec(v_h__1_105_);
v_a_109_ = lean_ctor_get(v_x_104_, 0);
lean_inc(v_a_109_);
lean_dec_ref_known(v_x_104_, 1);
v___x_110_ = lean_apply_1(v_h__2_106_, v_a_109_);
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_111_, lean_object* v_h__1_112_, lean_object* v_h__2_113_){
_start:
{
if (lean_obj_tag(v_x_111_) == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec(v_h__1_112_);
v___x_114_ = lean_box(0);
v___x_115_ = lean_apply_1(v_h__2_113_, v___x_114_);
return v___x_115_;
}
else
{
lean_object* v_val_116_; lean_object* v___x_117_; 
lean_dec(v_h__2_113_);
v_val_116_ = lean_ctor_get(v_x_111_, 0);
lean_inc(v_val_116_);
lean_dec_ref_known(v_x_111_, 1);
v___x_117_ = lean_apply_1(v_h__1_112_, v_val_116_);
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_118_, lean_object* v_motive_119_, lean_object* v_x_120_, lean_object* v_h__1_121_, lean_object* v_h__2_122_){
_start:
{
if (lean_obj_tag(v_x_120_) == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec(v_h__1_121_);
v___x_123_ = lean_box(0);
v___x_124_ = lean_apply_1(v_h__2_122_, v___x_123_);
return v___x_124_;
}
else
{
lean_object* v_val_125_; lean_object* v___x_126_; 
lean_dec(v_h__2_122_);
v_val_125_ = lean_ctor_get(v_x_120_, 0);
lean_inc(v_val_125_);
lean_dec_ref_known(v_x_120_, 1);
v___x_126_ = lean_apply_1(v_h__1_121_, v_val_125_);
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__3_splitter___redArg(lean_object* v_data_127_, lean_object* v_h__1_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_apply_2(v_h__1_128_, v_data_127_, lean_box(0));
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__3_splitter(lean_object* v_00_u03b1_130_, lean_object* v_00_u03b2_131_, lean_object* v_motive_132_, lean_object* v_data_133_, lean_object* v_h__1_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lean_apply_2(v_h__1_134_, v_data_133_, lean_box(0));
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter___redArg(lean_object* v_m_136_, lean_object* v_h__1_137_){
_start:
{
lean_object* v_size_138_; lean_object* v_buckets_139_; lean_object* v___x_140_; 
v_size_138_ = lean_ctor_get(v_m_136_, 0);
lean_inc(v_size_138_);
v_buckets_139_ = lean_ctor_get(v_m_136_, 1);
lean_inc_ref(v_buckets_139_);
lean_dec_ref(v_m_136_);
v___x_140_ = lean_apply_3(v_h__1_137_, v_size_138_, v_buckets_139_, lean_box(0));
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter(lean_object* v_00_u03b1_141_, lean_object* v_00_u03b2_142_, lean_object* v_motive_143_, lean_object* v_m_144_, lean_object* v_h__1_145_){
_start:
{
lean_object* v_size_146_; lean_object* v_buckets_147_; lean_object* v___x_148_; 
v_size_146_ = lean_ctor_get(v_m_144_, 0);
lean_inc(v_size_146_);
v_buckets_147_ = lean_ctor_get(v_m_144_, 1);
lean_inc_ref(v_buckets_147_);
lean_dec_ref(v_m_144_);
v___x_148_ = lean_apply_3(v_h__1_145_, v_size_146_, v_buckets_147_, lean_box(0));
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___redArg(lean_object* v_x_149_, lean_object* v_h__1_150_, lean_object* v_h__2_151_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec(v_h__2_151_);
v___x_152_ = lean_box(0);
v___x_153_ = lean_apply_1(v_h__1_150_, v___x_152_);
return v___x_153_;
}
else
{
lean_object* v_val_154_; lean_object* v___x_155_; 
lean_dec(v_h__1_150_);
v_val_154_ = lean_ctor_get(v_x_149_, 0);
lean_inc(v_val_154_);
lean_dec_ref_known(v_x_149_, 1);
v___x_155_ = lean_apply_1(v_h__2_151_, v_val_154_);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(lean_object* v_00_u03b1_156_, lean_object* v_00_u03b2_157_, lean_object* v_a_158_, lean_object* v_motive_159_, lean_object* v_x_160_, lean_object* v_h__1_161_, lean_object* v_h__2_162_){
_start:
{
if (lean_obj_tag(v_x_160_) == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec(v_h__2_162_);
v___x_163_ = lean_box(0);
v___x_164_ = lean_apply_1(v_h__1_161_, v___x_163_);
return v___x_164_;
}
else
{
lean_object* v_val_165_; lean_object* v___x_166_; 
lean_dec(v_h__1_161_);
v_val_165_ = lean_ctor_get(v_x_160_, 0);
lean_inc(v_val_165_);
lean_dec_ref_known(v_x_160_, 1);
v___x_166_ = lean_apply_1(v_h__2_162_, v_val_165_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___boxed(lean_object* v_00_u03b1_167_, lean_object* v_00_u03b2_168_, lean_object* v_a_169_, lean_object* v_motive_170_, lean_object* v_x_171_, lean_object* v_h__1_172_, lean_object* v_h__2_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(v_00_u03b1_167_, v_00_u03b2_168_, v_a_169_, v_motive_170_, v_x_171_, v_h__1_172_, v_h__2_173_);
lean_dec(v_a_169_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter___redArg(lean_object* v_x_175_, lean_object* v_h__1_176_, lean_object* v_h__2_177_){
_start:
{
if (lean_obj_tag(v_x_175_) == 0)
{
lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v_h__2_177_);
v___x_178_ = lean_box(0);
v___x_179_ = lean_apply_1(v_h__1_176_, v___x_178_);
return v___x_179_;
}
else
{
lean_object* v_val_180_; lean_object* v___x_181_; 
lean_dec(v_h__1_176_);
v_val_180_ = lean_ctor_get(v_x_175_, 0);
lean_inc(v_val_180_);
lean_dec_ref_known(v_x_175_, 1);
v___x_181_ = lean_apply_1(v_h__2_177_, v_val_180_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter(lean_object* v_00_u03b2_182_, lean_object* v_motive_183_, lean_object* v_x_184_, lean_object* v_h__1_185_, lean_object* v_h__2_186_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec(v_h__2_186_);
v___x_187_ = lean_box(0);
v___x_188_ = lean_apply_1(v_h__1_185_, v___x_187_);
return v___x_188_;
}
else
{
lean_object* v_val_189_; lean_object* v___x_190_; 
lean_dec(v_h__1_185_);
v_val_189_ = lean_ctor_get(v_x_184_, 0);
lean_inc(v_val_189_);
lean_dec_ref_known(v_x_184_, 1);
v___x_190_ = lean_apply_1(v_h__2_186_, v_val_189_);
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_insertList_u2098_match__1_splitter___redArg(lean_object* v_l_191_, lean_object* v_h__1_192_, lean_object* v_h__2_193_){
_start:
{
if (lean_obj_tag(v_l_191_) == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec(v_h__2_193_);
v___x_194_ = lean_box(0);
v___x_195_ = lean_apply_1(v_h__1_192_, v___x_194_);
return v___x_195_;
}
else
{
lean_object* v_head_196_; lean_object* v_tail_197_; lean_object* v___x_198_; 
lean_dec(v_h__1_192_);
v_head_196_ = lean_ctor_get(v_l_191_, 0);
lean_inc(v_head_196_);
v_tail_197_ = lean_ctor_get(v_l_191_, 1);
lean_inc(v_tail_197_);
lean_dec_ref_known(v_l_191_, 2);
v___x_198_ = lean_apply_2(v_h__2_193_, v_head_196_, v_tail_197_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_insertList_u2098_match__1_splitter(lean_object* v_00_u03b1_199_, lean_object* v_00_u03b2_200_, lean_object* v_motive_201_, lean_object* v_l_202_, lean_object* v_h__1_203_, lean_object* v_h__2_204_){
_start:
{
if (lean_obj_tag(v_l_202_) == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec(v_h__2_204_);
v___x_205_ = lean_box(0);
v___x_206_ = lean_apply_1(v_h__1_203_, v___x_205_);
return v___x_206_;
}
else
{
lean_object* v_head_207_; lean_object* v_tail_208_; lean_object* v___x_209_; 
lean_dec(v_h__1_203_);
v_head_207_ = lean_ctor_get(v_l_202_, 0);
lean_inc(v_head_207_);
v_tail_208_ = lean_ctor_get(v_l_202_, 1);
lean_inc(v_tail_208_);
lean_dec_ref_known(v_l_202_, 2);
v___x_209_ = lean_apply_2(v_h__2_204_, v_head_207_, v_tail_208_);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_210_, lean_object* v_h__1_211_, lean_object* v_h__2_212_){
_start:
{
if (lean_obj_tag(v_x_210_) == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec(v_h__2_212_);
v___x_213_ = lean_box(0);
v___x_214_ = lean_apply_1(v_h__1_211_, v___x_213_);
return v___x_214_;
}
else
{
lean_object* v_head_215_; lean_object* v_tail_216_; lean_object* v_fst_217_; lean_object* v_snd_218_; lean_object* v___x_219_; 
lean_dec(v_h__1_211_);
v_head_215_ = lean_ctor_get(v_x_210_, 0);
lean_inc(v_head_215_);
v_tail_216_ = lean_ctor_get(v_x_210_, 1);
lean_inc(v_tail_216_);
lean_dec_ref_known(v_x_210_, 2);
v_fst_217_ = lean_ctor_get(v_head_215_, 0);
lean_inc(v_fst_217_);
v_snd_218_ = lean_ctor_get(v_head_215_, 1);
lean_inc(v_snd_218_);
lean_dec(v_head_215_);
v___x_219_ = lean_apply_3(v_h__2_212_, v_fst_217_, v_snd_218_, v_tail_216_);
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_220_, lean_object* v_00_u03b2_221_, lean_object* v_motive_222_, lean_object* v_x_223_, lean_object* v_h__1_224_, lean_object* v_h__2_225_){
_start:
{
if (lean_obj_tag(v_x_223_) == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec(v_h__2_225_);
v___x_226_ = lean_box(0);
v___x_227_ = lean_apply_1(v_h__1_224_, v___x_226_);
return v___x_227_;
}
else
{
lean_object* v_head_228_; lean_object* v_tail_229_; lean_object* v_fst_230_; lean_object* v_snd_231_; lean_object* v___x_232_; 
lean_dec(v_h__1_224_);
v_head_228_ = lean_ctor_get(v_x_223_, 0);
lean_inc(v_head_228_);
v_tail_229_ = lean_ctor_get(v_x_223_, 1);
lean_inc(v_tail_229_);
lean_dec_ref_known(v_x_223_, 2);
v_fst_230_ = lean_ctor_get(v_head_228_, 0);
lean_inc(v_fst_230_);
v_snd_231_ = lean_ctor_get(v_head_228_, 1);
lean_inc(v_snd_231_);
lean_dec(v_head_228_);
v___x_232_ = lean_apply_3(v_h__2_225_, v_fst_230_, v_snd_231_, v_tail_229_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_eraseList_u2098_match__1_splitter___redArg(lean_object* v_l_233_, lean_object* v_h__1_234_, lean_object* v_h__2_235_){
_start:
{
if (lean_obj_tag(v_l_233_) == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v_h__2_235_);
v___x_236_ = lean_box(0);
v___x_237_ = lean_apply_1(v_h__1_234_, v___x_236_);
return v___x_237_;
}
else
{
lean_object* v_head_238_; lean_object* v_tail_239_; lean_object* v___x_240_; 
lean_dec(v_h__1_234_);
v_head_238_ = lean_ctor_get(v_l_233_, 0);
lean_inc(v_head_238_);
v_tail_239_ = lean_ctor_get(v_l_233_, 1);
lean_inc(v_tail_239_);
lean_dec_ref_known(v_l_233_, 2);
v___x_240_ = lean_apply_2(v_h__2_235_, v_head_238_, v_tail_239_);
return v___x_240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_eraseList_u2098_match__1_splitter(lean_object* v_00_u03b1_241_, lean_object* v_motive_242_, lean_object* v_l_243_, lean_object* v_h__1_244_, lean_object* v_h__2_245_){
_start:
{
if (lean_obj_tag(v_l_243_) == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec(v_h__2_245_);
v___x_246_ = lean_box(0);
v___x_247_ = lean_apply_1(v_h__1_244_, v___x_246_);
return v___x_247_;
}
else
{
lean_object* v_head_248_; lean_object* v_tail_249_; lean_object* v___x_250_; 
lean_dec(v_h__1_244_);
v_head_248_ = lean_ctor_get(v_l_243_, 0);
lean_inc(v_head_248_);
v_tail_249_ = lean_ctor_get(v_l_243_, 1);
lean_inc(v_tail_249_);
lean_dec_ref_known(v_l_243_, 2);
v___x_250_ = lean_apply_2(v_h__2_245_, v_head_248_, v_tail_249_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___redArg(lean_object* v_toInsert_251_, lean_object* v_h__1_252_, lean_object* v_h__2_253_){
_start:
{
if (lean_obj_tag(v_toInsert_251_) == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v_h__2_253_);
v___x_254_ = lean_box(0);
v___x_255_ = lean_apply_1(v_h__1_252_, v___x_254_);
return v___x_255_;
}
else
{
lean_object* v_head_256_; lean_object* v_tail_257_; lean_object* v___x_258_; 
lean_dec(v_h__1_252_);
v_head_256_ = lean_ctor_get(v_toInsert_251_, 0);
lean_inc(v_head_256_);
v_tail_257_ = lean_ctor_get(v_toInsert_251_, 1);
lean_inc(v_tail_257_);
lean_dec_ref_known(v_toInsert_251_, 2);
v___x_258_ = lean_apply_2(v_h__2_253_, v_head_256_, v_tail_257_);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter(lean_object* v_00_u03b1_259_, lean_object* v_motive_260_, lean_object* v_toInsert_261_, lean_object* v_h__1_262_, lean_object* v_h__2_263_){
_start:
{
if (lean_obj_tag(v_toInsert_261_) == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v_h__2_263_);
v___x_264_ = lean_box(0);
v___x_265_ = lean_apply_1(v_h__1_262_, v___x_264_);
return v___x_265_;
}
else
{
lean_object* v_head_266_; lean_object* v_tail_267_; lean_object* v___x_268_; 
lean_dec(v_h__1_262_);
v_head_266_ = lean_ctor_get(v_toInsert_261_, 0);
lean_inc(v_head_266_);
v_tail_267_ = lean_ctor_get(v_toInsert_261_, 1);
lean_inc(v_tail_267_);
lean_dec_ref_known(v_toInsert_261_, 2);
v___x_268_ = lean_apply_2(v_h__2_263_, v_head_266_, v_tail_267_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter___redArg(lean_object* v_x_269_, lean_object* v_h__1_270_, lean_object* v_h__2_271_){
_start:
{
if (lean_obj_tag(v_x_269_) == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec(v_h__1_270_);
v___x_272_ = lean_box(0);
v___x_273_ = lean_apply_1(v_h__2_271_, v___x_272_);
return v___x_273_;
}
else
{
lean_object* v_val_274_; lean_object* v___x_275_; 
lean_dec(v_h__2_271_);
v_val_274_ = lean_ctor_get(v_x_269_, 0);
lean_inc(v_val_274_);
lean_dec_ref_known(v_x_269_, 1);
v___x_275_ = lean_apply_1(v_h__1_270_, v_val_274_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter(lean_object* v_00_u03b1_276_, lean_object* v_00_u03b2_277_, lean_object* v_motive_278_, lean_object* v_x_279_, lean_object* v_h__1_280_, lean_object* v_h__2_281_){
_start:
{
if (lean_obj_tag(v_x_279_) == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec(v_h__1_280_);
v___x_282_ = lean_box(0);
v___x_283_ = lean_apply_1(v_h__2_281_, v___x_282_);
return v___x_283_;
}
else
{
lean_object* v_val_284_; lean_object* v___x_285_; 
lean_dec(v_h__2_281_);
v_val_284_ = lean_ctor_get(v_x_279_, 0);
lean_inc(v_val_284_);
lean_dec_ref_known(v_x_279_, 1);
v___x_285_ = lean_apply_1(v_h__1_280_, v_val_284_);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098_match__1_splitter___redArg(lean_object* v_x_286_, lean_object* v_h__1_287_, lean_object* v_h__2_288_){
_start:
{
if (lean_obj_tag(v_x_286_) == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v_h__1_287_);
v___x_289_ = lean_box(0);
v___x_290_ = lean_apply_1(v_h__2_288_, v___x_289_);
return v___x_290_;
}
else
{
lean_object* v_val_291_; lean_object* v___x_292_; 
lean_dec(v_h__2_288_);
v_val_291_ = lean_ctor_get(v_x_286_, 0);
lean_inc(v_val_291_);
lean_dec_ref_known(v_x_286_, 1);
v___x_292_ = lean_apply_1(v_h__1_287_, v_val_291_);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098_match__1_splitter(lean_object* v_00_u03b1_293_, lean_object* v_00_u03b2_294_, lean_object* v_motive_295_, lean_object* v_x_296_, lean_object* v_h__1_297_, lean_object* v_h__2_298_){
_start:
{
if (lean_obj_tag(v_x_296_) == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec(v_h__1_297_);
v___x_299_ = lean_box(0);
v___x_300_ = lean_apply_1(v_h__2_298_, v___x_299_);
return v___x_300_;
}
else
{
lean_object* v_val_301_; lean_object* v___x_302_; 
lean_dec(v_h__2_298_);
v_val_301_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_val_301_);
lean_dec_ref_known(v_x_296_, 1);
v___x_302_ = lean_apply_1(v_h__1_297_, v_val_301_);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0(lean_object* v_inst_303_, lean_object* v_inst_304_, lean_object* v_m_u2081_305_, lean_object* v_x1_306_, lean_object* v_x2_307_, lean_object* v_x3_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(v_inst_303_, v_inst_304_, v_m_u2081_305_, v_x1_306_, v_x2_307_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0___boxed(lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_m_u2081_312_, lean_object* v_x1_313_, lean_object* v_x2_314_, lean_object* v_x3_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0(v_inst_310_, v_inst_311_, v_m_u2081_312_, v_x1_313_, v_x2_314_, v_x3_315_);
lean_dec(v_x3_315_);
lean_dec_ref(v_m_u2081_312_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__1(lean_object* v___x_317_, lean_object* v___f_318_, lean_object* v_acc_319_, lean_object* v_l_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_317_, v___f_318_, v_acc_319_, v_l_320_);
return v___x_321_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_box(0);
v___x_342_ = lean_unsigned_to_nat(16u);
v___x_343_ = lean_mk_array(v___x_342_, v___x_341_);
return v___x_343_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10, &l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10_once, _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg(lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_m_u2081_349_, lean_object* v_m_u2082_350_){
_start:
{
lean_object* v___x_351_; lean_object* v_buckets_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_351_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__9));
v_buckets_352_ = lean_ctor_get(v_m_u2082_350_, 1);
lean_inc_ref(v_buckets_352_);
lean_dec_ref(v_m_u2082_350_);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11, &l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11_once, _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11);
v___x_355_ = lean_array_get_size(v_buckets_352_);
v___x_356_ = lean_nat_dec_lt(v___x_353_, v___x_355_);
if (v___x_356_ == 0)
{
lean_dec_ref(v_buckets_352_);
lean_dec_ref(v_m_u2081_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
return v___x_354_;
}
else
{
lean_object* v___f_357_; lean_object* v___f_358_; size_t v___x_359_; size_t v___x_360_; lean_object* v___x_361_; 
v___f_357_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_357_, 0, v_inst_347_);
lean_closure_set(v___f_357_, 1, v_inst_348_);
lean_closure_set(v___f_357_, 2, v_m_u2081_349_);
v___f_358_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__1), 4, 2);
lean_closure_set(v___f_358_, 0, v___x_351_);
lean_closure_set(v___f_358_, 1, v___f_357_);
v___x_359_ = ((size_t)0ULL);
v___x_360_ = lean_usize_of_nat(v___x_355_);
v___x_361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_351_, v___f_358_, v_buckets_352_, v___x_359_, v___x_360_, v___x_354_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098(lean_object* v_00_u03b1_362_, lean_object* v_00_u03b2_363_, lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_m_u2081_366_, lean_object* v_m_u2082_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg(v_inst_364_, v_inst_365_, v_m_u2081_366_, v_m_u2082_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098_match__1_splitter___redArg(lean_object* v_l_369_, lean_object* v_h__1_370_, lean_object* v_h__2_371_){
_start:
{
if (lean_obj_tag(v_l_369_) == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; 
lean_dec(v_h__2_371_);
v___x_372_ = lean_box(0);
v___x_373_ = lean_apply_1(v_h__1_370_, v___x_372_);
return v___x_373_;
}
else
{
lean_object* v_head_374_; lean_object* v_tail_375_; lean_object* v___x_376_; 
lean_dec(v_h__1_370_);
v_head_374_ = lean_ctor_get(v_l_369_, 0);
lean_inc(v_head_374_);
v_tail_375_ = lean_ctor_get(v_l_369_, 1);
lean_inc(v_tail_375_);
lean_dec_ref_known(v_l_369_, 2);
v___x_376_ = lean_apply_2(v_h__2_371_, v_head_374_, v_tail_375_);
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098_match__1_splitter(lean_object* v_00_u03b1_377_, lean_object* v_00_u03b2_378_, lean_object* v_motive_379_, lean_object* v_l_380_, lean_object* v_h__1_381_, lean_object* v_h__2_382_){
_start:
{
if (lean_obj_tag(v_l_380_) == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec(v_h__2_382_);
v___x_383_ = lean_box(0);
v___x_384_ = lean_apply_1(v_h__1_381_, v___x_383_);
return v___x_384_;
}
else
{
lean_object* v_head_385_; lean_object* v_tail_386_; lean_object* v___x_387_; 
lean_dec(v_h__1_381_);
v_head_385_ = lean_ctor_get(v_l_380_, 0);
lean_inc(v_head_385_);
v_tail_386_ = lean_ctor_get(v_l_380_, 1);
lean_inc(v_tail_386_);
lean_dec_ref_known(v_l_380_, 2);
v___x_387_ = lean_apply_2(v_h__2_382_, v_head_385_, v_tail_386_);
return v___x_387_;
}
}
}
lean_object* runtime_initialize_Std_Data_Internal_List_Associative(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Raw(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Model(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_RawDef(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_Internal_WF(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_RawDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DHashMap_Internal_WF(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Internal_List_Associative(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Raw(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_Model(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_RawDef(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_Internal_WF(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Internal_List_Associative(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_RawDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DHashMap_Internal_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DHashMap_Internal_WF(builtin);
}
#ifdef __cplusplus
}
#endif
