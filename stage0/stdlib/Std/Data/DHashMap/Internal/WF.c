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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_getEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_5_; 
lean_dec(v_h__2_4_);
v___x_5_ = lean_apply_1(v_h__1_3_, v_x_1_);
return v___x_5_;
}
else
{
lean_object* v_key_6_; lean_object* v_value_7_; lean_object* v_tail_8_; lean_object* v___x_9_; 
lean_dec(v_h__1_3_);
v_key_6_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_key_6_);
v_value_7_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_value_7_);
v_tail_8_ = lean_ctor_get(v_x_2_, 2);
lean_inc(v_tail_8_);
lean_dec_ref(v_x_2_);
v___x_9_ = lean_apply_4(v_h__2_4_, v_x_1_, v_key_6_, v_value_7_, v_tail_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter(lean_object* v_00_u03b1_10_, lean_object* v_00_u03b2_11_, lean_object* v_00_u03b4_12_, lean_object* v_motive_13_, lean_object* v_x_14_, lean_object* v_x_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_){
_start:
{
if (lean_obj_tag(v_x_15_) == 0)
{
lean_object* v___x_18_; 
lean_dec(v_h__2_17_);
v___x_18_ = lean_apply_1(v_h__1_16_, v_x_14_);
return v___x_18_;
}
else
{
lean_object* v_key_19_; lean_object* v_value_20_; lean_object* v_tail_21_; lean_object* v___x_22_; 
lean_dec(v_h__1_16_);
v_key_19_ = lean_ctor_get(v_x_15_, 0);
lean_inc(v_key_19_);
v_value_20_ = lean_ctor_get(v_x_15_, 1);
lean_inc(v_value_20_);
v_tail_21_ = lean_ctor_get(v_x_15_, 2);
lean_inc(v_tail_21_);
lean_dec_ref(v_x_15_);
v___x_22_ = lean_apply_4(v_h__2_17_, v_x_14_, v_key_19_, v_value_20_, v_tail_21_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__3_splitter___redArg(lean_object* v_x_23_, lean_object* v_x_24_, lean_object* v_h__1_25_, lean_object* v_h__2_26_){
_start:
{
if (lean_obj_tag(v_x_23_) == 0)
{
lean_object* v___x_27_; 
lean_dec(v_h__2_26_);
v___x_27_ = lean_apply_1(v_h__1_25_, v_x_24_);
return v___x_27_;
}
else
{
lean_object* v_key_28_; lean_object* v_value_29_; lean_object* v_tail_30_; lean_object* v___x_31_; 
lean_dec(v_h__1_25_);
v_key_28_ = lean_ctor_get(v_x_23_, 0);
lean_inc(v_key_28_);
v_value_29_ = lean_ctor_get(v_x_23_, 1);
lean_inc(v_value_29_);
v_tail_30_ = lean_ctor_get(v_x_23_, 2);
lean_inc(v_tail_30_);
lean_dec_ref(v_x_23_);
v___x_31_ = lean_apply_4(v_h__2_26_, v_key_28_, v_value_29_, v_tail_30_, v_x_24_);
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__3_splitter(lean_object* v_00_u03b1_32_, lean_object* v_00_u03b2_33_, lean_object* v_00_u03b4_34_, lean_object* v_motive_35_, lean_object* v_x_36_, lean_object* v_x_37_, lean_object* v_h__1_38_, lean_object* v_h__2_39_){
_start:
{
if (lean_obj_tag(v_x_36_) == 0)
{
lean_object* v___x_40_; 
lean_dec(v_h__2_39_);
v___x_40_ = lean_apply_1(v_h__1_38_, v_x_37_);
return v___x_40_;
}
else
{
lean_object* v_key_41_; lean_object* v_value_42_; lean_object* v_tail_43_; lean_object* v___x_44_; 
lean_dec(v_h__1_38_);
v_key_41_ = lean_ctor_get(v_x_36_, 0);
lean_inc(v_key_41_);
v_value_42_ = lean_ctor_get(v_x_36_, 1);
lean_inc(v_value_42_);
v_tail_43_ = lean_ctor_get(v_x_36_, 2);
lean_inc(v_tail_43_);
lean_dec_ref(v_x_36_);
v___x_44_ = lean_apply_4(v_h__2_39_, v_key_41_, v_value_42_, v_tail_43_, v_x_37_);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__1_splitter___redArg(lean_object* v_____do__lift_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_){
_start:
{
if (lean_obj_tag(v_____do__lift_45_) == 0)
{
lean_object* v_a_48_; lean_object* v___x_49_; 
lean_dec(v_h__2_47_);
v_a_48_ = lean_ctor_get(v_____do__lift_45_, 0);
lean_inc(v_a_48_);
lean_dec_ref(v_____do__lift_45_);
v___x_49_ = lean_apply_1(v_h__1_46_, v_a_48_);
return v___x_49_;
}
else
{
lean_object* v_a_50_; lean_object* v___x_51_; 
lean_dec(v_h__1_46_);
v_a_50_ = lean_ctor_get(v_____do__lift_45_, 0);
lean_inc(v_a_50_);
lean_dec_ref(v_____do__lift_45_);
v___x_51_ = lean_apply_1(v_h__2_47_, v_a_50_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__1_splitter(lean_object* v_00_u03b4_52_, lean_object* v_motive_53_, lean_object* v_____do__lift_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_){
_start:
{
if (lean_obj_tag(v_____do__lift_54_) == 0)
{
lean_object* v_a_57_; lean_object* v___x_58_; 
lean_dec(v_h__2_56_);
v_a_57_ = lean_ctor_get(v_____do__lift_54_, 0);
lean_inc(v_a_57_);
lean_dec_ref(v_____do__lift_54_);
v___x_58_ = lean_apply_1(v_h__1_55_, v_a_57_);
return v___x_58_;
}
else
{
lean_object* v_a_59_; lean_object* v___x_60_; 
lean_dec(v_h__1_55_);
v_a_59_ = lean_ctor_get(v_____do__lift_54_, 0);
lean_inc(v_a_59_);
lean_dec_ref(v_____do__lift_54_);
v___x_60_ = lean_apply_1(v_h__2_56_, v_a_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_){
_start:
{
if (lean_obj_tag(v_x_61_) == 0)
{
lean_object* v_a_64_; lean_object* v___x_65_; 
lean_dec(v_h__2_63_);
v_a_64_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_a_64_);
lean_dec_ref(v_x_61_);
v___x_65_ = lean_apply_1(v_h__1_62_, v_a_64_);
return v___x_65_;
}
else
{
lean_object* v_a_66_; lean_object* v___x_67_; 
lean_dec(v_h__1_62_);
v_a_66_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_a_66_);
lean_dec_ref(v_x_61_);
v___x_67_ = lean_apply_1(v_h__2_63_, v_a_66_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_68_, lean_object* v_motive_69_, lean_object* v_x_70_, lean_object* v_h__1_71_, lean_object* v_h__2_72_){
_start:
{
if (lean_obj_tag(v_x_70_) == 0)
{
lean_object* v_a_73_; lean_object* v___x_74_; 
lean_dec(v_h__2_72_);
v_a_73_ = lean_ctor_get(v_x_70_, 0);
lean_inc(v_a_73_);
lean_dec_ref(v_x_70_);
v___x_74_ = lean_apply_1(v_h__1_71_, v_a_73_);
return v___x_74_;
}
else
{
lean_object* v_a_75_; lean_object* v___x_76_; 
lean_dec(v_h__1_71_);
v_a_75_ = lean_ctor_get(v_x_70_, 0);
lean_inc(v_a_75_);
lean_dec_ref(v_x_70_);
v___x_76_ = lean_apply_1(v_h__2_72_, v_a_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_77_, lean_object* v_h__1_78_, lean_object* v_h__2_79_){
_start:
{
if (lean_obj_tag(v_x_77_) == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec(v_h__1_78_);
v___x_80_ = lean_box(0);
v___x_81_ = lean_apply_1(v_h__2_79_, v___x_80_);
return v___x_81_;
}
else
{
lean_object* v_val_82_; lean_object* v___x_83_; 
lean_dec(v_h__2_79_);
v_val_82_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_val_82_);
lean_dec_ref(v_x_77_);
v___x_83_ = lean_apply_1(v_h__1_78_, v_val_82_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_84_, lean_object* v_motive_85_, lean_object* v_x_86_, lean_object* v_h__1_87_, lean_object* v_h__2_88_){
_start:
{
if (lean_obj_tag(v_x_86_) == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec(v_h__1_87_);
v___x_89_ = lean_box(0);
v___x_90_ = lean_apply_1(v_h__2_88_, v___x_89_);
return v___x_90_;
}
else
{
lean_object* v_val_91_; lean_object* v___x_92_; 
lean_dec(v_h__2_88_);
v_val_91_ = lean_ctor_get(v_x_86_, 0);
lean_inc(v_val_91_);
lean_dec_ref(v_x_86_);
v___x_92_ = lean_apply_1(v_h__1_87_, v_val_91_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__3_splitter___redArg(lean_object* v_data_93_, lean_object* v_h__1_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_apply_2(v_h__1_94_, v_data_93_, lean_box(0));
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__3_splitter(lean_object* v_00_u03b1_96_, lean_object* v_00_u03b2_97_, lean_object* v_motive_98_, lean_object* v_data_99_, lean_object* v_h__1_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_apply_2(v_h__1_100_, v_data_99_, lean_box(0));
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter___redArg(lean_object* v_m_102_, lean_object* v_h__1_103_){
_start:
{
lean_object* v_size_104_; lean_object* v_buckets_105_; lean_object* v___x_106_; 
v_size_104_ = lean_ctor_get(v_m_102_, 0);
lean_inc(v_size_104_);
v_buckets_105_ = lean_ctor_get(v_m_102_, 1);
lean_inc_ref(v_buckets_105_);
lean_dec_ref(v_m_102_);
v___x_106_ = lean_apply_3(v_h__1_103_, v_size_104_, v_buckets_105_, lean_box(0));
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter(lean_object* v_00_u03b1_107_, lean_object* v_00_u03b2_108_, lean_object* v_motive_109_, lean_object* v_m_110_, lean_object* v_h__1_111_){
_start:
{
lean_object* v_size_112_; lean_object* v_buckets_113_; lean_object* v___x_114_; 
v_size_112_ = lean_ctor_get(v_m_110_, 0);
lean_inc(v_size_112_);
v_buckets_113_ = lean_ctor_get(v_m_110_, 1);
lean_inc_ref(v_buckets_113_);
lean_dec_ref(v_m_110_);
v___x_114_ = lean_apply_3(v_h__1_111_, v_size_112_, v_buckets_113_, lean_box(0));
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___redArg(lean_object* v_x_115_, lean_object* v_h__1_116_, lean_object* v_h__2_117_){
_start:
{
if (lean_obj_tag(v_x_115_) == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_dec(v_h__2_117_);
v___x_118_ = lean_box(0);
v___x_119_ = lean_apply_1(v_h__1_116_, v___x_118_);
return v___x_119_;
}
else
{
lean_object* v_val_120_; lean_object* v___x_121_; 
lean_dec(v_h__1_116_);
v_val_120_ = lean_ctor_get(v_x_115_, 0);
lean_inc(v_val_120_);
lean_dec_ref(v_x_115_);
v___x_121_ = lean_apply_1(v_h__2_117_, v_val_120_);
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(lean_object* v_00_u03b1_122_, lean_object* v_00_u03b2_123_, lean_object* v_a_124_, lean_object* v_motive_125_, lean_object* v_x_126_, lean_object* v_h__1_127_, lean_object* v_h__2_128_){
_start:
{
if (lean_obj_tag(v_x_126_) == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec(v_h__2_128_);
v___x_129_ = lean_box(0);
v___x_130_ = lean_apply_1(v_h__1_127_, v___x_129_);
return v___x_130_;
}
else
{
lean_object* v_val_131_; lean_object* v___x_132_; 
lean_dec(v_h__1_127_);
v_val_131_ = lean_ctor_get(v_x_126_, 0);
lean_inc(v_val_131_);
lean_dec_ref(v_x_126_);
v___x_132_ = lean_apply_1(v_h__2_128_, v_val_131_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___boxed(lean_object* v_00_u03b1_133_, lean_object* v_00_u03b2_134_, lean_object* v_a_135_, lean_object* v_motive_136_, lean_object* v_x_137_, lean_object* v_h__1_138_, lean_object* v_h__2_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(v_00_u03b1_133_, v_00_u03b2_134_, v_a_135_, v_motive_136_, v_x_137_, v_h__1_138_, v_h__2_139_);
lean_dec(v_a_135_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter___redArg(lean_object* v_x_141_, lean_object* v_h__1_142_, lean_object* v_h__2_143_){
_start:
{
if (lean_obj_tag(v_x_141_) == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v_h__2_143_);
v___x_144_ = lean_box(0);
v___x_145_ = lean_apply_1(v_h__1_142_, v___x_144_);
return v___x_145_;
}
else
{
lean_object* v_val_146_; lean_object* v___x_147_; 
lean_dec(v_h__1_142_);
v_val_146_ = lean_ctor_get(v_x_141_, 0);
lean_inc(v_val_146_);
lean_dec_ref(v_x_141_);
v___x_147_ = lean_apply_1(v_h__2_143_, v_val_146_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter(lean_object* v_00_u03b2_148_, lean_object* v_motive_149_, lean_object* v_x_150_, lean_object* v_h__1_151_, lean_object* v_h__2_152_){
_start:
{
if (lean_obj_tag(v_x_150_) == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec(v_h__2_152_);
v___x_153_ = lean_box(0);
v___x_154_ = lean_apply_1(v_h__1_151_, v___x_153_);
return v___x_154_;
}
else
{
lean_object* v_val_155_; lean_object* v___x_156_; 
lean_dec(v_h__1_151_);
v_val_155_ = lean_ctor_get(v_x_150_, 0);
lean_inc(v_val_155_);
lean_dec_ref(v_x_150_);
v___x_156_ = lean_apply_1(v_h__2_152_, v_val_155_);
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_157_, lean_object* v_h__1_158_, lean_object* v_h__2_159_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec(v_h__2_159_);
v___x_160_ = lean_box(0);
v___x_161_ = lean_apply_1(v_h__1_158_, v___x_160_);
return v___x_161_;
}
else
{
lean_object* v_head_162_; lean_object* v_tail_163_; lean_object* v_fst_164_; lean_object* v_snd_165_; lean_object* v___x_166_; 
lean_dec(v_h__1_158_);
v_head_162_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_head_162_);
v_tail_163_ = lean_ctor_get(v_x_157_, 1);
lean_inc(v_tail_163_);
lean_dec_ref(v_x_157_);
v_fst_164_ = lean_ctor_get(v_head_162_, 0);
lean_inc(v_fst_164_);
v_snd_165_ = lean_ctor_get(v_head_162_, 1);
lean_inc(v_snd_165_);
lean_dec(v_head_162_);
v___x_166_ = lean_apply_3(v_h__2_159_, v_fst_164_, v_snd_165_, v_tail_163_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_167_, lean_object* v_00_u03b2_168_, lean_object* v_motive_169_, lean_object* v_x_170_, lean_object* v_h__1_171_, lean_object* v_h__2_172_){
_start:
{
if (lean_obj_tag(v_x_170_) == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec(v_h__2_172_);
v___x_173_ = lean_box(0);
v___x_174_ = lean_apply_1(v_h__1_171_, v___x_173_);
return v___x_174_;
}
else
{
lean_object* v_head_175_; lean_object* v_tail_176_; lean_object* v_fst_177_; lean_object* v_snd_178_; lean_object* v___x_179_; 
lean_dec(v_h__1_171_);
v_head_175_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_head_175_);
v_tail_176_ = lean_ctor_get(v_x_170_, 1);
lean_inc(v_tail_176_);
lean_dec_ref(v_x_170_);
v_fst_177_ = lean_ctor_get(v_head_175_, 0);
lean_inc(v_fst_177_);
v_snd_178_ = lean_ctor_get(v_head_175_, 1);
lean_inc(v_snd_178_);
lean_dec(v_head_175_);
v___x_179_ = lean_apply_3(v_h__2_172_, v_fst_177_, v_snd_178_, v_tail_176_);
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___redArg(lean_object* v_toInsert_180_, lean_object* v_h__1_181_, lean_object* v_h__2_182_){
_start:
{
if (lean_obj_tag(v_toInsert_180_) == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_h__2_182_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_apply_1(v_h__1_181_, v___x_183_);
return v___x_184_;
}
else
{
lean_object* v_head_185_; lean_object* v_tail_186_; lean_object* v___x_187_; 
lean_dec(v_h__1_181_);
v_head_185_ = lean_ctor_get(v_toInsert_180_, 0);
lean_inc(v_head_185_);
v_tail_186_ = lean_ctor_get(v_toInsert_180_, 1);
lean_inc(v_tail_186_);
lean_dec_ref(v_toInsert_180_);
v___x_187_ = lean_apply_2(v_h__2_182_, v_head_185_, v_tail_186_);
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter(lean_object* v_00_u03b1_188_, lean_object* v_motive_189_, lean_object* v_toInsert_190_, lean_object* v_h__1_191_, lean_object* v_h__2_192_){
_start:
{
if (lean_obj_tag(v_toInsert_190_) == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v_h__2_192_);
v___x_193_ = lean_box(0);
v___x_194_ = lean_apply_1(v_h__1_191_, v___x_193_);
return v___x_194_;
}
else
{
lean_object* v_head_195_; lean_object* v_tail_196_; lean_object* v___x_197_; 
lean_dec(v_h__1_191_);
v_head_195_ = lean_ctor_get(v_toInsert_190_, 0);
lean_inc(v_head_195_);
v_tail_196_ = lean_ctor_get(v_toInsert_190_, 1);
lean_inc(v_tail_196_);
lean_dec_ref(v_toInsert_190_);
v___x_197_ = lean_apply_2(v_h__2_192_, v_head_195_, v_tail_196_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter___redArg(lean_object* v_x_198_, lean_object* v_h__1_199_, lean_object* v_h__2_200_){
_start:
{
if (lean_obj_tag(v_x_198_) == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec(v_h__1_199_);
v___x_201_ = lean_box(0);
v___x_202_ = lean_apply_1(v_h__2_200_, v___x_201_);
return v___x_202_;
}
else
{
lean_object* v_val_203_; lean_object* v___x_204_; 
lean_dec(v_h__2_200_);
v_val_203_ = lean_ctor_get(v_x_198_, 0);
lean_inc(v_val_203_);
lean_dec_ref(v_x_198_);
v___x_204_ = lean_apply_1(v_h__1_199_, v_val_203_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter(lean_object* v_00_u03b1_205_, lean_object* v_00_u03b2_206_, lean_object* v_motive_207_, lean_object* v_x_208_, lean_object* v_h__1_209_, lean_object* v_h__2_210_){
_start:
{
if (lean_obj_tag(v_x_208_) == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v_h__1_209_);
v___x_211_ = lean_box(0);
v___x_212_ = lean_apply_1(v_h__2_210_, v___x_211_);
return v___x_212_;
}
else
{
lean_object* v_val_213_; lean_object* v___x_214_; 
lean_dec(v_h__2_210_);
v_val_213_ = lean_ctor_get(v_x_208_, 0);
lean_inc(v_val_213_);
lean_dec_ref(v_x_208_);
v___x_214_ = lean_apply_1(v_h__1_209_, v_val_213_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098_match__1_splitter___redArg(lean_object* v_x_215_, lean_object* v_h__1_216_, lean_object* v_h__2_217_){
_start:
{
if (lean_obj_tag(v_x_215_) == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec(v_h__1_216_);
v___x_218_ = lean_box(0);
v___x_219_ = lean_apply_1(v_h__2_217_, v___x_218_);
return v___x_219_;
}
else
{
lean_object* v_val_220_; lean_object* v___x_221_; 
lean_dec(v_h__2_217_);
v_val_220_ = lean_ctor_get(v_x_215_, 0);
lean_inc(v_val_220_);
lean_dec_ref(v_x_215_);
v___x_221_ = lean_apply_1(v_h__1_216_, v_val_220_);
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098_match__1_splitter(lean_object* v_00_u03b1_222_, lean_object* v_00_u03b2_223_, lean_object* v_motive_224_, lean_object* v_x_225_, lean_object* v_h__1_226_, lean_object* v_h__2_227_){
_start:
{
if (lean_obj_tag(v_x_225_) == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec(v_h__1_226_);
v___x_228_ = lean_box(0);
v___x_229_ = lean_apply_1(v_h__2_227_, v___x_228_);
return v___x_229_;
}
else
{
lean_object* v_val_230_; lean_object* v___x_231_; 
lean_dec(v_h__2_227_);
v_val_230_ = lean_ctor_get(v_x_225_, 0);
lean_inc(v_val_230_);
lean_dec_ref(v_x_225_);
v___x_231_ = lean_apply_1(v_h__1_226_, v_val_230_);
return v___x_231_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0(lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_m_u2081_234_, lean_object* v_x1_235_, lean_object* v_x2_236_, lean_object* v_x3_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(v_inst_232_, v_inst_233_, v_m_u2081_234_, v_x1_235_, v_x2_236_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0___boxed(lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_m_u2081_241_, lean_object* v_x1_242_, lean_object* v_x2_243_, lean_object* v_x3_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0(v_inst_239_, v_inst_240_, v_m_u2081_241_, v_x1_242_, v_x2_243_, v_x3_244_);
lean_dec(v_x3_244_);
lean_dec_ref(v_m_u2081_241_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__1(lean_object* v___x_246_, lean_object* v___f_247_, lean_object* v_acc_248_, lean_object* v_l_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_246_, v___f_247_, v_acc_248_, v_l_249_);
return v___x_250_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = lean_box(0);
v___x_271_ = lean_unsigned_to_nat(16u);
v___x_272_ = lean_mk_array(v___x_271_, v___x_270_);
return v___x_272_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10, &l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10_once, _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10);
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v___x_273_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg(lean_object* v_inst_276_, lean_object* v_inst_277_, lean_object* v_m_u2081_278_, lean_object* v_m_u2082_279_){
_start:
{
lean_object* v___x_280_; lean_object* v_buckets_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_280_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__9));
v_buckets_281_ = lean_ctor_get(v_m_u2082_279_, 1);
lean_inc_ref(v_buckets_281_);
lean_dec_ref(v_m_u2082_279_);
v___x_282_ = lean_unsigned_to_nat(0u);
v___x_283_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11, &l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11_once, _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11);
v___x_284_ = lean_array_get_size(v_buckets_281_);
v___x_285_ = lean_nat_dec_lt(v___x_282_, v___x_284_);
if (v___x_285_ == 0)
{
lean_dec_ref(v_buckets_281_);
lean_dec_ref(v_m_u2081_278_);
lean_dec_ref(v_inst_277_);
lean_dec_ref(v_inst_276_);
return v___x_283_;
}
else
{
lean_object* v___f_286_; lean_object* v___f_287_; uint8_t v___x_288_; 
v___f_286_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_286_, 0, v_inst_276_);
lean_closure_set(v___f_286_, 1, v_inst_277_);
lean_closure_set(v___f_286_, 2, v_m_u2081_278_);
v___f_287_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__1), 4, 2);
lean_closure_set(v___f_287_, 0, v___x_280_);
lean_closure_set(v___f_287_, 1, v___f_286_);
v___x_288_ = lean_nat_dec_le(v___x_284_, v___x_284_);
if (v___x_288_ == 0)
{
if (v___x_285_ == 0)
{
lean_dec_ref(v___f_287_);
lean_dec_ref(v_buckets_281_);
return v___x_283_;
}
else
{
size_t v___x_289_; size_t v___x_290_; lean_object* v___x_291_; 
v___x_289_ = ((size_t)0ULL);
v___x_290_ = lean_usize_of_nat(v___x_284_);
v___x_291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_280_, v___f_287_, v_buckets_281_, v___x_289_, v___x_290_, v___x_283_);
return v___x_291_;
}
}
else
{
size_t v___x_292_; size_t v___x_293_; lean_object* v___x_294_; 
v___x_292_ = ((size_t)0ULL);
v___x_293_ = lean_usize_of_nat(v___x_284_);
v___x_294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_280_, v___f_287_, v_buckets_281_, v___x_292_, v___x_293_, v___x_283_);
return v___x_294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098(lean_object* v_00_u03b1_295_, lean_object* v_00_u03b2_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_m_u2081_299_, lean_object* v_m_u2082_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg(v_inst_297_, v_inst_298_, v_m_u2081_299_, v_m_u2082_300_);
return v___x_301_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_Internal_WF(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
