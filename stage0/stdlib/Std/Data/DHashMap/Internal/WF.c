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
lean_object* v___x_18_; 
v___x_18_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_foldlM_match__1_splitter___redArg(v_x_14_, v_x_15_, v_h__1_16_, v_h__2_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__3_splitter___redArg(lean_object* v_x_19_, lean_object* v_x_20_, lean_object* v_h__1_21_, lean_object* v_h__2_22_){
_start:
{
if (lean_obj_tag(v_x_19_) == 0)
{
lean_object* v___x_23_; 
lean_dec(v_h__2_22_);
v___x_23_ = lean_apply_1(v_h__1_21_, v_x_20_);
return v___x_23_;
}
else
{
lean_object* v_key_24_; lean_object* v_value_25_; lean_object* v_tail_26_; lean_object* v___x_27_; 
lean_dec(v_h__1_21_);
v_key_24_ = lean_ctor_get(v_x_19_, 0);
lean_inc(v_key_24_);
v_value_25_ = lean_ctor_get(v_x_19_, 1);
lean_inc(v_value_25_);
v_tail_26_ = lean_ctor_get(v_x_19_, 2);
lean_inc(v_tail_26_);
lean_dec_ref(v_x_19_);
v___x_27_ = lean_apply_4(v_h__2_22_, v_key_24_, v_value_25_, v_tail_26_, v_x_20_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__3_splitter(lean_object* v_00_u03b1_28_, lean_object* v_00_u03b2_29_, lean_object* v_00_u03b4_30_, lean_object* v_motive_31_, lean_object* v_x_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__3_splitter___redArg(v_x_32_, v_x_33_, v_h__1_34_, v_h__2_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__1_splitter___redArg(lean_object* v_____do__lift_37_, lean_object* v_h__1_38_, lean_object* v_h__2_39_){
_start:
{
if (lean_obj_tag(v_____do__lift_37_) == 0)
{
lean_object* v_a_40_; lean_object* v___x_41_; 
lean_dec(v_h__2_39_);
v_a_40_ = lean_ctor_get(v_____do__lift_37_, 0);
lean_inc(v_a_40_);
lean_dec_ref(v_____do__lift_37_);
v___x_41_ = lean_apply_1(v_h__1_38_, v_a_40_);
return v___x_41_;
}
else
{
lean_object* v_a_42_; lean_object* v___x_43_; 
lean_dec(v_h__1_38_);
v_a_42_ = lean_ctor_get(v_____do__lift_37_, 0);
lean_inc(v_a_42_);
lean_dec_ref(v_____do__lift_37_);
v___x_43_ = lean_apply_1(v_h__2_39_, v_a_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__1_splitter(lean_object* v_00_u03b4_44_, lean_object* v_motive_45_, lean_object* v_____do__lift_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__1_splitter___redArg(v_____do__lift_46_, v_h__1_47_, v_h__2_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_){
_start:
{
if (lean_obj_tag(v_x_50_) == 0)
{
lean_object* v_a_53_; lean_object* v___x_54_; 
lean_dec(v_h__2_52_);
v_a_53_ = lean_ctor_get(v_x_50_, 0);
lean_inc(v_a_53_);
lean_dec_ref(v_x_50_);
v___x_54_ = lean_apply_1(v_h__1_51_, v_a_53_);
return v___x_54_;
}
else
{
lean_object* v_a_55_; lean_object* v___x_56_; 
lean_dec(v_h__1_51_);
v_a_55_ = lean_ctor_get(v_x_50_, 0);
lean_inc(v_a_55_);
lean_dec_ref(v_x_50_);
v___x_56_ = lean_apply_1(v_h__2_52_, v_a_55_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_57_, lean_object* v_motive_58_, lean_object* v_x_59_, lean_object* v_h__1_60_, lean_object* v_h__2_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter___redArg(v_x_59_, v_h__1_60_, v_h__2_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_63_, lean_object* v_h__1_64_, lean_object* v_h__2_65_){
_start:
{
if (lean_obj_tag(v_x_63_) == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; 
lean_dec(v_h__1_64_);
v___x_66_ = lean_box(0);
v___x_67_ = lean_apply_1(v_h__2_65_, v___x_66_);
return v___x_67_;
}
else
{
lean_object* v_val_68_; lean_object* v___x_69_; 
lean_dec(v_h__2_65_);
v_val_68_ = lean_ctor_get(v_x_63_, 0);
lean_inc(v_val_68_);
lean_dec_ref(v_x_63_);
v___x_69_ = lean_apply_1(v_h__1_64_, v_val_68_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_70_, lean_object* v_motive_71_, lean_object* v_x_72_, lean_object* v_h__1_73_, lean_object* v_h__2_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter___redArg(v_x_72_, v_h__1_73_, v_h__2_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__3_splitter___redArg(lean_object* v_data_76_, lean_object* v_h__1_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_apply_2(v_h__1_77_, v_data_76_, lean_box(0));
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__3_splitter(lean_object* v_00_u03b1_79_, lean_object* v_00_u03b2_80_, lean_object* v_motive_81_, lean_object* v_data_82_, lean_object* v_h__1_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_apply_2(v_h__1_83_, v_data_82_, lean_box(0));
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter___redArg(lean_object* v_m_85_, lean_object* v_h__1_86_){
_start:
{
lean_object* v_size_87_; lean_object* v_buckets_88_; lean_object* v___x_89_; 
v_size_87_ = lean_ctor_get(v_m_85_, 0);
lean_inc(v_size_87_);
v_buckets_88_ = lean_ctor_get(v_m_85_, 1);
lean_inc_ref(v_buckets_88_);
lean_dec_ref(v_m_85_);
v___x_89_ = lean_apply_3(v_h__1_86_, v_size_87_, v_buckets_88_, lean_box(0));
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter(lean_object* v_00_u03b1_90_, lean_object* v_00_u03b2_91_, lean_object* v_motive_92_, lean_object* v_m_93_, lean_object* v_h__1_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter___redArg(v_m_93_, v_h__1_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___redArg(lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
lean_object* v___x_99_; lean_object* v___x_100_; 
lean_dec(v_h__2_98_);
v___x_99_ = lean_box(0);
v___x_100_ = lean_apply_1(v_h__1_97_, v___x_99_);
return v___x_100_;
}
else
{
lean_object* v_val_101_; lean_object* v___x_102_; 
lean_dec(v_h__1_97_);
v_val_101_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_val_101_);
lean_dec_ref(v_x_96_);
v___x_102_ = lean_apply_1(v_h__2_98_, v_val_101_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(lean_object* v_00_u03b1_103_, lean_object* v_00_u03b2_104_, lean_object* v_a_105_, lean_object* v_motive_106_, lean_object* v_x_107_, lean_object* v_h__1_108_, lean_object* v_h__2_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___redArg(v_x_107_, v_h__1_108_, v_h__2_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___boxed(lean_object* v_00_u03b1_111_, lean_object* v_00_u03b2_112_, lean_object* v_a_113_, lean_object* v_motive_114_, lean_object* v_x_115_, lean_object* v_h__1_116_, lean_object* v_h__2_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(v_00_u03b1_111_, v_00_u03b2_112_, v_a_113_, v_motive_114_, v_x_115_, v_h__1_116_, v_h__2_117_);
lean_dec(v_a_113_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter___redArg(lean_object* v_x_119_, lean_object* v_h__1_120_, lean_object* v_h__2_121_){
_start:
{
if (lean_obj_tag(v_x_119_) == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v_h__2_121_);
v___x_122_ = lean_box(0);
v___x_123_ = lean_apply_1(v_h__1_120_, v___x_122_);
return v___x_123_;
}
else
{
lean_object* v_val_124_; lean_object* v___x_125_; 
lean_dec(v_h__1_120_);
v_val_124_ = lean_ctor_get(v_x_119_, 0);
lean_inc(v_val_124_);
lean_dec_ref(v_x_119_);
v___x_125_ = lean_apply_1(v_h__2_121_, v_val_124_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter(lean_object* v_00_u03b2_126_, lean_object* v_motive_127_, lean_object* v_x_128_, lean_object* v_h__1_129_, lean_object* v_h__2_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter___redArg(v_x_128_, v_h__1_129_, v_h__2_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(lean_object* v_x_132_, lean_object* v_h__1_133_, lean_object* v_h__2_134_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec(v_h__2_134_);
v___x_135_ = lean_box(0);
v___x_136_ = lean_apply_1(v_h__1_133_, v___x_135_);
return v___x_136_;
}
else
{
lean_object* v_head_137_; lean_object* v_tail_138_; lean_object* v_fst_139_; lean_object* v_snd_140_; lean_object* v___x_141_; 
lean_dec(v_h__1_133_);
v_head_137_ = lean_ctor_get(v_x_132_, 0);
lean_inc(v_head_137_);
v_tail_138_ = lean_ctor_get(v_x_132_, 1);
lean_inc(v_tail_138_);
lean_dec_ref(v_x_132_);
v_fst_139_ = lean_ctor_get(v_head_137_, 0);
lean_inc(v_fst_139_);
v_snd_140_ = lean_ctor_get(v_head_137_, 1);
lean_inc(v_snd_140_);
lean_dec(v_head_137_);
v___x_141_ = lean_apply_3(v_h__2_134_, v_fst_139_, v_snd_140_, v_tail_138_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_getEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_142_, lean_object* v_00_u03b2_143_, lean_object* v_motive_144_, lean_object* v_x_145_, lean_object* v_h__1_146_, lean_object* v_h__2_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_getEntry_x3f_match__1_splitter___redArg(v_x_145_, v_h__1_146_, v_h__2_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___redArg(lean_object* v_toInsert_149_, lean_object* v_h__1_150_, lean_object* v_h__2_151_){
_start:
{
if (lean_obj_tag(v_toInsert_149_) == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec(v_h__2_151_);
v___x_152_ = lean_box(0);
v___x_153_ = lean_apply_1(v_h__1_150_, v___x_152_);
return v___x_153_;
}
else
{
lean_object* v_head_154_; lean_object* v_tail_155_; lean_object* v___x_156_; 
lean_dec(v_h__1_150_);
v_head_154_ = lean_ctor_get(v_toInsert_149_, 0);
lean_inc(v_head_154_);
v_tail_155_ = lean_ctor_get(v_toInsert_149_, 1);
lean_inc(v_tail_155_);
lean_dec_ref(v_toInsert_149_);
v___x_156_ = lean_apply_2(v_h__2_151_, v_head_154_, v_tail_155_);
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter(lean_object* v_00_u03b1_157_, lean_object* v_motive_158_, lean_object* v_toInsert_159_, lean_object* v_h__1_160_, lean_object* v_h__2_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_Internal_List_insertListIfNewUnit_match__1_splitter___redArg(v_toInsert_159_, v_h__1_160_, v_h__2_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter___redArg(lean_object* v_x_163_, lean_object* v_h__1_164_, lean_object* v_h__2_165_){
_start:
{
if (lean_obj_tag(v_x_163_) == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_h__1_164_);
v___x_166_ = lean_box(0);
v___x_167_ = lean_apply_1(v_h__2_165_, v___x_166_);
return v___x_167_;
}
else
{
lean_object* v_val_168_; lean_object* v___x_169_; 
lean_dec(v_h__2_165_);
v_val_168_ = lean_ctor_get(v_x_163_, 0);
lean_inc(v_val_168_);
lean_dec_ref(v_x_163_);
v___x_169_ = lean_apply_1(v_h__1_164_, v_val_168_);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter(lean_object* v_00_u03b1_170_, lean_object* v_00_u03b2_171_, lean_object* v_motive_172_, lean_object* v_x_173_, lean_object* v_h__1_174_, lean_object* v_h__2_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter___redArg(v_x_173_, v_h__1_174_, v_h__2_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098_match__1_splitter___redArg(lean_object* v_x_177_, lean_object* v_h__1_178_, lean_object* v_h__2_179_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec(v_h__1_178_);
v___x_180_ = lean_box(0);
v___x_181_ = lean_apply_1(v_h__2_179_, v___x_180_);
return v___x_181_;
}
else
{
lean_object* v_val_182_; lean_object* v___x_183_; 
lean_dec(v_h__2_179_);
v_val_182_ = lean_ctor_get(v_x_177_, 0);
lean_inc(v_val_182_);
lean_dec_ref(v_x_177_);
v___x_183_ = lean_apply_1(v_h__1_178_, v_val_182_);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098_match__1_splitter(lean_object* v_00_u03b1_184_, lean_object* v_00_u03b2_185_, lean_object* v_motive_186_, lean_object* v_x_187_, lean_object* v_h__1_188_, lean_object* v_h__2_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098_match__1_splitter___redArg(v_x_187_, v_h__1_188_, v_h__2_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0(lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_m_u2081_193_, lean_object* v_x1_194_, lean_object* v_x2_195_, lean_object* v_x3_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(v_inst_191_, v_inst_192_, v_m_u2081_193_, v_x1_194_, v_x2_195_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0___boxed(lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_m_u2081_200_, lean_object* v_x1_201_, lean_object* v_x2_202_, lean_object* v_x3_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0(v_inst_198_, v_inst_199_, v_m_u2081_200_, v_x1_201_, v_x2_202_, v_x3_203_);
lean_dec(v_x3_203_);
lean_dec_ref(v_m_u2081_200_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__1(lean_object* v___x_205_, lean_object* v___f_206_, lean_object* v_acc_207_, lean_object* v_l_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_205_, v___f_206_, v_acc_207_, v_l_208_);
return v___x_209_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_box(0);
v___x_230_ = lean_unsigned_to_nat(16u);
v___x_231_ = lean_mk_array(v___x_230_, v___x_229_);
return v___x_231_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10, &l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10_once, _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10);
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v___x_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg(lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_m_u2081_237_, lean_object* v_m_u2082_238_){
_start:
{
lean_object* v___x_239_; lean_object* v_buckets_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_239_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__9));
v_buckets_240_ = lean_ctor_get(v_m_u2082_238_, 1);
lean_inc_ref(v_buckets_240_);
lean_dec_ref(v_m_u2082_238_);
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11, &l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11_once, _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11);
v___x_243_ = lean_array_get_size(v_buckets_240_);
v___x_244_ = lean_nat_dec_lt(v___x_241_, v___x_243_);
if (v___x_244_ == 0)
{
lean_dec_ref(v_buckets_240_);
lean_dec_ref(v_m_u2081_237_);
lean_dec_ref(v_inst_236_);
lean_dec_ref(v_inst_235_);
return v___x_242_;
}
else
{
lean_object* v___f_245_; lean_object* v___f_246_; uint8_t v___x_247_; 
v___f_245_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_245_, 0, v_inst_235_);
lean_closure_set(v___f_245_, 1, v_inst_236_);
lean_closure_set(v___f_245_, 2, v_m_u2081_237_);
v___f_246_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__1), 4, 2);
lean_closure_set(v___f_246_, 0, v___x_239_);
lean_closure_set(v___f_246_, 1, v___f_245_);
v___x_247_ = lean_nat_dec_le(v___x_243_, v___x_243_);
if (v___x_247_ == 0)
{
if (v___x_244_ == 0)
{
lean_dec_ref(v___f_246_);
lean_dec_ref(v_buckets_240_);
return v___x_242_;
}
else
{
size_t v___x_248_; size_t v___x_249_; lean_object* v___x_250_; 
v___x_248_ = ((size_t)0ULL);
v___x_249_ = lean_usize_of_nat(v___x_243_);
v___x_250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_239_, v___f_246_, v_buckets_240_, v___x_248_, v___x_249_, v___x_242_);
return v___x_250_;
}
}
else
{
size_t v___x_251_; size_t v___x_252_; lean_object* v___x_253_; 
v___x_251_ = ((size_t)0ULL);
v___x_252_ = lean_usize_of_nat(v___x_243_);
v___x_253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_239_, v___f_246_, v_buckets_240_, v___x_251_, v___x_252_, v___x_242_);
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098(lean_object* v_00_u03b1_254_, lean_object* v_00_u03b2_255_, lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_m_u2081_258_, lean_object* v_m_u2082_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg(v_inst_256_, v_inst_257_, v_m_u2081_258_, v_m_u2082_259_);
return v___x_260_;
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
