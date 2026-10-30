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
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v_a_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v_a_4_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_4_);
lean_dec_ref_known(v_x_1_, 1);
v___x_5_ = lean_apply_1(v_h__1_2_, v_a_4_);
return v___x_5_;
}
else
{
lean_object* v_a_6_; lean_object* v___x_7_; 
lean_dec(v_h__1_2_);
v_a_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_6_);
lean_dec_ref_known(v_x_1_, 1);
v___x_7_ = lean_apply_1(v_h__2_3_, v_a_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__List_forIn_x27__cons_match__1_splitter(lean_object* v_00_u03b2_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_14_; 
lean_dec(v_h__2_12_);
v_a_13_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_a_13_);
lean_dec_ref_known(v_x_10_, 1);
v___x_14_ = lean_apply_1(v_h__1_11_, v_a_13_);
return v___x_14_;
}
else
{
lean_object* v_a_15_; lean_object* v___x_16_; 
lean_dec(v_h__1_11_);
v_a_15_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_a_15_);
lean_dec_ref_known(v_x_10_, 1);
v___x_16_ = lean_apply_1(v_h__2_12_, v_a_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__1_splitter___redArg(lean_object* v_____do__lift_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
_start:
{
if (lean_obj_tag(v_____do__lift_17_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_21_; 
lean_dec(v_h__2_19_);
v_a_20_ = lean_ctor_get(v_____do__lift_17_, 0);
lean_inc(v_a_20_);
lean_dec_ref_known(v_____do__lift_17_, 1);
v___x_21_ = lean_apply_1(v_h__1_18_, v_a_20_);
return v___x_21_;
}
else
{
lean_object* v_a_22_; lean_object* v___x_23_; 
lean_dec(v_h__1_18_);
v_a_22_ = lean_ctor_get(v_____do__lift_17_, 0);
lean_inc(v_a_22_);
lean_dec_ref_known(v_____do__lift_17_, 1);
v___x_23_ = lean_apply_1(v_h__2_19_, v_a_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_AssocList_forInStep_go_match__1_splitter(lean_object* v_00_u03b4_24_, lean_object* v_motive_25_, lean_object* v_____do__lift_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_){
_start:
{
if (lean_obj_tag(v_____do__lift_26_) == 0)
{
lean_object* v_a_29_; lean_object* v___x_30_; 
lean_dec(v_h__2_28_);
v_a_29_ = lean_ctor_get(v_____do__lift_26_, 0);
lean_inc(v_a_29_);
lean_dec_ref_known(v_____do__lift_26_, 1);
v___x_30_ = lean_apply_1(v_h__1_27_, v_a_29_);
return v___x_30_;
}
else
{
lean_object* v_a_31_; lean_object* v___x_32_; 
lean_dec(v_h__1_27_);
v_a_31_ = lean_ctor_get(v_____do__lift_26_, 0);
lean_inc(v_a_31_);
lean_dec_ref_known(v_____do__lift_26_, 1);
v___x_32_ = lean_apply_1(v_h__2_28_, v_a_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
if (lean_obj_tag(v_x_33_) == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec(v_h__1_34_);
v___x_36_ = lean_box(0);
v___x_37_ = lean_apply_1(v_h__2_35_, v___x_36_);
return v___x_37_;
}
else
{
lean_object* v_val_38_; lean_object* v___x_39_; 
lean_dec(v_h__2_35_);
v_val_38_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_val_38_);
lean_dec_ref_known(v_x_33_, 1);
v___x_39_ = lean_apply_1(v_h__1_34_, v_val_38_);
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_40_, lean_object* v_motive_41_, lean_object* v_x_42_, lean_object* v_h__1_43_, lean_object* v_h__2_44_){
_start:
{
if (lean_obj_tag(v_x_42_) == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; 
lean_dec(v_h__1_43_);
v___x_45_ = lean_box(0);
v___x_46_ = lean_apply_1(v_h__2_44_, v___x_45_);
return v___x_46_;
}
else
{
lean_object* v_val_47_; lean_object* v___x_48_; 
lean_dec(v_h__2_44_);
v_val_47_ = lean_ctor_get(v_x_42_, 0);
lean_inc(v_val_47_);
lean_dec_ref_known(v_x_42_, 1);
v___x_48_ = lean_apply_1(v_h__1_43_, v_val_47_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___redArg(lean_object* v_x_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; 
lean_dec(v_h__2_51_);
v___x_52_ = lean_box(0);
v___x_53_ = lean_apply_1(v_h__1_50_, v___x_52_);
return v___x_53_;
}
else
{
lean_object* v_val_54_; lean_object* v___x_55_; 
lean_dec(v_h__1_50_);
v_val_54_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_val_54_);
lean_dec_ref_known(v_x_49_, 1);
v___x_55_ = lean_apply_1(v_h__2_51_, v_val_54_);
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(lean_object* v_00_u03b1_56_, lean_object* v_00_u03b2_57_, lean_object* v_a_58_, lean_object* v_motive_59_, lean_object* v_x_60_, lean_object* v_h__1_61_, lean_object* v_h__2_62_){
_start:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; 
lean_dec(v_h__2_62_);
v___x_63_ = lean_box(0);
v___x_64_ = lean_apply_1(v_h__1_61_, v___x_63_);
return v___x_64_;
}
else
{
lean_object* v_val_65_; lean_object* v___x_66_; 
lean_dec(v_h__1_61_);
v_val_65_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_val_65_);
lean_dec_ref_known(v_x_60_, 1);
v___x_66_ = lean_apply_1(v_h__2_62_, v_val_65_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___boxed(lean_object* v_00_u03b1_67_, lean_object* v_00_u03b2_68_, lean_object* v_a_69_, lean_object* v_motive_70_, lean_object* v_x_71_, lean_object* v_h__1_72_, lean_object* v_h__2_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(v_00_u03b1_67_, v_00_u03b2_68_, v_a_69_, v_motive_70_, v_x_71_, v_h__1_72_, v_h__2_73_);
lean_dec(v_a_69_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter___redArg(lean_object* v_x_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec(v_h__2_77_);
v___x_78_ = lean_box(0);
v___x_79_ = lean_apply_1(v_h__1_76_, v___x_78_);
return v___x_79_;
}
else
{
lean_object* v_val_80_; lean_object* v___x_81_; 
lean_dec(v_h__1_76_);
v_val_80_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_val_80_);
lean_dec_ref_known(v_x_75_, 1);
v___x_81_ = lean_apply_1(v_h__2_77_, v_val_80_);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter(lean_object* v_00_u03b2_82_, lean_object* v_motive_83_, lean_object* v_x_84_, lean_object* v_h__1_85_, lean_object* v_h__2_86_){
_start:
{
if (lean_obj_tag(v_x_84_) == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec(v_h__2_86_);
v___x_87_ = lean_box(0);
v___x_88_ = lean_apply_1(v_h__1_85_, v___x_87_);
return v___x_88_;
}
else
{
lean_object* v_val_89_; lean_object* v___x_90_; 
lean_dec(v_h__1_85_);
v_val_89_ = lean_ctor_get(v_x_84_, 0);
lean_inc(v_val_89_);
lean_dec_ref_known(v_x_84_, 1);
v___x_90_ = lean_apply_1(v_h__2_86_, v_val_89_);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter___redArg(lean_object* v_x_91_, lean_object* v_h__1_92_, lean_object* v_h__2_93_){
_start:
{
if (lean_obj_tag(v_x_91_) == 0)
{
lean_object* v___x_94_; lean_object* v___x_95_; 
lean_dec(v_h__1_92_);
v___x_94_ = lean_box(0);
v___x_95_ = lean_apply_1(v_h__2_93_, v___x_94_);
return v___x_95_;
}
else
{
lean_object* v_val_96_; lean_object* v___x_97_; 
lean_dec(v_h__2_93_);
v_val_96_ = lean_ctor_get(v_x_91_, 0);
lean_inc(v_val_96_);
lean_dec_ref_known(v_x_91_, 1);
v___x_97_ = lean_apply_1(v_h__1_92_, v_val_96_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_match__1_splitter(lean_object* v_00_u03b1_98_, lean_object* v_00_u03b2_99_, lean_object* v_motive_100_, lean_object* v_x_101_, lean_object* v_h__1_102_, lean_object* v_h__2_103_){
_start:
{
if (lean_obj_tag(v_x_101_) == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v_h__1_102_);
v___x_104_ = lean_box(0);
v___x_105_ = lean_apply_1(v_h__2_103_, v___x_104_);
return v___x_105_;
}
else
{
lean_object* v_val_106_; lean_object* v___x_107_; 
lean_dec(v_h__2_103_);
v_val_106_ = lean_ctor_get(v_x_101_, 0);
lean_inc(v_val_106_);
lean_dec_ref_known(v_x_101_, 1);
v___x_107_ = lean_apply_1(v_h__1_102_, v_val_106_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098_match__1_splitter___redArg(lean_object* v_x_108_, lean_object* v_h__1_109_, lean_object* v_h__2_110_){
_start:
{
if (lean_obj_tag(v_x_108_) == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; 
lean_dec(v_h__1_109_);
v___x_111_ = lean_box(0);
v___x_112_ = lean_apply_1(v_h__2_110_, v___x_111_);
return v___x_112_;
}
else
{
lean_object* v_val_113_; lean_object* v___x_114_; 
lean_dec(v_h__2_110_);
v_val_113_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_val_113_);
lean_dec_ref_known(v_x_108_, 1);
v___x_114_ = lean_apply_1(v_h__1_109_, v_val_113_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_WF_0__Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098_match__1_splitter(lean_object* v_00_u03b1_115_, lean_object* v_00_u03b2_116_, lean_object* v_motive_117_, lean_object* v_x_118_, lean_object* v_h__1_119_, lean_object* v_h__2_120_){
_start:
{
if (lean_obj_tag(v_x_118_) == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; 
lean_dec(v_h__1_119_);
v___x_121_ = lean_box(0);
v___x_122_ = lean_apply_1(v_h__2_120_, v___x_121_);
return v___x_122_;
}
else
{
lean_object* v_val_123_; lean_object* v___x_124_; 
lean_dec(v_h__2_120_);
v_val_123_ = lean_ctor_get(v_x_118_, 0);
lean_inc(v_val_123_);
lean_dec_ref_known(v_x_118_, 1);
v___x_124_ = lean_apply_1(v_h__1_119_, v_val_123_);
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0(lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_m_u2081_127_, lean_object* v_x1_128_, lean_object* v_x2_129_, lean_object* v_x3_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(v_inst_125_, v_inst_126_, v_m_u2081_127_, v_x1_128_, v_x2_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0___boxed(lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_m_u2081_134_, lean_object* v_x1_135_, lean_object* v_x2_136_, lean_object* v_x3_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0(v_inst_132_, v_inst_133_, v_m_u2081_134_, v_x1_135_, v_x2_136_, v_x3_137_);
lean_dec(v_x3_137_);
lean_dec_ref(v_m_u2081_134_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__1(lean_object* v___x_139_, lean_object* v___f_140_, lean_object* v_acc_141_, lean_object* v_l_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_139_, v___f_140_, v_acc_141_, v_l_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_box(0);
v___x_164_ = lean_unsigned_to_nat(16u);
v___x_165_ = lean_mk_array(v___x_164_, v___x_163_);
return v___x_165_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10, &l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10_once, _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__10);
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_166_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg(lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_m_u2081_171_, lean_object* v_m_u2082_172_){
_start:
{
lean_object* v___x_173_; lean_object* v_buckets_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_173_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__9));
v_buckets_174_ = lean_ctor_get(v_m_u2082_172_, 1);
lean_inc_ref(v_buckets_174_);
lean_dec_ref(v_m_u2082_172_);
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11, &l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11_once, _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___closed__11);
v___x_177_ = lean_array_get_size(v_buckets_174_);
v___x_178_ = lean_nat_dec_lt(v___x_175_, v___x_177_);
if (v___x_178_ == 0)
{
lean_dec_ref(v_buckets_174_);
lean_dec_ref(v_m_u2081_171_);
lean_dec_ref(v_inst_170_);
lean_dec_ref(v_inst_169_);
return v___x_176_;
}
else
{
lean_object* v___f_179_; lean_object* v___f_180_; size_t v___x_181_; size_t v___x_182_; lean_object* v___x_183_; 
v___f_179_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_179_, 0, v_inst_169_);
lean_closure_set(v___f_179_, 1, v_inst_170_);
lean_closure_set(v___f_179_, 2, v_m_u2081_171_);
v___f_180_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg___lam__1), 4, 2);
lean_closure_set(v___f_180_, 0, v___x_173_);
lean_closure_set(v___f_180_, 1, v___f_179_);
v___x_181_ = ((size_t)0ULL);
v___x_182_ = lean_usize_of_nat(v___x_177_);
v___x_183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_173_, v___f_180_, v_buckets_174_, v___x_181_, v___x_182_, v___x_176_);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098(lean_object* v_00_u03b1_184_, lean_object* v_00_u03b2_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_m_u2081_188_, lean_object* v_m_u2082_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller_u2098___redArg(v_inst_186_, v_inst_187_, v_m_u2081_188_, v_m_u2082_189_);
return v___x_190_;
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
