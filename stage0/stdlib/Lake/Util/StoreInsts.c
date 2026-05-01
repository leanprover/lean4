// Lean compiler output
// Module: Lake.Util.StoreInsts
// Imports: public import Init.Data.Order public import Lean.Data.NameMap.Basic public import Lake.Util.RBArray public import Lake.Util.Family public import Lake.Util.Store
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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBArray_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_cmp_2_, lean_object* v_k_3_, lean_object* v___y_4_){
_start:
{
lean_object* v_toApplicative_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_15_; 
v_toApplicative_5_ = lean_ctor_get(v_inst_1_, 0);
v_isSharedCheck_15_ = !lean_is_exclusive(v_inst_1_);
if (v_isSharedCheck_15_ == 0)
{
lean_object* v_unused_16_; 
v_unused_16_ = lean_ctor_get(v_inst_1_, 1);
lean_dec(v_unused_16_);
v___x_7_ = v_inst_1_;
v_isShared_8_ = v_isSharedCheck_15_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_toApplicative_5_);
lean_dec(v_inst_1_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_15_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v_toPure_9_; lean_object* v___x_10_; lean_object* v___x_12_; 
v_toPure_9_ = lean_ctor_get(v_toApplicative_5_, 1);
lean_inc(v_toPure_9_);
lean_dec_ref(v_toApplicative_5_);
lean_inc(v___y_4_);
v___x_10_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_2_, v___y_4_, v_k_3_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v___y_4_);
lean_ctor_set(v___x_7_, 0, v___x_10_);
v___x_12_ = v___x_7_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v___x_10_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v___y_4_);
v___x_12_ = v_reuseFailAlloc_14_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
lean_object* v___x_13_; 
v___x_13_ = lean_apply_2(v_toPure_9_, lean_box(0), v___x_12_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__1(lean_object* v_inst_17_, lean_object* v_cmp_18_, lean_object* v_k_19_, lean_object* v_a_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_toApplicative_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_33_; 
v_toApplicative_22_ = lean_ctor_get(v_inst_17_, 0);
v_isSharedCheck_33_ = !lean_is_exclusive(v_inst_17_);
if (v_isSharedCheck_33_ == 0)
{
lean_object* v_unused_34_; 
v_unused_34_ = lean_ctor_get(v_inst_17_, 1);
lean_dec(v_unused_34_);
v___x_24_ = v_inst_17_;
v_isShared_25_ = v_isSharedCheck_33_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_toApplicative_22_);
lean_dec(v_inst_17_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_33_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v_toPure_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_30_; 
v_toPure_26_ = lean_ctor_get(v_toApplicative_22_, 1);
lean_inc(v_toPure_26_);
lean_dec_ref(v_toApplicative_22_);
v___x_27_ = lean_box(0);
v___x_28_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_18_, v_k_19_, v_a_20_, v___y_21_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 1, v___x_28_);
lean_ctor_set(v___x_24_, 0, v___x_27_);
v___x_30_ = v___x_24_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v___x_27_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v___x_28_);
v___x_30_ = v_reuseFailAlloc_32_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
lean_object* v___x_31_; 
v___x_31_ = lean_apply_2(v_toPure_26_, lean_box(0), v___x_30_);
return v___x_31_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg(lean_object* v_cmp_35_, lean_object* v_inst_36_){
_start:
{
lean_object* v___f_37_; lean_object* v___f_38_; lean_object* v___x_39_; 
lean_inc_ref(v_cmp_35_);
lean_inc_ref(v_inst_36_);
v___f_37_ = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__0), 4, 2);
lean_closure_set(v___f_37_, 0, v_inst_36_);
lean_closure_set(v___f_37_, 1, v_cmp_35_);
v___f_38_ = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__1), 5, 2);
lean_closure_set(v___f_38_, 0, v_inst_36_);
lean_closure_set(v___f_38_, 1, v_cmp_35_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v___f_37_);
lean_ctor_set(v___x_39_, 1, v___f_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp(lean_object* v_00_u03ba_40_, lean_object* v_m_41_, lean_object* v_00_u03b2_42_, lean_object* v_cmp_43_, lean_object* v_inst_44_, lean_object* v_inst_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg(v_cmp_43_, v_inst_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__0(lean_object* v_cmp_47_, lean_object* v_k_48_, lean_object* v_m_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
lean_inc(v_m_49_);
v___x_50_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_47_, v_m_49_, v_k_48_);
v___x_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v_m_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__1(lean_object* v_cmp_52_, lean_object* v_inst_53_, lean_object* v_k_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___f_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___f_56_ = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_56_, 0, v_cmp_52_);
lean_closure_set(v___f_56_, 1, v_k_54_);
lean_inc(v___y_55_);
v___x_57_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_57_, 0, lean_box(0));
lean_closure_set(v___x_57_, 1, lean_box(0));
lean_closure_set(v___x_57_, 2, lean_box(0));
lean_closure_set(v___x_57_, 3, v___y_55_);
lean_closure_set(v___x_57_, 4, v___f_56_);
v___x_58_ = lean_apply_2(v_inst_53_, lean_box(0), v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__1___boxed(lean_object* v_cmp_59_, lean_object* v_inst_60_, lean_object* v_k_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__1(v_cmp_59_, v_inst_60_, v_k_61_, v___y_62_);
lean_dec(v___y_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__2(lean_object* v_cmp_64_, lean_object* v_k_65_, lean_object* v_a_66_, lean_object* v_s_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_box(0);
v___x_69_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_64_, v_k_65_, v_a_66_, v_s_67_);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_68_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3(lean_object* v_cmp_71_, lean_object* v_inst_72_, lean_object* v_k_73_, lean_object* v_a_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___f_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___f_76_ = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__2), 4, 3);
lean_closure_set(v___f_76_, 0, v_cmp_71_);
lean_closure_set(v___f_76_, 1, v_k_73_);
lean_closure_set(v___f_76_, 2, v_a_74_);
lean_inc(v___y_75_);
v___x_77_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_77_, 0, lean_box(0));
lean_closure_set(v___x_77_, 1, lean_box(0));
lean_closure_set(v___x_77_, 2, lean_box(0));
lean_closure_set(v___x_77_, 3, v___y_75_);
lean_closure_set(v___x_77_, 4, v___f_76_);
v___x_78_ = lean_apply_2(v_inst_72_, lean_box(0), v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3___boxed(lean_object* v_cmp_79_, lean_object* v_inst_80_, lean_object* v_k_81_, lean_object* v_a_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3(v_cmp_79_, v_inst_80_, v_k_81_, v_a_82_, v___y_83_);
lean_dec(v___y_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg(lean_object* v_cmp_85_, lean_object* v_inst_86_){
_start:
{
lean_object* v___f_87_; lean_object* v___f_88_; lean_object* v___x_89_; 
lean_inc(v_inst_86_);
lean_inc_ref(v_cmp_85_);
v___f_87_ = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_87_, 0, v_cmp_85_);
lean_closure_set(v___f_87_, 1, v_inst_86_);
v___f_88_ = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_88_, 0, v_cmp_85_);
lean_closure_set(v___f_88_, 1, v_inst_86_);
v___x_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_89_, 0, v___f_87_);
lean_ctor_set(v___x_89_, 1, v___f_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp(lean_object* v_00_u03ba_90_, lean_object* v_00_u03c9_91_, lean_object* v_m_92_, lean_object* v_00_u03b2_93_, lean_object* v_cmp_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_inst_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg(v_cmp_94_, v_inst_95_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___boxed(lean_object* v_00_u03ba_99_, lean_object* v_00_u03c9_100_, lean_object* v_m_101_, lean_object* v_00_u03b2_102_, lean_object* v_cmp_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_inst_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp(v_00_u03ba_99_, v_00_u03c9_100_, v_m_101_, v_00_u03b2_102_, v_cmp_103_, v_inst_104_, v_inst_105_, v_inst_106_);
lean_dec_ref(v_inst_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__0(lean_object* v_inst_108_, lean_object* v_cmp_109_, lean_object* v_k_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_toApplicative_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_123_; 
v_toApplicative_112_ = lean_ctor_get(v_inst_108_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v_inst_108_);
if (v_isSharedCheck_123_ == 0)
{
lean_object* v_unused_124_; 
v_unused_124_ = lean_ctor_get(v_inst_108_, 1);
lean_dec(v_unused_124_);
v___x_114_ = v_inst_108_;
v_isShared_115_ = v_isSharedCheck_123_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_toApplicative_112_);
lean_dec(v_inst_108_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_123_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v_toPure_116_; lean_object* v_toTreeMap_117_; lean_object* v___x_118_; lean_object* v___x_120_; 
v_toPure_116_ = lean_ctor_get(v_toApplicative_112_, 1);
lean_inc(v_toPure_116_);
lean_dec_ref(v_toApplicative_112_);
v_toTreeMap_117_ = lean_ctor_get(v___y_111_, 0);
lean_inc(v_toTreeMap_117_);
v___x_118_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_109_, v_toTreeMap_117_, v_k_110_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 1, v___y_111_);
lean_ctor_set(v___x_114_, 0, v___x_118_);
v___x_120_ = v___x_114_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_118_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v___y_111_);
v___x_120_ = v_reuseFailAlloc_122_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_object* v___x_121_; 
v___x_121_ = lean_apply_2(v_toPure_116_, lean_box(0), v___x_120_);
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__1(lean_object* v_inst_125_, lean_object* v_cmp_126_, lean_object* v_k_127_, lean_object* v_a_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_toApplicative_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_141_; 
v_toApplicative_130_ = lean_ctor_get(v_inst_125_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v_inst_125_);
if (v_isSharedCheck_141_ == 0)
{
lean_object* v_unused_142_; 
v_unused_142_ = lean_ctor_get(v_inst_125_, 1);
lean_dec(v_unused_142_);
v___x_132_ = v_inst_125_;
v_isShared_133_ = v_isSharedCheck_141_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_toApplicative_130_);
lean_dec(v_inst_125_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_141_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v_toPure_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
v_toPure_134_ = lean_ctor_get(v_toApplicative_130_, 1);
lean_inc(v_toPure_134_);
lean_dec_ref(v_toApplicative_130_);
v___x_135_ = lean_box(0);
v___x_136_ = l_Lake_RBArray_insert___redArg(v_cmp_126_, v___y_129_, v_k_127_, v_a_128_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v___x_136_);
lean_ctor_set(v___x_132_, 0, v___x_135_);
v___x_138_ = v___x_132_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v___x_136_);
v___x_138_ = v_reuseFailAlloc_140_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_139_; 
v___x_139_ = lean_apply_2(v_toPure_134_, lean_box(0), v___x_138_);
return v___x_139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg(lean_object* v_cmp_143_, lean_object* v_inst_144_){
_start:
{
lean_object* v___f_145_; lean_object* v___f_146_; lean_object* v___x_147_; 
lean_inc_ref(v_cmp_143_);
lean_inc_ref(v_inst_144_);
v___f_145_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__0), 4, 2);
lean_closure_set(v___f_145_, 0, v_inst_144_);
lean_closure_set(v___f_145_, 1, v_cmp_143_);
v___f_146_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_146_, 0, v_inst_144_);
lean_closure_set(v___f_146_, 1, v_cmp_143_);
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v___f_145_);
lean_ctor_set(v___x_147_, 1, v___f_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad(lean_object* v_m_148_, lean_object* v_00_u03ba_149_, lean_object* v_00_u03b1_150_, lean_object* v_cmp_151_, lean_object* v_inst_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg(v_cmp_151_, v_inst_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__0(lean_object* v_cmp_154_, lean_object* v_k_155_, lean_object* v_m_156_){
_start:
{
lean_object* v_toTreeMap_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v_toTreeMap_157_ = lean_ctor_get(v_m_156_, 0);
lean_inc(v_toTreeMap_157_);
v___x_158_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_154_, v_toTreeMap_157_, v_k_155_);
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v_m_156_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1(lean_object* v_cmp_160_, lean_object* v_inst_161_, lean_object* v_k_162_, lean_object* v___y_163_){
_start:
{
lean_object* v___f_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___f_164_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__0), 3, 2);
lean_closure_set(v___f_164_, 0, v_cmp_160_);
lean_closure_set(v___f_164_, 1, v_k_162_);
lean_inc(v___y_163_);
v___x_165_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_165_, 0, lean_box(0));
lean_closure_set(v___x_165_, 1, lean_box(0));
lean_closure_set(v___x_165_, 2, lean_box(0));
lean_closure_set(v___x_165_, 3, v___y_163_);
lean_closure_set(v___x_165_, 4, v___f_164_);
v___x_166_ = lean_apply_2(v_inst_161_, lean_box(0), v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1___boxed(lean_object* v_cmp_167_, lean_object* v_inst_168_, lean_object* v_k_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1(v_cmp_167_, v_inst_168_, v_k_169_, v___y_170_);
lean_dec(v___y_170_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__2(lean_object* v_cmp_172_, lean_object* v_k_173_, lean_object* v_a_174_, lean_object* v_s_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_box(0);
v___x_177_ = l_Lake_RBArray_insert___redArg(v_cmp_172_, v_s_175_, v_k_173_, v_a_174_);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3(lean_object* v_cmp_179_, lean_object* v_inst_180_, lean_object* v_k_181_, lean_object* v_a_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___f_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___f_184_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__2), 4, 3);
lean_closure_set(v___f_184_, 0, v_cmp_179_);
lean_closure_set(v___f_184_, 1, v_k_181_);
lean_closure_set(v___f_184_, 2, v_a_182_);
lean_inc(v___y_183_);
v___x_185_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_185_, 0, lean_box(0));
lean_closure_set(v___x_185_, 1, lean_box(0));
lean_closure_set(v___x_185_, 2, lean_box(0));
lean_closure_set(v___x_185_, 3, v___y_183_);
lean_closure_set(v___x_185_, 4, v___f_184_);
v___x_186_ = lean_apply_2(v_inst_180_, lean_box(0), v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3___boxed(lean_object* v_cmp_187_, lean_object* v_inst_188_, lean_object* v_k_189_, lean_object* v_a_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3(v_cmp_187_, v_inst_188_, v_k_189_, v_a_190_, v___y_191_);
lean_dec(v___y_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg(lean_object* v_cmp_193_, lean_object* v_inst_194_){
_start:
{
lean_object* v___f_195_; lean_object* v___f_196_; lean_object* v___x_197_; 
lean_inc(v_inst_194_);
lean_inc_ref(v_cmp_193_);
v___f_195_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_195_, 0, v_cmp_193_);
lean_closure_set(v___f_195_, 1, v_inst_194_);
v___f_196_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_196_, 0, v_cmp_193_);
lean_closure_set(v___f_196_, 1, v_inst_194_);
v___x_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_197_, 0, v___f_195_);
lean_ctor_set(v___x_197_, 1, v___f_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad(lean_object* v_00_u03c9_198_, lean_object* v_m_199_, lean_object* v_00_u03ba_200_, lean_object* v_00_u03b1_201_, lean_object* v_cmp_202_, lean_object* v_inst_203_, lean_object* v_inst_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg(v_cmp_202_, v_inst_203_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___boxed(lean_object* v_00_u03c9_206_, lean_object* v_m_207_, lean_object* v_00_u03ba_208_, lean_object* v_00_u03b1_209_, lean_object* v_cmp_210_, lean_object* v_inst_211_, lean_object* v_inst_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad(v_00_u03c9_206_, v_m_207_, v_00_u03ba_208_, v_00_u03b1_209_, v_cmp_210_, v_inst_211_, v_inst_212_);
lean_dec_ref(v_inst_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0(lean_object* v_inst_214_, lean_object* v_k_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_toApplicative_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_227_; 
v_toApplicative_217_ = lean_ctor_get(v_inst_214_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v_inst_214_);
if (v_isSharedCheck_227_ == 0)
{
lean_object* v_unused_228_; 
v_unused_228_ = lean_ctor_get(v_inst_214_, 1);
lean_dec(v_unused_228_);
v___x_219_ = v_inst_214_;
v_isShared_220_ = v_isSharedCheck_227_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_toApplicative_217_);
lean_dec(v_inst_214_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_227_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v_toPure_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v_toPure_221_ = lean_ctor_get(v_toApplicative_217_, 1);
lean_inc(v_toPure_221_);
lean_dec_ref(v_toApplicative_217_);
v___x_222_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_216_, v_k_215_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___y_216_);
lean_ctor_set(v___x_219_, 0, v___x_222_);
v___x_224_ = v___x_219_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v___y_216_);
v___x_224_ = v_reuseFailAlloc_226_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_225_; 
v___x_225_ = lean_apply_2(v_toPure_221_, lean_box(0), v___x_224_);
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0___boxed(lean_object* v_inst_229_, lean_object* v_k_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0(v_inst_229_, v_k_230_, v___y_231_);
lean_dec(v_k_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__1(lean_object* v_inst_233_, lean_object* v_k_234_, lean_object* v_a_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_toApplicative_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_248_; 
v_toApplicative_237_ = lean_ctor_get(v_inst_233_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v_inst_233_);
if (v_isSharedCheck_248_ == 0)
{
lean_object* v_unused_249_; 
v_unused_249_ = lean_ctor_get(v_inst_233_, 1);
lean_dec(v_unused_249_);
v___x_239_ = v_inst_233_;
v_isShared_240_ = v_isSharedCheck_248_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_toApplicative_237_);
lean_dec(v_inst_233_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_248_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v_toPure_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
v_toPure_241_ = lean_ctor_get(v_toApplicative_237_, 1);
lean_inc(v_toPure_241_);
lean_dec_ref(v_toApplicative_237_);
v___x_242_ = lean_box(0);
v___x_243_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_234_, v_a_235_, v___y_236_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_243_);
lean_ctor_set(v___x_239_, 0, v___x_242_);
v___x_245_ = v___x_239_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v___x_243_);
v___x_245_ = v_reuseFailAlloc_247_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; 
v___x_246_ = lean_apply_2(v_toPure_241_, lean_box(0), v___x_245_);
return v___x_246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg(lean_object* v_inst_250_){
_start:
{
lean_object* v___f_251_; lean_object* v___f_252_; lean_object* v___x_253_; 
lean_inc_ref(v_inst_250_);
v___f_251_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_251_, 0, v_inst_250_);
v___f_252_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__1), 4, 1);
lean_closure_set(v___f_252_, 0, v_inst_250_);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___f_251_);
lean_ctor_set(v___x_253_, 1, v___f_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad(lean_object* v_m_254_, lean_object* v_00_u03b1_255_, lean_object* v_inst_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg(v_inst_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0(lean_object* v_k_258_, lean_object* v_m_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_m_259_, v_k_258_);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v_m_259_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0___boxed(lean_object* v_k_262_, lean_object* v_m_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0(v_k_262_, v_m_263_);
lean_dec(v_k_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__1(lean_object* v_inst_265_, lean_object* v_k_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___f_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___f_268_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_268_, 0, v_k_266_);
lean_inc(v___y_267_);
v___x_269_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_269_, 0, lean_box(0));
lean_closure_set(v___x_269_, 1, lean_box(0));
lean_closure_set(v___x_269_, 2, lean_box(0));
lean_closure_set(v___x_269_, 3, v___y_267_);
lean_closure_set(v___x_269_, 4, v___f_268_);
v___x_270_ = lean_apply_2(v_inst_265_, lean_box(0), v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__1___boxed(lean_object* v_inst_271_, lean_object* v_k_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__1(v_inst_271_, v_k_272_, v___y_273_);
lean_dec(v___y_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__2(lean_object* v_k_275_, lean_object* v_a_276_, lean_object* v_s_277_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = lean_box(0);
v___x_279_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_275_, v_a_276_, v_s_277_);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3(lean_object* v_inst_281_, lean_object* v_k_282_, lean_object* v_a_283_, lean_object* v___y_284_){
_start:
{
lean_object* v___f_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___f_285_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_285_, 0, v_k_282_);
lean_closure_set(v___f_285_, 1, v_a_283_);
lean_inc(v___y_284_);
v___x_286_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_286_, 0, lean_box(0));
lean_closure_set(v___x_286_, 1, lean_box(0));
lean_closure_set(v___x_286_, 2, lean_box(0));
lean_closure_set(v___x_286_, 3, v___y_284_);
lean_closure_set(v___x_286_, 4, v___f_285_);
v___x_287_ = lean_apply_2(v_inst_281_, lean_box(0), v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3___boxed(lean_object* v_inst_288_, lean_object* v_k_289_, lean_object* v_a_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3(v_inst_288_, v_k_289_, v_a_290_, v___y_291_);
lean_dec(v___y_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg(lean_object* v_inst_293_){
_start:
{
lean_object* v___f_294_; lean_object* v___f_295_; lean_object* v___x_296_; 
lean_inc(v_inst_293_);
v___f_294_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_294_, 0, v_inst_293_);
v___f_295_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3___boxed), 4, 1);
lean_closure_set(v___f_295_, 0, v_inst_293_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v___f_294_);
lean_ctor_set(v___x_296_, 1, v___f_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad(lean_object* v_00_u03c9_297_, lean_object* v_m_298_, lean_object* v_00_u03b1_299_, lean_object* v_inst_300_, lean_object* v_inst_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg(v_inst_300_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___boxed(lean_object* v_00_u03c9_303_, lean_object* v_m_304_, lean_object* v_00_u03b1_305_, lean_object* v_inst_306_, lean_object* v_inst_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad(v_00_u03c9_303_, v_m_304_, v_00_u03b1_305_, v_inst_306_, v_inst_307_);
lean_dec_ref(v_inst_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg___lam__0(lean_object* v_store_309_, lean_object* v_k_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = lean_apply_2(v_store_309_, v_k_310_, v_a_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg(lean_object* v_k_313_, lean_object* v_inst_314_){
_start:
{
lean_object* v_fetch_x3f_315_; lean_object* v_store_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_325_; 
v_fetch_x3f_315_ = lean_ctor_get(v_inst_314_, 0);
v_store_316_ = lean_ctor_get(v_inst_314_, 1);
v_isSharedCheck_325_ = !lean_is_exclusive(v_inst_314_);
if (v_isSharedCheck_325_ == 0)
{
v___x_318_ = v_inst_314_;
v_isShared_319_ = v_isSharedCheck_325_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_store_316_);
lean_inc(v_fetch_x3f_315_);
lean_dec(v_inst_314_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_325_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___f_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
lean_inc(v_k_313_);
v___f_320_ = lean_alloc_closure((void*)(l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg___lam__0), 3, 2);
lean_closure_set(v___f_320_, 0, v_store_316_);
lean_closure_set(v___f_320_, 1, v_k_313_);
v___x_321_ = lean_apply_1(v_fetch_x3f_315_, v_k_313_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 1, v___f_320_);
lean_ctor_set(v___x_318_, 0, v___x_321_);
v___x_323_ = v___x_318_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v___f_320_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut(lean_object* v_00_u03ba_326_, lean_object* v_00_u03b2_327_, lean_object* v_m_328_, lean_object* v_k_329_, lean_object* v_00_u03b1_330_, lean_object* v_inst_331_, lean_object* v_t_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg(v_k_329_, v_inst_331_);
return v___x_333_;
}
}
lean_object* runtime_initialize_Init_Data_Order(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_NameMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_RBArray(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Family(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Store(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_StoreInsts(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_RBArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Family(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Store(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_StoreInsts(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order(uint8_t builtin);
lean_object* initialize_Lean_Data_NameMap_Basic(uint8_t builtin);
lean_object* initialize_Lake_Util_RBArray(uint8_t builtin);
lean_object* initialize_Lake_Util_Family(uint8_t builtin);
lean_object* initialize_Lake_Util_Store(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_StoreInsts(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_NameMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_RBArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Family(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Store(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_StoreInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_StoreInsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_StoreInsts(builtin);
}
#ifdef __cplusplus
}
#endif
