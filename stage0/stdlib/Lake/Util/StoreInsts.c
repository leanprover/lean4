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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBArray_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__0(lean_object* v_cmp_1_, lean_object* v_k_2_, lean_object* v_toPure_3_, lean_object* v_____x_4_){
_start:
{
lean_object* v_fst_5_; lean_object* v_snd_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_15_; 
v_fst_5_ = lean_ctor_get(v_____x_4_, 0);
v_snd_6_ = lean_ctor_get(v_____x_4_, 1);
v_isSharedCheck_15_ = !lean_is_exclusive(v_____x_4_);
if (v_isSharedCheck_15_ == 0)
{
v___x_8_ = v_____x_4_;
v_isShared_9_ = v_isSharedCheck_15_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_snd_6_);
lean_inc(v_fst_5_);
lean_dec(v_____x_4_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_15_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; lean_object* v___x_12_; 
v___x_10_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_1_, v_fst_5_, v_k_2_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 0, v___x_10_);
v___x_12_ = v___x_8_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v___x_10_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v_snd_6_);
v___x_12_ = v_reuseFailAlloc_14_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
lean_object* v___x_13_; 
v___x_13_ = lean_apply_2(v_toPure_3_, lean_box(0), v___x_12_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__1(lean_object* v_inst_16_, lean_object* v_cmp_17_, lean_object* v_k_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_toApplicative_20_; lean_object* v_toBind_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_32_; 
v_toApplicative_20_ = lean_ctor_get(v_inst_16_, 0);
v_toBind_21_ = lean_ctor_get(v_inst_16_, 1);
v_isSharedCheck_32_ = !lean_is_exclusive(v_inst_16_);
if (v_isSharedCheck_32_ == 0)
{
v___x_23_ = v_inst_16_;
v_isShared_24_ = v_isSharedCheck_32_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_toBind_21_);
lean_inc(v_toApplicative_20_);
lean_dec(v_inst_16_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_32_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v_toPure_25_; lean_object* v___f_26_; lean_object* v___x_28_; 
v_toPure_25_ = lean_ctor_get(v_toApplicative_20_, 1);
lean_inc(v_toPure_25_);
lean_dec_ref(v_toApplicative_20_);
lean_inc(v_toPure_25_);
v___f_26_ = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_26_, 0, v_cmp_17_);
lean_closure_set(v___f_26_, 1, v_k_18_);
lean_closure_set(v___f_26_, 2, v_toPure_25_);
lean_inc(v___y_19_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 1, v___y_19_);
lean_ctor_set(v___x_23_, 0, v___y_19_);
v___x_28_ = v___x_23_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___y_19_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v___y_19_);
v___x_28_ = v_reuseFailAlloc_31_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_apply_2(v_toPure_25_, lean_box(0), v___x_28_);
v___x_30_ = lean_apply_4(v_toBind_21_, lean_box(0), lean_box(0), v___x_29_, v___f_26_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__2(lean_object* v_inst_33_, lean_object* v_cmp_34_, lean_object* v_k_35_, lean_object* v_a_36_, lean_object* v___y_37_){
_start:
{
lean_object* v_toApplicative_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_49_; 
v_toApplicative_38_ = lean_ctor_get(v_inst_33_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v_inst_33_);
if (v_isSharedCheck_49_ == 0)
{
lean_object* v_unused_50_; 
v_unused_50_ = lean_ctor_get(v_inst_33_, 1);
lean_dec(v_unused_50_);
v___x_40_ = v_inst_33_;
v_isShared_41_ = v_isSharedCheck_49_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_toApplicative_38_);
lean_dec(v_inst_33_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_49_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v_toPure_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
v_toPure_42_ = lean_ctor_get(v_toApplicative_38_, 1);
lean_inc(v_toPure_42_);
lean_dec_ref(v_toApplicative_38_);
v___x_43_ = lean_box(0);
v___x_44_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_34_, v_k_35_, v_a_36_, v___y_37_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 1, v___x_44_);
lean_ctor_set(v___x_40_, 0, v___x_43_);
v___x_46_ = v___x_40_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v___x_43_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v___x_44_);
v___x_46_ = v_reuseFailAlloc_48_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_47_; 
v___x_47_ = lean_apply_2(v_toPure_42_, lean_box(0), v___x_46_);
return v___x_47_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg(lean_object* v_cmp_51_, lean_object* v_inst_52_){
_start:
{
lean_object* v___f_53_; lean_object* v___f_54_; lean_object* v___x_55_; 
lean_inc_ref(v_cmp_51_);
lean_inc_ref(v_inst_52_);
v___f_53_ = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__1), 4, 2);
lean_closure_set(v___f_53_, 0, v_inst_52_);
lean_closure_set(v___f_53_, 1, v_cmp_51_);
v___f_54_ = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__2), 5, 2);
lean_closure_set(v___f_54_, 0, v_inst_52_);
lean_closure_set(v___f_54_, 1, v_cmp_51_);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___f_53_);
lean_ctor_set(v___x_55_, 1, v___f_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp(lean_object* v_00_u03ba_56_, lean_object* v_m_57_, lean_object* v_00_u03b2_58_, lean_object* v_cmp_59_, lean_object* v_inst_60_, lean_object* v_inst_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg(v_cmp_59_, v_inst_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__0(lean_object* v_toApplicative_63_, lean_object* v_cmp_64_, lean_object* v_k_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_toPure_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_toPure_67_ = lean_ctor_get(v_toApplicative_63_, 1);
lean_inc(v_toPure_67_);
lean_dec_ref(v_toApplicative_63_);
v___x_68_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_64_, v_a_66_, v_k_65_);
v___x_69_ = lean_apply_2(v_toPure_67_, lean_box(0), v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__1(lean_object* v_inst_70_, lean_object* v_cmp_71_, lean_object* v_inst_72_, lean_object* v_k_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_toApplicative_75_; lean_object* v_toBind_76_; lean_object* v___f_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_toApplicative_75_ = lean_ctor_get(v_inst_70_, 0);
lean_inc_ref(v_toApplicative_75_);
v_toBind_76_ = lean_ctor_get(v_inst_70_, 1);
lean_inc(v_toBind_76_);
lean_dec_ref(v_inst_70_);
v___f_77_ = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__0), 4, 3);
lean_closure_set(v___f_77_, 0, v_toApplicative_75_);
lean_closure_set(v___f_77_, 1, v_cmp_71_);
lean_closure_set(v___f_77_, 2, v_k_73_);
lean_inc(v___y_74_);
v___x_78_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_78_, 0, lean_box(0));
lean_closure_set(v___x_78_, 1, lean_box(0));
lean_closure_set(v___x_78_, 2, v___y_74_);
v___x_79_ = lean_apply_2(v_inst_72_, lean_box(0), v___x_78_);
v___x_80_ = lean_apply_4(v_toBind_76_, lean_box(0), lean_box(0), v___x_79_, v___f_77_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__1___boxed(lean_object* v_inst_81_, lean_object* v_cmp_82_, lean_object* v_inst_83_, lean_object* v_k_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__1(v_inst_81_, v_cmp_82_, v_inst_83_, v_k_84_, v___y_85_);
lean_dec(v___y_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__2(lean_object* v_cmp_87_, lean_object* v_k_88_, lean_object* v_a_89_, lean_object* v_s_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_box(0);
v___x_92_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_87_, v_k_88_, v_a_89_, v_s_90_);
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3(lean_object* v_cmp_94_, lean_object* v_inst_95_, lean_object* v_k_96_, lean_object* v_a_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___f_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___f_99_ = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__2), 4, 3);
lean_closure_set(v___f_99_, 0, v_cmp_94_);
lean_closure_set(v___f_99_, 1, v_k_96_);
lean_closure_set(v___f_99_, 2, v_a_97_);
lean_inc(v___y_98_);
v___x_100_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_100_, 0, lean_box(0));
lean_closure_set(v___x_100_, 1, lean_box(0));
lean_closure_set(v___x_100_, 2, lean_box(0));
lean_closure_set(v___x_100_, 3, v___y_98_);
lean_closure_set(v___x_100_, 4, v___f_99_);
v___x_101_ = lean_apply_2(v_inst_95_, lean_box(0), v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3___boxed(lean_object* v_cmp_102_, lean_object* v_inst_103_, lean_object* v_k_104_, lean_object* v_a_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3(v_cmp_102_, v_inst_103_, v_k_104_, v_a_105_, v___y_106_);
lean_dec(v___y_106_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg(lean_object* v_cmp_108_, lean_object* v_inst_109_, lean_object* v_inst_110_){
_start:
{
lean_object* v___f_111_; lean_object* v___f_112_; lean_object* v___x_113_; 
lean_inc(v_inst_109_);
lean_inc_ref(v_cmp_108_);
v___f_111_ = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_111_, 0, v_inst_110_);
lean_closure_set(v___f_111_, 1, v_cmp_108_);
lean_closure_set(v___f_111_, 2, v_inst_109_);
v___f_112_ = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_112_, 0, v_cmp_108_);
lean_closure_set(v___f_112_, 1, v_inst_109_);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v___f_111_);
lean_ctor_set(v___x_113_, 1, v___f_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp(lean_object* v_00_u03ba_114_, lean_object* v_00_u03c9_115_, lean_object* v_m_116_, lean_object* v_00_u03b2_117_, lean_object* v_cmp_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_inst_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg(v_cmp_118_, v_inst_119_, v_inst_120_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__0(lean_object* v_cmp_123_, lean_object* v_k_124_, lean_object* v_toPure_125_, lean_object* v_____x_126_){
_start:
{
lean_object* v_fst_127_; lean_object* v_snd_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_138_; 
v_fst_127_ = lean_ctor_get(v_____x_126_, 0);
v_snd_128_ = lean_ctor_get(v_____x_126_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v_____x_126_);
if (v_isSharedCheck_138_ == 0)
{
v___x_130_ = v_____x_126_;
v_isShared_131_ = v_isSharedCheck_138_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_snd_128_);
lean_inc(v_fst_127_);
lean_dec(v_____x_126_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_138_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v_toTreeMap_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v_toTreeMap_132_ = lean_ctor_get(v_fst_127_, 0);
lean_inc(v_toTreeMap_132_);
lean_dec(v_fst_127_);
v___x_133_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_123_, v_toTreeMap_132_, v_k_124_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 0, v___x_133_);
v___x_135_ = v___x_130_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_snd_128_);
v___x_135_ = v_reuseFailAlloc_137_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; 
v___x_136_ = lean_apply_2(v_toPure_125_, lean_box(0), v___x_135_);
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__1(lean_object* v_inst_139_, lean_object* v_cmp_140_, lean_object* v_k_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_toApplicative_143_; lean_object* v_toBind_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_155_; 
v_toApplicative_143_ = lean_ctor_get(v_inst_139_, 0);
v_toBind_144_ = lean_ctor_get(v_inst_139_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_inst_139_);
if (v_isSharedCheck_155_ == 0)
{
v___x_146_ = v_inst_139_;
v_isShared_147_ = v_isSharedCheck_155_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_toBind_144_);
lean_inc(v_toApplicative_143_);
lean_dec(v_inst_139_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_155_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v_toPure_148_; lean_object* v___f_149_; lean_object* v___x_151_; 
v_toPure_148_ = lean_ctor_get(v_toApplicative_143_, 1);
lean_inc(v_toPure_148_);
lean_dec_ref(v_toApplicative_143_);
lean_inc(v_toPure_148_);
v___f_149_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_149_, 0, v_cmp_140_);
lean_closure_set(v___f_149_, 1, v_k_141_);
lean_closure_set(v___f_149_, 2, v_toPure_148_);
lean_inc_ref(v___y_142_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 1, v___y_142_);
lean_ctor_set(v___x_146_, 0, v___y_142_);
v___x_151_ = v___x_146_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___y_142_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v___y_142_);
v___x_151_ = v_reuseFailAlloc_154_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_apply_2(v_toPure_148_, lean_box(0), v___x_151_);
v___x_153_ = lean_apply_4(v_toBind_144_, lean_box(0), lean_box(0), v___x_152_, v___f_149_);
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__2(lean_object* v_inst_156_, lean_object* v_cmp_157_, lean_object* v_k_158_, lean_object* v_a_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_toApplicative_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_172_; 
v_toApplicative_161_ = lean_ctor_get(v_inst_156_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v_inst_156_);
if (v_isSharedCheck_172_ == 0)
{
lean_object* v_unused_173_; 
v_unused_173_ = lean_ctor_get(v_inst_156_, 1);
lean_dec(v_unused_173_);
v___x_163_ = v_inst_156_;
v_isShared_164_ = v_isSharedCheck_172_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_toApplicative_161_);
lean_dec(v_inst_156_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_172_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v_toPure_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v_toPure_165_ = lean_ctor_get(v_toApplicative_161_, 1);
lean_inc(v_toPure_165_);
lean_dec_ref(v_toApplicative_161_);
v___x_166_ = lean_box(0);
v___x_167_ = l_Lake_RBArray_insert___redArg(v_cmp_157_, v___y_160_, v_k_158_, v_a_159_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 1, v___x_167_);
lean_ctor_set(v___x_163_, 0, v___x_166_);
v___x_169_ = v___x_163_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_167_);
v___x_169_ = v_reuseFailAlloc_171_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_170_; 
v___x_170_ = lean_apply_2(v_toPure_165_, lean_box(0), v___x_169_);
return v___x_170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg(lean_object* v_cmp_174_, lean_object* v_inst_175_){
_start:
{
lean_object* v___f_176_; lean_object* v___f_177_; lean_object* v___x_178_; 
lean_inc_ref(v_cmp_174_);
lean_inc_ref(v_inst_175_);
v___f_176_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__1), 4, 2);
lean_closure_set(v___f_176_, 0, v_inst_175_);
lean_closure_set(v___f_176_, 1, v_cmp_174_);
v___f_177_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__2), 5, 2);
lean_closure_set(v___f_177_, 0, v_inst_175_);
lean_closure_set(v___f_177_, 1, v_cmp_174_);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___f_176_);
lean_ctor_set(v___x_178_, 1, v___f_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad(lean_object* v_m_179_, lean_object* v_00_u03ba_180_, lean_object* v_00_u03b1_181_, lean_object* v_cmp_182_, lean_object* v_inst_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg(v_cmp_182_, v_inst_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__0(lean_object* v_toApplicative_185_, lean_object* v_cmp_186_, lean_object* v_k_187_, lean_object* v_a_188_){
_start:
{
lean_object* v_toTreeMap_189_; lean_object* v_toPure_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_toTreeMap_189_ = lean_ctor_get(v_a_188_, 0);
lean_inc(v_toTreeMap_189_);
lean_dec_ref(v_a_188_);
v_toPure_190_ = lean_ctor_get(v_toApplicative_185_, 1);
lean_inc(v_toPure_190_);
lean_dec_ref(v_toApplicative_185_);
v___x_191_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_186_, v_toTreeMap_189_, v_k_187_);
v___x_192_ = lean_apply_2(v_toPure_190_, lean_box(0), v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1(lean_object* v_inst_193_, lean_object* v_cmp_194_, lean_object* v_inst_195_, lean_object* v_k_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_toApplicative_198_; lean_object* v_toBind_199_; lean_object* v___f_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_toApplicative_198_ = lean_ctor_get(v_inst_193_, 0);
lean_inc_ref(v_toApplicative_198_);
v_toBind_199_ = lean_ctor_get(v_inst_193_, 1);
lean_inc(v_toBind_199_);
lean_dec_ref(v_inst_193_);
v___f_200_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_200_, 0, v_toApplicative_198_);
lean_closure_set(v___f_200_, 1, v_cmp_194_);
lean_closure_set(v___f_200_, 2, v_k_196_);
lean_inc(v___y_197_);
v___x_201_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_201_, 0, lean_box(0));
lean_closure_set(v___x_201_, 1, lean_box(0));
lean_closure_set(v___x_201_, 2, v___y_197_);
v___x_202_ = lean_apply_2(v_inst_195_, lean_box(0), v___x_201_);
v___x_203_ = lean_apply_4(v_toBind_199_, lean_box(0), lean_box(0), v___x_202_, v___f_200_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1___boxed(lean_object* v_inst_204_, lean_object* v_cmp_205_, lean_object* v_inst_206_, lean_object* v_k_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1(v_inst_204_, v_cmp_205_, v_inst_206_, v_k_207_, v___y_208_);
lean_dec(v___y_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__2(lean_object* v_cmp_210_, lean_object* v_k_211_, lean_object* v_a_212_, lean_object* v_s_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_box(0);
v___x_215_ = l_Lake_RBArray_insert___redArg(v_cmp_210_, v_s_213_, v_k_211_, v_a_212_);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_214_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3(lean_object* v_cmp_217_, lean_object* v_inst_218_, lean_object* v_k_219_, lean_object* v_a_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___f_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___f_222_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__2), 4, 3);
lean_closure_set(v___f_222_, 0, v_cmp_217_);
lean_closure_set(v___f_222_, 1, v_k_219_);
lean_closure_set(v___f_222_, 2, v_a_220_);
lean_inc(v___y_221_);
v___x_223_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_223_, 0, lean_box(0));
lean_closure_set(v___x_223_, 1, lean_box(0));
lean_closure_set(v___x_223_, 2, lean_box(0));
lean_closure_set(v___x_223_, 3, v___y_221_);
lean_closure_set(v___x_223_, 4, v___f_222_);
v___x_224_ = lean_apply_2(v_inst_218_, lean_box(0), v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3___boxed(lean_object* v_cmp_225_, lean_object* v_inst_226_, lean_object* v_k_227_, lean_object* v_a_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3(v_cmp_225_, v_inst_226_, v_k_227_, v_a_228_, v___y_229_);
lean_dec(v___y_229_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg(lean_object* v_cmp_231_, lean_object* v_inst_232_, lean_object* v_inst_233_){
_start:
{
lean_object* v___f_234_; lean_object* v___f_235_; lean_object* v___x_236_; 
lean_inc(v_inst_232_);
lean_inc_ref(v_cmp_231_);
v___f_234_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_234_, 0, v_inst_233_);
lean_closure_set(v___f_234_, 1, v_cmp_231_);
lean_closure_set(v___f_234_, 2, v_inst_232_);
v___f_235_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_235_, 0, v_cmp_231_);
lean_closure_set(v___f_235_, 1, v_inst_232_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___f_234_);
lean_ctor_set(v___x_236_, 1, v___f_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad(lean_object* v_00_u03c9_237_, lean_object* v_m_238_, lean_object* v_00_u03ba_239_, lean_object* v_00_u03b1_240_, lean_object* v_cmp_241_, lean_object* v_inst_242_, lean_object* v_inst_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg(v_cmp_241_, v_inst_242_, v_inst_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0(lean_object* v_k_245_, lean_object* v_toPure_246_, lean_object* v_____x_247_){
_start:
{
lean_object* v_fst_248_; lean_object* v_snd_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_258_; 
v_fst_248_ = lean_ctor_get(v_____x_247_, 0);
v_snd_249_ = lean_ctor_get(v_____x_247_, 1);
v_isSharedCheck_258_ = !lean_is_exclusive(v_____x_247_);
if (v_isSharedCheck_258_ == 0)
{
v___x_251_ = v_____x_247_;
v_isShared_252_ = v_isSharedCheck_258_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_snd_249_);
lean_inc(v_fst_248_);
lean_dec(v_____x_247_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_258_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_253_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_fst_248_, v_k_245_);
lean_dec(v_fst_248_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v___x_253_);
v___x_255_ = v___x_251_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_snd_249_);
v___x_255_ = v_reuseFailAlloc_257_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; 
v___x_256_ = lean_apply_2(v_toPure_246_, lean_box(0), v___x_255_);
return v___x_256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0___boxed(lean_object* v_k_259_, lean_object* v_toPure_260_, lean_object* v_____x_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0(v_k_259_, v_toPure_260_, v_____x_261_);
lean_dec(v_k_259_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__1(lean_object* v_inst_263_, lean_object* v_k_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_toApplicative_266_; lean_object* v_toBind_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_278_; 
v_toApplicative_266_ = lean_ctor_get(v_inst_263_, 0);
v_toBind_267_ = lean_ctor_get(v_inst_263_, 1);
v_isSharedCheck_278_ = !lean_is_exclusive(v_inst_263_);
if (v_isSharedCheck_278_ == 0)
{
v___x_269_ = v_inst_263_;
v_isShared_270_ = v_isSharedCheck_278_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_toBind_267_);
lean_inc(v_toApplicative_266_);
lean_dec(v_inst_263_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_278_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v_toPure_271_; lean_object* v___f_272_; lean_object* v___x_274_; 
v_toPure_271_ = lean_ctor_get(v_toApplicative_266_, 1);
lean_inc(v_toPure_271_);
lean_dec_ref(v_toApplicative_266_);
lean_inc(v_toPure_271_);
v___f_272_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_272_, 0, v_k_264_);
lean_closure_set(v___f_272_, 1, v_toPure_271_);
lean_inc(v___y_265_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v___y_265_);
lean_ctor_set(v___x_269_, 0, v___y_265_);
v___x_274_ = v___x_269_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___y_265_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___y_265_);
v___x_274_ = v_reuseFailAlloc_277_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_apply_2(v_toPure_271_, lean_box(0), v___x_274_);
v___x_276_ = lean_apply_4(v_toBind_267_, lean_box(0), lean_box(0), v___x_275_, v___f_272_);
return v___x_276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__2(lean_object* v_inst_279_, lean_object* v_k_280_, lean_object* v_a_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_toApplicative_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_294_; 
v_toApplicative_283_ = lean_ctor_get(v_inst_279_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v_inst_279_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v_inst_279_, 1);
lean_dec(v_unused_295_);
v___x_285_ = v_inst_279_;
v_isShared_286_ = v_isSharedCheck_294_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_toApplicative_283_);
lean_dec(v_inst_279_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_294_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_toPure_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v_toPure_287_ = lean_ctor_get(v_toApplicative_283_, 1);
lean_inc(v_toPure_287_);
lean_dec_ref(v_toApplicative_283_);
v___x_288_ = lean_box(0);
v___x_289_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_280_, v_a_281_, v___y_282_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v___x_289_);
lean_ctor_set(v___x_285_, 0, v___x_288_);
v___x_291_ = v___x_285_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v___x_289_);
v___x_291_ = v_reuseFailAlloc_293_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; 
v___x_292_ = lean_apply_2(v_toPure_287_, lean_box(0), v___x_291_);
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg(lean_object* v_inst_296_){
_start:
{
lean_object* v___f_297_; lean_object* v___f_298_; lean_object* v___x_299_; 
lean_inc_ref(v_inst_296_);
v___f_297_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_297_, 0, v_inst_296_);
v___f_298_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__2), 4, 1);
lean_closure_set(v___f_298_, 0, v_inst_296_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v___f_297_);
lean_ctor_set(v___x_299_, 1, v___f_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad(lean_object* v_m_300_, lean_object* v_00_u03b1_301_, lean_object* v_inst_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg(v_inst_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0(lean_object* v_toApplicative_304_, lean_object* v_k_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_toPure_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_toPure_307_ = lean_ctor_get(v_toApplicative_304_, 1);
lean_inc(v_toPure_307_);
lean_dec_ref(v_toApplicative_304_);
v___x_308_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_306_, v_k_305_);
v___x_309_ = lean_apply_2(v_toPure_307_, lean_box(0), v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0___boxed(lean_object* v_toApplicative_310_, lean_object* v_k_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0(v_toApplicative_310_, v_k_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec(v_k_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__1(lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_k_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_toApplicative_318_; lean_object* v_toBind_319_; lean_object* v___f_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_toApplicative_318_ = lean_ctor_get(v_inst_314_, 0);
lean_inc_ref(v_toApplicative_318_);
v_toBind_319_ = lean_ctor_get(v_inst_314_, 1);
lean_inc(v_toBind_319_);
lean_dec_ref(v_inst_314_);
v___f_320_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_320_, 0, v_toApplicative_318_);
lean_closure_set(v___f_320_, 1, v_k_316_);
lean_inc(v___y_317_);
v___x_321_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_321_, 0, lean_box(0));
lean_closure_set(v___x_321_, 1, lean_box(0));
lean_closure_set(v___x_321_, 2, v___y_317_);
v___x_322_ = lean_apply_2(v_inst_315_, lean_box(0), v___x_321_);
v___x_323_ = lean_apply_4(v_toBind_319_, lean_box(0), lean_box(0), v___x_322_, v___f_320_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__1___boxed(lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_k_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__1(v_inst_324_, v_inst_325_, v_k_326_, v___y_327_);
lean_dec(v___y_327_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__2(lean_object* v_k_329_, lean_object* v_a_330_, lean_object* v_s_331_){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = lean_box(0);
v___x_333_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_329_, v_a_330_, v_s_331_);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3(lean_object* v_inst_335_, lean_object* v_k_336_, lean_object* v_a_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___f_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___f_339_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_339_, 0, v_k_336_);
lean_closure_set(v___f_339_, 1, v_a_337_);
lean_inc(v___y_338_);
v___x_340_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_340_, 0, lean_box(0));
lean_closure_set(v___x_340_, 1, lean_box(0));
lean_closure_set(v___x_340_, 2, lean_box(0));
lean_closure_set(v___x_340_, 3, v___y_338_);
lean_closure_set(v___x_340_, 4, v___f_339_);
v___x_341_ = lean_apply_2(v_inst_335_, lean_box(0), v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3___boxed(lean_object* v_inst_342_, lean_object* v_k_343_, lean_object* v_a_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3(v_inst_342_, v_k_343_, v_a_344_, v___y_345_);
lean_dec(v___y_345_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg(lean_object* v_inst_347_, lean_object* v_inst_348_){
_start:
{
lean_object* v___f_349_; lean_object* v___f_350_; lean_object* v___x_351_; 
lean_inc(v_inst_347_);
v___f_349_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_349_, 0, v_inst_348_);
lean_closure_set(v___f_349_, 1, v_inst_347_);
v___f_350_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3___boxed), 4, 1);
lean_closure_set(v___f_350_, 0, v_inst_347_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v___f_349_);
lean_ctor_set(v___x_351_, 1, v___f_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad(lean_object* v_00_u03c9_352_, lean_object* v_m_353_, lean_object* v_00_u03b1_354_, lean_object* v_inst_355_, lean_object* v_inst_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg(v_inst_355_, v_inst_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg___lam__0(lean_object* v_store_358_, lean_object* v_k_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_apply_2(v_store_358_, v_k_359_, v_a_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg(lean_object* v_k_362_, lean_object* v_inst_363_){
_start:
{
lean_object* v_fetch_x3f_364_; lean_object* v_store_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_374_; 
v_fetch_x3f_364_ = lean_ctor_get(v_inst_363_, 0);
v_store_365_ = lean_ctor_get(v_inst_363_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v_inst_363_);
if (v_isSharedCheck_374_ == 0)
{
v___x_367_ = v_inst_363_;
v_isShared_368_ = v_isSharedCheck_374_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_store_365_);
lean_inc(v_fetch_x3f_364_);
lean_dec(v_inst_363_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_374_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___f_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
lean_inc(v_k_362_);
v___f_369_ = lean_alloc_closure((void*)(l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg___lam__0), 3, 2);
lean_closure_set(v___f_369_, 0, v_store_365_);
lean_closure_set(v___f_369_, 1, v_k_362_);
v___x_370_ = lean_apply_1(v_fetch_x3f_364_, v_k_362_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 1, v___f_369_);
lean_ctor_set(v___x_367_, 0, v___x_370_);
v___x_372_ = v___x_367_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___f_369_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut(lean_object* v_00_u03ba_375_, lean_object* v_00_u03b2_376_, lean_object* v_m_377_, lean_object* v_k_378_, lean_object* v_00_u03b1_379_, lean_object* v_inst_380_, lean_object* v_t_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg(v_k_378_, v_inst_380_);
return v___x_382_;
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
