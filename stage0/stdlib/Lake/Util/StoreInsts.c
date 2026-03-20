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
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_78_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_78_, 0, lean_box(0));
lean_closure_set(v___x_78_, 1, lean_box(0));
lean_closure_set(v___x_78_, 2, v___y_74_);
v___x_79_ = lean_apply_2(v_inst_72_, lean_box(0), v___x_78_);
v___x_80_ = lean_apply_4(v_toBind_76_, lean_box(0), lean_box(0), v___x_79_, v___f_77_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__2(lean_object* v_cmp_81_, lean_object* v_k_82_, lean_object* v_a_83_, lean_object* v_s_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lean_box(0);
v___x_86_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_81_, v_k_82_, v_a_83_, v_s_84_);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3(lean_object* v_cmp_88_, lean_object* v_inst_89_, lean_object* v_k_90_, lean_object* v_a_91_, lean_object* v___y_92_){
_start:
{
lean_object* v___f_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___f_93_ = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__2), 4, 3);
lean_closure_set(v___f_93_, 0, v_cmp_88_);
lean_closure_set(v___f_93_, 1, v_k_90_);
lean_closure_set(v___f_93_, 2, v_a_91_);
v___x_94_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_94_, 0, lean_box(0));
lean_closure_set(v___x_94_, 1, lean_box(0));
lean_closure_set(v___x_94_, 2, lean_box(0));
lean_closure_set(v___x_94_, 3, v___y_92_);
lean_closure_set(v___x_94_, 4, v___f_93_);
v___x_95_ = lean_apply_2(v_inst_89_, lean_box(0), v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg(lean_object* v_cmp_96_, lean_object* v_inst_97_, lean_object* v_inst_98_){
_start:
{
lean_object* v___f_99_; lean_object* v___f_100_; lean_object* v___x_101_; 
lean_inc(v_inst_97_);
lean_inc_ref(v_cmp_96_);
v___f_99_ = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__1), 5, 3);
lean_closure_set(v___f_99_, 0, v_inst_98_);
lean_closure_set(v___f_99_, 1, v_cmp_96_);
lean_closure_set(v___f_99_, 2, v_inst_97_);
v___f_100_ = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3), 5, 2);
lean_closure_set(v___f_100_, 0, v_cmp_96_);
lean_closure_set(v___f_100_, 1, v_inst_97_);
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v___f_99_);
lean_ctor_set(v___x_101_, 1, v___f_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp(lean_object* v_00_u03ba_102_, lean_object* v_00_u03c9_103_, lean_object* v_m_104_, lean_object* v_00_u03b2_105_, lean_object* v_cmp_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_inst_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg(v_cmp_106_, v_inst_107_, v_inst_108_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__0(lean_object* v_cmp_111_, lean_object* v_k_112_, lean_object* v_toPure_113_, lean_object* v_____x_114_){
_start:
{
lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_126_; 
v_fst_115_ = lean_ctor_get(v_____x_114_, 0);
v_snd_116_ = lean_ctor_get(v_____x_114_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v_____x_114_);
if (v_isSharedCheck_126_ == 0)
{
v___x_118_ = v_____x_114_;
v_isShared_119_ = v_isSharedCheck_126_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_snd_116_);
lean_inc(v_fst_115_);
lean_dec(v_____x_114_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_126_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v_toTreeMap_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
v_toTreeMap_120_ = lean_ctor_get(v_fst_115_, 0);
lean_inc(v_toTreeMap_120_);
lean_dec(v_fst_115_);
v___x_121_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_111_, v_toTreeMap_120_, v_k_112_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_121_);
v___x_123_ = v___x_118_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_snd_116_);
v___x_123_ = v_reuseFailAlloc_125_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_124_; 
v___x_124_ = lean_apply_2(v_toPure_113_, lean_box(0), v___x_123_);
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__1(lean_object* v_inst_127_, lean_object* v_cmp_128_, lean_object* v_k_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_toApplicative_131_; lean_object* v_toBind_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_143_; 
v_toApplicative_131_ = lean_ctor_get(v_inst_127_, 0);
v_toBind_132_ = lean_ctor_get(v_inst_127_, 1);
v_isSharedCheck_143_ = !lean_is_exclusive(v_inst_127_);
if (v_isSharedCheck_143_ == 0)
{
v___x_134_ = v_inst_127_;
v_isShared_135_ = v_isSharedCheck_143_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_toBind_132_);
lean_inc(v_toApplicative_131_);
lean_dec(v_inst_127_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_143_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v_toPure_136_; lean_object* v___f_137_; lean_object* v___x_139_; 
v_toPure_136_ = lean_ctor_get(v_toApplicative_131_, 1);
lean_inc(v_toPure_136_);
lean_dec_ref(v_toApplicative_131_);
lean_inc(v_toPure_136_);
v___f_137_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_137_, 0, v_cmp_128_);
lean_closure_set(v___f_137_, 1, v_k_129_);
lean_closure_set(v___f_137_, 2, v_toPure_136_);
lean_inc_ref(v___y_130_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v___y_130_);
lean_ctor_set(v___x_134_, 0, v___y_130_);
v___x_139_ = v___x_134_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___y_130_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___y_130_);
v___x_139_ = v_reuseFailAlloc_142_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_apply_2(v_toPure_136_, lean_box(0), v___x_139_);
v___x_141_ = lean_apply_4(v_toBind_132_, lean_box(0), lean_box(0), v___x_140_, v___f_137_);
return v___x_141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__2(lean_object* v_inst_144_, lean_object* v_cmp_145_, lean_object* v_k_146_, lean_object* v_a_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_toApplicative_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_160_; 
v_toApplicative_149_ = lean_ctor_get(v_inst_144_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v_inst_144_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v_inst_144_, 1);
lean_dec(v_unused_161_);
v___x_151_ = v_inst_144_;
v_isShared_152_ = v_isSharedCheck_160_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_toApplicative_149_);
lean_dec(v_inst_144_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_160_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v_toPure_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
v_toPure_153_ = lean_ctor_get(v_toApplicative_149_, 1);
lean_inc(v_toPure_153_);
lean_dec_ref(v_toApplicative_149_);
v___x_154_ = lean_box(0);
v___x_155_ = l_Lake_RBArray_insert___redArg(v_cmp_145_, v___y_148_, v_k_146_, v_a_147_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 1, v___x_155_);
lean_ctor_set(v___x_151_, 0, v___x_154_);
v___x_157_ = v___x_151_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___x_155_);
v___x_157_ = v_reuseFailAlloc_159_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_158_; 
v___x_158_ = lean_apply_2(v_toPure_153_, lean_box(0), v___x_157_);
return v___x_158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg(lean_object* v_cmp_162_, lean_object* v_inst_163_){
_start:
{
lean_object* v___f_164_; lean_object* v___f_165_; lean_object* v___x_166_; 
lean_inc_ref(v_cmp_162_);
lean_inc_ref(v_inst_163_);
v___f_164_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__1), 4, 2);
lean_closure_set(v___f_164_, 0, v_inst_163_);
lean_closure_set(v___f_164_, 1, v_cmp_162_);
v___f_165_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__2), 5, 2);
lean_closure_set(v___f_165_, 0, v_inst_163_);
lean_closure_set(v___f_165_, 1, v_cmp_162_);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___f_164_);
lean_ctor_set(v___x_166_, 1, v___f_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad(lean_object* v_m_167_, lean_object* v_00_u03ba_168_, lean_object* v_00_u03b1_169_, lean_object* v_cmp_170_, lean_object* v_inst_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg(v_cmp_170_, v_inst_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__0(lean_object* v_toApplicative_173_, lean_object* v_cmp_174_, lean_object* v_k_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_toTreeMap_177_; lean_object* v_toPure_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_toTreeMap_177_ = lean_ctor_get(v_a_176_, 0);
lean_inc(v_toTreeMap_177_);
lean_dec_ref(v_a_176_);
v_toPure_178_ = lean_ctor_get(v_toApplicative_173_, 1);
lean_inc(v_toPure_178_);
lean_dec_ref(v_toApplicative_173_);
v___x_179_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_174_, v_toTreeMap_177_, v_k_175_);
v___x_180_ = lean_apply_2(v_toPure_178_, lean_box(0), v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1(lean_object* v_inst_181_, lean_object* v_cmp_182_, lean_object* v_inst_183_, lean_object* v_k_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_toApplicative_186_; lean_object* v_toBind_187_; lean_object* v___f_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_toApplicative_186_ = lean_ctor_get(v_inst_181_, 0);
lean_inc_ref(v_toApplicative_186_);
v_toBind_187_ = lean_ctor_get(v_inst_181_, 1);
lean_inc(v_toBind_187_);
lean_dec_ref(v_inst_181_);
v___f_188_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_188_, 0, v_toApplicative_186_);
lean_closure_set(v___f_188_, 1, v_cmp_182_);
lean_closure_set(v___f_188_, 2, v_k_184_);
v___x_189_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_189_, 0, lean_box(0));
lean_closure_set(v___x_189_, 1, lean_box(0));
lean_closure_set(v___x_189_, 2, v___y_185_);
v___x_190_ = lean_apply_2(v_inst_183_, lean_box(0), v___x_189_);
v___x_191_ = lean_apply_4(v_toBind_187_, lean_box(0), lean_box(0), v___x_190_, v___f_188_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__2(lean_object* v_cmp_192_, lean_object* v_k_193_, lean_object* v_a_194_, lean_object* v_s_195_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = lean_box(0);
v___x_197_ = l_Lake_RBArray_insert___redArg(v_cmp_192_, v_s_195_, v_k_193_, v_a_194_);
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3(lean_object* v_cmp_199_, lean_object* v_inst_200_, lean_object* v_k_201_, lean_object* v_a_202_, lean_object* v___y_203_){
_start:
{
lean_object* v___f_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___f_204_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__2), 4, 3);
lean_closure_set(v___f_204_, 0, v_cmp_199_);
lean_closure_set(v___f_204_, 1, v_k_201_);
lean_closure_set(v___f_204_, 2, v_a_202_);
v___x_205_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_205_, 0, lean_box(0));
lean_closure_set(v___x_205_, 1, lean_box(0));
lean_closure_set(v___x_205_, 2, lean_box(0));
lean_closure_set(v___x_205_, 3, v___y_203_);
lean_closure_set(v___x_205_, 4, v___f_204_);
v___x_206_ = lean_apply_2(v_inst_200_, lean_box(0), v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg(lean_object* v_cmp_207_, lean_object* v_inst_208_, lean_object* v_inst_209_){
_start:
{
lean_object* v___f_210_; lean_object* v___f_211_; lean_object* v___x_212_; 
lean_inc(v_inst_208_);
lean_inc_ref(v_cmp_207_);
v___f_210_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1), 5, 3);
lean_closure_set(v___f_210_, 0, v_inst_209_);
lean_closure_set(v___f_210_, 1, v_cmp_207_);
lean_closure_set(v___f_210_, 2, v_inst_208_);
v___f_211_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3), 5, 2);
lean_closure_set(v___f_211_, 0, v_cmp_207_);
lean_closure_set(v___f_211_, 1, v_inst_208_);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___f_210_);
lean_ctor_set(v___x_212_, 1, v___f_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad(lean_object* v_00_u03c9_213_, lean_object* v_m_214_, lean_object* v_00_u03ba_215_, lean_object* v_00_u03b1_216_, lean_object* v_cmp_217_, lean_object* v_inst_218_, lean_object* v_inst_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg(v_cmp_217_, v_inst_218_, v_inst_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0(lean_object* v_k_221_, lean_object* v_toPure_222_, lean_object* v_____x_223_){
_start:
{
lean_object* v_fst_224_; lean_object* v_snd_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_234_; 
v_fst_224_ = lean_ctor_get(v_____x_223_, 0);
v_snd_225_ = lean_ctor_get(v_____x_223_, 1);
v_isSharedCheck_234_ = !lean_is_exclusive(v_____x_223_);
if (v_isSharedCheck_234_ == 0)
{
v___x_227_ = v_____x_223_;
v_isShared_228_ = v_isSharedCheck_234_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_snd_225_);
lean_inc(v_fst_224_);
lean_dec(v_____x_223_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_234_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_fst_224_, v_k_221_);
lean_dec(v_fst_224_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_229_);
v___x_231_ = v___x_227_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_snd_225_);
v___x_231_ = v_reuseFailAlloc_233_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; 
v___x_232_ = lean_apply_2(v_toPure_222_, lean_box(0), v___x_231_);
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0___boxed(lean_object* v_k_235_, lean_object* v_toPure_236_, lean_object* v_____x_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0(v_k_235_, v_toPure_236_, v_____x_237_);
lean_dec(v_k_235_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__1(lean_object* v_inst_239_, lean_object* v_k_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_toApplicative_242_; lean_object* v_toBind_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_254_; 
v_toApplicative_242_ = lean_ctor_get(v_inst_239_, 0);
v_toBind_243_ = lean_ctor_get(v_inst_239_, 1);
v_isSharedCheck_254_ = !lean_is_exclusive(v_inst_239_);
if (v_isSharedCheck_254_ == 0)
{
v___x_245_ = v_inst_239_;
v_isShared_246_ = v_isSharedCheck_254_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_toBind_243_);
lean_inc(v_toApplicative_242_);
lean_dec(v_inst_239_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_254_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v_toPure_247_; lean_object* v___f_248_; lean_object* v___x_250_; 
v_toPure_247_ = lean_ctor_get(v_toApplicative_242_, 1);
lean_inc(v_toPure_247_);
lean_dec_ref(v_toApplicative_242_);
lean_inc(v_toPure_247_);
v___f_248_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_248_, 0, v_k_240_);
lean_closure_set(v___f_248_, 1, v_toPure_247_);
lean_inc(v___y_241_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 1, v___y_241_);
lean_ctor_set(v___x_245_, 0, v___y_241_);
v___x_250_ = v___x_245_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___y_241_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v___y_241_);
v___x_250_ = v_reuseFailAlloc_253_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_apply_2(v_toPure_247_, lean_box(0), v___x_250_);
v___x_252_ = lean_apply_4(v_toBind_243_, lean_box(0), lean_box(0), v___x_251_, v___f_248_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__2(lean_object* v_inst_255_, lean_object* v_k_256_, lean_object* v_a_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_toApplicative_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_270_; 
v_toApplicative_259_ = lean_ctor_get(v_inst_255_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v_inst_255_);
if (v_isSharedCheck_270_ == 0)
{
lean_object* v_unused_271_; 
v_unused_271_ = lean_ctor_get(v_inst_255_, 1);
lean_dec(v_unused_271_);
v___x_261_ = v_inst_255_;
v_isShared_262_ = v_isSharedCheck_270_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_toApplicative_259_);
lean_dec(v_inst_255_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_270_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v_toPure_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v_toPure_263_ = lean_ctor_get(v_toApplicative_259_, 1);
lean_inc(v_toPure_263_);
lean_dec_ref(v_toApplicative_259_);
v___x_264_ = lean_box(0);
v___x_265_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_256_, v_a_257_, v___y_258_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v___x_265_);
lean_ctor_set(v___x_261_, 0, v___x_264_);
v___x_267_ = v___x_261_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v___x_265_);
v___x_267_ = v_reuseFailAlloc_269_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; 
v___x_268_ = lean_apply_2(v_toPure_263_, lean_box(0), v___x_267_);
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg(lean_object* v_inst_272_){
_start:
{
lean_object* v___f_273_; lean_object* v___f_274_; lean_object* v___x_275_; 
lean_inc_ref(v_inst_272_);
v___f_273_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_273_, 0, v_inst_272_);
v___f_274_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__2), 4, 1);
lean_closure_set(v___f_274_, 0, v_inst_272_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___f_273_);
lean_ctor_set(v___x_275_, 1, v___f_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad(lean_object* v_m_276_, lean_object* v_00_u03b1_277_, lean_object* v_inst_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg(v_inst_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0(lean_object* v_toApplicative_280_, lean_object* v_k_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_toPure_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_toPure_283_ = lean_ctor_get(v_toApplicative_280_, 1);
lean_inc(v_toPure_283_);
lean_dec_ref(v_toApplicative_280_);
v___x_284_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_282_, v_k_281_);
v___x_285_ = lean_apply_2(v_toPure_283_, lean_box(0), v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0___boxed(lean_object* v_toApplicative_286_, lean_object* v_k_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0(v_toApplicative_286_, v_k_287_, v_a_288_);
lean_dec(v_a_288_);
lean_dec(v_k_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__1(lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_k_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_toApplicative_294_; lean_object* v_toBind_295_; lean_object* v___f_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_toApplicative_294_ = lean_ctor_get(v_inst_290_, 0);
lean_inc_ref(v_toApplicative_294_);
v_toBind_295_ = lean_ctor_get(v_inst_290_, 1);
lean_inc(v_toBind_295_);
lean_dec_ref(v_inst_290_);
v___f_296_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_296_, 0, v_toApplicative_294_);
lean_closure_set(v___f_296_, 1, v_k_292_);
v___x_297_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_297_, 0, lean_box(0));
lean_closure_set(v___x_297_, 1, lean_box(0));
lean_closure_set(v___x_297_, 2, v___y_293_);
v___x_298_ = lean_apply_2(v_inst_291_, lean_box(0), v___x_297_);
v___x_299_ = lean_apply_4(v_toBind_295_, lean_box(0), lean_box(0), v___x_298_, v___f_296_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__2(lean_object* v_k_300_, lean_object* v_a_301_, lean_object* v_s_302_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_box(0);
v___x_304_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_300_, v_a_301_, v_s_302_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3(lean_object* v_inst_306_, lean_object* v_k_307_, lean_object* v_a_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___f_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___f_310_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__2), 3, 2);
lean_closure_set(v___f_310_, 0, v_k_307_);
lean_closure_set(v___f_310_, 1, v_a_308_);
v___x_311_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_311_, 0, lean_box(0));
lean_closure_set(v___x_311_, 1, lean_box(0));
lean_closure_set(v___x_311_, 2, lean_box(0));
lean_closure_set(v___x_311_, 3, v___y_309_);
lean_closure_set(v___x_311_, 4, v___f_310_);
v___x_312_ = lean_apply_2(v_inst_306_, lean_box(0), v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg(lean_object* v_inst_313_, lean_object* v_inst_314_){
_start:
{
lean_object* v___f_315_; lean_object* v___f_316_; lean_object* v___x_317_; 
lean_inc(v_inst_313_);
v___f_315_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__1), 4, 2);
lean_closure_set(v___f_315_, 0, v_inst_314_);
lean_closure_set(v___f_315_, 1, v_inst_313_);
v___f_316_ = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3), 4, 1);
lean_closure_set(v___f_316_, 0, v_inst_313_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___f_315_);
lean_ctor_set(v___x_317_, 1, v___f_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad(lean_object* v_00_u03c9_318_, lean_object* v_m_319_, lean_object* v_00_u03b1_320_, lean_object* v_inst_321_, lean_object* v_inst_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg(v_inst_321_, v_inst_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg___lam__0(lean_object* v_store_324_, lean_object* v_k_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = lean_apply_2(v_store_324_, v_k_325_, v_a_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg(lean_object* v_k_328_, lean_object* v_inst_329_){
_start:
{
lean_object* v_fetch_x3f_330_; lean_object* v_store_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_340_; 
v_fetch_x3f_330_ = lean_ctor_get(v_inst_329_, 0);
v_store_331_ = lean_ctor_get(v_inst_329_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v_inst_329_);
if (v_isSharedCheck_340_ == 0)
{
v___x_333_ = v_inst_329_;
v_isShared_334_ = v_isSharedCheck_340_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_store_331_);
lean_inc(v_fetch_x3f_330_);
lean_dec(v_inst_329_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_340_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___f_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
lean_inc(v_k_328_);
v___f_335_ = lean_alloc_closure((void*)(l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg___lam__0), 3, 2);
lean_closure_set(v___f_335_, 0, v_store_331_);
lean_closure_set(v___f_335_, 1, v_k_328_);
v___x_336_ = lean_apply_1(v_fetch_x3f_330_, v_k_328_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v___f_335_);
lean_ctor_set(v___x_333_, 0, v___x_336_);
v___x_338_ = v___x_333_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v___f_335_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut(lean_object* v_00_u03ba_341_, lean_object* v_00_u03b2_342_, lean_object* v_m_343_, lean_object* v_k_344_, lean_object* v_00_u03b1_345_, lean_object* v_inst_346_, lean_object* v_t_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg(v_k_344_, v_inst_346_);
return v___x_348_;
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
