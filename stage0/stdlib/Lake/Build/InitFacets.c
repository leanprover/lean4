// Lean compiler output
// Module: Lake.Build.InitFacets
// Imports: public import Lake.Config.FacetConfig import Lake.Build.Module import Lake.Build.Package import Lake.Build.Library import Lake.Build.Executable import Lake.Build.ExternLib import Lake.Build.InputFile
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
extern lean_object* l_Lake_ExternLib_initFacetConfigs;
extern lean_object* l_Lake_LeanExe_initFacetConfigs;
extern lean_object* l_Lake_LeanLib_initFacetConfigs;
extern lean_object* l_Lake_Package_initFacetConfigs;
extern lean_object* l_Lake_Module_initFacetConfigs;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lake_InputFile_initFacetConfigs;
extern lean_object* l_Lake_InputDir_initFacetConfigs;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_initFacetConfigs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_initFacetConfigs___closed__0;
static lean_once_cell_t l_Lake_initFacetConfigs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_initFacetConfigs___closed__1;
static lean_once_cell_t l_Lake_initFacetConfigs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_initFacetConfigs___closed__2;
static lean_once_cell_t l_Lake_initFacetConfigs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_initFacetConfigs___closed__3;
static lean_once_cell_t l_Lake_initFacetConfigs___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_initFacetConfigs___closed__4;
static lean_once_cell_t l_Lake_initFacetConfigs___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_initFacetConfigs___closed__5;
static lean_once_cell_t l_Lake_initFacetConfigs___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_initFacetConfigs___closed__6;
LEAN_EXPORT lean_object* l_Lake_initFacetConfigs;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0___redArg(lean_object* v_k_1_, lean_object* v_v_2_, lean_object* v_t_3_){
_start:
{
if (lean_obj_tag(v_t_3_) == 0)
{
lean_object* v_size_4_; lean_object* v_k_5_; lean_object* v_v_6_; lean_object* v_l_7_; lean_object* v_r_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_288_; 
v_size_4_ = lean_ctor_get(v_t_3_, 0);
v_k_5_ = lean_ctor_get(v_t_3_, 1);
v_v_6_ = lean_ctor_get(v_t_3_, 2);
v_l_7_ = lean_ctor_get(v_t_3_, 3);
v_r_8_ = lean_ctor_get(v_t_3_, 4);
v_isSharedCheck_288_ = !lean_is_exclusive(v_t_3_);
if (v_isSharedCheck_288_ == 0)
{
v___x_10_ = v_t_3_;
v_isShared_11_ = v_isSharedCheck_288_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_r_8_);
lean_inc(v_l_7_);
lean_inc(v_v_6_);
lean_inc(v_k_5_);
lean_inc(v_size_4_);
lean_dec(v_t_3_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_288_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
uint8_t v___x_12_; 
v___x_12_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1_, v_k_5_);
switch(v___x_12_)
{
case 0:
{
lean_object* v_impl_13_; lean_object* v___x_14_; 
lean_dec(v_size_4_);
v_impl_13_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0___redArg(v_k_1_, v_v_2_, v_l_7_);
v___x_14_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_8_) == 0)
{
lean_object* v_size_15_; lean_object* v_size_16_; lean_object* v_k_17_; lean_object* v_v_18_; lean_object* v_l_19_; lean_object* v_r_20_; lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v_size_15_ = lean_ctor_get(v_r_8_, 0);
v_size_16_ = lean_ctor_get(v_impl_13_, 0);
lean_inc(v_size_16_);
v_k_17_ = lean_ctor_get(v_impl_13_, 1);
lean_inc(v_k_17_);
v_v_18_ = lean_ctor_get(v_impl_13_, 2);
lean_inc(v_v_18_);
v_l_19_ = lean_ctor_get(v_impl_13_, 3);
lean_inc(v_l_19_);
v_r_20_ = lean_ctor_get(v_impl_13_, 4);
lean_inc(v_r_20_);
v___x_21_ = lean_unsigned_to_nat(3u);
v___x_22_ = lean_nat_mul(v___x_21_, v_size_15_);
v___x_23_ = lean_nat_dec_lt(v___x_22_, v_size_16_);
lean_dec(v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_27_; 
lean_dec(v_r_20_);
lean_dec(v_l_19_);
lean_dec(v_v_18_);
lean_dec(v_k_17_);
v___x_24_ = lean_nat_add(v___x_14_, v_size_16_);
lean_dec(v_size_16_);
v___x_25_ = lean_nat_add(v___x_24_, v_size_15_);
lean_dec(v___x_24_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 3, v_impl_13_);
lean_ctor_set(v___x_10_, 0, v___x_25_);
v___x_27_ = v___x_10_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v___x_25_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_28_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_28_, 3, v_impl_13_);
lean_ctor_set(v_reuseFailAlloc_28_, 4, v_r_8_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
else
{
lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_94_; 
v_isSharedCheck_94_ = !lean_is_exclusive(v_impl_13_);
if (v_isSharedCheck_94_ == 0)
{
lean_object* v_unused_95_; lean_object* v_unused_96_; lean_object* v_unused_97_; lean_object* v_unused_98_; lean_object* v_unused_99_; 
v_unused_95_ = lean_ctor_get(v_impl_13_, 4);
lean_dec(v_unused_95_);
v_unused_96_ = lean_ctor_get(v_impl_13_, 3);
lean_dec(v_unused_96_);
v_unused_97_ = lean_ctor_get(v_impl_13_, 2);
lean_dec(v_unused_97_);
v_unused_98_ = lean_ctor_get(v_impl_13_, 1);
lean_dec(v_unused_98_);
v_unused_99_ = lean_ctor_get(v_impl_13_, 0);
lean_dec(v_unused_99_);
v___x_30_ = v_impl_13_;
v_isShared_31_ = v_isSharedCheck_94_;
goto v_resetjp_29_;
}
else
{
lean_dec(v_impl_13_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_94_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v_size_32_; lean_object* v_size_33_; lean_object* v_k_34_; lean_object* v_v_35_; lean_object* v_l_36_; lean_object* v_r_37_; lean_object* v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v_size_32_ = lean_ctor_get(v_l_19_, 0);
v_size_33_ = lean_ctor_get(v_r_20_, 0);
v_k_34_ = lean_ctor_get(v_r_20_, 1);
v_v_35_ = lean_ctor_get(v_r_20_, 2);
v_l_36_ = lean_ctor_get(v_r_20_, 3);
v_r_37_ = lean_ctor_get(v_r_20_, 4);
v___x_38_ = lean_unsigned_to_nat(2u);
v___x_39_ = lean_nat_mul(v___x_38_, v_size_32_);
v___x_40_ = lean_nat_dec_lt(v_size_33_, v___x_39_);
lean_dec(v___x_39_);
if (v___x_40_ == 0)
{
lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_69_; 
lean_inc(v_r_37_);
lean_inc(v_l_36_);
lean_inc(v_v_35_);
lean_inc(v_k_34_);
v_isSharedCheck_69_ = !lean_is_exclusive(v_r_20_);
if (v_isSharedCheck_69_ == 0)
{
lean_object* v_unused_70_; lean_object* v_unused_71_; lean_object* v_unused_72_; lean_object* v_unused_73_; lean_object* v_unused_74_; 
v_unused_70_ = lean_ctor_get(v_r_20_, 4);
lean_dec(v_unused_70_);
v_unused_71_ = lean_ctor_get(v_r_20_, 3);
lean_dec(v_unused_71_);
v_unused_72_ = lean_ctor_get(v_r_20_, 2);
lean_dec(v_unused_72_);
v_unused_73_ = lean_ctor_get(v_r_20_, 1);
lean_dec(v_unused_73_);
v_unused_74_ = lean_ctor_get(v_r_20_, 0);
lean_dec(v_unused_74_);
v___x_42_ = v_r_20_;
v_isShared_43_ = v_isSharedCheck_69_;
goto v_resetjp_41_;
}
else
{
lean_dec(v_r_20_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_69_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___y_47_; lean_object* v___y_48_; lean_object* v___y_49_; lean_object* v___x_57_; lean_object* v___y_59_; 
v___x_44_ = lean_nat_add(v___x_14_, v_size_16_);
lean_dec(v_size_16_);
v___x_45_ = lean_nat_add(v___x_44_, v_size_15_);
lean_dec(v___x_44_);
v___x_57_ = lean_nat_add(v___x_14_, v_size_32_);
if (lean_obj_tag(v_l_36_) == 0)
{
lean_object* v_size_67_; 
v_size_67_ = lean_ctor_get(v_l_36_, 0);
lean_inc(v_size_67_);
v___y_59_ = v_size_67_;
goto v___jp_58_;
}
else
{
lean_object* v___x_68_; 
v___x_68_ = lean_unsigned_to_nat(0u);
v___y_59_ = v___x_68_;
goto v___jp_58_;
}
v___jp_46_:
{
lean_object* v___x_50_; lean_object* v___x_52_; 
v___x_50_ = lean_nat_add(v___y_47_, v___y_49_);
lean_dec(v___y_49_);
lean_dec(v___y_47_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 4, v_r_8_);
lean_ctor_set(v___x_42_, 3, v_r_37_);
lean_ctor_set(v___x_42_, 2, v_v_6_);
lean_ctor_set(v___x_42_, 1, v_k_5_);
lean_ctor_set(v___x_42_, 0, v___x_50_);
v___x_52_ = v___x_42_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_50_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_56_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_56_, 3, v_r_37_);
lean_ctor_set(v_reuseFailAlloc_56_, 4, v_r_8_);
v___x_52_ = v_reuseFailAlloc_56_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
lean_object* v___x_54_; 
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 4, v___x_52_);
lean_ctor_set(v___x_30_, 3, v___y_48_);
lean_ctor_set(v___x_30_, 2, v_v_35_);
lean_ctor_set(v___x_30_, 1, v_k_34_);
lean_ctor_set(v___x_30_, 0, v___x_45_);
v___x_54_ = v___x_30_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_45_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v_k_34_);
lean_ctor_set(v_reuseFailAlloc_55_, 2, v_v_35_);
lean_ctor_set(v_reuseFailAlloc_55_, 3, v___y_48_);
lean_ctor_set(v_reuseFailAlloc_55_, 4, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
v___jp_58_:
{
lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_60_ = lean_nat_add(v___x_57_, v___y_59_);
lean_dec(v___y_59_);
lean_dec(v___x_57_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v_l_36_);
lean_ctor_set(v___x_10_, 3, v_l_19_);
lean_ctor_set(v___x_10_, 2, v_v_18_);
lean_ctor_set(v___x_10_, 1, v_k_17_);
lean_ctor_set(v___x_10_, 0, v___x_60_);
v___x_62_ = v___x_10_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v_k_17_);
lean_ctor_set(v_reuseFailAlloc_66_, 2, v_v_18_);
lean_ctor_set(v_reuseFailAlloc_66_, 3, v_l_19_);
lean_ctor_set(v_reuseFailAlloc_66_, 4, v_l_36_);
v___x_62_ = v_reuseFailAlloc_66_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
lean_object* v___x_63_; 
v___x_63_ = lean_nat_add(v___x_14_, v_size_15_);
if (lean_obj_tag(v_r_37_) == 0)
{
lean_object* v_size_64_; 
v_size_64_ = lean_ctor_get(v_r_37_, 0);
lean_inc(v_size_64_);
v___y_47_ = v___x_63_;
v___y_48_ = v___x_62_;
v___y_49_ = v_size_64_;
goto v___jp_46_;
}
else
{
lean_object* v___x_65_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___y_47_ = v___x_63_;
v___y_48_ = v___x_62_;
v___y_49_ = v___x_65_;
goto v___jp_46_;
}
}
}
}
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
lean_del_object(v___x_10_);
v___x_75_ = lean_nat_add(v___x_14_, v_size_16_);
lean_dec(v_size_16_);
v___x_76_ = lean_nat_add(v___x_75_, v_size_15_);
lean_dec(v___x_75_);
v___x_77_ = lean_nat_add(v___x_14_, v_size_15_);
v___x_78_ = lean_nat_add(v___x_77_, v_size_33_);
lean_dec(v___x_77_);
lean_inc_ref(v_r_8_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 4, v_r_8_);
lean_ctor_set(v___x_30_, 3, v_r_20_);
lean_ctor_set(v___x_30_, 2, v_v_6_);
lean_ctor_set(v___x_30_, 1, v_k_5_);
lean_ctor_set(v___x_30_, 0, v___x_78_);
v___x_80_ = v___x_30_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_78_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_93_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_93_, 3, v_r_20_);
lean_ctor_set(v_reuseFailAlloc_93_, 4, v_r_8_);
v___x_80_ = v_reuseFailAlloc_93_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_87_; 
v_isSharedCheck_87_ = !lean_is_exclusive(v_r_8_);
if (v_isSharedCheck_87_ == 0)
{
lean_object* v_unused_88_; lean_object* v_unused_89_; lean_object* v_unused_90_; lean_object* v_unused_91_; lean_object* v_unused_92_; 
v_unused_88_ = lean_ctor_get(v_r_8_, 4);
lean_dec(v_unused_88_);
v_unused_89_ = lean_ctor_get(v_r_8_, 3);
lean_dec(v_unused_89_);
v_unused_90_ = lean_ctor_get(v_r_8_, 2);
lean_dec(v_unused_90_);
v_unused_91_ = lean_ctor_get(v_r_8_, 1);
lean_dec(v_unused_91_);
v_unused_92_ = lean_ctor_get(v_r_8_, 0);
lean_dec(v_unused_92_);
v___x_82_ = v_r_8_;
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
else
{
lean_dec(v_r_8_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 4, v___x_80_);
lean_ctor_set(v___x_82_, 3, v_l_19_);
lean_ctor_set(v___x_82_, 2, v_v_18_);
lean_ctor_set(v___x_82_, 1, v_k_17_);
lean_ctor_set(v___x_82_, 0, v___x_76_);
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_76_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_k_17_);
lean_ctor_set(v_reuseFailAlloc_86_, 2, v_v_18_);
lean_ctor_set(v_reuseFailAlloc_86_, 3, v_l_19_);
lean_ctor_set(v_reuseFailAlloc_86_, 4, v___x_80_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_100_; 
v_l_100_ = lean_ctor_get(v_impl_13_, 3);
lean_inc(v_l_100_);
if (lean_obj_tag(v_l_100_) == 0)
{
lean_object* v_r_101_; lean_object* v_k_102_; lean_object* v_v_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_114_; 
v_r_101_ = lean_ctor_get(v_impl_13_, 4);
v_k_102_ = lean_ctor_get(v_impl_13_, 1);
v_v_103_ = lean_ctor_get(v_impl_13_, 2);
v_isSharedCheck_114_ = !lean_is_exclusive(v_impl_13_);
if (v_isSharedCheck_114_ == 0)
{
lean_object* v_unused_115_; lean_object* v_unused_116_; 
v_unused_115_ = lean_ctor_get(v_impl_13_, 3);
lean_dec(v_unused_115_);
v_unused_116_ = lean_ctor_get(v_impl_13_, 0);
lean_dec(v_unused_116_);
v___x_105_ = v_impl_13_;
v_isShared_106_ = v_isSharedCheck_114_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_r_101_);
lean_inc(v_v_103_);
lean_inc(v_k_102_);
lean_dec(v_impl_13_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_114_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_101_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 3, v_r_101_);
lean_ctor_set(v___x_105_, 2, v_v_6_);
lean_ctor_set(v___x_105_, 1, v_k_5_);
lean_ctor_set(v___x_105_, 0, v___x_14_);
v___x_109_ = v___x_105_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_14_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_113_, 3, v_r_101_);
lean_ctor_set(v_reuseFailAlloc_113_, 4, v_r_101_);
v___x_109_ = v_reuseFailAlloc_113_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_111_; 
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v___x_109_);
lean_ctor_set(v___x_10_, 3, v_l_100_);
lean_ctor_set(v___x_10_, 2, v_v_103_);
lean_ctor_set(v___x_10_, 1, v_k_102_);
lean_ctor_set(v___x_10_, 0, v___x_107_);
v___x_111_ = v___x_10_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_k_102_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v_v_103_);
lean_ctor_set(v_reuseFailAlloc_112_, 3, v_l_100_);
lean_ctor_set(v_reuseFailAlloc_112_, 4, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
else
{
lean_object* v_r_117_; 
v_r_117_ = lean_ctor_get(v_impl_13_, 4);
lean_inc(v_r_117_);
if (lean_obj_tag(v_r_117_) == 0)
{
lean_object* v_k_118_; lean_object* v_v_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_142_; 
v_k_118_ = lean_ctor_get(v_impl_13_, 1);
v_v_119_ = lean_ctor_get(v_impl_13_, 2);
v_isSharedCheck_142_ = !lean_is_exclusive(v_impl_13_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; lean_object* v_unused_144_; lean_object* v_unused_145_; 
v_unused_143_ = lean_ctor_get(v_impl_13_, 4);
lean_dec(v_unused_143_);
v_unused_144_ = lean_ctor_get(v_impl_13_, 3);
lean_dec(v_unused_144_);
v_unused_145_ = lean_ctor_get(v_impl_13_, 0);
lean_dec(v_unused_145_);
v___x_121_ = v_impl_13_;
v_isShared_122_ = v_isSharedCheck_142_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_v_119_);
lean_inc(v_k_118_);
lean_dec(v_impl_13_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_142_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v_k_123_; lean_object* v_v_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_138_; 
v_k_123_ = lean_ctor_get(v_r_117_, 1);
v_v_124_ = lean_ctor_get(v_r_117_, 2);
v_isSharedCheck_138_ = !lean_is_exclusive(v_r_117_);
if (v_isSharedCheck_138_ == 0)
{
lean_object* v_unused_139_; lean_object* v_unused_140_; lean_object* v_unused_141_; 
v_unused_139_ = lean_ctor_get(v_r_117_, 4);
lean_dec(v_unused_139_);
v_unused_140_ = lean_ctor_get(v_r_117_, 3);
lean_dec(v_unused_140_);
v_unused_141_ = lean_ctor_get(v_r_117_, 0);
lean_dec(v_unused_141_);
v___x_126_ = v_r_117_;
v_isShared_127_ = v_isSharedCheck_138_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_v_124_);
lean_inc(v_k_123_);
lean_dec(v_r_117_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_138_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_128_ = lean_unsigned_to_nat(3u);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 4, v_l_100_);
lean_ctor_set(v___x_126_, 3, v_l_100_);
lean_ctor_set(v___x_126_, 2, v_v_119_);
lean_ctor_set(v___x_126_, 1, v_k_118_);
lean_ctor_set(v___x_126_, 0, v___x_14_);
v___x_130_ = v___x_126_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_14_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_k_118_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v_v_119_);
lean_ctor_set(v_reuseFailAlloc_137_, 3, v_l_100_);
lean_ctor_set(v_reuseFailAlloc_137_, 4, v_l_100_);
v___x_130_ = v_reuseFailAlloc_137_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_132_; 
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 4, v_l_100_);
lean_ctor_set(v___x_121_, 2, v_v_6_);
lean_ctor_set(v___x_121_, 1, v_k_5_);
lean_ctor_set(v___x_121_, 0, v___x_14_);
v___x_132_ = v___x_121_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_14_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_136_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_136_, 3, v_l_100_);
lean_ctor_set(v_reuseFailAlloc_136_, 4, v_l_100_);
v___x_132_ = v_reuseFailAlloc_136_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_134_; 
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v___x_132_);
lean_ctor_set(v___x_10_, 3, v___x_130_);
lean_ctor_set(v___x_10_, 2, v_v_124_);
lean_ctor_set(v___x_10_, 1, v_k_123_);
lean_ctor_set(v___x_10_, 0, v___x_128_);
v___x_134_ = v___x_10_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_128_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_k_123_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v_v_124_);
lean_ctor_set(v_reuseFailAlloc_135_, 3, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_135_, 4, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
}
else
{
lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_146_ = lean_unsigned_to_nat(2u);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v_r_117_);
lean_ctor_set(v___x_10_, 3, v_impl_13_);
lean_ctor_set(v___x_10_, 0, v___x_146_);
v___x_148_ = v___x_10_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_149_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_149_, 3, v_impl_13_);
lean_ctor_set(v_reuseFailAlloc_149_, 4, v_r_117_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
case 1:
{
lean_object* v___x_151_; 
lean_dec(v_v_6_);
lean_dec(v_k_5_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 2, v_v_2_);
lean_ctor_set(v___x_10_, 1, v_k_1_);
v___x_151_ = v___x_10_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_size_4_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_k_1_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v_v_2_);
lean_ctor_set(v_reuseFailAlloc_152_, 3, v_l_7_);
lean_ctor_set(v_reuseFailAlloc_152_, 4, v_r_8_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
default: 
{
lean_object* v_impl_153_; lean_object* v___x_154_; 
lean_dec(v_size_4_);
v_impl_153_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0___redArg(v_k_1_, v_v_2_, v_r_8_);
v___x_154_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_7_) == 0)
{
lean_object* v_size_155_; lean_object* v_size_156_; lean_object* v_k_157_; lean_object* v_v_158_; lean_object* v_l_159_; lean_object* v_r_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_size_155_ = lean_ctor_get(v_l_7_, 0);
v_size_156_ = lean_ctor_get(v_impl_153_, 0);
lean_inc(v_size_156_);
v_k_157_ = lean_ctor_get(v_impl_153_, 1);
lean_inc(v_k_157_);
v_v_158_ = lean_ctor_get(v_impl_153_, 2);
lean_inc(v_v_158_);
v_l_159_ = lean_ctor_get(v_impl_153_, 3);
lean_inc(v_l_159_);
v_r_160_ = lean_ctor_get(v_impl_153_, 4);
lean_inc(v_r_160_);
v___x_161_ = lean_unsigned_to_nat(3u);
v___x_162_ = lean_nat_mul(v___x_161_, v_size_155_);
v___x_163_ = lean_nat_dec_lt(v___x_162_, v_size_156_);
lean_dec(v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
lean_dec(v_r_160_);
lean_dec(v_l_159_);
lean_dec(v_v_158_);
lean_dec(v_k_157_);
v___x_164_ = lean_nat_add(v___x_154_, v_size_155_);
v___x_165_ = lean_nat_add(v___x_164_, v_size_156_);
lean_dec(v_size_156_);
lean_dec(v___x_164_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v_impl_153_);
lean_ctor_set(v___x_10_, 0, v___x_165_);
v___x_167_ = v___x_10_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_168_, 3, v_l_7_);
lean_ctor_set(v_reuseFailAlloc_168_, 4, v_impl_153_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
else
{
lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_232_; 
v_isSharedCheck_232_ = !lean_is_exclusive(v_impl_153_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; lean_object* v_unused_234_; lean_object* v_unused_235_; lean_object* v_unused_236_; lean_object* v_unused_237_; 
v_unused_233_ = lean_ctor_get(v_impl_153_, 4);
lean_dec(v_unused_233_);
v_unused_234_ = lean_ctor_get(v_impl_153_, 3);
lean_dec(v_unused_234_);
v_unused_235_ = lean_ctor_get(v_impl_153_, 2);
lean_dec(v_unused_235_);
v_unused_236_ = lean_ctor_get(v_impl_153_, 1);
lean_dec(v_unused_236_);
v_unused_237_ = lean_ctor_get(v_impl_153_, 0);
lean_dec(v_unused_237_);
v___x_170_ = v_impl_153_;
v_isShared_171_ = v_isSharedCheck_232_;
goto v_resetjp_169_;
}
else
{
lean_dec(v_impl_153_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_232_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v_size_172_; lean_object* v_k_173_; lean_object* v_v_174_; lean_object* v_l_175_; lean_object* v_r_176_; lean_object* v_size_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_size_172_ = lean_ctor_get(v_l_159_, 0);
v_k_173_ = lean_ctor_get(v_l_159_, 1);
v_v_174_ = lean_ctor_get(v_l_159_, 2);
v_l_175_ = lean_ctor_get(v_l_159_, 3);
v_r_176_ = lean_ctor_get(v_l_159_, 4);
v_size_177_ = lean_ctor_get(v_r_160_, 0);
v___x_178_ = lean_unsigned_to_nat(2u);
v___x_179_ = lean_nat_mul(v___x_178_, v_size_177_);
v___x_180_ = lean_nat_dec_lt(v_size_172_, v___x_179_);
lean_dec(v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_208_; 
lean_inc(v_r_176_);
lean_inc(v_l_175_);
lean_inc(v_v_174_);
lean_inc(v_k_173_);
v_isSharedCheck_208_ = !lean_is_exclusive(v_l_159_);
if (v_isSharedCheck_208_ == 0)
{
lean_object* v_unused_209_; lean_object* v_unused_210_; lean_object* v_unused_211_; lean_object* v_unused_212_; lean_object* v_unused_213_; 
v_unused_209_ = lean_ctor_get(v_l_159_, 4);
lean_dec(v_unused_209_);
v_unused_210_ = lean_ctor_get(v_l_159_, 3);
lean_dec(v_unused_210_);
v_unused_211_ = lean_ctor_get(v_l_159_, 2);
lean_dec(v_unused_211_);
v_unused_212_ = lean_ctor_get(v_l_159_, 1);
lean_dec(v_unused_212_);
v_unused_213_ = lean_ctor_get(v_l_159_, 0);
lean_dec(v_unused_213_);
v___x_182_ = v_l_159_;
v_isShared_183_ = v_isSharedCheck_208_;
goto v_resetjp_181_;
}
else
{
lean_dec(v_l_159_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_208_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_198_; 
v___x_184_ = lean_nat_add(v___x_154_, v_size_155_);
v___x_185_ = lean_nat_add(v___x_184_, v_size_156_);
lean_dec(v_size_156_);
if (lean_obj_tag(v_l_175_) == 0)
{
lean_object* v_size_206_; 
v_size_206_ = lean_ctor_get(v_l_175_, 0);
lean_inc(v_size_206_);
v___y_198_ = v_size_206_;
goto v___jp_197_;
}
else
{
lean_object* v___x_207_; 
v___x_207_ = lean_unsigned_to_nat(0u);
v___y_198_ = v___x_207_;
goto v___jp_197_;
}
v___jp_186_:
{
lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_190_ = lean_nat_add(v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec(v___y_188_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 4, v_r_160_);
lean_ctor_set(v___x_182_, 3, v_r_176_);
lean_ctor_set(v___x_182_, 2, v_v_158_);
lean_ctor_set(v___x_182_, 1, v_k_157_);
lean_ctor_set(v___x_182_, 0, v___x_190_);
v___x_192_ = v___x_182_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_k_157_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_v_158_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v_r_176_);
lean_ctor_set(v_reuseFailAlloc_196_, 4, v_r_160_);
v___x_192_ = v_reuseFailAlloc_196_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_194_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 4, v___x_192_);
lean_ctor_set(v___x_170_, 3, v___y_187_);
lean_ctor_set(v___x_170_, 2, v_v_174_);
lean_ctor_set(v___x_170_, 1, v_k_173_);
lean_ctor_set(v___x_170_, 0, v___x_185_);
v___x_194_ = v___x_170_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_195_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_195_, 3, v___y_187_);
lean_ctor_set(v_reuseFailAlloc_195_, 4, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
v___jp_197_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_199_ = lean_nat_add(v___x_184_, v___y_198_);
lean_dec(v___y_198_);
lean_dec(v___x_184_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v_l_175_);
lean_ctor_set(v___x_10_, 0, v___x_199_);
v___x_201_ = v___x_10_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v_l_7_);
lean_ctor_set(v_reuseFailAlloc_205_, 4, v_l_175_);
v___x_201_ = v_reuseFailAlloc_205_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_202_; 
v___x_202_ = lean_nat_add(v___x_154_, v_size_177_);
if (lean_obj_tag(v_r_176_) == 0)
{
lean_object* v_size_203_; 
v_size_203_ = lean_ctor_get(v_r_176_, 0);
lean_inc(v_size_203_);
v___y_187_ = v___x_201_;
v___y_188_ = v___x_202_;
v___y_189_ = v_size_203_;
goto v___jp_186_;
}
else
{
lean_object* v___x_204_; 
v___x_204_ = lean_unsigned_to_nat(0u);
v___y_187_ = v___x_201_;
v___y_188_ = v___x_202_;
v___y_189_ = v___x_204_;
goto v___jp_186_;
}
}
}
}
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_218_; 
lean_del_object(v___x_10_);
v___x_214_ = lean_nat_add(v___x_154_, v_size_155_);
v___x_215_ = lean_nat_add(v___x_214_, v_size_156_);
lean_dec(v_size_156_);
v___x_216_ = lean_nat_add(v___x_214_, v_size_172_);
lean_dec(v___x_214_);
lean_inc_ref(v_l_7_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 4, v_l_159_);
lean_ctor_set(v___x_170_, 3, v_l_7_);
lean_ctor_set(v___x_170_, 2, v_v_6_);
lean_ctor_set(v___x_170_, 1, v_k_5_);
lean_ctor_set(v___x_170_, 0, v___x_216_);
v___x_218_ = v___x_170_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v_l_7_);
lean_ctor_set(v_reuseFailAlloc_231_, 4, v_l_159_);
v___x_218_ = v_reuseFailAlloc_231_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
v_isSharedCheck_225_ = !lean_is_exclusive(v_l_7_);
if (v_isSharedCheck_225_ == 0)
{
lean_object* v_unused_226_; lean_object* v_unused_227_; lean_object* v_unused_228_; lean_object* v_unused_229_; lean_object* v_unused_230_; 
v_unused_226_ = lean_ctor_get(v_l_7_, 4);
lean_dec(v_unused_226_);
v_unused_227_ = lean_ctor_get(v_l_7_, 3);
lean_dec(v_unused_227_);
v_unused_228_ = lean_ctor_get(v_l_7_, 2);
lean_dec(v_unused_228_);
v_unused_229_ = lean_ctor_get(v_l_7_, 1);
lean_dec(v_unused_229_);
v_unused_230_ = lean_ctor_get(v_l_7_, 0);
lean_dec(v_unused_230_);
v___x_220_ = v_l_7_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_dec(v_l_7_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 4, v_r_160_);
lean_ctor_set(v___x_220_, 3, v___x_218_);
lean_ctor_set(v___x_220_, 2, v_v_158_);
lean_ctor_set(v___x_220_, 1, v_k_157_);
lean_ctor_set(v___x_220_, 0, v___x_215_);
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_215_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_k_157_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v_v_158_);
lean_ctor_set(v_reuseFailAlloc_224_, 3, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_224_, 4, v_r_160_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_238_; 
v_l_238_ = lean_ctor_get(v_impl_153_, 3);
lean_inc(v_l_238_);
if (lean_obj_tag(v_l_238_) == 0)
{
lean_object* v_r_239_; lean_object* v_k_240_; lean_object* v_v_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_264_; 
v_r_239_ = lean_ctor_get(v_impl_153_, 4);
v_k_240_ = lean_ctor_get(v_impl_153_, 1);
v_v_241_ = lean_ctor_get(v_impl_153_, 2);
v_isSharedCheck_264_ = !lean_is_exclusive(v_impl_153_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; lean_object* v_unused_266_; 
v_unused_265_ = lean_ctor_get(v_impl_153_, 3);
lean_dec(v_unused_265_);
v_unused_266_ = lean_ctor_get(v_impl_153_, 0);
lean_dec(v_unused_266_);
v___x_243_ = v_impl_153_;
v_isShared_244_ = v_isSharedCheck_264_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_r_239_);
lean_inc(v_v_241_);
lean_inc(v_k_240_);
lean_dec(v_impl_153_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_264_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v_k_245_; lean_object* v_v_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_260_; 
v_k_245_ = lean_ctor_get(v_l_238_, 1);
v_v_246_ = lean_ctor_get(v_l_238_, 2);
v_isSharedCheck_260_ = !lean_is_exclusive(v_l_238_);
if (v_isSharedCheck_260_ == 0)
{
lean_object* v_unused_261_; lean_object* v_unused_262_; lean_object* v_unused_263_; 
v_unused_261_ = lean_ctor_get(v_l_238_, 4);
lean_dec(v_unused_261_);
v_unused_262_ = lean_ctor_get(v_l_238_, 3);
lean_dec(v_unused_262_);
v_unused_263_ = lean_ctor_get(v_l_238_, 0);
lean_dec(v_unused_263_);
v___x_248_ = v_l_238_;
v_isShared_249_ = v_isSharedCheck_260_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_v_246_);
lean_inc(v_k_245_);
lean_dec(v_l_238_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_260_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_250_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_239_, 2);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 4, v_r_239_);
lean_ctor_set(v___x_248_, 3, v_r_239_);
lean_ctor_set(v___x_248_, 2, v_v_6_);
lean_ctor_set(v___x_248_, 1, v_k_5_);
lean_ctor_set(v___x_248_, 0, v___x_154_);
v___x_252_ = v___x_248_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_259_, 3, v_r_239_);
lean_ctor_set(v_reuseFailAlloc_259_, 4, v_r_239_);
v___x_252_ = v_reuseFailAlloc_259_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_254_; 
lean_inc(v_r_239_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 3, v_r_239_);
lean_ctor_set(v___x_243_, 0, v___x_154_);
v___x_254_ = v___x_243_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_k_240_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_v_241_);
lean_ctor_set(v_reuseFailAlloc_258_, 3, v_r_239_);
lean_ctor_set(v_reuseFailAlloc_258_, 4, v_r_239_);
v___x_254_ = v_reuseFailAlloc_258_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_256_; 
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v___x_254_);
lean_ctor_set(v___x_10_, 3, v___x_252_);
lean_ctor_set(v___x_10_, 2, v_v_246_);
lean_ctor_set(v___x_10_, 1, v_k_245_);
lean_ctor_set(v___x_10_, 0, v___x_250_);
v___x_256_ = v___x_10_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_k_245_);
lean_ctor_set(v_reuseFailAlloc_257_, 2, v_v_246_);
lean_ctor_set(v_reuseFailAlloc_257_, 3, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_257_, 4, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
}
}
else
{
lean_object* v_r_267_; 
v_r_267_ = lean_ctor_get(v_impl_153_, 4);
lean_inc(v_r_267_);
if (lean_obj_tag(v_r_267_) == 0)
{
lean_object* v_k_268_; lean_object* v_v_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_280_; 
v_k_268_ = lean_ctor_get(v_impl_153_, 1);
v_v_269_ = lean_ctor_get(v_impl_153_, 2);
v_isSharedCheck_280_ = !lean_is_exclusive(v_impl_153_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; 
v_unused_281_ = lean_ctor_get(v_impl_153_, 4);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_impl_153_, 3);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v_impl_153_, 0);
lean_dec(v_unused_283_);
v___x_271_ = v_impl_153_;
v_isShared_272_ = v_isSharedCheck_280_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_v_269_);
lean_inc(v_k_268_);
lean_dec(v_impl_153_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_280_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = lean_unsigned_to_nat(3u);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 4, v_l_238_);
lean_ctor_set(v___x_271_, 2, v_v_6_);
lean_ctor_set(v___x_271_, 1, v_k_5_);
lean_ctor_set(v___x_271_, 0, v___x_154_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_l_238_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_l_238_);
v___x_275_ = v_reuseFailAlloc_279_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_277_; 
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v_r_267_);
lean_ctor_set(v___x_10_, 3, v___x_275_);
lean_ctor_set(v___x_10_, 2, v_v_269_);
lean_ctor_set(v___x_10_, 1, v_k_268_);
lean_ctor_set(v___x_10_, 0, v___x_273_);
v___x_277_ = v___x_10_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_k_268_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_v_269_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_r_267_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
else
{
lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_284_ = lean_unsigned_to_nat(2u);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 4, v_impl_153_);
lean_ctor_set(v___x_10_, 3, v_r_267_);
lean_ctor_set(v___x_10_, 0, v___x_284_);
v___x_286_ = v___x_10_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_287_, 3, v_r_267_);
lean_ctor_set(v_reuseFailAlloc_287_, 4, v_impl_153_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v_k_1_);
lean_ctor_set(v___x_290_, 2, v_v_2_);
lean_ctor_set(v___x_290_, 3, v_t_3_);
lean_ctor_set(v___x_290_, 4, v_t_3_);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__1_spec__1(lean_object* v_init_291_, lean_object* v_x_292_){
_start:
{
if (lean_obj_tag(v_x_292_) == 0)
{
lean_object* v_k_293_; lean_object* v_v_294_; lean_object* v_l_295_; lean_object* v_r_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_k_293_ = lean_ctor_get(v_x_292_, 1);
lean_inc(v_k_293_);
v_v_294_ = lean_ctor_get(v_x_292_, 2);
lean_inc(v_v_294_);
v_l_295_ = lean_ctor_get(v_x_292_, 3);
lean_inc(v_l_295_);
v_r_296_ = lean_ctor_get(v_x_292_, 4);
lean_inc(v_r_296_);
lean_dec_ref(v_x_292_);
v___x_297_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__1_spec__1(v_init_291_, v_l_295_);
v___x_298_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0___redArg(v_k_293_, v_v_294_, v___x_297_);
v_init_291_ = v___x_298_;
v_x_292_ = v_r_296_;
goto _start;
}
else
{
return v_init_291_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert___redArg(lean_object* v_group_300_, lean_object* v_map_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__1_spec__1(v_map_301_, v_group_300_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert(lean_object* v_k_303_, lean_object* v_group_304_, lean_object* v_map_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__1_spec__1(v_map_305_, v_group_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert___boxed(lean_object* v_k_307_, lean_object* v_group_308_, lean_object* v_map_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert(v_k_307_, v_group_308_, v_map_309_);
lean_dec(v_k_307_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0(lean_object* v_00_u03b2_311_, lean_object* v_k_312_, lean_object* v_v_313_, lean_object* v_t_314_, lean_object* v_hl_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0___redArg(v_k_312_, v_v_313_, v_t_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__1(lean_object* v_init_317_, lean_object* v_t_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__1_spec__1(v_init_317_, v_t_318_);
return v___x_319_;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = l_Lake_Module_initFacetConfigs;
v___x_321_ = lean_box(1);
v___x_322_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__1_spec__1(v___x_321_, v___x_320_);
return v___x_322_;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = l_Lake_Package_initFacetConfigs;
v___x_324_ = lean_obj_once(&l_Lake_initFacetConfigs___closed__0, &l_Lake_initFacetConfigs___closed__0_once, _init_l_Lake_initFacetConfigs___closed__0);
v___x_325_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__1_spec__1(v___x_324_, v___x_323_);
return v___x_325_;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = l_Lake_LeanLib_initFacetConfigs;
v___x_327_ = lean_obj_once(&l_Lake_initFacetConfigs___closed__1, &l_Lake_initFacetConfigs___closed__1_once, _init_l_Lake_initFacetConfigs___closed__1);
v___x_328_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__1_spec__1(v___x_327_, v___x_326_);
return v___x_328_;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = l_Lake_LeanExe_initFacetConfigs;
v___x_330_ = lean_obj_once(&l_Lake_initFacetConfigs___closed__2, &l_Lake_initFacetConfigs___closed__2_once, _init_l_Lake_initFacetConfigs___closed__2);
v___x_331_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__1_spec__1(v___x_330_, v___x_329_);
return v___x_331_;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = l_Lake_ExternLib_initFacetConfigs;
v___x_333_ = lean_obj_once(&l_Lake_initFacetConfigs___closed__3, &l_Lake_initFacetConfigs___closed__3_once, _init_l_Lake_initFacetConfigs___closed__3);
v___x_334_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__1_spec__1(v___x_333_, v___x_332_);
return v___x_334_;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = l_Lake_InputFile_initFacetConfigs;
v___x_336_ = lean_obj_once(&l_Lake_initFacetConfigs___closed__4, &l_Lake_initFacetConfigs___closed__4_once, _init_l_Lake_initFacetConfigs___closed__4);
v___x_337_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__1_spec__1(v___x_336_, v___x_335_);
return v___x_337_;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = l_Lake_InputDir_initFacetConfigs;
v___x_339_ = lean_obj_once(&l_Lake_initFacetConfigs___closed__5, &l_Lake_initFacetConfigs___closed__5_once, _init_l_Lake_initFacetConfigs___closed__5);
v___x_340_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__1_spec__1(v___x_339_, v___x_338_);
return v___x_340_;
}
}
static lean_object* _init_l_Lake_initFacetConfigs(void){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = lean_obj_once(&l_Lake_initFacetConfigs___closed__6, &l_Lake_initFacetConfigs___closed__6_once, _init_l_Lake_initFacetConfigs___closed__6);
return v___x_341_;
}
}
lean_object* runtime_initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Module(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Library(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Executable(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_ExternLib(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_InputFile(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_InitFacets(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Library(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Executable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_ExternLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_InputFile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_initFacetConfigs = _init_l_Lake_initFacetConfigs();
lean_mark_persistent(l_Lake_initFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_InitFacets(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* initialize_Lake_Build_Module(uint8_t builtin);
lean_object* initialize_Lake_Build_Package(uint8_t builtin);
lean_object* initialize_Lake_Build_Library(uint8_t builtin);
lean_object* initialize_Lake_Build_Executable(uint8_t builtin);
lean_object* initialize_Lake_Build_ExternLib(uint8_t builtin);
lean_object* initialize_Lake_Build_InputFile(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_InitFacets(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Library(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Executable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_ExternLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_InputFile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_InitFacets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_InitFacets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_InitFacets(builtin);
}
#ifdef __cplusplus
}
#endif
