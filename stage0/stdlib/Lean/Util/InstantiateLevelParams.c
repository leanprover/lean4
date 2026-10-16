// Lean compiler output
// Module: Lean.Util.InstantiateLevelParams
// Imports: public import Lean.Util.ReplaceExpr
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
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_substParams_go(lean_object*, lean_object*);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParams___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsNoCache(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsArray___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___lam__0(lean_object* v_s_1_, lean_object* v_u_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_1_, v_u_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn(lean_object* v_s_4_, lean_object* v_e_5_){
_start:
{
uint8_t v___x_6_; 
v___x_6_ = l_Lean_Expr_hasLevelParam(v_e_5_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; 
lean_dec_ref(v_s_4_);
v___x_7_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7_, 0, v_e_5_);
return v___x_7_;
}
else
{
switch(lean_obj_tag(v_e_5_))
{
case 4:
{
lean_object* v_declName_8_; lean_object* v_us_9_; lean_object* v___f_10_; lean_object* v___x_11_; lean_object* v___x_12_; uint8_t v___x_13_; 
v_declName_8_ = lean_ctor_get(v_e_5_, 0);
v_us_9_ = lean_ctor_get(v_e_5_, 1);
v___f_10_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___lam__0), 2, 1);
lean_closure_set(v___f_10_, 0, v_s_4_);
v___x_11_ = lean_box(0);
lean_inc(v_us_9_);
v___x_12_ = l_List_mapTR_loop___redArg(v___f_10_, v_us_9_, v___x_11_);
v___x_13_ = l_ptrEqList___redArg(v_us_9_, v___x_12_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; lean_object* v___x_15_; 
lean_inc(v_declName_8_);
lean_dec_ref_known(v_e_5_, 2);
v___x_14_ = l_Lean_Expr_const___override(v_declName_8_, v___x_12_);
v___x_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
else
{
lean_object* v___x_16_; 
lean_dec(v___x_12_);
v___x_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_16_, 0, v_e_5_);
return v___x_16_;
}
}
case 3:
{
lean_object* v_u_17_; lean_object* v___x_18_; size_t v___x_19_; size_t v___x_20_; uint8_t v___x_21_; 
v_u_17_ = lean_ctor_get(v_e_5_, 0);
lean_inc(v_u_17_);
v___x_18_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_4_, v_u_17_);
v___x_19_ = lean_ptr_addr(v_u_17_);
v___x_20_ = lean_ptr_addr(v___x_18_);
v___x_21_ = lean_usize_dec_eq(v___x_19_, v___x_20_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec_ref_known(v_e_5_, 1);
v___x_22_ = l_Lean_Expr_sort___override(v___x_18_);
v___x_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
return v___x_23_;
}
else
{
lean_object* v___x_24_; 
lean_dec(v___x_18_);
v___x_24_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_24_, 0, v_e_5_);
return v___x_24_;
}
}
default: 
{
lean_object* v___x_25_; 
lean_dec_ref(v_e_5_);
lean_dec_ref(v_s_4_);
v___x_25_ = lean_box(0);
return v___x_25_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore(lean_object* v_s_26_, lean_object* v_e_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn), 2, 1);
lean_closure_set(v___x_28_, 0, v_s_26_);
v___x_29_ = lean_replace_expr(v___x_28_, v_e_27_);
lean_dec_ref(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___boxed(lean_object* v_s_30_, lean_object* v_e_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Expr_instantiateLevelParamsCore(v_s_30_, v_e_31_);
lean_dec_ref(v_e_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst(lean_object* v_x_33_, lean_object* v_x_34_, lean_object* v_x_35_){
_start:
{
if (lean_obj_tag(v_x_33_) == 1)
{
if (lean_obj_tag(v_x_34_) == 1)
{
lean_object* v_head_36_; lean_object* v_tail_37_; lean_object* v_head_38_; lean_object* v_tail_39_; uint8_t v___x_40_; 
v_head_36_ = lean_ctor_get(v_x_33_, 0);
v_tail_37_ = lean_ctor_get(v_x_33_, 1);
v_head_38_ = lean_ctor_get(v_x_34_, 0);
v_tail_39_ = lean_ctor_get(v_x_34_, 1);
v___x_40_ = lean_name_eq(v_head_36_, v_x_35_);
if (v___x_40_ == 0)
{
v_x_33_ = v_tail_37_;
v_x_34_ = v_tail_39_;
goto _start;
}
else
{
lean_object* v___x_42_; 
lean_inc(v_head_38_);
v___x_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_42_, 0, v_head_38_);
return v___x_42_;
}
}
else
{
lean_object* v___x_43_; 
v___x_43_ = lean_box(0);
return v___x_43_;
}
}
else
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst___boxed(lean_object* v_x_45_, lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst(v_x_45_, v_x_46_, v_x_47_);
lean_dec(v_x_47_);
lean_dec(v_x_46_);
lean_dec(v_x_45_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0_spec__0_spec__1(lean_object* v_paramNames_49_, lean_object* v_lvls_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
if (lean_obj_tag(v_a_51_) == 0)
{
lean_object* v___x_53_; 
lean_dec(v_lvls_50_);
lean_dec(v_paramNames_49_);
v___x_53_ = l_List_reverse___redArg(v_a_52_);
return v___x_53_;
}
else
{
lean_object* v_head_54_; lean_object* v_tail_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_65_; 
v_head_54_ = lean_ctor_get(v_a_51_, 0);
v_tail_55_ = lean_ctor_get(v_a_51_, 1);
v_isSharedCheck_65_ = !lean_is_exclusive(v_a_51_);
if (v_isSharedCheck_65_ == 0)
{
v___x_57_ = v_a_51_;
v_isShared_58_ = v_isSharedCheck_65_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_tail_55_);
lean_inc(v_head_54_);
lean_dec(v_a_51_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_65_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_62_; 
lean_inc(v_lvls_50_);
lean_inc(v_paramNames_49_);
v___x_59_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst___boxed), 3, 2);
lean_closure_set(v___x_59_, 0, v_paramNames_49_);
lean_closure_set(v___x_59_, 1, v_lvls_50_);
v___x_60_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_59_, v_head_54_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 1, v_a_52_);
lean_ctor_set(v___x_57_, 0, v___x_60_);
v___x_62_ = v___x_57_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_a_52_);
v___x_62_ = v_reuseFailAlloc_64_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
v_a_51_ = v_tail_55_;
v_a_52_ = v___x_62_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0_spec__0(lean_object* v_paramNames_66_, lean_object* v_lvls_67_, lean_object* v_e_68_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = l_Lean_Expr_hasLevelParam(v_e_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; 
lean_dec(v_lvls_67_);
lean_dec(v_paramNames_66_);
v___x_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_70_, 0, v_e_68_);
return v___x_70_;
}
else
{
switch(lean_obj_tag(v_e_68_))
{
case 4:
{
lean_object* v_declName_71_; lean_object* v_us_72_; lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v_declName_71_ = lean_ctor_get(v_e_68_, 0);
v_us_72_ = lean_ctor_get(v_e_68_, 1);
v___x_73_ = lean_box(0);
lean_inc(v_us_72_);
v___x_74_ = l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0_spec__0_spec__1(v_paramNames_66_, v_lvls_67_, v_us_72_, v___x_73_);
v___x_75_ = l_ptrEqList___redArg(v_us_72_, v___x_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; 
lean_inc(v_declName_71_);
lean_dec_ref_known(v_e_68_, 2);
v___x_76_ = l_Lean_Expr_const___override(v_declName_71_, v___x_74_);
v___x_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
return v___x_77_;
}
else
{
lean_object* v___x_78_; 
lean_dec(v___x_74_);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v_e_68_);
return v___x_78_;
}
}
case 3:
{
lean_object* v_u_79_; lean_object* v___x_80_; lean_object* v___x_81_; size_t v___x_82_; size_t v___x_83_; uint8_t v___x_84_; 
v_u_79_ = lean_ctor_get(v_e_68_, 0);
v___x_80_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst___boxed), 3, 2);
lean_closure_set(v___x_80_, 0, v_paramNames_66_);
lean_closure_set(v___x_80_, 1, v_lvls_67_);
lean_inc(v_u_79_);
v___x_81_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_80_, v_u_79_);
v___x_82_ = lean_ptr_addr(v_u_79_);
v___x_83_ = lean_ptr_addr(v___x_81_);
v___x_84_ = lean_usize_dec_eq(v___x_82_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec_ref_known(v_e_68_, 1);
v___x_85_ = l_Lean_Expr_sort___override(v___x_81_);
v___x_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
return v___x_86_;
}
else
{
lean_object* v___x_87_; 
lean_dec(v___x_81_);
v___x_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_87_, 0, v_e_68_);
return v___x_87_;
}
}
default: 
{
lean_object* v___x_88_; 
lean_dec_ref(v_e_68_);
lean_dec(v_lvls_67_);
lean_dec(v_paramNames_66_);
v___x_88_ = lean_box(0);
return v___x_88_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0(lean_object* v_paramNames_89_, lean_object* v_lvls_90_, lean_object* v_e_91_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0_spec__0), 3, 2);
lean_closure_set(v___x_92_, 0, v_paramNames_89_);
lean_closure_set(v___x_92_, 1, v_lvls_90_);
v___x_93_ = lean_replace_expr(v___x_92_, v_e_91_);
lean_dec_ref(v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0___boxed(lean_object* v_paramNames_94_, lean_object* v_lvls_95_, lean_object* v_e_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0(v_paramNames_94_, v_lvls_95_, v_e_96_);
lean_dec_ref(v_e_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParams(lean_object* v_e_98_, lean_object* v_paramNames_99_, lean_object* v_lvls_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = l_List_isEmpty___redArg(v_paramNames_99_);
if (v___x_101_ == 0)
{
uint8_t v___x_102_; 
v___x_102_ = l_List_isEmpty___redArg(v_lvls_100_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0(v_paramNames_99_, v_lvls_100_, v_e_98_);
return v___x_103_;
}
else
{
lean_dec(v_lvls_100_);
lean_dec(v_paramNames_99_);
lean_inc_ref(v_e_98_);
return v_e_98_;
}
}
else
{
lean_dec(v_lvls_100_);
lean_dec(v_paramNames_99_);
lean_inc_ref(v_e_98_);
return v_e_98_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParams___boxed(lean_object* v_e_104_, lean_object* v_paramNames_105_, lean_object* v_lvls_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_Expr_instantiateLevelParams(v_e_104_, v_paramNames_105_, v_lvls_106_);
lean_dec_ref(v_e_104_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(lean_object* v_paramNames_108_, lean_object* v_lvls_109_, lean_object* v_e_110_){
_start:
{
lean_object* v___x_111_; 
lean_inc_ref(v_e_110_);
lean_inc(v_lvls_109_);
lean_inc(v_paramNames_108_);
v___x_111_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0_spec__0(v_paramNames_108_, v_lvls_109_, v_e_110_);
if (lean_obj_tag(v___x_111_) == 0)
{
switch(lean_obj_tag(v_e_110_))
{
case 7:
{
lean_object* v_binderName_112_; lean_object* v_binderType_113_; lean_object* v_body_114_; uint8_t v_binderInfo_115_; lean_object* v_d_116_; lean_object* v_b_117_; size_t v___x_118_; size_t v___x_119_; uint8_t v___x_120_; 
v_binderName_112_ = lean_ctor_get(v_e_110_, 0);
v_binderType_113_ = lean_ctor_get(v_e_110_, 1);
v_body_114_ = lean_ctor_get(v_e_110_, 2);
v_binderInfo_115_ = lean_ctor_get_uint8(v_e_110_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_113_);
lean_inc(v_lvls_109_);
lean_inc(v_paramNames_108_);
v_d_116_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_108_, v_lvls_109_, v_binderType_113_);
lean_inc_ref(v_body_114_);
v_b_117_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_108_, v_lvls_109_, v_body_114_);
v___x_118_ = lean_ptr_addr(v_binderType_113_);
v___x_119_ = lean_ptr_addr(v_d_116_);
v___x_120_ = lean_usize_dec_eq(v___x_118_, v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; 
lean_inc(v_binderName_112_);
lean_dec_ref_known(v_e_110_, 3);
v___x_121_ = l_Lean_Expr_forallE___override(v_binderName_112_, v_d_116_, v_b_117_, v_binderInfo_115_);
return v___x_121_;
}
else
{
size_t v___x_122_; size_t v___x_123_; uint8_t v___x_124_; 
v___x_122_ = lean_ptr_addr(v_body_114_);
v___x_123_ = lean_ptr_addr(v_b_117_);
v___x_124_ = lean_usize_dec_eq(v___x_122_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
lean_inc(v_binderName_112_);
lean_dec_ref_known(v_e_110_, 3);
v___x_125_ = l_Lean_Expr_forallE___override(v_binderName_112_, v_d_116_, v_b_117_, v_binderInfo_115_);
return v___x_125_;
}
else
{
uint8_t v___x_126_; 
v___x_126_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_115_, v_binderInfo_115_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
lean_inc(v_binderName_112_);
lean_dec_ref_known(v_e_110_, 3);
v___x_127_ = l_Lean_Expr_forallE___override(v_binderName_112_, v_d_116_, v_b_117_, v_binderInfo_115_);
return v___x_127_;
}
else
{
lean_dec_ref(v_b_117_);
lean_dec_ref(v_d_116_);
return v_e_110_;
}
}
}
}
case 6:
{
lean_object* v_binderName_128_; lean_object* v_binderType_129_; lean_object* v_body_130_; uint8_t v_binderInfo_131_; lean_object* v_d_132_; lean_object* v_b_133_; size_t v___x_134_; size_t v___x_135_; uint8_t v___x_136_; 
v_binderName_128_ = lean_ctor_get(v_e_110_, 0);
v_binderType_129_ = lean_ctor_get(v_e_110_, 1);
v_body_130_ = lean_ctor_get(v_e_110_, 2);
v_binderInfo_131_ = lean_ctor_get_uint8(v_e_110_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_129_);
lean_inc(v_lvls_109_);
lean_inc(v_paramNames_108_);
v_d_132_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_108_, v_lvls_109_, v_binderType_129_);
lean_inc_ref(v_body_130_);
v_b_133_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_108_, v_lvls_109_, v_body_130_);
v___x_134_ = lean_ptr_addr(v_binderType_129_);
v___x_135_ = lean_ptr_addr(v_d_132_);
v___x_136_ = lean_usize_dec_eq(v___x_134_, v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; 
lean_inc(v_binderName_128_);
lean_dec_ref_known(v_e_110_, 3);
v___x_137_ = l_Lean_Expr_lam___override(v_binderName_128_, v_d_132_, v_b_133_, v_binderInfo_131_);
return v___x_137_;
}
else
{
size_t v___x_138_; size_t v___x_139_; uint8_t v___x_140_; 
v___x_138_ = lean_ptr_addr(v_body_130_);
v___x_139_ = lean_ptr_addr(v_b_133_);
v___x_140_ = lean_usize_dec_eq(v___x_138_, v___x_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; 
lean_inc(v_binderName_128_);
lean_dec_ref_known(v_e_110_, 3);
v___x_141_ = l_Lean_Expr_lam___override(v_binderName_128_, v_d_132_, v_b_133_, v_binderInfo_131_);
return v___x_141_;
}
else
{
uint8_t v___x_142_; 
v___x_142_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_131_, v_binderInfo_131_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
lean_inc(v_binderName_128_);
lean_dec_ref_known(v_e_110_, 3);
v___x_143_ = l_Lean_Expr_lam___override(v_binderName_128_, v_d_132_, v_b_133_, v_binderInfo_131_);
return v___x_143_;
}
else
{
lean_dec_ref(v_b_133_);
lean_dec_ref(v_d_132_);
return v_e_110_;
}
}
}
}
case 10:
{
lean_object* v_data_144_; lean_object* v_expr_145_; lean_object* v_b_146_; size_t v___x_147_; size_t v___x_148_; uint8_t v___x_149_; 
v_data_144_ = lean_ctor_get(v_e_110_, 0);
v_expr_145_ = lean_ctor_get(v_e_110_, 1);
lean_inc_ref(v_expr_145_);
v_b_146_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_108_, v_lvls_109_, v_expr_145_);
v___x_147_ = lean_ptr_addr(v_expr_145_);
v___x_148_ = lean_ptr_addr(v_b_146_);
v___x_149_ = lean_usize_dec_eq(v___x_147_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; 
lean_inc(v_data_144_);
lean_dec_ref_known(v_e_110_, 2);
v___x_150_ = l_Lean_Expr_mdata___override(v_data_144_, v_b_146_);
return v___x_150_;
}
else
{
lean_dec_ref(v_b_146_);
return v_e_110_;
}
}
case 8:
{
lean_object* v_declName_151_; lean_object* v_type_152_; lean_object* v_value_153_; lean_object* v_body_154_; uint8_t v_nondep_155_; lean_object* v_t_156_; lean_object* v_v_157_; lean_object* v_b_158_; size_t v___x_159_; size_t v___x_160_; uint8_t v___x_161_; 
v_declName_151_ = lean_ctor_get(v_e_110_, 0);
v_type_152_ = lean_ctor_get(v_e_110_, 1);
v_value_153_ = lean_ctor_get(v_e_110_, 2);
v_body_154_ = lean_ctor_get(v_e_110_, 3);
v_nondep_155_ = lean_ctor_get_uint8(v_e_110_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_152_);
lean_inc_n(v_lvls_109_, 2);
lean_inc_n(v_paramNames_108_, 2);
v_t_156_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_108_, v_lvls_109_, v_type_152_);
lean_inc_ref(v_value_153_);
v_v_157_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_108_, v_lvls_109_, v_value_153_);
lean_inc_ref(v_body_154_);
v_b_158_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_108_, v_lvls_109_, v_body_154_);
v___x_159_ = lean_ptr_addr(v_type_152_);
v___x_160_ = lean_ptr_addr(v_t_156_);
v___x_161_ = lean_usize_dec_eq(v___x_159_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; 
lean_inc(v_declName_151_);
lean_dec_ref_known(v_e_110_, 4);
v___x_162_ = l_Lean_Expr_letE___override(v_declName_151_, v_t_156_, v_v_157_, v_b_158_, v_nondep_155_);
return v___x_162_;
}
else
{
size_t v___x_163_; size_t v___x_164_; uint8_t v___x_165_; 
v___x_163_ = lean_ptr_addr(v_value_153_);
v___x_164_ = lean_ptr_addr(v_v_157_);
v___x_165_ = lean_usize_dec_eq(v___x_163_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; 
lean_inc(v_declName_151_);
lean_dec_ref_known(v_e_110_, 4);
v___x_166_ = l_Lean_Expr_letE___override(v_declName_151_, v_t_156_, v_v_157_, v_b_158_, v_nondep_155_);
return v___x_166_;
}
else
{
size_t v___x_167_; size_t v___x_168_; uint8_t v___x_169_; 
v___x_167_ = lean_ptr_addr(v_body_154_);
v___x_168_ = lean_ptr_addr(v_b_158_);
v___x_169_ = lean_usize_dec_eq(v___x_167_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
lean_inc(v_declName_151_);
lean_dec_ref_known(v_e_110_, 4);
v___x_170_ = l_Lean_Expr_letE___override(v_declName_151_, v_t_156_, v_v_157_, v_b_158_, v_nondep_155_);
return v___x_170_;
}
else
{
lean_dec_ref(v_b_158_);
lean_dec_ref(v_v_157_);
lean_dec_ref(v_t_156_);
return v_e_110_;
}
}
}
}
case 5:
{
lean_object* v_fn_171_; lean_object* v_arg_172_; lean_object* v_f_173_; lean_object* v_a_174_; size_t v___x_175_; size_t v___x_176_; uint8_t v___x_177_; 
v_fn_171_ = lean_ctor_get(v_e_110_, 0);
v_arg_172_ = lean_ctor_get(v_e_110_, 1);
lean_inc_ref(v_fn_171_);
lean_inc(v_lvls_109_);
lean_inc(v_paramNames_108_);
v_f_173_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_108_, v_lvls_109_, v_fn_171_);
lean_inc_ref(v_arg_172_);
v_a_174_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_108_, v_lvls_109_, v_arg_172_);
v___x_175_ = lean_ptr_addr(v_fn_171_);
v___x_176_ = lean_ptr_addr(v_f_173_);
v___x_177_ = lean_usize_dec_eq(v___x_175_, v___x_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
lean_dec_ref_known(v_e_110_, 2);
v___x_178_ = l_Lean_Expr_app___override(v_f_173_, v_a_174_);
return v___x_178_;
}
else
{
size_t v___x_179_; size_t v___x_180_; uint8_t v___x_181_; 
v___x_179_ = lean_ptr_addr(v_arg_172_);
v___x_180_ = lean_ptr_addr(v_a_174_);
v___x_181_ = lean_usize_dec_eq(v___x_179_, v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
lean_dec_ref_known(v_e_110_, 2);
v___x_182_ = l_Lean_Expr_app___override(v_f_173_, v_a_174_);
return v___x_182_;
}
else
{
lean_dec_ref(v_a_174_);
lean_dec_ref(v_f_173_);
return v_e_110_;
}
}
}
case 11:
{
lean_object* v_typeName_183_; lean_object* v_idx_184_; lean_object* v_struct_185_; lean_object* v_b_186_; size_t v___x_187_; size_t v___x_188_; uint8_t v___x_189_; 
v_typeName_183_ = lean_ctor_get(v_e_110_, 0);
v_idx_184_ = lean_ctor_get(v_e_110_, 1);
v_struct_185_ = lean_ctor_get(v_e_110_, 2);
lean_inc_ref(v_struct_185_);
v_b_186_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_108_, v_lvls_109_, v_struct_185_);
v___x_187_ = lean_ptr_addr(v_struct_185_);
v___x_188_ = lean_ptr_addr(v_b_186_);
v___x_189_ = lean_usize_dec_eq(v___x_187_, v___x_188_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; 
lean_inc(v_idx_184_);
lean_inc(v_typeName_183_);
lean_dec_ref_known(v_e_110_, 3);
v___x_190_ = l_Lean_Expr_proj___override(v_typeName_183_, v_idx_184_, v_b_186_);
return v___x_190_;
}
else
{
lean_dec_ref(v_b_186_);
return v_e_110_;
}
}
default: 
{
lean_dec(v_lvls_109_);
lean_dec(v_paramNames_108_);
return v_e_110_;
}
}
}
else
{
lean_object* v_val_191_; 
lean_dec_ref(v_e_110_);
lean_dec(v_lvls_109_);
lean_dec(v_paramNames_108_);
v_val_191_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_val_191_);
lean_dec_ref_known(v___x_111_, 1);
return v_val_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsNoCache(lean_object* v_e_192_, lean_object* v_paramNames_193_, lean_object* v_lvls_194_){
_start:
{
uint8_t v___x_195_; 
v___x_195_ = l_List_isEmpty___redArg(v_paramNames_193_);
if (v___x_195_ == 0)
{
uint8_t v___x_196_; 
v___x_196_ = l_List_isEmpty___redArg(v_lvls_194_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_193_, v_lvls_194_, v_e_192_);
return v___x_197_;
}
else
{
lean_dec(v_lvls_194_);
lean_dec(v_paramNames_193_);
return v_e_192_;
}
}
else
{
lean_dec(v_lvls_194_);
lean_dec(v_paramNames_193_);
return v_e_192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(lean_object* v_ps_198_, lean_object* v_us_199_, lean_object* v_p_x27_200_, lean_object* v_i_201_){
_start:
{
lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_202_ = lean_array_get_size(v_ps_198_);
v___x_203_ = lean_nat_dec_lt(v_i_201_, v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; 
lean_dec(v_i_201_);
v___x_204_ = lean_box(0);
return v___x_204_;
}
else
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = lean_array_get_size(v_us_199_);
v___x_206_ = lean_nat_dec_lt(v_i_201_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; 
lean_dec(v_i_201_);
v___x_207_ = lean_box(0);
return v___x_207_;
}
else
{
lean_object* v_p_208_; uint8_t v___x_209_; 
v_p_208_ = lean_array_fget_borrowed(v_ps_198_, v_i_201_);
v___x_209_ = lean_name_eq(v_p_208_, v_p_x27_200_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = lean_nat_add(v_i_201_, v___x_210_);
lean_dec(v_i_201_);
v_i_201_ = v___x_211_;
goto _start;
}
else
{
lean_object* v_u_213_; lean_object* v___x_214_; 
v_u_213_ = lean_array_fget_borrowed(v_us_199_, v_i_201_);
lean_dec(v_i_201_);
lean_inc(v_u_213_);
v___x_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_214_, 0, v_u_213_);
return v___x_214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray___boxed(lean_object* v_ps_215_, lean_object* v_us_216_, lean_object* v_p_x27_217_, lean_object* v_i_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(v_ps_215_, v_us_216_, v_p_x27_217_, v_i_218_);
lean_dec(v_p_x27_217_);
lean_dec_ref(v_us_216_);
lean_dec_ref(v_ps_215_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0(lean_object* v_paramNames_220_, lean_object* v_lvls_221_, lean_object* v_p_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(v_paramNames_220_, v_lvls_221_, v_p_222_, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed(lean_object* v_paramNames_225_, lean_object* v_lvls_226_, lean_object* v_p_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0(v_paramNames_225_, v_lvls_226_, v_p_227_);
lean_dec(v_p_227_);
lean_dec_ref(v_lvls_226_);
lean_dec_ref(v_paramNames_225_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0_spec__1(lean_object* v_paramNames_229_, lean_object* v_lvls_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
if (lean_obj_tag(v_a_231_) == 0)
{
lean_object* v___x_233_; 
lean_dec_ref(v_lvls_230_);
lean_dec_ref(v_paramNames_229_);
v___x_233_ = l_List_reverse___redArg(v_a_232_);
return v___x_233_;
}
else
{
lean_object* v_head_234_; lean_object* v_tail_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_245_; 
v_head_234_ = lean_ctor_get(v_a_231_, 0);
v_tail_235_ = lean_ctor_get(v_a_231_, 1);
v_isSharedCheck_245_ = !lean_is_exclusive(v_a_231_);
if (v_isSharedCheck_245_ == 0)
{
v___x_237_ = v_a_231_;
v_isShared_238_ = v_isSharedCheck_245_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_tail_235_);
lean_inc(v_head_234_);
lean_dec(v_a_231_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_245_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___f_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
lean_inc_ref(v_lvls_230_);
lean_inc_ref(v_paramNames_229_);
v___f_239_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_239_, 0, v_paramNames_229_);
lean_closure_set(v___f_239_, 1, v_lvls_230_);
v___x_240_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___f_239_, v_head_234_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v_a_232_);
lean_ctor_set(v___x_237_, 0, v___x_240_);
v___x_242_ = v___x_237_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_a_232_);
v___x_242_ = v_reuseFailAlloc_244_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
v_a_231_ = v_tail_235_;
v_a_232_ = v___x_242_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0(lean_object* v_paramNames_246_, lean_object* v_lvls_247_, lean_object* v_e_248_){
_start:
{
uint8_t v___x_249_; 
v___x_249_ = l_Lean_Expr_hasLevelParam(v_e_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec_ref(v_lvls_247_);
lean_dec_ref(v_paramNames_246_);
v___x_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_250_, 0, v_e_248_);
return v___x_250_;
}
else
{
switch(lean_obj_tag(v_e_248_))
{
case 4:
{
lean_object* v_declName_251_; lean_object* v_us_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v_declName_251_ = lean_ctor_get(v_e_248_, 0);
v_us_252_ = lean_ctor_get(v_e_248_, 1);
v___x_253_ = lean_box(0);
lean_inc(v_us_252_);
v___x_254_ = l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0_spec__1(v_paramNames_246_, v_lvls_247_, v_us_252_, v___x_253_);
v___x_255_ = l_ptrEqList___redArg(v_us_252_, v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_inc(v_declName_251_);
lean_dec_ref_known(v_e_248_, 2);
v___x_256_ = l_Lean_Expr_const___override(v_declName_251_, v___x_254_);
v___x_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
else
{
lean_object* v___x_258_; 
lean_dec(v___x_254_);
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v_e_248_);
return v___x_258_;
}
}
case 3:
{
lean_object* v_u_259_; lean_object* v___f_260_; lean_object* v___x_261_; size_t v___x_262_; size_t v___x_263_; uint8_t v___x_264_; 
v_u_259_ = lean_ctor_get(v_e_248_, 0);
v___f_260_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_260_, 0, v_paramNames_246_);
lean_closure_set(v___f_260_, 1, v_lvls_247_);
lean_inc(v_u_259_);
v___x_261_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___f_260_, v_u_259_);
v___x_262_ = lean_ptr_addr(v_u_259_);
v___x_263_ = lean_ptr_addr(v___x_261_);
v___x_264_ = lean_usize_dec_eq(v___x_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec_ref_known(v_e_248_, 1);
v___x_265_ = l_Lean_Expr_sort___override(v___x_261_);
v___x_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
else
{
lean_object* v___x_267_; 
lean_dec(v___x_261_);
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v_e_248_);
return v___x_267_;
}
}
default: 
{
lean_object* v___x_268_; 
lean_dec_ref(v_e_248_);
lean_dec_ref(v_lvls_247_);
lean_dec_ref(v_paramNames_246_);
v___x_268_ = lean_box(0);
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(lean_object* v_paramNames_269_, lean_object* v_lvls_270_, lean_object* v_e_271_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0), 3, 2);
lean_closure_set(v___x_272_, 0, v_paramNames_269_);
lean_closure_set(v___x_272_, 1, v_lvls_270_);
v___x_273_ = lean_replace_expr(v___x_272_, v_e_271_);
lean_dec_ref(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0___boxed(lean_object* v_paramNames_274_, lean_object* v_lvls_275_, lean_object* v_e_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(v_paramNames_274_, v_lvls_275_, v_e_276_);
lean_dec_ref(v_e_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object* v_e_278_, lean_object* v_paramNames_279_, lean_object* v_lvls_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_281_ = lean_array_get_size(v_paramNames_279_);
v___x_282_ = lean_unsigned_to_nat(0u);
v___x_283_ = lean_nat_dec_eq(v___x_281_, v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = lean_array_get_size(v_lvls_280_);
v___x_285_ = lean_nat_dec_eq(v___x_284_, v___x_282_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(v_paramNames_279_, v_lvls_280_, v_e_278_);
return v___x_286_;
}
else
{
lean_dec_ref(v_lvls_280_);
lean_dec_ref(v_paramNames_279_);
lean_inc_ref(v_e_278_);
return v_e_278_;
}
}
else
{
lean_dec_ref(v_lvls_280_);
lean_dec_ref(v_paramNames_279_);
lean_inc_ref(v_e_278_);
return v_e_278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsArray___boxed(lean_object* v_e_287_, lean_object* v_paramNames_288_, lean_object* v_lvls_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Expr_instantiateLevelParamsArray(v_e_287_, v_paramNames_288_, v_lvls_289_);
lean_dec_ref(v_e_287_);
return v_res_290_;
}
}
lean_object* runtime_initialize_Lean_Util_ReplaceExpr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_InstantiateLevelParams(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Util_ReplaceExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_InstantiateLevelParams(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_InstantiateLevelParams(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_ReplaceExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_InstantiateLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_InstantiateLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_InstantiateLevelParams(builtin);
}
#ifdef __cplusplus
}
#endif
