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
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
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
uint8_t v___y_102_; uint8_t v___x_104_; 
v___x_104_ = l_List_isEmpty___redArg(v_paramNames_99_);
if (v___x_104_ == 0)
{
uint8_t v___x_105_; 
v___x_105_ = l_List_isEmpty___redArg(v_lvls_100_);
v___y_102_ = v___x_105_;
goto v___jp_101_;
}
else
{
v___y_102_ = v___x_104_;
goto v___jp_101_;
}
v___jp_101_:
{
if (v___y_102_ == 0)
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParams___boxed(lean_object* v_e_106_, lean_object* v_paramNames_107_, lean_object* v_lvls_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_Expr_instantiateLevelParams(v_e_106_, v_paramNames_107_, v_lvls_108_);
lean_dec_ref(v_e_106_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(lean_object* v_paramNames_110_, lean_object* v_lvls_111_, lean_object* v_e_112_){
_start:
{
lean_object* v___x_113_; 
lean_inc_ref(v_e_112_);
lean_inc(v_lvls_111_);
lean_inc(v_paramNames_110_);
v___x_113_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0_spec__0(v_paramNames_110_, v_lvls_111_, v_e_112_);
if (lean_obj_tag(v___x_113_) == 0)
{
switch(lean_obj_tag(v_e_112_))
{
case 7:
{
lean_object* v_binderName_114_; lean_object* v_binderType_115_; lean_object* v_body_116_; uint8_t v_binderInfo_117_; lean_object* v_d_118_; lean_object* v_b_119_; size_t v___x_120_; size_t v___x_121_; uint8_t v___x_122_; 
v_binderName_114_ = lean_ctor_get(v_e_112_, 0);
v_binderType_115_ = lean_ctor_get(v_e_112_, 1);
v_body_116_ = lean_ctor_get(v_e_112_, 2);
v_binderInfo_117_ = lean_ctor_get_uint8(v_e_112_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_115_);
lean_inc(v_lvls_111_);
lean_inc(v_paramNames_110_);
v_d_118_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_binderType_115_);
lean_inc_ref(v_body_116_);
v_b_119_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_body_116_);
v___x_120_ = lean_ptr_addr(v_binderType_115_);
v___x_121_ = lean_ptr_addr(v_d_118_);
v___x_122_ = lean_usize_dec_eq(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
lean_inc(v_binderName_114_);
lean_dec_ref_known(v_e_112_, 3);
v___x_123_ = l_Lean_Expr_forallE___override(v_binderName_114_, v_d_118_, v_b_119_, v_binderInfo_117_);
return v___x_123_;
}
else
{
size_t v___x_124_; size_t v___x_125_; uint8_t v___x_126_; 
v___x_124_ = lean_ptr_addr(v_body_116_);
v___x_125_ = lean_ptr_addr(v_b_119_);
v___x_126_ = lean_usize_dec_eq(v___x_124_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
lean_inc(v_binderName_114_);
lean_dec_ref_known(v_e_112_, 3);
v___x_127_ = l_Lean_Expr_forallE___override(v_binderName_114_, v_d_118_, v_b_119_, v_binderInfo_117_);
return v___x_127_;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_117_, v_binderInfo_117_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
lean_inc(v_binderName_114_);
lean_dec_ref_known(v_e_112_, 3);
v___x_129_ = l_Lean_Expr_forallE___override(v_binderName_114_, v_d_118_, v_b_119_, v_binderInfo_117_);
return v___x_129_;
}
else
{
lean_dec_ref(v_b_119_);
lean_dec_ref(v_d_118_);
return v_e_112_;
}
}
}
}
case 6:
{
lean_object* v_binderName_130_; lean_object* v_binderType_131_; lean_object* v_body_132_; uint8_t v_binderInfo_133_; lean_object* v_d_134_; lean_object* v_b_135_; size_t v___x_136_; size_t v___x_137_; uint8_t v___x_138_; 
v_binderName_130_ = lean_ctor_get(v_e_112_, 0);
v_binderType_131_ = lean_ctor_get(v_e_112_, 1);
v_body_132_ = lean_ctor_get(v_e_112_, 2);
v_binderInfo_133_ = lean_ctor_get_uint8(v_e_112_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_131_);
lean_inc(v_lvls_111_);
lean_inc(v_paramNames_110_);
v_d_134_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_binderType_131_);
lean_inc_ref(v_body_132_);
v_b_135_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_body_132_);
v___x_136_ = lean_ptr_addr(v_binderType_131_);
v___x_137_ = lean_ptr_addr(v_d_134_);
v___x_138_ = lean_usize_dec_eq(v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; 
lean_inc(v_binderName_130_);
lean_dec_ref_known(v_e_112_, 3);
v___x_139_ = l_Lean_Expr_lam___override(v_binderName_130_, v_d_134_, v_b_135_, v_binderInfo_133_);
return v___x_139_;
}
else
{
size_t v___x_140_; size_t v___x_141_; uint8_t v___x_142_; 
v___x_140_ = lean_ptr_addr(v_body_132_);
v___x_141_ = lean_ptr_addr(v_b_135_);
v___x_142_ = lean_usize_dec_eq(v___x_140_, v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
lean_inc(v_binderName_130_);
lean_dec_ref_known(v_e_112_, 3);
v___x_143_ = l_Lean_Expr_lam___override(v_binderName_130_, v_d_134_, v_b_135_, v_binderInfo_133_);
return v___x_143_;
}
else
{
uint8_t v___x_144_; 
v___x_144_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_133_, v_binderInfo_133_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; 
lean_inc(v_binderName_130_);
lean_dec_ref_known(v_e_112_, 3);
v___x_145_ = l_Lean_Expr_lam___override(v_binderName_130_, v_d_134_, v_b_135_, v_binderInfo_133_);
return v___x_145_;
}
else
{
lean_dec_ref(v_b_135_);
lean_dec_ref(v_d_134_);
return v_e_112_;
}
}
}
}
case 10:
{
lean_object* v_data_146_; lean_object* v_expr_147_; lean_object* v_b_148_; size_t v___x_149_; size_t v___x_150_; uint8_t v___x_151_; 
v_data_146_ = lean_ctor_get(v_e_112_, 0);
v_expr_147_ = lean_ctor_get(v_e_112_, 1);
lean_inc_ref(v_expr_147_);
v_b_148_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_expr_147_);
v___x_149_ = lean_ptr_addr(v_expr_147_);
v___x_150_ = lean_ptr_addr(v_b_148_);
v___x_151_ = lean_usize_dec_eq(v___x_149_, v___x_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; 
lean_inc(v_data_146_);
lean_dec_ref_known(v_e_112_, 2);
v___x_152_ = l_Lean_Expr_mdata___override(v_data_146_, v_b_148_);
return v___x_152_;
}
else
{
lean_dec_ref(v_b_148_);
return v_e_112_;
}
}
case 8:
{
lean_object* v_declName_153_; lean_object* v_type_154_; lean_object* v_value_155_; lean_object* v_body_156_; uint8_t v_nondep_157_; lean_object* v_t_158_; lean_object* v_v_159_; lean_object* v_b_160_; size_t v___x_161_; size_t v___x_162_; uint8_t v___x_163_; 
v_declName_153_ = lean_ctor_get(v_e_112_, 0);
v_type_154_ = lean_ctor_get(v_e_112_, 1);
v_value_155_ = lean_ctor_get(v_e_112_, 2);
v_body_156_ = lean_ctor_get(v_e_112_, 3);
v_nondep_157_ = lean_ctor_get_uint8(v_e_112_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_154_);
lean_inc_n(v_lvls_111_, 2);
lean_inc_n(v_paramNames_110_, 2);
v_t_158_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_type_154_);
lean_inc_ref(v_value_155_);
v_v_159_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_value_155_);
lean_inc_ref(v_body_156_);
v_b_160_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_body_156_);
v___x_161_ = lean_ptr_addr(v_type_154_);
v___x_162_ = lean_ptr_addr(v_t_158_);
v___x_163_ = lean_usize_dec_eq(v___x_161_, v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
lean_inc(v_declName_153_);
lean_dec_ref_known(v_e_112_, 4);
v___x_164_ = l_Lean_Expr_letE___override(v_declName_153_, v_t_158_, v_v_159_, v_b_160_, v_nondep_157_);
return v___x_164_;
}
else
{
size_t v___x_165_; size_t v___x_166_; uint8_t v___x_167_; 
v___x_165_ = lean_ptr_addr(v_value_155_);
v___x_166_ = lean_ptr_addr(v_v_159_);
v___x_167_ = lean_usize_dec_eq(v___x_165_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; 
lean_inc(v_declName_153_);
lean_dec_ref_known(v_e_112_, 4);
v___x_168_ = l_Lean_Expr_letE___override(v_declName_153_, v_t_158_, v_v_159_, v_b_160_, v_nondep_157_);
return v___x_168_;
}
else
{
size_t v___x_169_; size_t v___x_170_; uint8_t v___x_171_; 
v___x_169_ = lean_ptr_addr(v_body_156_);
v___x_170_ = lean_ptr_addr(v_b_160_);
v___x_171_ = lean_usize_dec_eq(v___x_169_, v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; 
lean_inc(v_declName_153_);
lean_dec_ref_known(v_e_112_, 4);
v___x_172_ = l_Lean_Expr_letE___override(v_declName_153_, v_t_158_, v_v_159_, v_b_160_, v_nondep_157_);
return v___x_172_;
}
else
{
lean_dec_ref(v_b_160_);
lean_dec_ref(v_v_159_);
lean_dec_ref(v_t_158_);
return v_e_112_;
}
}
}
}
case 5:
{
lean_object* v_fn_173_; lean_object* v_arg_174_; lean_object* v_f_175_; lean_object* v_a_176_; size_t v___x_177_; size_t v___x_178_; uint8_t v___x_179_; 
v_fn_173_ = lean_ctor_get(v_e_112_, 0);
v_arg_174_ = lean_ctor_get(v_e_112_, 1);
lean_inc_ref(v_fn_173_);
lean_inc(v_lvls_111_);
lean_inc(v_paramNames_110_);
v_f_175_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_fn_173_);
lean_inc_ref(v_arg_174_);
v_a_176_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_arg_174_);
v___x_177_ = lean_ptr_addr(v_fn_173_);
v___x_178_ = lean_ptr_addr(v_f_175_);
v___x_179_ = lean_usize_dec_eq(v___x_177_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; 
lean_dec_ref_known(v_e_112_, 2);
v___x_180_ = l_Lean_Expr_app___override(v_f_175_, v_a_176_);
return v___x_180_;
}
else
{
size_t v___x_181_; size_t v___x_182_; uint8_t v___x_183_; 
v___x_181_ = lean_ptr_addr(v_arg_174_);
v___x_182_ = lean_ptr_addr(v_a_176_);
v___x_183_ = lean_usize_dec_eq(v___x_181_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; 
lean_dec_ref_known(v_e_112_, 2);
v___x_184_ = l_Lean_Expr_app___override(v_f_175_, v_a_176_);
return v___x_184_;
}
else
{
lean_dec_ref(v_a_176_);
lean_dec_ref(v_f_175_);
return v_e_112_;
}
}
}
case 11:
{
lean_object* v_typeName_185_; lean_object* v_idx_186_; lean_object* v_struct_187_; lean_object* v_b_188_; size_t v___x_189_; size_t v___x_190_; uint8_t v___x_191_; 
v_typeName_185_ = lean_ctor_get(v_e_112_, 0);
v_idx_186_ = lean_ctor_get(v_e_112_, 1);
v_struct_187_ = lean_ctor_get(v_e_112_, 2);
lean_inc_ref(v_struct_187_);
v_b_188_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_struct_187_);
v___x_189_ = lean_ptr_addr(v_struct_187_);
v___x_190_ = lean_ptr_addr(v_b_188_);
v___x_191_ = lean_usize_dec_eq(v___x_189_, v___x_190_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; 
lean_inc(v_idx_186_);
lean_inc(v_typeName_185_);
lean_dec_ref_known(v_e_112_, 3);
v___x_192_ = l_Lean_Expr_proj___override(v_typeName_185_, v_idx_186_, v_b_188_);
return v___x_192_;
}
else
{
lean_dec_ref(v_b_188_);
return v_e_112_;
}
}
default: 
{
lean_dec(v_lvls_111_);
lean_dec(v_paramNames_110_);
return v_e_112_;
}
}
}
else
{
lean_object* v_val_193_; 
lean_dec_ref(v_e_112_);
lean_dec(v_lvls_111_);
lean_dec(v_paramNames_110_);
v_val_193_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_val_193_);
lean_dec_ref_known(v___x_113_, 1);
return v_val_193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsNoCache(lean_object* v_e_194_, lean_object* v_paramNames_195_, lean_object* v_lvls_196_){
_start:
{
uint8_t v___y_198_; uint8_t v___x_200_; 
v___x_200_ = l_List_isEmpty___redArg(v_paramNames_195_);
if (v___x_200_ == 0)
{
uint8_t v___x_201_; 
v___x_201_ = l_List_isEmpty___redArg(v_lvls_196_);
v___y_198_ = v___x_201_;
goto v___jp_197_;
}
else
{
v___y_198_ = v___x_200_;
goto v___jp_197_;
}
v___jp_197_:
{
if (v___y_198_ == 0)
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_195_, v_lvls_196_, v_e_194_);
return v___x_199_;
}
else
{
lean_dec(v_lvls_196_);
lean_dec(v_paramNames_195_);
return v_e_194_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(lean_object* v_ps_202_, lean_object* v_us_203_, lean_object* v_p_x27_204_, lean_object* v_i_205_){
_start:
{
lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_206_ = lean_array_get_size(v_ps_202_);
v___x_207_ = lean_nat_dec_lt(v_i_205_, v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; 
lean_dec(v_i_205_);
v___x_208_ = lean_box(0);
return v___x_208_;
}
else
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = lean_array_get_size(v_us_203_);
v___x_210_ = lean_nat_dec_lt(v_i_205_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; 
lean_dec(v_i_205_);
v___x_211_ = lean_box(0);
return v___x_211_;
}
else
{
lean_object* v_p_212_; uint8_t v___x_213_; 
v_p_212_ = lean_array_fget_borrowed(v_ps_202_, v_i_205_);
v___x_213_ = lean_name_eq(v_p_212_, v_p_x27_204_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_nat_add(v_i_205_, v___x_214_);
lean_dec(v_i_205_);
v_i_205_ = v___x_215_;
goto _start;
}
else
{
lean_object* v_u_217_; lean_object* v___x_218_; 
v_u_217_ = lean_array_fget_borrowed(v_us_203_, v_i_205_);
lean_dec(v_i_205_);
lean_inc(v_u_217_);
v___x_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_218_, 0, v_u_217_);
return v___x_218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray___boxed(lean_object* v_ps_219_, lean_object* v_us_220_, lean_object* v_p_x27_221_, lean_object* v_i_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(v_ps_219_, v_us_220_, v_p_x27_221_, v_i_222_);
lean_dec(v_p_x27_221_);
lean_dec_ref(v_us_220_);
lean_dec_ref(v_ps_219_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0(lean_object* v_paramNames_224_, lean_object* v_lvls_225_, lean_object* v_p_226_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(v_paramNames_224_, v_lvls_225_, v_p_226_, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed(lean_object* v_paramNames_229_, lean_object* v_lvls_230_, lean_object* v_p_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0(v_paramNames_229_, v_lvls_230_, v_p_231_);
lean_dec(v_p_231_);
lean_dec_ref(v_lvls_230_);
lean_dec_ref(v_paramNames_229_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0_spec__1(lean_object* v_paramNames_233_, lean_object* v_lvls_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
if (lean_obj_tag(v_a_235_) == 0)
{
lean_object* v___x_237_; 
lean_dec_ref(v_lvls_234_);
lean_dec_ref(v_paramNames_233_);
v___x_237_ = l_List_reverse___redArg(v_a_236_);
return v___x_237_;
}
else
{
lean_object* v_head_238_; lean_object* v_tail_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_249_; 
v_head_238_ = lean_ctor_get(v_a_235_, 0);
v_tail_239_ = lean_ctor_get(v_a_235_, 1);
v_isSharedCheck_249_ = !lean_is_exclusive(v_a_235_);
if (v_isSharedCheck_249_ == 0)
{
v___x_241_ = v_a_235_;
v_isShared_242_ = v_isSharedCheck_249_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_tail_239_);
lean_inc(v_head_238_);
lean_dec(v_a_235_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_249_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___f_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
lean_inc_ref(v_lvls_234_);
lean_inc_ref(v_paramNames_233_);
v___f_243_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_243_, 0, v_paramNames_233_);
lean_closure_set(v___f_243_, 1, v_lvls_234_);
v___x_244_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___f_243_, v_head_238_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v_a_236_);
lean_ctor_set(v___x_241_, 0, v___x_244_);
v___x_246_ = v___x_241_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_a_236_);
v___x_246_ = v_reuseFailAlloc_248_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
v_a_235_ = v_tail_239_;
v_a_236_ = v___x_246_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0(lean_object* v_paramNames_250_, lean_object* v_lvls_251_, lean_object* v_e_252_){
_start:
{
uint8_t v___x_253_; 
v___x_253_ = l_Lean_Expr_hasLevelParam(v_e_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
lean_dec_ref(v_lvls_251_);
lean_dec_ref(v_paramNames_250_);
v___x_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_254_, 0, v_e_252_);
return v___x_254_;
}
else
{
switch(lean_obj_tag(v_e_252_))
{
case 4:
{
lean_object* v_declName_255_; lean_object* v_us_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v_declName_255_ = lean_ctor_get(v_e_252_, 0);
v_us_256_ = lean_ctor_get(v_e_252_, 1);
v___x_257_ = lean_box(0);
lean_inc(v_us_256_);
v___x_258_ = l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0_spec__1(v_paramNames_250_, v_lvls_251_, v_us_256_, v___x_257_);
v___x_259_ = l_ptrEqList___redArg(v_us_256_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_inc(v_declName_255_);
lean_dec_ref_known(v_e_252_, 2);
v___x_260_ = l_Lean_Expr_const___override(v_declName_255_, v___x_258_);
v___x_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
return v___x_261_;
}
else
{
lean_object* v___x_262_; 
lean_dec(v___x_258_);
v___x_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_262_, 0, v_e_252_);
return v___x_262_;
}
}
case 3:
{
lean_object* v_u_263_; lean_object* v___f_264_; lean_object* v___x_265_; size_t v___x_266_; size_t v___x_267_; uint8_t v___x_268_; 
v_u_263_ = lean_ctor_get(v_e_252_, 0);
v___f_264_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_264_, 0, v_paramNames_250_);
lean_closure_set(v___f_264_, 1, v_lvls_251_);
lean_inc(v_u_263_);
v___x_265_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___f_264_, v_u_263_);
v___x_266_ = lean_ptr_addr(v_u_263_);
v___x_267_ = lean_ptr_addr(v___x_265_);
v___x_268_ = lean_usize_dec_eq(v___x_266_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec_ref_known(v_e_252_, 1);
v___x_269_ = l_Lean_Expr_sort___override(v___x_265_);
v___x_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
else
{
lean_object* v___x_271_; 
lean_dec(v___x_265_);
v___x_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_271_, 0, v_e_252_);
return v___x_271_;
}
}
default: 
{
lean_object* v___x_272_; 
lean_dec_ref(v_e_252_);
lean_dec_ref(v_lvls_251_);
lean_dec_ref(v_paramNames_250_);
v___x_272_ = lean_box(0);
return v___x_272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(lean_object* v_paramNames_273_, lean_object* v_lvls_274_, lean_object* v_e_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0), 3, 2);
lean_closure_set(v___x_276_, 0, v_paramNames_273_);
lean_closure_set(v___x_276_, 1, v_lvls_274_);
v___x_277_ = lean_replace_expr(v___x_276_, v_e_275_);
lean_dec_ref(v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0___boxed(lean_object* v_paramNames_278_, lean_object* v_lvls_279_, lean_object* v_e_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(v_paramNames_278_, v_lvls_279_, v_e_280_);
lean_dec_ref(v_e_280_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object* v_e_282_, lean_object* v_paramNames_283_, lean_object* v_lvls_284_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_285_ = lean_array_get_size(v_paramNames_283_);
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = lean_nat_dec_eq(v___x_285_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_array_get_size(v_lvls_284_);
v___x_289_ = lean_nat_dec_eq(v___x_288_, v___x_286_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(v_paramNames_283_, v_lvls_284_, v_e_282_);
return v___x_290_;
}
else
{
lean_dec_ref(v_lvls_284_);
lean_dec_ref(v_paramNames_283_);
lean_inc_ref(v_e_282_);
return v_e_282_;
}
}
else
{
lean_dec_ref(v_lvls_284_);
lean_dec_ref(v_paramNames_283_);
lean_inc_ref(v_e_282_);
return v_e_282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsArray___boxed(lean_object* v_e_291_, lean_object* v_paramNames_292_, lean_object* v_lvls_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Expr_instantiateLevelParamsArray(v_e_291_, v_paramNames_292_, v_lvls_293_);
lean_dec_ref(v_e_291_);
return v_res_294_;
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
