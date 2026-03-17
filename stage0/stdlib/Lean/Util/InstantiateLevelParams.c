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
lean_dec_ref(v_e_5_);
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
lean_dec_ref(v_e_5_);
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
lean_dec_ref(v_e_68_);
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
lean_dec_ref(v_e_68_);
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
lean_object* v_binderName_114_; lean_object* v_binderType_115_; lean_object* v_body_116_; uint8_t v_binderInfo_117_; lean_object* v_d_118_; lean_object* v_b_119_; uint8_t v___y_121_; size_t v___x_125_; size_t v___x_126_; uint8_t v___x_127_; 
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
v___x_125_ = lean_ptr_addr(v_binderType_115_);
v___x_126_ = lean_ptr_addr(v_d_118_);
v___x_127_ = lean_usize_dec_eq(v___x_125_, v___x_126_);
if (v___x_127_ == 0)
{
v___y_121_ = v___x_127_;
goto v___jp_120_;
}
else
{
size_t v___x_128_; size_t v___x_129_; uint8_t v___x_130_; 
v___x_128_ = lean_ptr_addr(v_body_116_);
v___x_129_ = lean_ptr_addr(v_b_119_);
v___x_130_ = lean_usize_dec_eq(v___x_128_, v___x_129_);
v___y_121_ = v___x_130_;
goto v___jp_120_;
}
v___jp_120_:
{
if (v___y_121_ == 0)
{
lean_object* v___x_122_; 
lean_inc(v_binderName_114_);
lean_dec_ref(v_e_112_);
v___x_122_ = l_Lean_Expr_forallE___override(v_binderName_114_, v_d_118_, v_b_119_, v_binderInfo_117_);
return v___x_122_;
}
else
{
uint8_t v___x_123_; 
v___x_123_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_117_, v_binderInfo_117_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; 
lean_inc(v_binderName_114_);
lean_dec_ref(v_e_112_);
v___x_124_ = l_Lean_Expr_forallE___override(v_binderName_114_, v_d_118_, v_b_119_, v_binderInfo_117_);
return v___x_124_;
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
lean_object* v_binderName_131_; lean_object* v_binderType_132_; lean_object* v_body_133_; uint8_t v_binderInfo_134_; lean_object* v_d_135_; lean_object* v_b_136_; uint8_t v___y_138_; size_t v___x_142_; size_t v___x_143_; uint8_t v___x_144_; 
v_binderName_131_ = lean_ctor_get(v_e_112_, 0);
v_binderType_132_ = lean_ctor_get(v_e_112_, 1);
v_body_133_ = lean_ctor_get(v_e_112_, 2);
v_binderInfo_134_ = lean_ctor_get_uint8(v_e_112_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_132_);
lean_inc(v_lvls_111_);
lean_inc(v_paramNames_110_);
v_d_135_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_binderType_132_);
lean_inc_ref(v_body_133_);
v_b_136_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_body_133_);
v___x_142_ = lean_ptr_addr(v_binderType_132_);
v___x_143_ = lean_ptr_addr(v_d_135_);
v___x_144_ = lean_usize_dec_eq(v___x_142_, v___x_143_);
if (v___x_144_ == 0)
{
v___y_138_ = v___x_144_;
goto v___jp_137_;
}
else
{
size_t v___x_145_; size_t v___x_146_; uint8_t v___x_147_; 
v___x_145_ = lean_ptr_addr(v_body_133_);
v___x_146_ = lean_ptr_addr(v_b_136_);
v___x_147_ = lean_usize_dec_eq(v___x_145_, v___x_146_);
v___y_138_ = v___x_147_;
goto v___jp_137_;
}
v___jp_137_:
{
if (v___y_138_ == 0)
{
lean_object* v___x_139_; 
lean_inc(v_binderName_131_);
lean_dec_ref(v_e_112_);
v___x_139_ = l_Lean_Expr_lam___override(v_binderName_131_, v_d_135_, v_b_136_, v_binderInfo_134_);
return v___x_139_;
}
else
{
uint8_t v___x_140_; 
v___x_140_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_134_, v_binderInfo_134_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; 
lean_inc(v_binderName_131_);
lean_dec_ref(v_e_112_);
v___x_141_ = l_Lean_Expr_lam___override(v_binderName_131_, v_d_135_, v_b_136_, v_binderInfo_134_);
return v___x_141_;
}
else
{
lean_dec_ref(v_b_136_);
lean_dec_ref(v_d_135_);
return v_e_112_;
}
}
}
}
case 10:
{
lean_object* v_data_148_; lean_object* v_expr_149_; lean_object* v_b_150_; size_t v___x_151_; size_t v___x_152_; uint8_t v___x_153_; 
v_data_148_ = lean_ctor_get(v_e_112_, 0);
v_expr_149_ = lean_ctor_get(v_e_112_, 1);
lean_inc_ref(v_expr_149_);
v_b_150_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_expr_149_);
v___x_151_ = lean_ptr_addr(v_expr_149_);
v___x_152_ = lean_ptr_addr(v_b_150_);
v___x_153_ = lean_usize_dec_eq(v___x_151_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; 
lean_inc(v_data_148_);
lean_dec_ref(v_e_112_);
v___x_154_ = l_Lean_Expr_mdata___override(v_data_148_, v_b_150_);
return v___x_154_;
}
else
{
lean_dec_ref(v_b_150_);
return v_e_112_;
}
}
case 8:
{
lean_object* v_declName_155_; lean_object* v_type_156_; lean_object* v_value_157_; lean_object* v_body_158_; uint8_t v_nondep_159_; lean_object* v_t_160_; lean_object* v_v_161_; lean_object* v_b_162_; uint8_t v___y_164_; size_t v___x_170_; size_t v___x_171_; uint8_t v___x_172_; 
v_declName_155_ = lean_ctor_get(v_e_112_, 0);
v_type_156_ = lean_ctor_get(v_e_112_, 1);
v_value_157_ = lean_ctor_get(v_e_112_, 2);
v_body_158_ = lean_ctor_get(v_e_112_, 3);
v_nondep_159_ = lean_ctor_get_uint8(v_e_112_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_156_);
lean_inc(v_lvls_111_);
lean_inc(v_paramNames_110_);
v_t_160_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_type_156_);
lean_inc_ref(v_value_157_);
lean_inc(v_lvls_111_);
lean_inc(v_paramNames_110_);
v_v_161_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_value_157_);
lean_inc_ref(v_body_158_);
v_b_162_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_body_158_);
v___x_170_ = lean_ptr_addr(v_type_156_);
v___x_171_ = lean_ptr_addr(v_t_160_);
v___x_172_ = lean_usize_dec_eq(v___x_170_, v___x_171_);
if (v___x_172_ == 0)
{
v___y_164_ = v___x_172_;
goto v___jp_163_;
}
else
{
size_t v___x_173_; size_t v___x_174_; uint8_t v___x_175_; 
v___x_173_ = lean_ptr_addr(v_value_157_);
v___x_174_ = lean_ptr_addr(v_v_161_);
v___x_175_ = lean_usize_dec_eq(v___x_173_, v___x_174_);
v___y_164_ = v___x_175_;
goto v___jp_163_;
}
v___jp_163_:
{
if (v___y_164_ == 0)
{
lean_object* v___x_165_; 
lean_inc(v_declName_155_);
lean_dec_ref(v_e_112_);
v___x_165_ = l_Lean_Expr_letE___override(v_declName_155_, v_t_160_, v_v_161_, v_b_162_, v_nondep_159_);
return v___x_165_;
}
else
{
size_t v___x_166_; size_t v___x_167_; uint8_t v___x_168_; 
v___x_166_ = lean_ptr_addr(v_body_158_);
v___x_167_ = lean_ptr_addr(v_b_162_);
v___x_168_ = lean_usize_dec_eq(v___x_166_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
lean_inc(v_declName_155_);
lean_dec_ref(v_e_112_);
v___x_169_ = l_Lean_Expr_letE___override(v_declName_155_, v_t_160_, v_v_161_, v_b_162_, v_nondep_159_);
return v___x_169_;
}
else
{
lean_dec_ref(v_b_162_);
lean_dec_ref(v_v_161_);
lean_dec_ref(v_t_160_);
return v_e_112_;
}
}
}
}
case 5:
{
lean_object* v_fn_176_; lean_object* v_arg_177_; lean_object* v_f_178_; lean_object* v_a_179_; uint8_t v___y_181_; size_t v___x_183_; size_t v___x_184_; uint8_t v___x_185_; 
v_fn_176_ = lean_ctor_get(v_e_112_, 0);
v_arg_177_ = lean_ctor_get(v_e_112_, 1);
lean_inc_ref(v_fn_176_);
lean_inc(v_lvls_111_);
lean_inc(v_paramNames_110_);
v_f_178_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_fn_176_);
lean_inc_ref(v_arg_177_);
v_a_179_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_arg_177_);
v___x_183_ = lean_ptr_addr(v_fn_176_);
v___x_184_ = lean_ptr_addr(v_f_178_);
v___x_185_ = lean_usize_dec_eq(v___x_183_, v___x_184_);
if (v___x_185_ == 0)
{
v___y_181_ = v___x_185_;
goto v___jp_180_;
}
else
{
size_t v___x_186_; size_t v___x_187_; uint8_t v___x_188_; 
v___x_186_ = lean_ptr_addr(v_arg_177_);
v___x_187_ = lean_ptr_addr(v_a_179_);
v___x_188_ = lean_usize_dec_eq(v___x_186_, v___x_187_);
v___y_181_ = v___x_188_;
goto v___jp_180_;
}
v___jp_180_:
{
if (v___y_181_ == 0)
{
lean_object* v___x_182_; 
lean_dec_ref(v_e_112_);
v___x_182_ = l_Lean_Expr_app___override(v_f_178_, v_a_179_);
return v___x_182_;
}
else
{
lean_dec_ref(v_a_179_);
lean_dec_ref(v_f_178_);
return v_e_112_;
}
}
}
case 11:
{
lean_object* v_typeName_189_; lean_object* v_idx_190_; lean_object* v_struct_191_; lean_object* v_b_192_; size_t v___x_193_; size_t v___x_194_; uint8_t v___x_195_; 
v_typeName_189_ = lean_ctor_get(v_e_112_, 0);
v_idx_190_ = lean_ctor_get(v_e_112_, 1);
v_struct_191_ = lean_ctor_get(v_e_112_, 2);
lean_inc_ref(v_struct_191_);
v_b_192_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_110_, v_lvls_111_, v_struct_191_);
v___x_193_ = lean_ptr_addr(v_struct_191_);
v___x_194_ = lean_ptr_addr(v_b_192_);
v___x_195_ = lean_usize_dec_eq(v___x_193_, v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; 
lean_inc(v_idx_190_);
lean_inc(v_typeName_189_);
lean_dec_ref(v_e_112_);
v___x_196_ = l_Lean_Expr_proj___override(v_typeName_189_, v_idx_190_, v_b_192_);
return v___x_196_;
}
else
{
lean_dec_ref(v_b_192_);
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
lean_object* v_val_197_; 
lean_dec_ref(v_e_112_);
lean_dec(v_lvls_111_);
lean_dec(v_paramNames_110_);
v_val_197_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_val_197_);
lean_dec_ref(v___x_113_);
return v_val_197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsNoCache(lean_object* v_e_198_, lean_object* v_paramNames_199_, lean_object* v_lvls_200_){
_start:
{
uint8_t v___y_202_; uint8_t v___x_204_; 
v___x_204_ = l_List_isEmpty___redArg(v_paramNames_199_);
if (v___x_204_ == 0)
{
uint8_t v___x_205_; 
v___x_205_ = l_List_isEmpty___redArg(v_lvls_200_);
v___y_202_ = v___x_205_;
goto v___jp_201_;
}
else
{
v___y_202_ = v___x_204_;
goto v___jp_201_;
}
v___jp_201_:
{
if (v___y_202_ == 0)
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_199_, v_lvls_200_, v_e_198_);
return v___x_203_;
}
else
{
lean_dec(v_lvls_200_);
lean_dec(v_paramNames_199_);
return v_e_198_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(lean_object* v_ps_206_, lean_object* v_us_207_, lean_object* v_p_x27_208_, lean_object* v_i_209_){
_start:
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = lean_array_get_size(v_ps_206_);
v___x_211_ = lean_nat_dec_lt(v_i_209_, v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; 
lean_dec(v_i_209_);
v___x_212_ = lean_box(0);
return v___x_212_;
}
else
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_array_get_size(v_us_207_);
v___x_214_ = lean_nat_dec_lt(v_i_209_, v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
lean_dec(v_i_209_);
v___x_215_ = lean_box(0);
return v___x_215_;
}
else
{
lean_object* v_p_216_; uint8_t v___x_217_; 
v_p_216_ = lean_array_fget_borrowed(v_ps_206_, v_i_209_);
v___x_217_ = lean_name_eq(v_p_216_, v_p_x27_208_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_unsigned_to_nat(1u);
v___x_219_ = lean_nat_add(v_i_209_, v___x_218_);
lean_dec(v_i_209_);
v_i_209_ = v___x_219_;
goto _start;
}
else
{
lean_object* v_u_221_; lean_object* v___x_222_; 
v_u_221_ = lean_array_fget_borrowed(v_us_207_, v_i_209_);
lean_dec(v_i_209_);
lean_inc(v_u_221_);
v___x_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_222_, 0, v_u_221_);
return v___x_222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray___boxed(lean_object* v_ps_223_, lean_object* v_us_224_, lean_object* v_p_x27_225_, lean_object* v_i_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(v_ps_223_, v_us_224_, v_p_x27_225_, v_i_226_);
lean_dec(v_p_x27_225_);
lean_dec_ref(v_us_224_);
lean_dec_ref(v_ps_223_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0(lean_object* v_paramNames_228_, lean_object* v_lvls_229_, lean_object* v_p_230_){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(v_paramNames_228_, v_lvls_229_, v_p_230_, v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed(lean_object* v_paramNames_233_, lean_object* v_lvls_234_, lean_object* v_p_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0(v_paramNames_233_, v_lvls_234_, v_p_235_);
lean_dec(v_p_235_);
lean_dec_ref(v_lvls_234_);
lean_dec_ref(v_paramNames_233_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0_spec__1(lean_object* v_paramNames_237_, lean_object* v_lvls_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
if (lean_obj_tag(v_a_239_) == 0)
{
lean_object* v___x_241_; 
lean_dec_ref(v_lvls_238_);
lean_dec_ref(v_paramNames_237_);
v___x_241_ = l_List_reverse___redArg(v_a_240_);
return v___x_241_;
}
else
{
lean_object* v_head_242_; lean_object* v_tail_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_253_; 
v_head_242_ = lean_ctor_get(v_a_239_, 0);
v_tail_243_ = lean_ctor_get(v_a_239_, 1);
v_isSharedCheck_253_ = !lean_is_exclusive(v_a_239_);
if (v_isSharedCheck_253_ == 0)
{
v___x_245_ = v_a_239_;
v_isShared_246_ = v_isSharedCheck_253_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_tail_243_);
lean_inc(v_head_242_);
lean_dec(v_a_239_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_253_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___f_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
lean_inc_ref(v_lvls_238_);
lean_inc_ref(v_paramNames_237_);
v___f_247_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_247_, 0, v_paramNames_237_);
lean_closure_set(v___f_247_, 1, v_lvls_238_);
v___x_248_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___f_247_, v_head_242_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 1, v_a_240_);
lean_ctor_set(v___x_245_, 0, v___x_248_);
v___x_250_ = v___x_245_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_a_240_);
v___x_250_ = v_reuseFailAlloc_252_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
v_a_239_ = v_tail_243_;
v_a_240_ = v___x_250_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0(lean_object* v_paramNames_254_, lean_object* v_lvls_255_, lean_object* v_e_256_){
_start:
{
uint8_t v___x_257_; 
v___x_257_ = l_Lean_Expr_hasLevelParam(v_e_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
lean_dec_ref(v_lvls_255_);
lean_dec_ref(v_paramNames_254_);
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v_e_256_);
return v___x_258_;
}
else
{
switch(lean_obj_tag(v_e_256_))
{
case 4:
{
lean_object* v_declName_259_; lean_object* v_us_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_declName_259_ = lean_ctor_get(v_e_256_, 0);
v_us_260_ = lean_ctor_get(v_e_256_, 1);
v___x_261_ = lean_box(0);
lean_inc(v_us_260_);
v___x_262_ = l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0_spec__1(v_paramNames_254_, v_lvls_255_, v_us_260_, v___x_261_);
v___x_263_ = l_ptrEqList___redArg(v_us_260_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_inc(v_declName_259_);
lean_dec_ref(v_e_256_);
v___x_264_ = l_Lean_Expr_const___override(v_declName_259_, v___x_262_);
v___x_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
else
{
lean_object* v___x_266_; 
lean_dec(v___x_262_);
v___x_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_266_, 0, v_e_256_);
return v___x_266_;
}
}
case 3:
{
lean_object* v_u_267_; lean_object* v___f_268_; lean_object* v___x_269_; size_t v___x_270_; size_t v___x_271_; uint8_t v___x_272_; 
v_u_267_ = lean_ctor_get(v_e_256_, 0);
v___f_268_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_268_, 0, v_paramNames_254_);
lean_closure_set(v___f_268_, 1, v_lvls_255_);
lean_inc(v_u_267_);
v___x_269_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___f_268_, v_u_267_);
v___x_270_ = lean_ptr_addr(v_u_267_);
v___x_271_ = lean_ptr_addr(v___x_269_);
v___x_272_ = lean_usize_dec_eq(v___x_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
lean_dec_ref(v_e_256_);
v___x_273_ = l_Lean_Expr_sort___override(v___x_269_);
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
return v___x_274_;
}
else
{
lean_object* v___x_275_; 
lean_dec(v___x_269_);
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v_e_256_);
return v___x_275_;
}
}
default: 
{
lean_object* v___x_276_; 
lean_dec_ref(v_e_256_);
lean_dec_ref(v_lvls_255_);
lean_dec_ref(v_paramNames_254_);
v___x_276_ = lean_box(0);
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(lean_object* v_paramNames_277_, lean_object* v_lvls_278_, lean_object* v_e_279_){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0), 3, 2);
lean_closure_set(v___x_280_, 0, v_paramNames_277_);
lean_closure_set(v___x_280_, 1, v_lvls_278_);
v___x_281_ = lean_replace_expr(v___x_280_, v_e_279_);
lean_dec_ref(v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0___boxed(lean_object* v_paramNames_282_, lean_object* v_lvls_283_, lean_object* v_e_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(v_paramNames_282_, v_lvls_283_, v_e_284_);
lean_dec_ref(v_e_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object* v_e_286_, lean_object* v_paramNames_287_, lean_object* v_lvls_288_){
_start:
{
uint8_t v___y_290_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_292_ = lean_array_get_size(v_paramNames_287_);
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_nat_dec_eq(v___x_292_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = lean_array_get_size(v_lvls_288_);
v___x_296_ = lean_nat_dec_eq(v___x_295_, v___x_293_);
v___y_290_ = v___x_296_;
goto v___jp_289_;
}
else
{
v___y_290_ = v___x_294_;
goto v___jp_289_;
}
v___jp_289_:
{
if (v___y_290_ == 0)
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(v_paramNames_287_, v_lvls_288_, v_e_286_);
return v___x_291_;
}
else
{
lean_dec_ref(v_lvls_288_);
lean_dec_ref(v_paramNames_287_);
lean_inc_ref(v_e_286_);
return v_e_286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsArray___boxed(lean_object* v_e_297_, lean_object* v_paramNames_298_, lean_object* v_lvls_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Expr_instantiateLevelParamsArray(v_e_297_, v_paramNames_298_, v_lvls_299_);
lean_dec_ref(v_e_297_);
return v_res_300_;
}
}
lean_object* runtime_initialize_Lean_Util_ReplaceExpr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_InstantiateLevelParams(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
