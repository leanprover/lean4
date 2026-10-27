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
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_Level_substParams_go(lean_object*, lean_object*);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
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
lean_object* lean_replace_expr(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_level_params(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsImpl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParams___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__1(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsImpl___boxed(lean_object* v_e_52_, lean_object* v_paramNames_53_, lean_object* v_lvls_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lean_expr_instantiate_level_params(v_e_52_, v_paramNames_53_, v_lvls_54_);
lean_dec(v_lvls_54_);
lean_dec(v_paramNames_53_);
lean_dec_ref(v_e_52_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParams(lean_object* v_e_56_, lean_object* v_paramNames_57_, lean_object* v_lvls_58_){
_start:
{
uint8_t v___x_59_; 
v___x_59_ = l_List_isEmpty___redArg(v_paramNames_57_);
if (v___x_59_ == 0)
{
uint8_t v___x_60_; 
v___x_60_ = l_List_isEmpty___redArg(v_lvls_58_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
v___x_61_ = lean_expr_instantiate_level_params(v_e_56_, v_paramNames_57_, v_lvls_58_);
return v___x_61_;
}
else
{
lean_inc_ref(v_e_56_);
return v_e_56_;
}
}
else
{
lean_inc_ref(v_e_56_);
return v_e_56_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParams___boxed(lean_object* v_e_62_, lean_object* v_paramNames_63_, lean_object* v_lvls_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Expr_instantiateLevelParams(v_e_62_, v_paramNames_63_, v_lvls_64_);
lean_dec(v_lvls_64_);
lean_dec(v_paramNames_63_);
lean_dec_ref(v_e_62_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0_spec__0(lean_object* v_paramNames_66_, lean_object* v_lvls_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
if (lean_obj_tag(v_a_68_) == 0)
{
lean_object* v___x_70_; 
lean_dec(v_lvls_67_);
lean_dec(v_paramNames_66_);
v___x_70_ = l_List_reverse___redArg(v_a_69_);
return v___x_70_;
}
else
{
lean_object* v_head_71_; lean_object* v_tail_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_82_; 
v_head_71_ = lean_ctor_get(v_a_68_, 0);
v_tail_72_ = lean_ctor_get(v_a_68_, 1);
v_isSharedCheck_82_ = !lean_is_exclusive(v_a_68_);
if (v_isSharedCheck_82_ == 0)
{
v___x_74_ = v_a_68_;
v_isShared_75_ = v_isSharedCheck_82_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_tail_72_);
lean_inc(v_head_71_);
lean_dec(v_a_68_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_82_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_79_; 
lean_inc(v_lvls_67_);
lean_inc(v_paramNames_66_);
v___x_76_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst___boxed), 3, 2);
lean_closure_set(v___x_76_, 0, v_paramNames_66_);
lean_closure_set(v___x_76_, 1, v_lvls_67_);
v___x_77_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_76_, v_head_71_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 1, v_a_69_);
lean_ctor_set(v___x_74_, 0, v___x_77_);
v___x_79_ = v___x_74_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_a_69_);
v___x_79_ = v_reuseFailAlloc_81_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
v_a_68_ = v_tail_72_;
v_a_69_ = v___x_79_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(lean_object* v_paramNames_83_, lean_object* v_lvls_84_, lean_object* v_e_85_){
_start:
{
uint8_t v___x_86_; 
v___x_86_ = l_Lean_Expr_hasLevelParam(v_e_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; 
lean_dec(v_lvls_84_);
lean_dec(v_paramNames_83_);
v___x_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_87_, 0, v_e_85_);
return v___x_87_;
}
else
{
switch(lean_obj_tag(v_e_85_))
{
case 4:
{
lean_object* v_declName_88_; lean_object* v_us_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_declName_88_ = lean_ctor_get(v_e_85_, 0);
v_us_89_ = lean_ctor_get(v_e_85_, 1);
v___x_90_ = lean_box(0);
lean_inc(v_us_89_);
v___x_91_ = l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0_spec__0(v_paramNames_83_, v_lvls_84_, v_us_89_, v___x_90_);
v___x_92_ = l_ptrEqList___redArg(v_us_89_, v___x_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; 
lean_inc(v_declName_88_);
lean_dec_ref_known(v_e_85_, 2);
v___x_93_ = l_Lean_Expr_const___override(v_declName_88_, v___x_91_);
v___x_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
else
{
lean_object* v___x_95_; 
lean_dec(v___x_91_);
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v_e_85_);
return v___x_95_;
}
}
case 3:
{
lean_object* v_u_96_; lean_object* v___x_97_; lean_object* v___x_98_; size_t v___x_99_; size_t v___x_100_; uint8_t v___x_101_; 
v_u_96_ = lean_ctor_get(v_e_85_, 0);
v___x_97_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst___boxed), 3, 2);
lean_closure_set(v___x_97_, 0, v_paramNames_83_);
lean_closure_set(v___x_97_, 1, v_lvls_84_);
lean_inc(v_u_96_);
v___x_98_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_97_, v_u_96_);
v___x_99_ = lean_ptr_addr(v_u_96_);
v___x_100_ = lean_ptr_addr(v___x_98_);
v___x_101_ = lean_usize_dec_eq(v___x_99_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec_ref_known(v_e_85_, 1);
v___x_102_ = l_Lean_Expr_sort___override(v___x_98_);
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
else
{
lean_object* v___x_104_; 
lean_dec(v___x_98_);
v___x_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_104_, 0, v_e_85_);
return v___x_104_;
}
}
default: 
{
lean_object* v___x_105_; 
lean_dec_ref(v_e_85_);
lean_dec(v_lvls_84_);
lean_dec(v_paramNames_83_);
v___x_105_ = lean_box(0);
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__1(lean_object* v_paramNames_106_, lean_object* v_lvls_107_, lean_object* v_e_108_){
_start:
{
lean_object* v___x_109_; 
lean_inc_ref(v_e_108_);
lean_inc(v_lvls_107_);
lean_inc(v_paramNames_106_);
v___x_109_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_106_, v_lvls_107_, v_e_108_);
if (lean_obj_tag(v___x_109_) == 0)
{
switch(lean_obj_tag(v_e_108_))
{
case 7:
{
lean_object* v_binderName_110_; lean_object* v_binderType_111_; lean_object* v_body_112_; uint8_t v_binderInfo_113_; lean_object* v_d_114_; lean_object* v_b_115_; size_t v___x_116_; size_t v___x_117_; uint8_t v___x_118_; 
v_binderName_110_ = lean_ctor_get(v_e_108_, 0);
v_binderType_111_ = lean_ctor_get(v_e_108_, 1);
v_body_112_ = lean_ctor_get(v_e_108_, 2);
v_binderInfo_113_ = lean_ctor_get_uint8(v_e_108_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_111_);
lean_inc(v_lvls_107_);
lean_inc(v_paramNames_106_);
v_d_114_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__1(v_paramNames_106_, v_lvls_107_, v_binderType_111_);
lean_inc_ref(v_body_112_);
v_b_115_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__1(v_paramNames_106_, v_lvls_107_, v_body_112_);
v___x_116_ = lean_ptr_addr(v_binderType_111_);
v___x_117_ = lean_ptr_addr(v_d_114_);
v___x_118_ = lean_usize_dec_eq(v___x_116_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; 
lean_inc(v_binderName_110_);
lean_dec_ref_known(v_e_108_, 3);
v___x_119_ = l_Lean_Expr_forallE___override(v_binderName_110_, v_d_114_, v_b_115_, v_binderInfo_113_);
return v___x_119_;
}
else
{
size_t v___x_120_; size_t v___x_121_; uint8_t v___x_122_; 
v___x_120_ = lean_ptr_addr(v_body_112_);
v___x_121_ = lean_ptr_addr(v_b_115_);
v___x_122_ = lean_usize_dec_eq(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
lean_inc(v_binderName_110_);
lean_dec_ref_known(v_e_108_, 3);
v___x_123_ = l_Lean_Expr_forallE___override(v_binderName_110_, v_d_114_, v_b_115_, v_binderInfo_113_);
return v___x_123_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_113_, v_binderInfo_113_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
lean_inc(v_binderName_110_);
lean_dec_ref_known(v_e_108_, 3);
v___x_125_ = l_Lean_Expr_forallE___override(v_binderName_110_, v_d_114_, v_b_115_, v_binderInfo_113_);
return v___x_125_;
}
else
{
lean_dec_ref(v_b_115_);
lean_dec_ref(v_d_114_);
return v_e_108_;
}
}
}
}
case 6:
{
lean_object* v_binderName_126_; lean_object* v_binderType_127_; lean_object* v_body_128_; uint8_t v_binderInfo_129_; lean_object* v_d_130_; lean_object* v_b_131_; size_t v___x_132_; size_t v___x_133_; uint8_t v___x_134_; 
v_binderName_126_ = lean_ctor_get(v_e_108_, 0);
v_binderType_127_ = lean_ctor_get(v_e_108_, 1);
v_body_128_ = lean_ctor_get(v_e_108_, 2);
v_binderInfo_129_ = lean_ctor_get_uint8(v_e_108_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_127_);
lean_inc(v_lvls_107_);
lean_inc(v_paramNames_106_);
v_d_130_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__1(v_paramNames_106_, v_lvls_107_, v_binderType_127_);
lean_inc_ref(v_body_128_);
v_b_131_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__1(v_paramNames_106_, v_lvls_107_, v_body_128_);
v___x_132_ = lean_ptr_addr(v_binderType_127_);
v___x_133_ = lean_ptr_addr(v_d_130_);
v___x_134_ = lean_usize_dec_eq(v___x_132_, v___x_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; 
lean_inc(v_binderName_126_);
lean_dec_ref_known(v_e_108_, 3);
v___x_135_ = l_Lean_Expr_lam___override(v_binderName_126_, v_d_130_, v_b_131_, v_binderInfo_129_);
return v___x_135_;
}
else
{
size_t v___x_136_; size_t v___x_137_; uint8_t v___x_138_; 
v___x_136_ = lean_ptr_addr(v_body_128_);
v___x_137_ = lean_ptr_addr(v_b_131_);
v___x_138_ = lean_usize_dec_eq(v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; 
lean_inc(v_binderName_126_);
lean_dec_ref_known(v_e_108_, 3);
v___x_139_ = l_Lean_Expr_lam___override(v_binderName_126_, v_d_130_, v_b_131_, v_binderInfo_129_);
return v___x_139_;
}
else
{
uint8_t v___x_140_; 
v___x_140_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_129_, v_binderInfo_129_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; 
lean_inc(v_binderName_126_);
lean_dec_ref_known(v_e_108_, 3);
v___x_141_ = l_Lean_Expr_lam___override(v_binderName_126_, v_d_130_, v_b_131_, v_binderInfo_129_);
return v___x_141_;
}
else
{
lean_dec_ref(v_b_131_);
lean_dec_ref(v_d_130_);
return v_e_108_;
}
}
}
}
case 10:
{
lean_object* v_data_142_; lean_object* v_expr_143_; lean_object* v_b_144_; size_t v___x_145_; size_t v___x_146_; uint8_t v___x_147_; 
v_data_142_ = lean_ctor_get(v_e_108_, 0);
v_expr_143_ = lean_ctor_get(v_e_108_, 1);
lean_inc_ref(v_expr_143_);
v_b_144_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__1(v_paramNames_106_, v_lvls_107_, v_expr_143_);
v___x_145_ = lean_ptr_addr(v_expr_143_);
v___x_146_ = lean_ptr_addr(v_b_144_);
v___x_147_ = lean_usize_dec_eq(v___x_145_, v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; 
lean_inc(v_data_142_);
lean_dec_ref_known(v_e_108_, 2);
v___x_148_ = l_Lean_Expr_mdata___override(v_data_142_, v_b_144_);
return v___x_148_;
}
else
{
lean_dec_ref(v_b_144_);
return v_e_108_;
}
}
case 8:
{
lean_object* v_declName_149_; lean_object* v_type_150_; lean_object* v_value_151_; lean_object* v_body_152_; uint8_t v_nondep_153_; lean_object* v_t_154_; lean_object* v_v_155_; lean_object* v_b_156_; size_t v___x_157_; size_t v___x_158_; uint8_t v___x_159_; 
v_declName_149_ = lean_ctor_get(v_e_108_, 0);
v_type_150_ = lean_ctor_get(v_e_108_, 1);
v_value_151_ = lean_ctor_get(v_e_108_, 2);
v_body_152_ = lean_ctor_get(v_e_108_, 3);
v_nondep_153_ = lean_ctor_get_uint8(v_e_108_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_150_);
lean_inc_n(v_lvls_107_, 2);
lean_inc_n(v_paramNames_106_, 2);
v_t_154_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__1(v_paramNames_106_, v_lvls_107_, v_type_150_);
lean_inc_ref(v_value_151_);
v_v_155_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__1(v_paramNames_106_, v_lvls_107_, v_value_151_);
lean_inc_ref(v_body_152_);
v_b_156_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__1(v_paramNames_106_, v_lvls_107_, v_body_152_);
v___x_157_ = lean_ptr_addr(v_type_150_);
v___x_158_ = lean_ptr_addr(v_t_154_);
v___x_159_ = lean_usize_dec_eq(v___x_157_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; 
lean_inc(v_declName_149_);
lean_dec_ref_known(v_e_108_, 4);
v___x_160_ = l_Lean_Expr_letE___override(v_declName_149_, v_t_154_, v_v_155_, v_b_156_, v_nondep_153_);
return v___x_160_;
}
else
{
size_t v___x_161_; size_t v___x_162_; uint8_t v___x_163_; 
v___x_161_ = lean_ptr_addr(v_value_151_);
v___x_162_ = lean_ptr_addr(v_v_155_);
v___x_163_ = lean_usize_dec_eq(v___x_161_, v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
lean_inc(v_declName_149_);
lean_dec_ref_known(v_e_108_, 4);
v___x_164_ = l_Lean_Expr_letE___override(v_declName_149_, v_t_154_, v_v_155_, v_b_156_, v_nondep_153_);
return v___x_164_;
}
else
{
size_t v___x_165_; size_t v___x_166_; uint8_t v___x_167_; 
v___x_165_ = lean_ptr_addr(v_body_152_);
v___x_166_ = lean_ptr_addr(v_b_156_);
v___x_167_ = lean_usize_dec_eq(v___x_165_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; 
lean_inc(v_declName_149_);
lean_dec_ref_known(v_e_108_, 4);
v___x_168_ = l_Lean_Expr_letE___override(v_declName_149_, v_t_154_, v_v_155_, v_b_156_, v_nondep_153_);
return v___x_168_;
}
else
{
lean_dec_ref(v_b_156_);
lean_dec_ref(v_v_155_);
lean_dec_ref(v_t_154_);
return v_e_108_;
}
}
}
}
case 5:
{
lean_object* v_fn_169_; lean_object* v_arg_170_; lean_object* v_f_171_; lean_object* v_a_172_; size_t v___x_173_; size_t v___x_174_; uint8_t v___x_175_; 
v_fn_169_ = lean_ctor_get(v_e_108_, 0);
v_arg_170_ = lean_ctor_get(v_e_108_, 1);
lean_inc_ref(v_fn_169_);
lean_inc(v_lvls_107_);
lean_inc(v_paramNames_106_);
v_f_171_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__1(v_paramNames_106_, v_lvls_107_, v_fn_169_);
lean_inc_ref(v_arg_170_);
v_a_172_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__1(v_paramNames_106_, v_lvls_107_, v_arg_170_);
v___x_173_ = lean_ptr_addr(v_fn_169_);
v___x_174_ = lean_ptr_addr(v_f_171_);
v___x_175_ = lean_usize_dec_eq(v___x_173_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; 
lean_dec_ref_known(v_e_108_, 2);
v___x_176_ = l_Lean_Expr_app___override(v_f_171_, v_a_172_);
return v___x_176_;
}
else
{
size_t v___x_177_; size_t v___x_178_; uint8_t v___x_179_; 
v___x_177_ = lean_ptr_addr(v_arg_170_);
v___x_178_ = lean_ptr_addr(v_a_172_);
v___x_179_ = lean_usize_dec_eq(v___x_177_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; 
lean_dec_ref_known(v_e_108_, 2);
v___x_180_ = l_Lean_Expr_app___override(v_f_171_, v_a_172_);
return v___x_180_;
}
else
{
lean_dec_ref(v_a_172_);
lean_dec_ref(v_f_171_);
return v_e_108_;
}
}
}
case 11:
{
lean_object* v_typeName_181_; lean_object* v_idx_182_; lean_object* v_struct_183_; lean_object* v_b_184_; size_t v___x_185_; size_t v___x_186_; uint8_t v___x_187_; 
v_typeName_181_ = lean_ctor_get(v_e_108_, 0);
v_idx_182_ = lean_ctor_get(v_e_108_, 1);
v_struct_183_ = lean_ctor_get(v_e_108_, 2);
lean_inc_ref(v_struct_183_);
v_b_184_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__1(v_paramNames_106_, v_lvls_107_, v_struct_183_);
v___x_185_ = lean_ptr_addr(v_struct_183_);
v___x_186_ = lean_ptr_addr(v_b_184_);
v___x_187_ = lean_usize_dec_eq(v___x_185_, v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; 
lean_inc(v_idx_182_);
lean_inc(v_typeName_181_);
lean_dec_ref_known(v_e_108_, 3);
v___x_188_ = l_Lean_Expr_proj___override(v_typeName_181_, v_idx_182_, v_b_184_);
return v___x_188_;
}
else
{
lean_dec_ref(v_b_184_);
return v_e_108_;
}
}
default: 
{
lean_dec(v_lvls_107_);
lean_dec(v_paramNames_106_);
return v_e_108_;
}
}
}
else
{
lean_object* v_val_189_; 
lean_dec_ref(v_e_108_);
lean_dec(v_lvls_107_);
lean_dec(v_paramNames_106_);
v_val_189_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_val_189_);
lean_dec_ref_known(v___x_109_, 1);
return v_val_189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsNoCache(lean_object* v_e_190_, lean_object* v_paramNames_191_, lean_object* v_lvls_192_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = l_List_isEmpty___redArg(v_paramNames_191_);
if (v___x_193_ == 0)
{
uint8_t v___x_194_; 
v___x_194_ = l_List_isEmpty___redArg(v_lvls_192_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__1(v_paramNames_191_, v_lvls_192_, v_e_190_);
return v___x_195_;
}
else
{
lean_dec(v_lvls_192_);
lean_dec(v_paramNames_191_);
return v_e_190_;
}
}
else
{
lean_dec(v_lvls_192_);
lean_dec(v_paramNames_191_);
return v_e_190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(lean_object* v_ps_196_, lean_object* v_us_197_, lean_object* v_p_x27_198_, lean_object* v_i_199_){
_start:
{
lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = lean_array_get_size(v_ps_196_);
v___x_201_ = lean_nat_dec_lt(v_i_199_, v___x_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; 
lean_dec(v_i_199_);
v___x_202_ = lean_box(0);
return v___x_202_;
}
else
{
lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_203_ = lean_array_get_size(v_us_197_);
v___x_204_ = lean_nat_dec_lt(v_i_199_, v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
lean_dec(v_i_199_);
v___x_205_ = lean_box(0);
return v___x_205_;
}
else
{
lean_object* v_p_206_; uint8_t v___x_207_; 
v_p_206_ = lean_array_fget_borrowed(v_ps_196_, v_i_199_);
v___x_207_ = lean_name_eq(v_p_206_, v_p_x27_198_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_unsigned_to_nat(1u);
v___x_209_ = lean_nat_add(v_i_199_, v___x_208_);
lean_dec(v_i_199_);
v_i_199_ = v___x_209_;
goto _start;
}
else
{
lean_object* v_u_211_; lean_object* v___x_212_; 
v_u_211_ = lean_array_fget_borrowed(v_us_197_, v_i_199_);
lean_dec(v_i_199_);
lean_inc(v_u_211_);
v___x_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_212_, 0, v_u_211_);
return v___x_212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray___boxed(lean_object* v_ps_213_, lean_object* v_us_214_, lean_object* v_p_x27_215_, lean_object* v_i_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(v_ps_213_, v_us_214_, v_p_x27_215_, v_i_216_);
lean_dec(v_p_x27_215_);
lean_dec_ref(v_us_214_);
lean_dec_ref(v_ps_213_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0(lean_object* v_paramNames_218_, lean_object* v_lvls_219_, lean_object* v_p_220_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(v_paramNames_218_, v_lvls_219_, v_p_220_, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed(lean_object* v_paramNames_223_, lean_object* v_lvls_224_, lean_object* v_p_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0(v_paramNames_223_, v_lvls_224_, v_p_225_);
lean_dec(v_p_225_);
lean_dec_ref(v_lvls_224_);
lean_dec_ref(v_paramNames_223_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0_spec__1(lean_object* v_paramNames_227_, lean_object* v_lvls_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
if (lean_obj_tag(v_a_229_) == 0)
{
lean_object* v___x_231_; 
lean_dec_ref(v_lvls_228_);
lean_dec_ref(v_paramNames_227_);
v___x_231_ = l_List_reverse___redArg(v_a_230_);
return v___x_231_;
}
else
{
lean_object* v_head_232_; lean_object* v_tail_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_243_; 
v_head_232_ = lean_ctor_get(v_a_229_, 0);
v_tail_233_ = lean_ctor_get(v_a_229_, 1);
v_isSharedCheck_243_ = !lean_is_exclusive(v_a_229_);
if (v_isSharedCheck_243_ == 0)
{
v___x_235_ = v_a_229_;
v_isShared_236_ = v_isSharedCheck_243_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_tail_233_);
lean_inc(v_head_232_);
lean_dec(v_a_229_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_243_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___f_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
lean_inc_ref(v_lvls_228_);
lean_inc_ref(v_paramNames_227_);
v___f_237_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_237_, 0, v_paramNames_227_);
lean_closure_set(v___f_237_, 1, v_lvls_228_);
v___x_238_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___f_237_, v_head_232_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v_a_230_);
lean_ctor_set(v___x_235_, 0, v___x_238_);
v___x_240_ = v___x_235_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_a_230_);
v___x_240_ = v_reuseFailAlloc_242_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
v_a_229_ = v_tail_233_;
v_a_230_ = v___x_240_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0(lean_object* v_paramNames_244_, lean_object* v_lvls_245_, lean_object* v_e_246_){
_start:
{
uint8_t v___x_247_; 
v___x_247_ = l_Lean_Expr_hasLevelParam(v_e_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
lean_dec_ref(v_lvls_245_);
lean_dec_ref(v_paramNames_244_);
v___x_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_248_, 0, v_e_246_);
return v___x_248_;
}
else
{
switch(lean_obj_tag(v_e_246_))
{
case 4:
{
lean_object* v_declName_249_; lean_object* v_us_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v_declName_249_ = lean_ctor_get(v_e_246_, 0);
v_us_250_ = lean_ctor_get(v_e_246_, 1);
v___x_251_ = lean_box(0);
lean_inc(v_us_250_);
v___x_252_ = l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0_spec__1(v_paramNames_244_, v_lvls_245_, v_us_250_, v___x_251_);
v___x_253_ = l_ptrEqList___redArg(v_us_250_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_inc(v_declName_249_);
lean_dec_ref_known(v_e_246_, 2);
v___x_254_ = l_Lean_Expr_const___override(v_declName_249_, v___x_252_);
v___x_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
else
{
lean_object* v___x_256_; 
lean_dec(v___x_252_);
v___x_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_256_, 0, v_e_246_);
return v___x_256_;
}
}
case 3:
{
lean_object* v_u_257_; lean_object* v___f_258_; lean_object* v___x_259_; size_t v___x_260_; size_t v___x_261_; uint8_t v___x_262_; 
v_u_257_ = lean_ctor_get(v_e_246_, 0);
v___f_258_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_258_, 0, v_paramNames_244_);
lean_closure_set(v___f_258_, 1, v_lvls_245_);
lean_inc(v_u_257_);
v___x_259_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___f_258_, v_u_257_);
v___x_260_ = lean_ptr_addr(v_u_257_);
v___x_261_ = lean_ptr_addr(v___x_259_);
v___x_262_ = lean_usize_dec_eq(v___x_260_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec_ref_known(v_e_246_, 1);
v___x_263_ = l_Lean_Expr_sort___override(v___x_259_);
v___x_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; 
lean_dec(v___x_259_);
v___x_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_265_, 0, v_e_246_);
return v___x_265_;
}
}
default: 
{
lean_object* v___x_266_; 
lean_dec_ref(v_e_246_);
lean_dec_ref(v_lvls_245_);
lean_dec_ref(v_paramNames_244_);
v___x_266_ = lean_box(0);
return v___x_266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(lean_object* v_paramNames_267_, lean_object* v_lvls_268_, lean_object* v_e_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0), 3, 2);
lean_closure_set(v___x_270_, 0, v_paramNames_267_);
lean_closure_set(v___x_270_, 1, v_lvls_268_);
v___x_271_ = lean_replace_expr(v___x_270_, v_e_269_);
lean_dec_ref(v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0___boxed(lean_object* v_paramNames_272_, lean_object* v_lvls_273_, lean_object* v_e_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(v_paramNames_272_, v_lvls_273_, v_e_274_);
lean_dec_ref(v_e_274_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object* v_e_276_, lean_object* v_paramNames_277_, lean_object* v_lvls_278_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_279_ = lean_array_get_size(v_paramNames_277_);
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = lean_nat_dec_eq(v___x_279_, v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_282_ = lean_array_get_size(v_lvls_278_);
v___x_283_ = lean_nat_dec_eq(v___x_282_, v___x_280_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(v_paramNames_277_, v_lvls_278_, v_e_276_);
return v___x_284_;
}
else
{
lean_dec_ref(v_lvls_278_);
lean_dec_ref(v_paramNames_277_);
lean_inc_ref(v_e_276_);
return v_e_276_;
}
}
else
{
lean_dec_ref(v_lvls_278_);
lean_dec_ref(v_paramNames_277_);
lean_inc_ref(v_e_276_);
return v_e_276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsArray___boxed(lean_object* v_e_285_, lean_object* v_paramNames_286_, lean_object* v_lvls_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Expr_instantiateLevelParamsArray(v_e_285_, v_paramNames_286_, v_lvls_287_);
lean_dec_ref(v_e_285_);
return v_res_288_;
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
