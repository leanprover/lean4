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
uint8_t lean_bool_not(uint8_t);
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
uint8_t v___x_6_; uint8_t v___x_7_; 
v___x_6_ = l_Lean_Expr_hasLevelParam(v_e_5_);
v___x_7_ = lean_bool_not(v___x_6_);
if (v___x_7_ == 0)
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
else
{
lean_object* v___x_26_; 
lean_dec_ref(v_s_4_);
v___x_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_26_, 0, v_e_5_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore(lean_object* v_s_27_, lean_object* v_e_28_){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn), 2, 1);
lean_closure_set(v___x_29_, 0, v_s_27_);
v___x_30_ = lean_replace_expr(v___x_29_, v_e_28_);
lean_dec_ref(v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___boxed(lean_object* v_s_31_, lean_object* v_e_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Expr_instantiateLevelParamsCore(v_s_31_, v_e_32_);
lean_dec_ref(v_e_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst(lean_object* v_x_34_, lean_object* v_x_35_, lean_object* v_x_36_){
_start:
{
if (lean_obj_tag(v_x_34_) == 1)
{
if (lean_obj_tag(v_x_35_) == 1)
{
lean_object* v_head_37_; lean_object* v_tail_38_; lean_object* v_head_39_; lean_object* v_tail_40_; uint8_t v___x_41_; 
v_head_37_ = lean_ctor_get(v_x_34_, 0);
v_tail_38_ = lean_ctor_get(v_x_34_, 1);
v_head_39_ = lean_ctor_get(v_x_35_, 0);
v_tail_40_ = lean_ctor_get(v_x_35_, 1);
v___x_41_ = lean_name_eq(v_head_37_, v_x_36_);
if (v___x_41_ == 0)
{
v_x_34_ = v_tail_38_;
v_x_35_ = v_tail_40_;
goto _start;
}
else
{
lean_object* v___x_43_; 
lean_inc(v_head_39_);
v___x_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_43_, 0, v_head_39_);
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
else
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst___boxed(lean_object* v_x_46_, lean_object* v_x_47_, lean_object* v_x_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst(v_x_46_, v_x_47_, v_x_48_);
lean_dec(v_x_48_);
lean_dec(v_x_47_);
lean_dec(v_x_46_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0_spec__0_spec__1(lean_object* v_paramNames_50_, lean_object* v_lvls_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
if (lean_obj_tag(v_a_52_) == 0)
{
lean_object* v___x_54_; 
lean_dec(v_lvls_51_);
lean_dec(v_paramNames_50_);
v___x_54_ = l_List_reverse___redArg(v_a_53_);
return v___x_54_;
}
else
{
lean_object* v_head_55_; lean_object* v_tail_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_66_; 
v_head_55_ = lean_ctor_get(v_a_52_, 0);
v_tail_56_ = lean_ctor_get(v_a_52_, 1);
v_isSharedCheck_66_ = !lean_is_exclusive(v_a_52_);
if (v_isSharedCheck_66_ == 0)
{
v___x_58_ = v_a_52_;
v_isShared_59_ = v_isSharedCheck_66_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_tail_56_);
lean_inc(v_head_55_);
lean_dec(v_a_52_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_66_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_63_; 
lean_inc(v_lvls_51_);
lean_inc(v_paramNames_50_);
v___x_60_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst___boxed), 3, 2);
lean_closure_set(v___x_60_, 0, v_paramNames_50_);
lean_closure_set(v___x_60_, 1, v_lvls_51_);
v___x_61_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_60_, v_head_55_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v_a_53_);
lean_ctor_set(v___x_58_, 0, v___x_61_);
v___x_63_ = v___x_58_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_61_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v_a_53_);
v___x_63_ = v_reuseFailAlloc_65_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
v_a_52_ = v_tail_56_;
v_a_53_ = v___x_63_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0_spec__0(lean_object* v_paramNames_67_, lean_object* v_lvls_68_, lean_object* v_e_69_){
_start:
{
uint8_t v___x_70_; uint8_t v___x_71_; 
v___x_70_ = l_Lean_Expr_hasLevelParam(v_e_69_);
v___x_71_ = lean_bool_not(v___x_70_);
if (v___x_71_ == 0)
{
switch(lean_obj_tag(v_e_69_))
{
case 4:
{
lean_object* v_declName_72_; lean_object* v_us_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v_declName_72_ = lean_ctor_get(v_e_69_, 0);
v_us_73_ = lean_ctor_get(v_e_69_, 1);
v___x_74_ = lean_box(0);
lean_inc(v_us_73_);
v___x_75_ = l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0_spec__0_spec__1(v_paramNames_67_, v_lvls_68_, v_us_73_, v___x_74_);
v___x_76_ = l_ptrEqList___redArg(v_us_73_, v___x_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; 
lean_inc(v_declName_72_);
lean_dec_ref_known(v_e_69_, 2);
v___x_77_ = l_Lean_Expr_const___override(v_declName_72_, v___x_75_);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
else
{
lean_object* v___x_79_; 
lean_dec(v___x_75_);
v___x_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_79_, 0, v_e_69_);
return v___x_79_;
}
}
case 3:
{
lean_object* v_u_80_; lean_object* v___x_81_; lean_object* v___x_82_; size_t v___x_83_; size_t v___x_84_; uint8_t v___x_85_; 
v_u_80_ = lean_ctor_get(v_e_69_, 0);
v___x_81_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubst___boxed), 3, 2);
lean_closure_set(v___x_81_, 0, v_paramNames_67_);
lean_closure_set(v___x_81_, 1, v_lvls_68_);
lean_inc(v_u_80_);
v___x_82_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_81_, v_u_80_);
v___x_83_ = lean_ptr_addr(v_u_80_);
v___x_84_ = lean_ptr_addr(v___x_82_);
v___x_85_ = lean_usize_dec_eq(v___x_83_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec_ref_known(v_e_69_, 1);
v___x_86_ = l_Lean_Expr_sort___override(v___x_82_);
v___x_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
return v___x_87_;
}
else
{
lean_object* v___x_88_; 
lean_dec(v___x_82_);
v___x_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_88_, 0, v_e_69_);
return v___x_88_;
}
}
default: 
{
lean_object* v___x_89_; 
lean_dec_ref(v_e_69_);
lean_dec(v_lvls_68_);
lean_dec(v_paramNames_67_);
v___x_89_ = lean_box(0);
return v___x_89_;
}
}
}
else
{
lean_object* v___x_90_; 
lean_dec(v_lvls_68_);
lean_dec(v_paramNames_67_);
v___x_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_90_, 0, v_e_69_);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0(lean_object* v_paramNames_91_, lean_object* v_lvls_92_, lean_object* v_e_93_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0_spec__0), 3, 2);
lean_closure_set(v___x_94_, 0, v_paramNames_91_);
lean_closure_set(v___x_94_, 1, v_lvls_92_);
v___x_95_ = lean_replace_expr(v___x_94_, v_e_93_);
lean_dec_ref(v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0___boxed(lean_object* v_paramNames_96_, lean_object* v_lvls_97_, lean_object* v_e_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0(v_paramNames_96_, v_lvls_97_, v_e_98_);
lean_dec_ref(v_e_98_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParams(lean_object* v_e_100_, lean_object* v_paramNames_101_, lean_object* v_lvls_102_){
_start:
{
uint8_t v___y_104_; uint8_t v___x_106_; 
v___x_106_ = l_List_isEmpty___redArg(v_paramNames_101_);
if (v___x_106_ == 0)
{
uint8_t v___x_107_; 
v___x_107_ = l_List_isEmpty___redArg(v_lvls_102_);
v___y_104_ = v___x_107_;
goto v___jp_103_;
}
else
{
v___y_104_ = v___x_106_;
goto v___jp_103_;
}
v___jp_103_:
{
if (v___y_104_ == 0)
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0(v_paramNames_101_, v_lvls_102_, v_e_100_);
return v___x_105_;
}
else
{
lean_dec(v_lvls_102_);
lean_dec(v_paramNames_101_);
lean_inc_ref(v_e_100_);
return v_e_100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParams___boxed(lean_object* v_e_108_, lean_object* v_paramNames_109_, lean_object* v_lvls_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_Expr_instantiateLevelParams(v_e_108_, v_paramNames_109_, v_lvls_110_);
lean_dec_ref(v_e_108_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(lean_object* v_paramNames_112_, lean_object* v_lvls_113_, lean_object* v_e_114_){
_start:
{
lean_object* v___x_115_; 
lean_inc_ref(v_e_114_);
lean_inc(v_lvls_113_);
lean_inc(v_paramNames_112_);
v___x_115_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParams_spec__0_spec__0(v_paramNames_112_, v_lvls_113_, v_e_114_);
if (lean_obj_tag(v___x_115_) == 0)
{
switch(lean_obj_tag(v_e_114_))
{
case 7:
{
lean_object* v_binderName_116_; lean_object* v_binderType_117_; lean_object* v_body_118_; uint8_t v_binderInfo_119_; lean_object* v_d_120_; lean_object* v_b_121_; uint8_t v___y_123_; size_t v___x_127_; size_t v___x_128_; uint8_t v___x_129_; 
v_binderName_116_ = lean_ctor_get(v_e_114_, 0);
v_binderType_117_ = lean_ctor_get(v_e_114_, 1);
v_body_118_ = lean_ctor_get(v_e_114_, 2);
v_binderInfo_119_ = lean_ctor_get_uint8(v_e_114_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_117_);
lean_inc(v_lvls_113_);
lean_inc(v_paramNames_112_);
v_d_120_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_112_, v_lvls_113_, v_binderType_117_);
lean_inc_ref(v_body_118_);
v_b_121_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_112_, v_lvls_113_, v_body_118_);
v___x_127_ = lean_ptr_addr(v_binderType_117_);
v___x_128_ = lean_ptr_addr(v_d_120_);
v___x_129_ = lean_usize_dec_eq(v___x_127_, v___x_128_);
if (v___x_129_ == 0)
{
v___y_123_ = v___x_129_;
goto v___jp_122_;
}
else
{
size_t v___x_130_; size_t v___x_131_; uint8_t v___x_132_; 
v___x_130_ = lean_ptr_addr(v_body_118_);
v___x_131_ = lean_ptr_addr(v_b_121_);
v___x_132_ = lean_usize_dec_eq(v___x_130_, v___x_131_);
v___y_123_ = v___x_132_;
goto v___jp_122_;
}
v___jp_122_:
{
if (v___y_123_ == 0)
{
lean_object* v___x_124_; 
lean_inc(v_binderName_116_);
lean_dec_ref_known(v_e_114_, 3);
v___x_124_ = l_Lean_Expr_forallE___override(v_binderName_116_, v_d_120_, v_b_121_, v_binderInfo_119_);
return v___x_124_;
}
else
{
uint8_t v___x_125_; 
v___x_125_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_119_, v_binderInfo_119_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
lean_inc(v_binderName_116_);
lean_dec_ref_known(v_e_114_, 3);
v___x_126_ = l_Lean_Expr_forallE___override(v_binderName_116_, v_d_120_, v_b_121_, v_binderInfo_119_);
return v___x_126_;
}
else
{
lean_dec_ref(v_b_121_);
lean_dec_ref(v_d_120_);
return v_e_114_;
}
}
}
}
case 6:
{
lean_object* v_binderName_133_; lean_object* v_binderType_134_; lean_object* v_body_135_; uint8_t v_binderInfo_136_; lean_object* v_d_137_; lean_object* v_b_138_; uint8_t v___y_140_; size_t v___x_144_; size_t v___x_145_; uint8_t v___x_146_; 
v_binderName_133_ = lean_ctor_get(v_e_114_, 0);
v_binderType_134_ = lean_ctor_get(v_e_114_, 1);
v_body_135_ = lean_ctor_get(v_e_114_, 2);
v_binderInfo_136_ = lean_ctor_get_uint8(v_e_114_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_134_);
lean_inc(v_lvls_113_);
lean_inc(v_paramNames_112_);
v_d_137_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_112_, v_lvls_113_, v_binderType_134_);
lean_inc_ref(v_body_135_);
v_b_138_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_112_, v_lvls_113_, v_body_135_);
v___x_144_ = lean_ptr_addr(v_binderType_134_);
v___x_145_ = lean_ptr_addr(v_d_137_);
v___x_146_ = lean_usize_dec_eq(v___x_144_, v___x_145_);
if (v___x_146_ == 0)
{
v___y_140_ = v___x_146_;
goto v___jp_139_;
}
else
{
size_t v___x_147_; size_t v___x_148_; uint8_t v___x_149_; 
v___x_147_ = lean_ptr_addr(v_body_135_);
v___x_148_ = lean_ptr_addr(v_b_138_);
v___x_149_ = lean_usize_dec_eq(v___x_147_, v___x_148_);
v___y_140_ = v___x_149_;
goto v___jp_139_;
}
v___jp_139_:
{
if (v___y_140_ == 0)
{
lean_object* v___x_141_; 
lean_inc(v_binderName_133_);
lean_dec_ref_known(v_e_114_, 3);
v___x_141_ = l_Lean_Expr_lam___override(v_binderName_133_, v_d_137_, v_b_138_, v_binderInfo_136_);
return v___x_141_;
}
else
{
uint8_t v___x_142_; 
v___x_142_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_136_, v_binderInfo_136_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
lean_inc(v_binderName_133_);
lean_dec_ref_known(v_e_114_, 3);
v___x_143_ = l_Lean_Expr_lam___override(v_binderName_133_, v_d_137_, v_b_138_, v_binderInfo_136_);
return v___x_143_;
}
else
{
lean_dec_ref(v_b_138_);
lean_dec_ref(v_d_137_);
return v_e_114_;
}
}
}
}
case 10:
{
lean_object* v_data_150_; lean_object* v_expr_151_; lean_object* v_b_152_; size_t v___x_153_; size_t v___x_154_; uint8_t v___x_155_; 
v_data_150_ = lean_ctor_get(v_e_114_, 0);
v_expr_151_ = lean_ctor_get(v_e_114_, 1);
lean_inc_ref(v_expr_151_);
v_b_152_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_112_, v_lvls_113_, v_expr_151_);
v___x_153_ = lean_ptr_addr(v_expr_151_);
v___x_154_ = lean_ptr_addr(v_b_152_);
v___x_155_ = lean_usize_dec_eq(v___x_153_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; 
lean_inc(v_data_150_);
lean_dec_ref_known(v_e_114_, 2);
v___x_156_ = l_Lean_Expr_mdata___override(v_data_150_, v_b_152_);
return v___x_156_;
}
else
{
lean_dec_ref(v_b_152_);
return v_e_114_;
}
}
case 8:
{
lean_object* v_declName_157_; lean_object* v_type_158_; lean_object* v_value_159_; lean_object* v_body_160_; uint8_t v_nondep_161_; lean_object* v_t_162_; lean_object* v_v_163_; lean_object* v_b_164_; uint8_t v___y_166_; size_t v___x_172_; size_t v___x_173_; uint8_t v___x_174_; 
v_declName_157_ = lean_ctor_get(v_e_114_, 0);
v_type_158_ = lean_ctor_get(v_e_114_, 1);
v_value_159_ = lean_ctor_get(v_e_114_, 2);
v_body_160_ = lean_ctor_get(v_e_114_, 3);
v_nondep_161_ = lean_ctor_get_uint8(v_e_114_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_158_);
lean_inc_n(v_lvls_113_, 2);
lean_inc_n(v_paramNames_112_, 2);
v_t_162_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_112_, v_lvls_113_, v_type_158_);
lean_inc_ref(v_value_159_);
v_v_163_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_112_, v_lvls_113_, v_value_159_);
lean_inc_ref(v_body_160_);
v_b_164_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_112_, v_lvls_113_, v_body_160_);
v___x_172_ = lean_ptr_addr(v_type_158_);
v___x_173_ = lean_ptr_addr(v_t_162_);
v___x_174_ = lean_usize_dec_eq(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
v___y_166_ = v___x_174_;
goto v___jp_165_;
}
else
{
size_t v___x_175_; size_t v___x_176_; uint8_t v___x_177_; 
v___x_175_ = lean_ptr_addr(v_value_159_);
v___x_176_ = lean_ptr_addr(v_v_163_);
v___x_177_ = lean_usize_dec_eq(v___x_175_, v___x_176_);
v___y_166_ = v___x_177_;
goto v___jp_165_;
}
v___jp_165_:
{
if (v___y_166_ == 0)
{
lean_object* v___x_167_; 
lean_inc(v_declName_157_);
lean_dec_ref_known(v_e_114_, 4);
v___x_167_ = l_Lean_Expr_letE___override(v_declName_157_, v_t_162_, v_v_163_, v_b_164_, v_nondep_161_);
return v___x_167_;
}
else
{
size_t v___x_168_; size_t v___x_169_; uint8_t v___x_170_; 
v___x_168_ = lean_ptr_addr(v_body_160_);
v___x_169_ = lean_ptr_addr(v_b_164_);
v___x_170_ = lean_usize_dec_eq(v___x_168_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; 
lean_inc(v_declName_157_);
lean_dec_ref_known(v_e_114_, 4);
v___x_171_ = l_Lean_Expr_letE___override(v_declName_157_, v_t_162_, v_v_163_, v_b_164_, v_nondep_161_);
return v___x_171_;
}
else
{
lean_dec_ref(v_b_164_);
lean_dec_ref(v_v_163_);
lean_dec_ref(v_t_162_);
return v_e_114_;
}
}
}
}
case 5:
{
lean_object* v_fn_178_; lean_object* v_arg_179_; lean_object* v_f_180_; lean_object* v_a_181_; uint8_t v___y_183_; size_t v___x_185_; size_t v___x_186_; uint8_t v___x_187_; 
v_fn_178_ = lean_ctor_get(v_e_114_, 0);
v_arg_179_ = lean_ctor_get(v_e_114_, 1);
lean_inc_ref(v_fn_178_);
lean_inc(v_lvls_113_);
lean_inc(v_paramNames_112_);
v_f_180_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_112_, v_lvls_113_, v_fn_178_);
lean_inc_ref(v_arg_179_);
v_a_181_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_112_, v_lvls_113_, v_arg_179_);
v___x_185_ = lean_ptr_addr(v_fn_178_);
v___x_186_ = lean_ptr_addr(v_f_180_);
v___x_187_ = lean_usize_dec_eq(v___x_185_, v___x_186_);
if (v___x_187_ == 0)
{
v___y_183_ = v___x_187_;
goto v___jp_182_;
}
else
{
size_t v___x_188_; size_t v___x_189_; uint8_t v___x_190_; 
v___x_188_ = lean_ptr_addr(v_arg_179_);
v___x_189_ = lean_ptr_addr(v_a_181_);
v___x_190_ = lean_usize_dec_eq(v___x_188_, v___x_189_);
v___y_183_ = v___x_190_;
goto v___jp_182_;
}
v___jp_182_:
{
if (v___y_183_ == 0)
{
lean_object* v___x_184_; 
lean_dec_ref_known(v_e_114_, 2);
v___x_184_ = l_Lean_Expr_app___override(v_f_180_, v_a_181_);
return v___x_184_;
}
else
{
lean_dec_ref(v_a_181_);
lean_dec_ref(v_f_180_);
return v_e_114_;
}
}
}
case 11:
{
lean_object* v_typeName_191_; lean_object* v_idx_192_; lean_object* v_struct_193_; lean_object* v_b_194_; size_t v___x_195_; size_t v___x_196_; uint8_t v___x_197_; 
v_typeName_191_ = lean_ctor_get(v_e_114_, 0);
v_idx_192_ = lean_ctor_get(v_e_114_, 1);
v_struct_193_ = lean_ctor_get(v_e_114_, 2);
lean_inc_ref(v_struct_193_);
v_b_194_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_112_, v_lvls_113_, v_struct_193_);
v___x_195_ = lean_ptr_addr(v_struct_193_);
v___x_196_ = lean_ptr_addr(v_b_194_);
v___x_197_ = lean_usize_dec_eq(v___x_195_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
lean_inc(v_idx_192_);
lean_inc(v_typeName_191_);
lean_dec_ref_known(v_e_114_, 3);
v___x_198_ = l_Lean_Expr_proj___override(v_typeName_191_, v_idx_192_, v_b_194_);
return v___x_198_;
}
else
{
lean_dec_ref(v_b_194_);
return v_e_114_;
}
}
default: 
{
lean_dec(v_lvls_113_);
lean_dec(v_paramNames_112_);
return v_e_114_;
}
}
}
else
{
lean_object* v_val_199_; 
lean_dec_ref(v_e_114_);
lean_dec(v_lvls_113_);
lean_dec(v_paramNames_112_);
v_val_199_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_val_199_);
lean_dec_ref_known(v___x_115_, 1);
return v_val_199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsNoCache(lean_object* v_e_200_, lean_object* v_paramNames_201_, lean_object* v_lvls_202_){
_start:
{
uint8_t v___y_204_; uint8_t v___x_206_; 
v___x_206_ = l_List_isEmpty___redArg(v_paramNames_201_);
if (v___x_206_ == 0)
{
uint8_t v___x_207_; 
v___x_207_ = l_List_isEmpty___redArg(v_lvls_202_);
v___y_204_ = v___x_207_;
goto v___jp_203_;
}
else
{
v___y_204_ = v___x_206_;
goto v___jp_203_;
}
v___jp_203_:
{
if (v___y_204_ == 0)
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Expr_replaceNoCache___at___00Lean_Expr_instantiateLevelParamsNoCache_spec__0(v_paramNames_201_, v_lvls_202_, v_e_200_);
return v___x_205_;
}
else
{
lean_dec(v_lvls_202_);
lean_dec(v_paramNames_201_);
return v_e_200_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(lean_object* v_ps_208_, lean_object* v_us_209_, lean_object* v_p_x27_210_, lean_object* v_i_211_){
_start:
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = lean_array_get_size(v_ps_208_);
v___x_213_ = lean_nat_dec_lt(v_i_211_, v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; 
lean_dec(v_i_211_);
v___x_214_ = lean_box(0);
return v___x_214_;
}
else
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = lean_array_get_size(v_us_209_);
v___x_216_ = lean_nat_dec_lt(v_i_211_, v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; 
lean_dec(v_i_211_);
v___x_217_ = lean_box(0);
return v___x_217_;
}
else
{
lean_object* v_p_218_; uint8_t v___x_219_; 
v_p_218_ = lean_array_fget_borrowed(v_ps_208_, v_i_211_);
v___x_219_ = lean_name_eq(v_p_218_, v_p_x27_210_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_unsigned_to_nat(1u);
v___x_221_ = lean_nat_add(v_i_211_, v___x_220_);
lean_dec(v_i_211_);
v_i_211_ = v___x_221_;
goto _start;
}
else
{
lean_object* v_u_223_; lean_object* v___x_224_; 
v_u_223_ = lean_array_fget_borrowed(v_us_209_, v_i_211_);
lean_dec(v_i_211_);
lean_inc(v_u_223_);
v___x_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_224_, 0, v_u_223_);
return v___x_224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray___boxed(lean_object* v_ps_225_, lean_object* v_us_226_, lean_object* v_p_x27_227_, lean_object* v_i_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(v_ps_225_, v_us_226_, v_p_x27_227_, v_i_228_);
lean_dec(v_p_x27_227_);
lean_dec_ref(v_us_226_);
lean_dec_ref(v_ps_225_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0(lean_object* v_paramNames_230_, lean_object* v_lvls_231_, lean_object* v_p_232_){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_getParamSubstArray(v_paramNames_230_, v_lvls_231_, v_p_232_, v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed(lean_object* v_paramNames_235_, lean_object* v_lvls_236_, lean_object* v_p_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0(v_paramNames_235_, v_lvls_236_, v_p_237_);
lean_dec(v_p_237_);
lean_dec_ref(v_lvls_236_);
lean_dec_ref(v_paramNames_235_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0_spec__1(lean_object* v_paramNames_239_, lean_object* v_lvls_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
if (lean_obj_tag(v_a_241_) == 0)
{
lean_object* v___x_243_; 
lean_dec_ref(v_lvls_240_);
lean_dec_ref(v_paramNames_239_);
v___x_243_ = l_List_reverse___redArg(v_a_242_);
return v___x_243_;
}
else
{
lean_object* v_head_244_; lean_object* v_tail_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_255_; 
v_head_244_ = lean_ctor_get(v_a_241_, 0);
v_tail_245_ = lean_ctor_get(v_a_241_, 1);
v_isSharedCheck_255_ = !lean_is_exclusive(v_a_241_);
if (v_isSharedCheck_255_ == 0)
{
v___x_247_ = v_a_241_;
v_isShared_248_ = v_isSharedCheck_255_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_tail_245_);
lean_inc(v_head_244_);
lean_dec(v_a_241_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_255_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___f_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
lean_inc_ref(v_lvls_240_);
lean_inc_ref(v_paramNames_239_);
v___f_249_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_249_, 0, v_paramNames_239_);
lean_closure_set(v___f_249_, 1, v_lvls_240_);
v___x_250_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___f_249_, v_head_244_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 1, v_a_242_);
lean_ctor_set(v___x_247_, 0, v___x_250_);
v___x_252_ = v___x_247_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_a_242_);
v___x_252_ = v_reuseFailAlloc_254_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
v_a_241_ = v_tail_245_;
v_a_242_ = v___x_252_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0(lean_object* v_paramNames_256_, lean_object* v_lvls_257_, lean_object* v_e_258_){
_start:
{
uint8_t v___x_259_; uint8_t v___x_260_; 
v___x_259_ = l_Lean_Expr_hasLevelParam(v_e_258_);
v___x_260_ = lean_bool_not(v___x_259_);
if (v___x_260_ == 0)
{
switch(lean_obj_tag(v_e_258_))
{
case 4:
{
lean_object* v_declName_261_; lean_object* v_us_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_declName_261_ = lean_ctor_get(v_e_258_, 0);
v_us_262_ = lean_ctor_get(v_e_258_, 1);
v___x_263_ = lean_box(0);
lean_inc(v_us_262_);
v___x_264_ = l_List_mapTR_loop___at___00__private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0_spec__1(v_paramNames_256_, v_lvls_257_, v_us_262_, v___x_263_);
v___x_265_ = l_ptrEqList___redArg(v_us_262_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; 
lean_inc(v_declName_261_);
lean_dec_ref_known(v_e_258_, 2);
v___x_266_ = l_Lean_Expr_const___override(v_declName_261_, v___x_264_);
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; 
lean_dec(v___x_264_);
v___x_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_268_, 0, v_e_258_);
return v___x_268_;
}
}
case 3:
{
lean_object* v_u_269_; lean_object* v___f_270_; lean_object* v___x_271_; size_t v___x_272_; size_t v___x_273_; uint8_t v___x_274_; 
v_u_269_ = lean_ctor_get(v_e_258_, 0);
v___f_270_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_270_, 0, v_paramNames_256_);
lean_closure_set(v___f_270_, 1, v_lvls_257_);
lean_inc(v_u_269_);
v___x_271_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___f_270_, v_u_269_);
v___x_272_ = lean_ptr_addr(v_u_269_);
v___x_273_ = lean_ptr_addr(v___x_271_);
v___x_274_ = lean_usize_dec_eq(v___x_272_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
lean_dec_ref_known(v_e_258_, 1);
v___x_275_ = l_Lean_Expr_sort___override(v___x_271_);
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
else
{
lean_object* v___x_277_; 
lean_dec(v___x_271_);
v___x_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_277_, 0, v_e_258_);
return v___x_277_;
}
}
default: 
{
lean_object* v___x_278_; 
lean_dec_ref(v_e_258_);
lean_dec_ref(v_lvls_257_);
lean_dec_ref(v_paramNames_256_);
v___x_278_ = lean_box(0);
return v___x_278_;
}
}
}
else
{
lean_object* v___x_279_; 
lean_dec_ref(v_lvls_257_);
lean_dec_ref(v_paramNames_256_);
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v_e_258_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(lean_object* v_paramNames_280_, lean_object* v_lvls_281_, lean_object* v_e_282_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_alloc_closure((void*)(l___private_Lean_Util_InstantiateLevelParams_0__Lean_Expr_instantiateLevelParamsCore_replaceFn___at___00Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0_spec__0), 3, 2);
lean_closure_set(v___x_283_, 0, v_paramNames_280_);
lean_closure_set(v___x_283_, 1, v_lvls_281_);
v___x_284_ = lean_replace_expr(v___x_283_, v_e_282_);
lean_dec_ref(v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0___boxed(lean_object* v_paramNames_285_, lean_object* v_lvls_286_, lean_object* v_e_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(v_paramNames_285_, v_lvls_286_, v_e_287_);
lean_dec_ref(v_e_287_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object* v_e_289_, lean_object* v_paramNames_290_, lean_object* v_lvls_291_){
_start:
{
uint8_t v___y_293_; lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_295_ = lean_array_get_size(v_paramNames_290_);
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_nat_dec_eq(v___x_295_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = lean_array_get_size(v_lvls_291_);
v___x_299_ = lean_nat_dec_eq(v___x_298_, v___x_296_);
v___y_293_ = v___x_299_;
goto v___jp_292_;
}
else
{
v___y_293_ = v___x_297_;
goto v___jp_292_;
}
v___jp_292_:
{
if (v___y_293_ == 0)
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Expr_instantiateLevelParamsCore___at___00Lean_Expr_instantiateLevelParamsArray_spec__0(v_paramNames_290_, v_lvls_291_, v_e_289_);
return v___x_294_;
}
else
{
lean_dec_ref(v_lvls_291_);
lean_dec_ref(v_paramNames_290_);
lean_inc_ref(v_e_289_);
return v_e_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsArray___boxed(lean_object* v_e_300_, lean_object* v_paramNames_301_, lean_object* v_lvls_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Expr_instantiateLevelParamsArray(v_e_300_, v_paramNames_301_, v_lvls_302_);
lean_dec_ref(v_e_300_);
return v_res_303_;
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
