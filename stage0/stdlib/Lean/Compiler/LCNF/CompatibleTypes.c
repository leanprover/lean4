// Lean compiler output
// Module: Lean.Compiler.LCNF.CompatibleTypes
// Imports: public import Lean.Compiler.LCNF.InferType
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
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_compatibleTypesQuick(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compatibleTypesQuick___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
else
{
uint8_t v___x_4_; 
v___x_4_ = 0;
return v___x_4_;
}
}
else
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_5_; 
v___x_5_ = 0;
return v___x_5_;
}
else
{
lean_object* v_head_6_; lean_object* v_tail_7_; lean_object* v_head_8_; lean_object* v_tail_9_; uint8_t v___x_10_; 
v_head_6_ = lean_ctor_get(v_x_1_, 0);
v_tail_7_ = lean_ctor_get(v_x_1_, 1);
v_head_8_ = lean_ctor_get(v_x_2_, 0);
v_tail_9_ = lean_ctor_get(v_x_2_, 1);
v___x_10_ = l_Lean_Level_isEquiv(v_head_6_, v_head_8_);
if (v___x_10_ == 0)
{
return v___x_10_;
}
else
{
v_x_1_ = v_tail_7_;
v_x_2_ = v_tail_9_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0___boxed(lean_object* v_x_12_, lean_object* v_x_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(v_x_12_, v_x_13_);
lean_dec(v_x_13_);
lean_dec(v_x_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_compatibleTypesQuick(lean_object* v_a_16_, lean_object* v_b_17_){
_start:
{
uint8_t v___y_19_; lean_object* v_d_u2081_20_; lean_object* v_b_u2081_21_; lean_object* v_d_u2082_22_; lean_object* v_b_u2082_23_; uint8_t v___y_27_; uint8_t v___x_59_; 
v___x_59_ = l_Lean_Expr_isErased(v_a_16_);
if (v___x_59_ == 0)
{
uint8_t v___x_60_; 
v___x_60_ = l_Lean_Expr_isErased(v_b_17_);
v___y_27_ = v___x_60_;
goto v___jp_26_;
}
else
{
v___y_27_ = v___x_59_;
goto v___jp_26_;
}
v___jp_18_:
{
uint8_t v___x_24_; 
v___x_24_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_d_u2081_20_, v_d_u2082_22_);
if (v___x_24_ == 0)
{
lean_dec_ref(v_b_u2082_23_);
lean_dec_ref(v_b_u2081_21_);
return v___y_19_;
}
else
{
v_a_16_ = v_b_u2081_21_;
v_b_17_ = v_b_u2082_23_;
goto _start;
}
}
v___jp_26_:
{
uint8_t v___x_28_; 
v___x_28_ = 1;
if (v___y_27_ == 0)
{
lean_object* v_a_x27_29_; lean_object* v_b_x27_30_; uint8_t v___x_31_; 
lean_inc_ref(v_a_16_);
v_a_x27_29_ = l_Lean_Expr_headBeta(v_a_16_);
lean_inc_ref(v_b_17_);
v_b_x27_30_ = l_Lean_Expr_headBeta(v_b_17_);
v___x_31_ = lean_expr_eqv(v_a_16_, v_a_x27_29_);
if (v___x_31_ == 0)
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
v_a_16_ = v_a_x27_29_;
v_b_17_ = v_b_x27_30_;
goto _start;
}
else
{
uint8_t v___x_33_; 
v___x_33_ = lean_expr_eqv(v_b_17_, v_b_x27_30_);
if (v___x_33_ == 0)
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
v_a_16_ = v_a_x27_29_;
v_b_17_ = v_b_x27_30_;
goto _start;
}
else
{
uint8_t v___x_35_; 
lean_dec_ref(v_b_x27_30_);
lean_dec_ref(v_a_x27_29_);
v___x_35_ = lean_expr_eqv(v_a_16_, v_b_17_);
if (v___x_35_ == 0)
{
switch(lean_obj_tag(v_a_16_))
{
case 5:
{
if (lean_obj_tag(v_b_17_) == 5)
{
lean_object* v_fn_36_; lean_object* v_arg_37_; lean_object* v_fn_38_; lean_object* v_arg_39_; uint8_t v___x_40_; 
v_fn_36_ = lean_ctor_get(v_a_16_, 0);
lean_inc_ref(v_fn_36_);
v_arg_37_ = lean_ctor_get(v_a_16_, 1);
lean_inc_ref(v_arg_37_);
lean_dec_ref_known(v_a_16_, 2);
v_fn_38_ = lean_ctor_get(v_b_17_, 0);
lean_inc_ref(v_fn_38_);
v_arg_39_ = lean_ctor_get(v_b_17_, 1);
lean_inc_ref(v_arg_39_);
lean_dec_ref_known(v_b_17_, 2);
v___x_40_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_fn_36_, v_fn_38_);
if (v___x_40_ == 0)
{
lean_dec_ref(v_arg_39_);
lean_dec_ref(v_arg_37_);
return v___x_35_;
}
else
{
v_a_16_ = v_arg_37_;
v_b_17_ = v_arg_39_;
goto _start;
}
}
else
{
lean_dec_ref_known(v_a_16_, 2);
lean_dec_ref(v_b_17_);
return v___x_35_;
}
}
case 7:
{
if (lean_obj_tag(v_b_17_) == 7)
{
lean_object* v_binderType_42_; lean_object* v_body_43_; lean_object* v_binderType_44_; lean_object* v_body_45_; 
v_binderType_42_ = lean_ctor_get(v_a_16_, 1);
lean_inc_ref(v_binderType_42_);
v_body_43_ = lean_ctor_get(v_a_16_, 2);
lean_inc_ref(v_body_43_);
lean_dec_ref_known(v_a_16_, 3);
v_binderType_44_ = lean_ctor_get(v_b_17_, 1);
lean_inc_ref(v_binderType_44_);
v_body_45_ = lean_ctor_get(v_b_17_, 2);
lean_inc_ref(v_body_45_);
lean_dec_ref_known(v_b_17_, 3);
v___y_19_ = v___x_35_;
v_d_u2081_20_ = v_binderType_42_;
v_b_u2081_21_ = v_body_43_;
v_d_u2082_22_ = v_binderType_44_;
v_b_u2082_23_ = v_body_45_;
goto v___jp_18_;
}
else
{
lean_dec_ref_known(v_a_16_, 3);
lean_dec_ref(v_b_17_);
return v___x_35_;
}
}
case 6:
{
if (lean_obj_tag(v_b_17_) == 6)
{
lean_object* v_binderType_46_; lean_object* v_body_47_; lean_object* v_binderType_48_; lean_object* v_body_49_; 
v_binderType_46_ = lean_ctor_get(v_a_16_, 1);
lean_inc_ref(v_binderType_46_);
v_body_47_ = lean_ctor_get(v_a_16_, 2);
lean_inc_ref(v_body_47_);
lean_dec_ref_known(v_a_16_, 3);
v_binderType_48_ = lean_ctor_get(v_b_17_, 1);
lean_inc_ref(v_binderType_48_);
v_body_49_ = lean_ctor_get(v_b_17_, 2);
lean_inc_ref(v_body_49_);
lean_dec_ref_known(v_b_17_, 3);
v___y_19_ = v___x_35_;
v_d_u2081_20_ = v_binderType_46_;
v_b_u2081_21_ = v_body_47_;
v_d_u2082_22_ = v_binderType_48_;
v_b_u2082_23_ = v_body_49_;
goto v___jp_18_;
}
else
{
lean_dec_ref_known(v_a_16_, 3);
lean_dec_ref(v_b_17_);
return v___x_35_;
}
}
case 3:
{
if (lean_obj_tag(v_b_17_) == 3)
{
lean_object* v_u_50_; lean_object* v_u_51_; uint8_t v___x_52_; 
v_u_50_ = lean_ctor_get(v_a_16_, 0);
lean_inc(v_u_50_);
lean_dec_ref_known(v_a_16_, 1);
v_u_51_ = lean_ctor_get(v_b_17_, 0);
lean_inc(v_u_51_);
lean_dec_ref_known(v_b_17_, 1);
v___x_52_ = l_Lean_Level_isEquiv(v_u_50_, v_u_51_);
lean_dec(v_u_51_);
lean_dec(v_u_50_);
return v___x_52_;
}
else
{
lean_dec_ref_known(v_a_16_, 1);
lean_dec_ref(v_b_17_);
return v___x_35_;
}
}
case 4:
{
if (lean_obj_tag(v_b_17_) == 4)
{
lean_object* v_declName_53_; lean_object* v_us_54_; lean_object* v_declName_55_; lean_object* v_us_56_; uint8_t v___x_57_; 
v_declName_53_ = lean_ctor_get(v_a_16_, 0);
lean_inc(v_declName_53_);
v_us_54_ = lean_ctor_get(v_a_16_, 1);
lean_inc(v_us_54_);
lean_dec_ref_known(v_a_16_, 2);
v_declName_55_ = lean_ctor_get(v_b_17_, 0);
lean_inc(v_declName_55_);
v_us_56_ = lean_ctor_get(v_b_17_, 1);
lean_inc(v_us_56_);
lean_dec_ref_known(v_b_17_, 2);
v___x_57_ = lean_name_eq(v_declName_53_, v_declName_55_);
lean_dec(v_declName_55_);
lean_dec(v_declName_53_);
if (v___x_57_ == 0)
{
lean_dec(v_us_56_);
lean_dec(v_us_54_);
return v___x_35_;
}
else
{
uint8_t v___x_58_; 
v___x_58_ = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(v_us_54_, v_us_56_);
lean_dec(v_us_56_);
lean_dec(v_us_54_);
return v___x_58_;
}
}
else
{
lean_dec_ref_known(v_a_16_, 2);
lean_dec_ref(v_b_17_);
return v___x_35_;
}
}
default: 
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
return v___x_35_;
}
}
}
else
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
return v___x_28_;
}
}
}
}
else
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
return v___x_28_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compatibleTypesQuick___boxed(lean_object* v_a_61_, lean_object* v_b_62_){
_start:
{
uint8_t v_res_63_; lean_object* v_r_64_; 
v_res_63_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_a_61_, v_b_62_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = l_Lean_Expr_bvar___override(v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(lean_object* v_e_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_74_; 
lean_inc_ref(v_e_67_);
v___x_74_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_94_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_94_ == 0)
{
v___x_77_ = v___x_74_;
v_isShared_78_ = v_isSharedCheck_94_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_94_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Expr_headBeta(v_a_75_);
if (lean_obj_tag(v___x_79_) == 7)
{
lean_object* v_binderName_80_; lean_object* v_binderType_81_; uint8_t v_binderInfo_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_88_; 
v_binderName_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_binderName_80_);
v_binderType_81_ = lean_ctor_get(v___x_79_, 1);
lean_inc_ref(v_binderType_81_);
v_binderInfo_82_ = lean_ctor_get_uint8(v___x_79_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_79_, 3);
v___x_83_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0, &l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0_once, _init_l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0);
v___x_84_ = l_Lean_Expr_app___override(v_e_67_, v___x_83_);
v___x_85_ = l_Lean_Expr_lam___override(v_binderName_80_, v_binderType_81_, v___x_84_, v_binderInfo_82_);
v___x_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_86_);
v___x_88_ = v___x_77_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
else
{
lean_object* v___x_90_; lean_object* v___x_92_; 
lean_dec_ref(v___x_79_);
lean_dec_ref(v_e_67_);
v___x_90_ = lean_box(0);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_90_);
v___x_92_ = v___x_77_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_90_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
else
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
lean_dec_ref(v_e_67_);
v_a_95_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v___x_74_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_74_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___boxed(lean_object* v_e_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_e_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec_ref(v_a_104_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(lean_object* v___y_111_){
_start:
{
lean_object* v___x_113_; lean_object* v_ngen_114_; lean_object* v_namePrefix_115_; lean_object* v_idx_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_146_; 
v___x_113_ = lean_st_ref_get(v___y_111_);
v_ngen_114_ = lean_ctor_get(v___x_113_, 2);
lean_inc_ref(v_ngen_114_);
lean_dec(v___x_113_);
v_namePrefix_115_ = lean_ctor_get(v_ngen_114_, 0);
v_idx_116_ = lean_ctor_get(v_ngen_114_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_ngen_114_);
if (v_isSharedCheck_146_ == 0)
{
v___x_118_ = v_ngen_114_;
v_isShared_119_ = v_isSharedCheck_146_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_idx_116_);
lean_inc(v_namePrefix_115_);
lean_dec(v_ngen_114_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_146_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v_r_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
lean_inc(v_idx_116_);
lean_inc(v_namePrefix_115_);
v_r_120_ = l_Lean_Name_num___override(v_namePrefix_115_, v_idx_116_);
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = lean_nat_add(v_idx_116_, v___x_121_);
lean_dec(v_idx_116_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v___x_122_);
v___x_124_ = v___x_118_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_namePrefix_115_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v___x_122_);
v___x_124_ = v_reuseFailAlloc_145_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_125_; lean_object* v_env_126_; lean_object* v_nextMacroScope_127_; lean_object* v_auxDeclNGen_128_; lean_object* v_traceState_129_; lean_object* v_cache_130_; lean_object* v_recordedDeps_131_; lean_object* v_messages_132_; lean_object* v_infoState_133_; lean_object* v_snapshotTasks_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_143_; 
v___x_125_ = lean_st_ref_take(v___y_111_);
v_env_126_ = lean_ctor_get(v___x_125_, 0);
v_nextMacroScope_127_ = lean_ctor_get(v___x_125_, 1);
v_auxDeclNGen_128_ = lean_ctor_get(v___x_125_, 3);
v_traceState_129_ = lean_ctor_get(v___x_125_, 4);
v_cache_130_ = lean_ctor_get(v___x_125_, 5);
v_recordedDeps_131_ = lean_ctor_get(v___x_125_, 6);
v_messages_132_ = lean_ctor_get(v___x_125_, 7);
v_infoState_133_ = lean_ctor_get(v___x_125_, 8);
v_snapshotTasks_134_ = lean_ctor_get(v___x_125_, 9);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; 
v_unused_144_ = lean_ctor_get(v___x_125_, 2);
lean_dec(v_unused_144_);
v___x_136_ = v___x_125_;
v_isShared_137_ = v_isSharedCheck_143_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_snapshotTasks_134_);
lean_inc(v_infoState_133_);
lean_inc(v_messages_132_);
lean_inc(v_recordedDeps_131_);
lean_inc(v_cache_130_);
lean_inc(v_traceState_129_);
lean_inc(v_auxDeclNGen_128_);
lean_inc(v_nextMacroScope_127_);
lean_inc(v_env_126_);
lean_dec(v___x_125_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_143_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 2, v___x_124_);
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_env_126_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_nextMacroScope_127_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_142_, 3, v_auxDeclNGen_128_);
lean_ctor_set(v_reuseFailAlloc_142_, 4, v_traceState_129_);
lean_ctor_set(v_reuseFailAlloc_142_, 5, v_cache_130_);
lean_ctor_set(v_reuseFailAlloc_142_, 6, v_recordedDeps_131_);
lean_ctor_set(v_reuseFailAlloc_142_, 7, v_messages_132_);
lean_ctor_set(v_reuseFailAlloc_142_, 8, v_infoState_133_);
lean_ctor_set(v_reuseFailAlloc_142_, 9, v_snapshotTasks_134_);
v___x_139_ = v_reuseFailAlloc_142_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_st_ref_put(v___y_111_, v___x_139_);
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v_r_120_);
return v___x_141_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg___boxed(lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(v___y_147_);
lean_dec(v___y_147_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___x_156_; lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
v___x_156_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(v___y_154_);
v_a_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0___boxed(lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec_ref(v___y_165_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(lean_object* v_a_172_, lean_object* v_b_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_n_181_; lean_object* v_d_u2081_182_; lean_object* v_b_u2081_183_; uint8_t v_bi_184_; lean_object* v_d_u2082_185_; lean_object* v_b_u2082_186_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___y_191_; uint8_t v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; uint8_t v___y_263_; uint8_t v___x_325_; 
v___x_325_ = l_Lean_Expr_isErased(v_a_172_);
if (v___x_325_ == 0)
{
uint8_t v___x_326_; 
v___x_326_ = l_Lean_Expr_isErased(v_b_173_);
v___y_263_ = v___x_326_;
goto v___jp_262_;
}
else
{
v___y_263_ = v___x_325_;
goto v___jp_262_;
}
v___jp_180_:
{
lean_object* v___x_192_; 
lean_inc_ref(v___y_187_);
lean_inc_ref(v_d_u2081_182_);
v___x_192_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_d_u2081_182_, v_d_u2082_185_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; uint8_t v___x_194_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_a_193_);
v___x_194_ = lean_unbox(v_a_193_);
lean_dec(v_a_193_);
if (v___x_194_ == 0)
{
lean_dec_ref(v___y_187_);
lean_dec_ref(v_b_u2082_186_);
lean_dec_ref(v_b_u2081_183_);
lean_dec_ref(v_d_u2081_182_);
lean_dec(v_n_181_);
return v___x_192_;
}
else
{
lean_object* v___x_195_; 
lean_dec_ref_known(v___x_192_, 1);
v___x_195_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_197_; uint8_t v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc_n(v_a_196_, 2);
lean_dec_ref_known(v___x_195_, 1);
v___x_197_ = l_Lean_Expr_fvar___override(v_a_196_);
v___x_198_ = 0;
v___x_199_ = l_Lean_LocalContext_mkLocalDecl(v___y_187_, v_a_196_, v_n_181_, v_d_u2081_182_, v_bi_184_, v___x_198_);
v___x_200_ = lean_expr_instantiate1(v_b_u2081_183_, v___x_197_);
lean_dec_ref(v_b_u2081_183_);
v___x_201_ = lean_expr_instantiate1(v_b_u2082_186_, v___x_197_);
lean_dec_ref(v___x_197_);
lean_dec_ref(v_b_u2082_186_);
v_a_172_ = v___x_200_;
v_b_173_ = v___x_201_;
v_a_174_ = v___x_199_;
v_a_175_ = v___y_188_;
v_a_176_ = v___y_189_;
v_a_177_ = v___y_190_;
v_a_178_ = v___y_191_;
goto _start;
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
lean_dec_ref(v___y_187_);
lean_dec_ref(v_b_u2082_186_);
lean_dec_ref(v_b_u2081_183_);
lean_dec_ref(v_d_u2081_182_);
lean_dec(v_n_181_);
v_a_203_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_195_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_195_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_187_);
lean_dec_ref(v_b_u2082_186_);
lean_dec_ref(v_b_u2081_183_);
lean_dec_ref(v_d_u2081_182_);
lean_dec(v_n_181_);
return v___x_192_;
}
}
v___jp_211_:
{
uint8_t v___x_218_; 
v___x_218_ = l_Lean_Expr_isLambda(v_a_172_);
if (v___x_218_ == 0)
{
uint8_t v___x_219_; 
v___x_219_ = l_Lean_Expr_isLambda(v_b_173_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec_ref(v___y_213_);
lean_dec_ref(v_b_173_);
lean_dec_ref(v_a_172_);
v___x_220_ = lean_box(v___x_219_);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; 
v___x_222_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_a_172_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_233_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_233_ == 0)
{
v___x_225_ = v___x_222_;
v_isShared_226_ = v_isSharedCheck_233_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_233_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
if (lean_obj_tag(v_a_223_) == 1)
{
lean_object* v_val_227_; 
lean_del_object(v___x_225_);
v_val_227_ = lean_ctor_get(v_a_223_, 0);
lean_inc(v_val_227_);
lean_dec_ref_known(v_a_223_, 1);
v_a_172_ = v_val_227_;
v_a_174_ = v___y_213_;
v_a_175_ = v___y_214_;
v_a_176_ = v___y_215_;
v_a_177_ = v___y_216_;
v_a_178_ = v___y_217_;
goto _start;
}
else
{
lean_object* v___x_229_; lean_object* v___x_231_; 
lean_dec(v_a_223_);
lean_dec_ref(v___y_213_);
lean_dec_ref(v_b_173_);
v___x_229_ = lean_box(v___x_218_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_229_);
v___x_231_ = v___x_225_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_dec_ref(v___y_213_);
lean_dec_ref(v_b_173_);
v_a_234_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_222_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_222_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
else
{
lean_object* v___x_242_; 
v___x_242_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_b_173_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_253_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_253_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_253_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_253_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
if (lean_obj_tag(v_a_243_) == 1)
{
lean_object* v_val_247_; 
lean_del_object(v___x_245_);
v_val_247_ = lean_ctor_get(v_a_243_, 0);
lean_inc(v_val_247_);
lean_dec_ref_known(v_a_243_, 1);
v_b_173_ = v_val_247_;
v_a_174_ = v___y_213_;
v_a_175_ = v___y_214_;
v_a_176_ = v___y_215_;
v_a_177_ = v___y_216_;
v_a_178_ = v___y_217_;
goto _start;
}
else
{
lean_object* v___x_249_; lean_object* v___x_251_; 
lean_dec(v_a_243_);
lean_dec_ref(v___y_213_);
lean_dec_ref(v_a_172_);
v___x_249_ = lean_box(v___y_212_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_249_);
v___x_251_ = v___x_245_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_dec_ref(v___y_213_);
lean_dec_ref(v_a_172_);
v_a_254_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_242_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_242_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
v___jp_262_:
{
uint8_t v___x_264_; 
v___x_264_ = 1;
if (v___y_263_ == 0)
{
lean_object* v_a_x27_265_; lean_object* v_b_x27_266_; uint8_t v___x_267_; 
lean_inc_ref(v_a_172_);
v_a_x27_265_ = l_Lean_Expr_headBeta(v_a_172_);
lean_inc_ref(v_b_173_);
v_b_x27_266_ = l_Lean_Expr_headBeta(v_b_173_);
v___x_267_ = lean_expr_eqv(v_a_172_, v_a_x27_265_);
if (v___x_267_ == 0)
{
lean_dec_ref(v_b_173_);
lean_dec_ref(v_a_172_);
v_a_172_ = v_a_x27_265_;
v_b_173_ = v_b_x27_266_;
goto _start;
}
else
{
uint8_t v___x_269_; 
v___x_269_ = lean_expr_eqv(v_b_173_, v_b_x27_266_);
if (v___x_269_ == 0)
{
lean_dec_ref(v_b_173_);
lean_dec_ref(v_a_172_);
v_a_172_ = v_a_x27_265_;
v_b_173_ = v_b_x27_266_;
goto _start;
}
else
{
uint8_t v___x_271_; 
lean_dec_ref(v_b_x27_266_);
lean_dec_ref(v_a_x27_265_);
v___x_271_ = lean_expr_eqv(v_a_172_, v_b_173_);
if (v___x_271_ == 0)
{
switch(lean_obj_tag(v_a_172_))
{
case 5:
{
switch(lean_obj_tag(v_b_173_))
{
case 5:
{
lean_object* v_fn_272_; lean_object* v_arg_273_; lean_object* v_fn_274_; lean_object* v_arg_275_; lean_object* v___x_276_; 
v_fn_272_ = lean_ctor_get(v_a_172_, 0);
lean_inc_ref(v_fn_272_);
v_arg_273_ = lean_ctor_get(v_a_172_, 1);
lean_inc_ref(v_arg_273_);
lean_dec_ref_known(v_a_172_, 2);
v_fn_274_ = lean_ctor_get(v_b_173_, 0);
lean_inc_ref(v_fn_274_);
v_arg_275_ = lean_ctor_get(v_b_173_, 1);
lean_inc_ref(v_arg_275_);
lean_dec_ref_known(v_b_173_, 2);
lean_inc_ref(v_a_174_);
v___x_276_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_fn_272_, v_fn_274_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; uint8_t v___x_278_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
v___x_278_ = lean_unbox(v_a_277_);
lean_dec(v_a_277_);
if (v___x_278_ == 0)
{
lean_dec_ref(v_arg_275_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_a_174_);
return v___x_276_;
}
else
{
lean_dec_ref_known(v___x_276_, 1);
v_a_172_ = v_arg_273_;
v_b_173_ = v_arg_275_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_275_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_a_174_);
return v___x_276_;
}
}
case 10:
{
lean_object* v_expr_280_; 
v_expr_280_ = lean_ctor_get(v_b_173_, 1);
lean_inc_ref(v_expr_280_);
lean_dec_ref_known(v_b_173_, 2);
v_b_173_ = v_expr_280_;
goto _start;
}
default: 
{
v___y_212_ = v___x_271_;
v___y_213_ = v_a_174_;
v___y_214_ = v_a_175_;
v___y_215_ = v_a_176_;
v___y_216_ = v_a_177_;
v___y_217_ = v_a_178_;
goto v___jp_211_;
}
}
}
case 7:
{
switch(lean_obj_tag(v_b_173_))
{
case 7:
{
lean_object* v_binderName_282_; lean_object* v_binderType_283_; lean_object* v_body_284_; uint8_t v_binderInfo_285_; lean_object* v_binderType_286_; lean_object* v_body_287_; 
v_binderName_282_ = lean_ctor_get(v_a_172_, 0);
lean_inc(v_binderName_282_);
v_binderType_283_ = lean_ctor_get(v_a_172_, 1);
lean_inc_ref(v_binderType_283_);
v_body_284_ = lean_ctor_get(v_a_172_, 2);
lean_inc_ref(v_body_284_);
v_binderInfo_285_ = lean_ctor_get_uint8(v_a_172_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_172_, 3);
v_binderType_286_ = lean_ctor_get(v_b_173_, 1);
lean_inc_ref(v_binderType_286_);
v_body_287_ = lean_ctor_get(v_b_173_, 2);
lean_inc_ref(v_body_287_);
lean_dec_ref_known(v_b_173_, 3);
v_n_181_ = v_binderName_282_;
v_d_u2081_182_ = v_binderType_283_;
v_b_u2081_183_ = v_body_284_;
v_bi_184_ = v_binderInfo_285_;
v_d_u2082_185_ = v_binderType_286_;
v_b_u2082_186_ = v_body_287_;
v___y_187_ = v_a_174_;
v___y_188_ = v_a_175_;
v___y_189_ = v_a_176_;
v___y_190_ = v_a_177_;
v___y_191_ = v_a_178_;
goto v___jp_180_;
}
case 10:
{
lean_object* v_expr_288_; 
v_expr_288_ = lean_ctor_get(v_b_173_, 1);
lean_inc_ref(v_expr_288_);
lean_dec_ref_known(v_b_173_, 2);
v_b_173_ = v_expr_288_;
goto _start;
}
default: 
{
v___y_212_ = v___x_271_;
v___y_213_ = v_a_174_;
v___y_214_ = v_a_175_;
v___y_215_ = v_a_176_;
v___y_216_ = v_a_177_;
v___y_217_ = v_a_178_;
goto v___jp_211_;
}
}
}
case 6:
{
switch(lean_obj_tag(v_b_173_))
{
case 6:
{
lean_object* v_binderName_290_; lean_object* v_binderType_291_; lean_object* v_body_292_; uint8_t v_binderInfo_293_; lean_object* v_binderType_294_; lean_object* v_body_295_; 
v_binderName_290_ = lean_ctor_get(v_a_172_, 0);
lean_inc(v_binderName_290_);
v_binderType_291_ = lean_ctor_get(v_a_172_, 1);
lean_inc_ref(v_binderType_291_);
v_body_292_ = lean_ctor_get(v_a_172_, 2);
lean_inc_ref(v_body_292_);
v_binderInfo_293_ = lean_ctor_get_uint8(v_a_172_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_172_, 3);
v_binderType_294_ = lean_ctor_get(v_b_173_, 1);
lean_inc_ref(v_binderType_294_);
v_body_295_ = lean_ctor_get(v_b_173_, 2);
lean_inc_ref(v_body_295_);
lean_dec_ref_known(v_b_173_, 3);
v_n_181_ = v_binderName_290_;
v_d_u2081_182_ = v_binderType_291_;
v_b_u2081_183_ = v_body_292_;
v_bi_184_ = v_binderInfo_293_;
v_d_u2082_185_ = v_binderType_294_;
v_b_u2082_186_ = v_body_295_;
v___y_187_ = v_a_174_;
v___y_188_ = v_a_175_;
v___y_189_ = v_a_176_;
v___y_190_ = v_a_177_;
v___y_191_ = v_a_178_;
goto v___jp_180_;
}
case 10:
{
lean_object* v_expr_296_; 
v_expr_296_ = lean_ctor_get(v_b_173_, 1);
lean_inc_ref(v_expr_296_);
lean_dec_ref_known(v_b_173_, 2);
v_b_173_ = v_expr_296_;
goto _start;
}
default: 
{
v___y_212_ = v___x_271_;
v___y_213_ = v_a_174_;
v___y_214_ = v_a_175_;
v___y_215_ = v_a_176_;
v___y_216_ = v_a_177_;
v___y_217_ = v_a_178_;
goto v___jp_211_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_b_173_))
{
case 3:
{
lean_object* v_u_298_; lean_object* v_u_299_; uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec_ref(v_a_174_);
v_u_298_ = lean_ctor_get(v_a_172_, 0);
lean_inc(v_u_298_);
lean_dec_ref_known(v_a_172_, 1);
v_u_299_ = lean_ctor_get(v_b_173_, 0);
lean_inc(v_u_299_);
lean_dec_ref_known(v_b_173_, 1);
v___x_300_ = l_Lean_Level_isEquiv(v_u_298_, v_u_299_);
lean_dec(v_u_299_);
lean_dec(v_u_298_);
v___x_301_ = lean_box(v___x_300_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
case 10:
{
lean_object* v_expr_303_; 
v_expr_303_ = lean_ctor_get(v_b_173_, 1);
lean_inc_ref(v_expr_303_);
lean_dec_ref_known(v_b_173_, 2);
v_b_173_ = v_expr_303_;
goto _start;
}
default: 
{
v___y_212_ = v___x_271_;
v___y_213_ = v_a_174_;
v___y_214_ = v_a_175_;
v___y_215_ = v_a_176_;
v___y_216_ = v_a_177_;
v___y_217_ = v_a_178_;
goto v___jp_211_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_b_173_))
{
case 4:
{
lean_object* v_declName_305_; lean_object* v_us_306_; lean_object* v_declName_307_; lean_object* v_us_308_; uint8_t v___x_309_; 
lean_dec_ref(v_a_174_);
v_declName_305_ = lean_ctor_get(v_a_172_, 0);
lean_inc(v_declName_305_);
v_us_306_ = lean_ctor_get(v_a_172_, 1);
lean_inc(v_us_306_);
lean_dec_ref_known(v_a_172_, 2);
v_declName_307_ = lean_ctor_get(v_b_173_, 0);
lean_inc(v_declName_307_);
v_us_308_ = lean_ctor_get(v_b_173_, 1);
lean_inc(v_us_308_);
lean_dec_ref_known(v_b_173_, 2);
v___x_309_ = lean_name_eq(v_declName_305_, v_declName_307_);
lean_dec(v_declName_307_);
lean_dec(v_declName_305_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec(v_us_308_);
lean_dec(v_us_306_);
v___x_310_ = lean_box(v___x_271_);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
else
{
uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(v_us_306_, v_us_308_);
lean_dec(v_us_308_);
lean_dec(v_us_306_);
v___x_313_ = lean_box(v___x_312_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
case 10:
{
lean_object* v_expr_315_; 
v_expr_315_ = lean_ctor_get(v_b_173_, 1);
lean_inc_ref(v_expr_315_);
lean_dec_ref_known(v_b_173_, 2);
v_b_173_ = v_expr_315_;
goto _start;
}
default: 
{
v___y_212_ = v___x_271_;
v___y_213_ = v_a_174_;
v___y_214_ = v_a_175_;
v___y_215_ = v_a_176_;
v___y_216_ = v_a_177_;
v___y_217_ = v_a_178_;
goto v___jp_211_;
}
}
}
case 10:
{
lean_object* v_expr_317_; 
v_expr_317_ = lean_ctor_get(v_a_172_, 1);
lean_inc_ref(v_expr_317_);
lean_dec_ref_known(v_a_172_, 2);
v_a_172_ = v_expr_317_;
goto _start;
}
default: 
{
if (lean_obj_tag(v_b_173_) == 10)
{
lean_object* v_expr_319_; 
v_expr_319_ = lean_ctor_get(v_b_173_, 1);
lean_inc_ref(v_expr_319_);
lean_dec_ref_known(v_b_173_, 2);
v_b_173_ = v_expr_319_;
goto _start;
}
else
{
v___y_212_ = v___x_271_;
v___y_213_ = v_a_174_;
v___y_214_ = v_a_175_;
v___y_215_ = v_a_176_;
v___y_216_ = v_a_177_;
v___y_217_ = v_a_178_;
goto v___jp_211_;
}
}
}
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec_ref(v_a_174_);
lean_dec_ref(v_b_173_);
lean_dec_ref(v_a_172_);
v___x_321_ = lean_box(v___x_264_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
}
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec_ref(v_a_174_);
lean_dec_ref(v_b_173_);
lean_dec_ref(v_a_172_);
v___x_323_ = lean_box(v___x_264_);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull___boxed(lean_object* v_a_327_, lean_object* v_b_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_a_327_, v_b_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0(lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(v___y_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___boxed(lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0(v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(lean_object* v_a_350_, lean_object* v_b_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
uint8_t v___x_358_; 
lean_inc_ref(v_b_351_);
lean_inc_ref(v_a_350_);
v___x_358_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_a_350_, v_b_351_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; 
lean_inc_ref(v_a_352_);
v___x_359_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_a_350_, v_b_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
return v___x_359_;
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec_ref(v_b_351_);
lean_dec_ref(v_a_350_);
v___x_360_ = lean_box(v___x_358_);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes___boxed(lean_object* v_a_362_, lean_object* v_b_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(v_a_362_, v_b_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec_ref(v_a_364_);
return v_res_370_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_CompatibleTypes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_CompatibleTypes(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_CompatibleTypes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin);
}
#ifdef __cplusplus
}
#endif
