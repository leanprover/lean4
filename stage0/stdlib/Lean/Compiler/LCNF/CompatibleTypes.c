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
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
uint8_t v___x_18_; 
v___x_18_ = l_Lean_Expr_isErased(v_a_16_);
if (v___x_18_ == 0)
{
uint8_t v___x_19_; 
v___x_19_ = l_Lean_Expr_isErased(v_b_17_);
if (v___x_19_ == 0)
{
lean_object* v_a_x27_20_; lean_object* v_b_x27_21_; uint8_t v___x_22_; 
lean_inc_ref(v_a_16_);
v_a_x27_20_ = l_Lean_Expr_headBeta(v_a_16_);
lean_inc_ref(v_b_17_);
v_b_x27_21_ = l_Lean_Expr_headBeta(v_b_17_);
v___x_22_ = lean_expr_eqv(v_a_16_, v_a_x27_20_);
if (v___x_22_ == 0)
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
v_a_16_ = v_a_x27_20_;
v_b_17_ = v_b_x27_21_;
goto _start;
}
else
{
uint8_t v___x_24_; 
v___x_24_ = lean_expr_eqv(v_b_17_, v_b_x27_21_);
if (v___x_24_ == 0)
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
v_a_16_ = v_a_x27_20_;
v_b_17_ = v_b_x27_21_;
goto _start;
}
else
{
uint8_t v___x_26_; lean_object* v_d_u2081_28_; lean_object* v_b_u2081_29_; lean_object* v_d_u2082_30_; lean_object* v_b_u2082_31_; 
lean_dec_ref(v_b_x27_21_);
lean_dec_ref(v_a_x27_20_);
v___x_26_ = lean_expr_eqv(v_a_16_, v_b_17_);
if (v___x_26_ == 0)
{
switch(lean_obj_tag(v_a_16_))
{
case 5:
{
if (lean_obj_tag(v_b_17_) == 5)
{
lean_object* v_fn_34_; lean_object* v_arg_35_; lean_object* v_fn_36_; lean_object* v_arg_37_; uint8_t v___x_38_; 
v_fn_34_ = lean_ctor_get(v_a_16_, 0);
lean_inc_ref(v_fn_34_);
v_arg_35_ = lean_ctor_get(v_a_16_, 1);
lean_inc_ref(v_arg_35_);
lean_dec_ref_known(v_a_16_, 2);
v_fn_36_ = lean_ctor_get(v_b_17_, 0);
lean_inc_ref(v_fn_36_);
v_arg_37_ = lean_ctor_get(v_b_17_, 1);
lean_inc_ref(v_arg_37_);
lean_dec_ref_known(v_b_17_, 2);
v___x_38_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_fn_34_, v_fn_36_);
if (v___x_38_ == 0)
{
lean_dec_ref(v_arg_37_);
lean_dec_ref(v_arg_35_);
return v___x_26_;
}
else
{
v_a_16_ = v_arg_35_;
v_b_17_ = v_arg_37_;
goto _start;
}
}
else
{
lean_dec_ref_known(v_a_16_, 2);
lean_dec_ref(v_b_17_);
return v___x_26_;
}
}
case 7:
{
if (lean_obj_tag(v_b_17_) == 7)
{
lean_object* v_binderType_40_; lean_object* v_body_41_; lean_object* v_binderType_42_; lean_object* v_body_43_; 
v_binderType_40_ = lean_ctor_get(v_a_16_, 1);
lean_inc_ref(v_binderType_40_);
v_body_41_ = lean_ctor_get(v_a_16_, 2);
lean_inc_ref(v_body_41_);
lean_dec_ref_known(v_a_16_, 3);
v_binderType_42_ = lean_ctor_get(v_b_17_, 1);
lean_inc_ref(v_binderType_42_);
v_body_43_ = lean_ctor_get(v_b_17_, 2);
lean_inc_ref(v_body_43_);
lean_dec_ref_known(v_b_17_, 3);
v_d_u2081_28_ = v_binderType_40_;
v_b_u2081_29_ = v_body_41_;
v_d_u2082_30_ = v_binderType_42_;
v_b_u2082_31_ = v_body_43_;
goto v___jp_27_;
}
else
{
lean_dec_ref_known(v_a_16_, 3);
lean_dec_ref(v_b_17_);
return v___x_26_;
}
}
case 6:
{
if (lean_obj_tag(v_b_17_) == 6)
{
lean_object* v_binderType_44_; lean_object* v_body_45_; lean_object* v_binderType_46_; lean_object* v_body_47_; 
v_binderType_44_ = lean_ctor_get(v_a_16_, 1);
lean_inc_ref(v_binderType_44_);
v_body_45_ = lean_ctor_get(v_a_16_, 2);
lean_inc_ref(v_body_45_);
lean_dec_ref_known(v_a_16_, 3);
v_binderType_46_ = lean_ctor_get(v_b_17_, 1);
lean_inc_ref(v_binderType_46_);
v_body_47_ = lean_ctor_get(v_b_17_, 2);
lean_inc_ref(v_body_47_);
lean_dec_ref_known(v_b_17_, 3);
v_d_u2081_28_ = v_binderType_44_;
v_b_u2081_29_ = v_body_45_;
v_d_u2082_30_ = v_binderType_46_;
v_b_u2082_31_ = v_body_47_;
goto v___jp_27_;
}
else
{
lean_dec_ref_known(v_a_16_, 3);
lean_dec_ref(v_b_17_);
return v___x_26_;
}
}
case 3:
{
if (lean_obj_tag(v_b_17_) == 3)
{
lean_object* v_u_48_; lean_object* v_u_49_; uint8_t v___x_50_; 
v_u_48_ = lean_ctor_get(v_a_16_, 0);
lean_inc(v_u_48_);
lean_dec_ref_known(v_a_16_, 1);
v_u_49_ = lean_ctor_get(v_b_17_, 0);
lean_inc(v_u_49_);
lean_dec_ref_known(v_b_17_, 1);
v___x_50_ = l_Lean_Level_isEquiv(v_u_48_, v_u_49_);
lean_dec(v_u_49_);
lean_dec(v_u_48_);
return v___x_50_;
}
else
{
lean_dec_ref_known(v_a_16_, 1);
lean_dec_ref(v_b_17_);
return v___x_26_;
}
}
case 4:
{
if (lean_obj_tag(v_b_17_) == 4)
{
lean_object* v_declName_51_; lean_object* v_us_52_; lean_object* v_declName_53_; lean_object* v_us_54_; uint8_t v___x_55_; 
v_declName_51_ = lean_ctor_get(v_a_16_, 0);
lean_inc(v_declName_51_);
v_us_52_ = lean_ctor_get(v_a_16_, 1);
lean_inc(v_us_52_);
lean_dec_ref_known(v_a_16_, 2);
v_declName_53_ = lean_ctor_get(v_b_17_, 0);
lean_inc(v_declName_53_);
v_us_54_ = lean_ctor_get(v_b_17_, 1);
lean_inc(v_us_54_);
lean_dec_ref_known(v_b_17_, 2);
v___x_55_ = lean_name_eq(v_declName_51_, v_declName_53_);
lean_dec(v_declName_53_);
lean_dec(v_declName_51_);
if (v___x_55_ == 0)
{
lean_dec(v_us_54_);
lean_dec(v_us_52_);
return v___x_26_;
}
else
{
uint8_t v___x_56_; 
v___x_56_ = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(v_us_52_, v_us_54_);
lean_dec(v_us_54_);
lean_dec(v_us_52_);
return v___x_56_;
}
}
else
{
lean_dec_ref_known(v_a_16_, 2);
lean_dec_ref(v_b_17_);
return v___x_26_;
}
}
default: 
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
return v___x_26_;
}
}
}
else
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
return v___x_26_;
}
v___jp_27_:
{
uint8_t v___x_32_; 
v___x_32_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_d_u2081_28_, v_d_u2082_30_);
if (v___x_32_ == 0)
{
lean_dec_ref(v_b_u2082_31_);
lean_dec_ref(v_b_u2081_29_);
return v___x_26_;
}
else
{
v_a_16_ = v_b_u2081_29_;
v_b_17_ = v_b_u2082_31_;
goto _start;
}
}
}
}
}
else
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
return v___x_19_;
}
}
else
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compatibleTypesQuick___boxed(lean_object* v_a_57_, lean_object* v_b_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_a_57_, v_b_58_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = l_Lean_Expr_bvar___override(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(lean_object* v_e_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___x_70_; 
lean_inc_ref(v_e_63_);
v___x_70_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v_a_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_90_; 
v_a_71_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_90_ == 0)
{
v___x_73_ = v___x_70_;
v_isShared_74_ = v_isSharedCheck_90_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_a_71_);
lean_dec(v___x_70_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_90_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_Expr_headBeta(v_a_71_);
if (lean_obj_tag(v___x_75_) == 7)
{
lean_object* v_binderName_76_; lean_object* v_binderType_77_; uint8_t v_binderInfo_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
v_binderName_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_binderName_76_);
v_binderType_77_ = lean_ctor_get(v___x_75_, 1);
lean_inc_ref(v_binderType_77_);
v_binderInfo_78_ = lean_ctor_get_uint8(v___x_75_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_75_, 3);
v___x_79_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0, &l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0_once, _init_l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0);
v___x_80_ = l_Lean_Expr_app___override(v_e_63_, v___x_79_);
v___x_81_ = l_Lean_Expr_lam___override(v_binderName_76_, v_binderType_77_, v___x_80_, v_binderInfo_78_);
v___x_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 0, v___x_82_);
v___x_84_ = v___x_73_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
else
{
lean_object* v___x_86_; lean_object* v___x_88_; 
lean_dec_ref(v___x_75_);
lean_dec_ref(v_e_63_);
v___x_86_ = lean_box(0);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 0, v___x_86_);
v___x_88_ = v___x_73_;
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
}
}
else
{
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
lean_dec_ref(v_e_63_);
v_a_91_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v___x_70_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_70_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_91_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___boxed(lean_object* v_e_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_e_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
lean_dec_ref(v_a_100_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; lean_object* v_ngen_110_; lean_object* v_namePrefix_111_; lean_object* v_idx_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_142_; 
v___x_109_ = lean_st_ref_get(v___y_107_);
v_ngen_110_ = lean_ctor_get(v___x_109_, 2);
lean_inc_ref(v_ngen_110_);
lean_dec(v___x_109_);
v_namePrefix_111_ = lean_ctor_get(v_ngen_110_, 0);
v_idx_112_ = lean_ctor_get(v_ngen_110_, 1);
v_isSharedCheck_142_ = !lean_is_exclusive(v_ngen_110_);
if (v_isSharedCheck_142_ == 0)
{
v___x_114_ = v_ngen_110_;
v_isShared_115_ = v_isSharedCheck_142_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_idx_112_);
lean_inc(v_namePrefix_111_);
lean_dec(v_ngen_110_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_142_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v_r_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_120_; 
lean_inc(v_idx_112_);
lean_inc(v_namePrefix_111_);
v_r_116_ = l_Lean_Name_num___override(v_namePrefix_111_, v_idx_112_);
v___x_117_ = lean_unsigned_to_nat(1u);
v___x_118_ = lean_nat_add(v_idx_112_, v___x_117_);
lean_dec(v_idx_112_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 1, v___x_118_);
v___x_120_ = v___x_114_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_namePrefix_111_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v___x_118_);
v___x_120_ = v_reuseFailAlloc_141_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_object* v___x_121_; lean_object* v_env_122_; lean_object* v_nextMacroScope_123_; lean_object* v_auxDeclNGen_124_; lean_object* v_traceState_125_; lean_object* v_cache_126_; lean_object* v_recordedDeps_127_; lean_object* v_messages_128_; lean_object* v_infoState_129_; lean_object* v_snapshotTasks_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_139_; 
v___x_121_ = lean_st_ref_take(v___y_107_);
v_env_122_ = lean_ctor_get(v___x_121_, 0);
v_nextMacroScope_123_ = lean_ctor_get(v___x_121_, 1);
v_auxDeclNGen_124_ = lean_ctor_get(v___x_121_, 3);
v_traceState_125_ = lean_ctor_get(v___x_121_, 4);
v_cache_126_ = lean_ctor_get(v___x_121_, 5);
v_recordedDeps_127_ = lean_ctor_get(v___x_121_, 6);
v_messages_128_ = lean_ctor_get(v___x_121_, 7);
v_infoState_129_ = lean_ctor_get(v___x_121_, 8);
v_snapshotTasks_130_ = lean_ctor_get(v___x_121_, 9);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_139_ == 0)
{
lean_object* v_unused_140_; 
v_unused_140_ = lean_ctor_get(v___x_121_, 2);
lean_dec(v_unused_140_);
v___x_132_ = v___x_121_;
v_isShared_133_ = v_isSharedCheck_139_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_snapshotTasks_130_);
lean_inc(v_infoState_129_);
lean_inc(v_messages_128_);
lean_inc(v_recordedDeps_127_);
lean_inc(v_cache_126_);
lean_inc(v_traceState_125_);
lean_inc(v_auxDeclNGen_124_);
lean_inc(v_nextMacroScope_123_);
lean_inc(v_env_122_);
lean_dec(v___x_121_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_139_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 2, v___x_120_);
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_env_122_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_nextMacroScope_123_);
lean_ctor_set(v_reuseFailAlloc_138_, 2, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_138_, 3, v_auxDeclNGen_124_);
lean_ctor_set(v_reuseFailAlloc_138_, 4, v_traceState_125_);
lean_ctor_set(v_reuseFailAlloc_138_, 5, v_cache_126_);
lean_ctor_set(v_reuseFailAlloc_138_, 6, v_recordedDeps_127_);
lean_ctor_set(v_reuseFailAlloc_138_, 7, v_messages_128_);
lean_ctor_set(v_reuseFailAlloc_138_, 8, v_infoState_129_);
lean_ctor_set(v_reuseFailAlloc_138_, 9, v_snapshotTasks_130_);
v___x_135_ = v_reuseFailAlloc_138_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_st_ref_put(v___y_107_, v___x_135_);
v___x_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_137_, 0, v_r_116_);
return v___x_137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg___boxed(lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(v___y_143_);
lean_dec(v___y_143_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v___x_152_; lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
v___x_152_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(v___y_150_);
v_a_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_160_ == 0)
{
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_153_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0___boxed(lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec_ref(v___y_161_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(lean_object* v_a_168_, lean_object* v_b_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_n_177_; lean_object* v_d_u2081_178_; lean_object* v_b_u2081_179_; uint8_t v_bi_180_; lean_object* v_d_u2082_181_; lean_object* v_b_u2082_182_; lean_object* v___y_183_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_186_; lean_object* v___y_187_; uint8_t v___x_211_; 
v___x_211_ = l_Lean_Expr_isErased(v_a_168_);
if (v___x_211_ == 0)
{
uint8_t v___x_212_; 
v___x_212_ = l_Lean_Expr_isErased(v_b_169_);
if (v___x_212_ == 0)
{
lean_object* v_a_x27_213_; lean_object* v_b_x27_214_; uint8_t v___x_215_; 
lean_inc_ref(v_a_168_);
v_a_x27_213_ = l_Lean_Expr_headBeta(v_a_168_);
lean_inc_ref(v_b_169_);
v_b_x27_214_ = l_Lean_Expr_headBeta(v_b_169_);
v___x_215_ = lean_expr_eqv(v_a_168_, v_a_x27_213_);
if (v___x_215_ == 0)
{
lean_dec_ref(v_b_169_);
lean_dec_ref(v_a_168_);
v_a_168_ = v_a_x27_213_;
v_b_169_ = v_b_x27_214_;
goto _start;
}
else
{
uint8_t v___x_217_; 
v___x_217_ = lean_expr_eqv(v_b_169_, v_b_x27_214_);
if (v___x_217_ == 0)
{
lean_dec_ref(v_b_169_);
lean_dec_ref(v_a_168_);
v_a_168_ = v_a_x27_213_;
v_b_169_ = v_b_x27_214_;
goto _start;
}
else
{
uint8_t v___x_219_; lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; lean_object* v___y_225_; 
lean_dec_ref(v_b_x27_214_);
lean_dec_ref(v_a_x27_213_);
v___x_219_ = lean_expr_eqv(v_a_168_, v_b_169_);
if (v___x_219_ == 0)
{
switch(lean_obj_tag(v_a_168_))
{
case 5:
{
switch(lean_obj_tag(v_b_169_))
{
case 5:
{
lean_object* v_fn_270_; lean_object* v_arg_271_; lean_object* v_fn_272_; lean_object* v_arg_273_; lean_object* v___x_274_; 
v_fn_270_ = lean_ctor_get(v_a_168_, 0);
lean_inc_ref(v_fn_270_);
v_arg_271_ = lean_ctor_get(v_a_168_, 1);
lean_inc_ref(v_arg_271_);
lean_dec_ref_known(v_a_168_, 2);
v_fn_272_ = lean_ctor_get(v_b_169_, 0);
lean_inc_ref(v_fn_272_);
v_arg_273_ = lean_ctor_get(v_b_169_, 1);
lean_inc_ref(v_arg_273_);
lean_dec_ref_known(v_b_169_, 2);
lean_inc_ref(v_a_170_);
v___x_274_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_fn_270_, v_fn_272_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; uint8_t v___x_276_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
v___x_276_ = lean_unbox(v_a_275_);
if (v___x_276_ == 0)
{
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_271_);
lean_dec_ref(v_a_170_);
return v___x_274_;
}
else
{
lean_dec_ref_known(v___x_274_, 1);
v_a_168_ = v_arg_271_;
v_b_169_ = v_arg_273_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_271_);
lean_dec_ref(v_a_170_);
return v___x_274_;
}
}
case 10:
{
lean_object* v_expr_278_; 
v_expr_278_ = lean_ctor_get(v_b_169_, 1);
lean_inc_ref(v_expr_278_);
lean_dec_ref_known(v_b_169_, 2);
v_b_169_ = v_expr_278_;
goto _start;
}
default: 
{
v___y_221_ = v_a_170_;
v___y_222_ = v_a_171_;
v___y_223_ = v_a_172_;
v___y_224_ = v_a_173_;
v___y_225_ = v_a_174_;
goto v___jp_220_;
}
}
}
case 7:
{
switch(lean_obj_tag(v_b_169_))
{
case 7:
{
lean_object* v_binderName_280_; lean_object* v_binderType_281_; lean_object* v_body_282_; uint8_t v_binderInfo_283_; lean_object* v_binderType_284_; lean_object* v_body_285_; 
v_binderName_280_ = lean_ctor_get(v_a_168_, 0);
lean_inc(v_binderName_280_);
v_binderType_281_ = lean_ctor_get(v_a_168_, 1);
lean_inc_ref(v_binderType_281_);
v_body_282_ = lean_ctor_get(v_a_168_, 2);
lean_inc_ref(v_body_282_);
v_binderInfo_283_ = lean_ctor_get_uint8(v_a_168_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_168_, 3);
v_binderType_284_ = lean_ctor_get(v_b_169_, 1);
lean_inc_ref(v_binderType_284_);
v_body_285_ = lean_ctor_get(v_b_169_, 2);
lean_inc_ref(v_body_285_);
lean_dec_ref_known(v_b_169_, 3);
v_n_177_ = v_binderName_280_;
v_d_u2081_178_ = v_binderType_281_;
v_b_u2081_179_ = v_body_282_;
v_bi_180_ = v_binderInfo_283_;
v_d_u2082_181_ = v_binderType_284_;
v_b_u2082_182_ = v_body_285_;
v___y_183_ = v_a_170_;
v___y_184_ = v_a_171_;
v___y_185_ = v_a_172_;
v___y_186_ = v_a_173_;
v___y_187_ = v_a_174_;
goto v___jp_176_;
}
case 10:
{
lean_object* v_expr_286_; 
v_expr_286_ = lean_ctor_get(v_b_169_, 1);
lean_inc_ref(v_expr_286_);
lean_dec_ref_known(v_b_169_, 2);
v_b_169_ = v_expr_286_;
goto _start;
}
default: 
{
v___y_221_ = v_a_170_;
v___y_222_ = v_a_171_;
v___y_223_ = v_a_172_;
v___y_224_ = v_a_173_;
v___y_225_ = v_a_174_;
goto v___jp_220_;
}
}
}
case 6:
{
switch(lean_obj_tag(v_b_169_))
{
case 6:
{
lean_object* v_binderName_288_; lean_object* v_binderType_289_; lean_object* v_body_290_; uint8_t v_binderInfo_291_; lean_object* v_binderType_292_; lean_object* v_body_293_; 
v_binderName_288_ = lean_ctor_get(v_a_168_, 0);
lean_inc(v_binderName_288_);
v_binderType_289_ = lean_ctor_get(v_a_168_, 1);
lean_inc_ref(v_binderType_289_);
v_body_290_ = lean_ctor_get(v_a_168_, 2);
lean_inc_ref(v_body_290_);
v_binderInfo_291_ = lean_ctor_get_uint8(v_a_168_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_168_, 3);
v_binderType_292_ = lean_ctor_get(v_b_169_, 1);
lean_inc_ref(v_binderType_292_);
v_body_293_ = lean_ctor_get(v_b_169_, 2);
lean_inc_ref(v_body_293_);
lean_dec_ref_known(v_b_169_, 3);
v_n_177_ = v_binderName_288_;
v_d_u2081_178_ = v_binderType_289_;
v_b_u2081_179_ = v_body_290_;
v_bi_180_ = v_binderInfo_291_;
v_d_u2082_181_ = v_binderType_292_;
v_b_u2082_182_ = v_body_293_;
v___y_183_ = v_a_170_;
v___y_184_ = v_a_171_;
v___y_185_ = v_a_172_;
v___y_186_ = v_a_173_;
v___y_187_ = v_a_174_;
goto v___jp_176_;
}
case 10:
{
lean_object* v_expr_294_; 
v_expr_294_ = lean_ctor_get(v_b_169_, 1);
lean_inc_ref(v_expr_294_);
lean_dec_ref_known(v_b_169_, 2);
v_b_169_ = v_expr_294_;
goto _start;
}
default: 
{
v___y_221_ = v_a_170_;
v___y_222_ = v_a_171_;
v___y_223_ = v_a_172_;
v___y_224_ = v_a_173_;
v___y_225_ = v_a_174_;
goto v___jp_220_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_b_169_))
{
case 3:
{
lean_object* v_u_296_; lean_object* v_u_297_; uint8_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec_ref(v_a_170_);
v_u_296_ = lean_ctor_get(v_a_168_, 0);
lean_inc(v_u_296_);
lean_dec_ref_known(v_a_168_, 1);
v_u_297_ = lean_ctor_get(v_b_169_, 0);
lean_inc(v_u_297_);
lean_dec_ref_known(v_b_169_, 1);
v___x_298_ = l_Lean_Level_isEquiv(v_u_296_, v_u_297_);
lean_dec(v_u_297_);
lean_dec(v_u_296_);
v___x_299_ = lean_box(v___x_298_);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
case 10:
{
lean_object* v_expr_301_; 
v_expr_301_ = lean_ctor_get(v_b_169_, 1);
lean_inc_ref(v_expr_301_);
lean_dec_ref_known(v_b_169_, 2);
v_b_169_ = v_expr_301_;
goto _start;
}
default: 
{
v___y_221_ = v_a_170_;
v___y_222_ = v_a_171_;
v___y_223_ = v_a_172_;
v___y_224_ = v_a_173_;
v___y_225_ = v_a_174_;
goto v___jp_220_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_b_169_))
{
case 4:
{
lean_object* v_declName_303_; lean_object* v_us_304_; lean_object* v_declName_305_; lean_object* v_us_306_; uint8_t v___x_307_; 
lean_dec_ref(v_a_170_);
v_declName_303_ = lean_ctor_get(v_a_168_, 0);
lean_inc(v_declName_303_);
v_us_304_ = lean_ctor_get(v_a_168_, 1);
lean_inc(v_us_304_);
lean_dec_ref_known(v_a_168_, 2);
v_declName_305_ = lean_ctor_get(v_b_169_, 0);
lean_inc(v_declName_305_);
v_us_306_ = lean_ctor_get(v_b_169_, 1);
lean_inc(v_us_306_);
lean_dec_ref_known(v_b_169_, 2);
v___x_307_ = lean_name_eq(v_declName_303_, v_declName_305_);
lean_dec(v_declName_305_);
lean_dec(v_declName_303_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec(v_us_306_);
lean_dec(v_us_304_);
v___x_308_ = lean_box(v___x_219_);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
else
{
uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(v_us_304_, v_us_306_);
lean_dec(v_us_306_);
lean_dec(v_us_304_);
v___x_311_ = lean_box(v___x_310_);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
}
case 10:
{
lean_object* v_expr_313_; 
v_expr_313_ = lean_ctor_get(v_b_169_, 1);
lean_inc_ref(v_expr_313_);
lean_dec_ref_known(v_b_169_, 2);
v_b_169_ = v_expr_313_;
goto _start;
}
default: 
{
v___y_221_ = v_a_170_;
v___y_222_ = v_a_171_;
v___y_223_ = v_a_172_;
v___y_224_ = v_a_173_;
v___y_225_ = v_a_174_;
goto v___jp_220_;
}
}
}
case 10:
{
lean_object* v_expr_315_; 
v_expr_315_ = lean_ctor_get(v_a_168_, 1);
lean_inc_ref(v_expr_315_);
lean_dec_ref_known(v_a_168_, 2);
v_a_168_ = v_expr_315_;
goto _start;
}
default: 
{
if (lean_obj_tag(v_b_169_) == 10)
{
lean_object* v_expr_317_; 
v_expr_317_ = lean_ctor_get(v_b_169_, 1);
lean_inc_ref(v_expr_317_);
lean_dec_ref_known(v_b_169_, 2);
v_b_169_ = v_expr_317_;
goto _start;
}
else
{
v___y_221_ = v_a_170_;
v___y_222_ = v_a_171_;
v___y_223_ = v_a_172_;
v___y_224_ = v_a_173_;
v___y_225_ = v_a_174_;
goto v___jp_220_;
}
}
}
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref(v_a_170_);
lean_dec_ref(v_b_169_);
lean_dec_ref(v_a_168_);
v___x_319_ = lean_box(v___x_219_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
v___jp_220_:
{
uint8_t v___x_226_; 
v___x_226_ = l_Lean_Expr_isLambda(v_a_168_);
if (v___x_226_ == 0)
{
uint8_t v___x_227_; 
v___x_227_ = l_Lean_Expr_isLambda(v_b_169_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec_ref(v___y_221_);
lean_dec_ref(v_b_169_);
lean_dec_ref(v_a_168_);
v___x_228_ = lean_box(v___x_227_);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
else
{
lean_object* v___x_230_; 
v___x_230_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_a_168_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_241_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_241_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_241_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_241_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
if (lean_obj_tag(v_a_231_) == 1)
{
lean_object* v_val_235_; 
lean_del_object(v___x_233_);
v_val_235_ = lean_ctor_get(v_a_231_, 0);
lean_inc(v_val_235_);
lean_dec_ref_known(v_a_231_, 1);
v_a_168_ = v_val_235_;
v_a_170_ = v___y_221_;
v_a_171_ = v___y_222_;
v_a_172_ = v___y_223_;
v_a_173_ = v___y_224_;
v_a_174_ = v___y_225_;
goto _start;
}
else
{
lean_object* v___x_237_; lean_object* v___x_239_; 
lean_dec(v_a_231_);
lean_dec_ref(v___y_221_);
lean_dec_ref(v_b_169_);
v___x_237_ = lean_box(v___x_226_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_237_);
v___x_239_ = v___x_233_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
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
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_dec_ref(v___y_221_);
lean_dec_ref(v_b_169_);
v_a_242_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_230_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_230_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
else
{
lean_object* v___x_250_; 
v___x_250_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_b_169_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_261_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_261_ == 0)
{
v___x_253_ = v___x_250_;
v_isShared_254_ = v_isSharedCheck_261_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_261_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
if (lean_obj_tag(v_a_251_) == 1)
{
lean_object* v_val_255_; 
lean_del_object(v___x_253_);
v_val_255_ = lean_ctor_get(v_a_251_, 0);
lean_inc(v_val_255_);
lean_dec_ref_known(v_a_251_, 1);
v_b_169_ = v_val_255_;
v_a_170_ = v___y_221_;
v_a_171_ = v___y_222_;
v_a_172_ = v___y_223_;
v_a_173_ = v___y_224_;
v_a_174_ = v___y_225_;
goto _start;
}
else
{
lean_object* v___x_257_; lean_object* v___x_259_; 
lean_dec(v_a_251_);
lean_dec_ref(v___y_221_);
lean_dec_ref(v_a_168_);
v___x_257_ = lean_box(v___x_219_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v___x_257_);
v___x_259_ = v___x_253_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
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
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
lean_dec_ref(v___y_221_);
lean_dec_ref(v_a_168_);
v_a_262_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_250_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_250_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
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
lean_dec_ref(v_a_170_);
lean_dec_ref(v_b_169_);
lean_dec_ref(v_a_168_);
goto v___jp_207_;
}
}
else
{
lean_dec_ref(v_a_170_);
lean_dec_ref(v_b_169_);
lean_dec_ref(v_a_168_);
goto v___jp_207_;
}
v___jp_176_:
{
lean_object* v___x_188_; 
lean_inc_ref(v___y_183_);
lean_inc_ref(v_d_u2081_178_);
v___x_188_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_d_u2081_178_, v_d_u2082_181_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; uint8_t v___x_190_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
v___x_190_ = lean_unbox(v_a_189_);
if (v___x_190_ == 0)
{
lean_dec_ref(v___y_183_);
lean_dec_ref(v_b_u2082_182_);
lean_dec_ref(v_b_u2081_179_);
lean_dec_ref(v_d_u2081_178_);
lean_dec(v_n_177_);
return v___x_188_;
}
else
{
lean_object* v___x_191_; 
lean_dec_ref_known(v___x_188_, 1);
v___x_191_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_193_; uint8_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc_n(v_a_192_, 2);
lean_dec_ref_known(v___x_191_, 1);
v___x_193_ = l_Lean_Expr_fvar___override(v_a_192_);
v___x_194_ = 0;
v___x_195_ = l_Lean_LocalContext_mkLocalDecl(v___y_183_, v_a_192_, v_n_177_, v_d_u2081_178_, v_bi_180_, v___x_194_);
v___x_196_ = lean_expr_instantiate1(v_b_u2081_179_, v___x_193_);
lean_dec_ref(v_b_u2081_179_);
v___x_197_ = lean_expr_instantiate1(v_b_u2082_182_, v___x_193_);
lean_dec_ref(v___x_193_);
lean_dec_ref(v_b_u2082_182_);
v_a_168_ = v___x_196_;
v_b_169_ = v___x_197_;
v_a_170_ = v___x_195_;
v_a_171_ = v___y_184_;
v_a_172_ = v___y_185_;
v_a_173_ = v___y_186_;
v_a_174_ = v___y_187_;
goto _start;
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec_ref(v___y_183_);
lean_dec_ref(v_b_u2082_182_);
lean_dec_ref(v_b_u2081_179_);
lean_dec_ref(v_d_u2081_178_);
lean_dec(v_n_177_);
v_a_199_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_191_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_191_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_183_);
lean_dec_ref(v_b_u2082_182_);
lean_dec_ref(v_b_u2081_179_);
lean_dec_ref(v_d_u2081_178_);
lean_dec(v_n_177_);
return v___x_188_;
}
}
v___jp_207_:
{
uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = 1;
v___x_209_ = lean_box(v___x_208_);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull___boxed(lean_object* v_a_321_, lean_object* v_b_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_a_321_, v_b_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0(lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(v___y_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___boxed(lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0(v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(lean_object* v_a_344_, lean_object* v_b_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
uint8_t v___x_352_; 
lean_inc_ref(v_b_345_);
lean_inc_ref(v_a_344_);
v___x_352_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_a_344_, v_b_345_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; 
lean_inc_ref(v_a_346_);
v___x_353_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_a_344_, v_b_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
return v___x_353_;
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec_ref(v_b_345_);
lean_dec_ref(v_a_344_);
v___x_354_ = lean_box(v___x_352_);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes___boxed(lean_object* v_a_356_, lean_object* v_b_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(v_a_356_, v_b_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec_ref(v_a_358_);
return v_res_364_;
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
