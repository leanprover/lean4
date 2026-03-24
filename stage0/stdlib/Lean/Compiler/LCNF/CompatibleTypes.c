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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* v_d_u2081_19_; lean_object* v_b_u2081_20_; lean_object* v_d_u2082_21_; lean_object* v_b_u2082_22_; uint8_t v___y_26_; uint8_t v___x_58_; 
v___x_58_ = l_Lean_Expr_isErased(v_a_16_);
if (v___x_58_ == 0)
{
uint8_t v___x_59_; 
v___x_59_ = l_Lean_Expr_isErased(v_b_17_);
v___y_26_ = v___x_59_;
goto v___jp_25_;
}
else
{
v___y_26_ = v___x_58_;
goto v___jp_25_;
}
v___jp_18_:
{
uint8_t v___x_23_; 
v___x_23_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_d_u2081_19_, v_d_u2082_21_);
if (v___x_23_ == 0)
{
lean_dec_ref(v_b_u2082_22_);
lean_dec_ref(v_b_u2081_20_);
return v___x_23_;
}
else
{
v_a_16_ = v_b_u2081_20_;
v_b_17_ = v_b_u2082_22_;
goto _start;
}
}
v___jp_25_:
{
uint8_t v___x_27_; 
v___x_27_ = 1;
if (v___y_26_ == 0)
{
lean_object* v_a_x27_28_; lean_object* v_b_x27_29_; uint8_t v___x_30_; 
lean_inc_ref(v_a_16_);
v_a_x27_28_ = l_Lean_Expr_headBeta(v_a_16_);
lean_inc_ref(v_b_17_);
v_b_x27_29_ = l_Lean_Expr_headBeta(v_b_17_);
v___x_30_ = lean_expr_eqv(v_a_16_, v_a_x27_28_);
if (v___x_30_ == 0)
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
v_a_16_ = v_a_x27_28_;
v_b_17_ = v_b_x27_29_;
goto _start;
}
else
{
uint8_t v___x_32_; 
v___x_32_ = lean_expr_eqv(v_b_17_, v_b_x27_29_);
if (v___x_32_ == 0)
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
v_a_16_ = v_a_x27_28_;
v_b_17_ = v_b_x27_29_;
goto _start;
}
else
{
uint8_t v___x_34_; 
lean_dec_ref(v_b_x27_29_);
lean_dec_ref(v_a_x27_28_);
v___x_34_ = lean_expr_eqv(v_a_16_, v_b_17_);
if (v___x_34_ == 0)
{
switch(lean_obj_tag(v_a_16_))
{
case 5:
{
if (lean_obj_tag(v_b_17_) == 5)
{
lean_object* v_fn_35_; lean_object* v_arg_36_; lean_object* v_fn_37_; lean_object* v_arg_38_; uint8_t v___x_39_; 
v_fn_35_ = lean_ctor_get(v_a_16_, 0);
lean_inc_ref(v_fn_35_);
v_arg_36_ = lean_ctor_get(v_a_16_, 1);
lean_inc_ref(v_arg_36_);
lean_dec_ref(v_a_16_);
v_fn_37_ = lean_ctor_get(v_b_17_, 0);
lean_inc_ref(v_fn_37_);
v_arg_38_ = lean_ctor_get(v_b_17_, 1);
lean_inc_ref(v_arg_38_);
lean_dec_ref(v_b_17_);
v___x_39_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_fn_35_, v_fn_37_);
if (v___x_39_ == 0)
{
lean_dec_ref(v_arg_38_);
lean_dec_ref(v_arg_36_);
return v___x_39_;
}
else
{
v_a_16_ = v_arg_36_;
v_b_17_ = v_arg_38_;
goto _start;
}
}
else
{
lean_dec_ref(v_a_16_);
lean_dec_ref(v_b_17_);
return v___x_34_;
}
}
case 7:
{
if (lean_obj_tag(v_b_17_) == 7)
{
lean_object* v_binderType_41_; lean_object* v_body_42_; lean_object* v_binderType_43_; lean_object* v_body_44_; 
v_binderType_41_ = lean_ctor_get(v_a_16_, 1);
lean_inc_ref(v_binderType_41_);
v_body_42_ = lean_ctor_get(v_a_16_, 2);
lean_inc_ref(v_body_42_);
lean_dec_ref(v_a_16_);
v_binderType_43_ = lean_ctor_get(v_b_17_, 1);
lean_inc_ref(v_binderType_43_);
v_body_44_ = lean_ctor_get(v_b_17_, 2);
lean_inc_ref(v_body_44_);
lean_dec_ref(v_b_17_);
v_d_u2081_19_ = v_binderType_41_;
v_b_u2081_20_ = v_body_42_;
v_d_u2082_21_ = v_binderType_43_;
v_b_u2082_22_ = v_body_44_;
goto v___jp_18_;
}
else
{
lean_dec_ref(v_a_16_);
lean_dec_ref(v_b_17_);
return v___x_34_;
}
}
case 6:
{
if (lean_obj_tag(v_b_17_) == 6)
{
lean_object* v_binderType_45_; lean_object* v_body_46_; lean_object* v_binderType_47_; lean_object* v_body_48_; 
v_binderType_45_ = lean_ctor_get(v_a_16_, 1);
lean_inc_ref(v_binderType_45_);
v_body_46_ = lean_ctor_get(v_a_16_, 2);
lean_inc_ref(v_body_46_);
lean_dec_ref(v_a_16_);
v_binderType_47_ = lean_ctor_get(v_b_17_, 1);
lean_inc_ref(v_binderType_47_);
v_body_48_ = lean_ctor_get(v_b_17_, 2);
lean_inc_ref(v_body_48_);
lean_dec_ref(v_b_17_);
v_d_u2081_19_ = v_binderType_45_;
v_b_u2081_20_ = v_body_46_;
v_d_u2082_21_ = v_binderType_47_;
v_b_u2082_22_ = v_body_48_;
goto v___jp_18_;
}
else
{
lean_dec_ref(v_a_16_);
lean_dec_ref(v_b_17_);
return v___x_34_;
}
}
case 3:
{
if (lean_obj_tag(v_b_17_) == 3)
{
lean_object* v_u_49_; lean_object* v_u_50_; uint8_t v___x_51_; 
v_u_49_ = lean_ctor_get(v_a_16_, 0);
lean_inc(v_u_49_);
lean_dec_ref(v_a_16_);
v_u_50_ = lean_ctor_get(v_b_17_, 0);
lean_inc(v_u_50_);
lean_dec_ref(v_b_17_);
v___x_51_ = l_Lean_Level_isEquiv(v_u_49_, v_u_50_);
lean_dec(v_u_50_);
lean_dec(v_u_49_);
return v___x_51_;
}
else
{
lean_dec_ref(v_a_16_);
lean_dec_ref(v_b_17_);
return v___x_34_;
}
}
case 4:
{
if (lean_obj_tag(v_b_17_) == 4)
{
lean_object* v_declName_52_; lean_object* v_us_53_; lean_object* v_declName_54_; lean_object* v_us_55_; uint8_t v___x_56_; 
v_declName_52_ = lean_ctor_get(v_a_16_, 0);
lean_inc(v_declName_52_);
v_us_53_ = lean_ctor_get(v_a_16_, 1);
lean_inc(v_us_53_);
lean_dec_ref(v_a_16_);
v_declName_54_ = lean_ctor_get(v_b_17_, 0);
lean_inc(v_declName_54_);
v_us_55_ = lean_ctor_get(v_b_17_, 1);
lean_inc(v_us_55_);
lean_dec_ref(v_b_17_);
v___x_56_ = lean_name_eq(v_declName_52_, v_declName_54_);
lean_dec(v_declName_54_);
lean_dec(v_declName_52_);
if (v___x_56_ == 0)
{
lean_dec(v_us_55_);
lean_dec(v_us_53_);
return v___x_56_;
}
else
{
uint8_t v___x_57_; 
v___x_57_ = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(v_us_53_, v_us_55_);
lean_dec(v_us_55_);
lean_dec(v_us_53_);
return v___x_57_;
}
}
else
{
lean_dec_ref(v_a_16_);
lean_dec_ref(v_b_17_);
return v___x_34_;
}
}
default: 
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
return v___x_34_;
}
}
}
else
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
return v___x_27_;
}
}
}
}
else
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compatibleTypesQuick___boxed(lean_object* v_a_60_, lean_object* v_b_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_a_60_, v_b_61_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = l_Lean_Expr_bvar___override(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(lean_object* v_e_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v___x_73_; 
lean_inc_ref(v_e_66_);
v___x_73_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_93_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_93_ == 0)
{
v___x_76_ = v___x_73_;
v_isShared_77_ = v_isSharedCheck_93_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_dec(v___x_73_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_93_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Expr_headBeta(v_a_74_);
if (lean_obj_tag(v___x_78_) == 7)
{
lean_object* v_binderName_79_; lean_object* v_binderType_80_; uint8_t v_binderInfo_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v_binderName_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_binderName_79_);
v_binderType_80_ = lean_ctor_get(v___x_78_, 1);
lean_inc_ref(v_binderType_80_);
v_binderInfo_81_ = lean_ctor_get_uint8(v___x_78_, sizeof(void*)*3 + 8);
lean_dec_ref(v___x_78_);
v___x_82_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0, &l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0_once, _init_l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0);
v___x_83_ = l_Lean_Expr_app___override(v_e_66_, v___x_82_);
v___x_84_ = l_Lean_Expr_lam___override(v_binderName_79_, v_binderType_80_, v___x_83_, v_binderInfo_81_);
v___x_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 0, v___x_85_);
v___x_87_ = v___x_76_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
else
{
lean_object* v___x_89_; lean_object* v___x_91_; 
lean_dec_ref(v___x_78_);
lean_dec_ref(v_e_66_);
v___x_89_ = lean_box(0);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 0, v___x_89_);
v___x_91_ = v___x_76_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
else
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
lean_dec_ref(v_e_66_);
v_a_94_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___x_73_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_73_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___boxed(lean_object* v_e_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_e_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec_ref(v_a_103_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(lean_object* v___y_110_){
_start:
{
lean_object* v___x_112_; lean_object* v_ngen_113_; lean_object* v_namePrefix_114_; lean_object* v_idx_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_144_; 
v___x_112_ = lean_st_ref_get(v___y_110_);
v_ngen_113_ = lean_ctor_get(v___x_112_, 2);
lean_inc_ref(v_ngen_113_);
lean_dec(v___x_112_);
v_namePrefix_114_ = lean_ctor_get(v_ngen_113_, 0);
v_idx_115_ = lean_ctor_get(v_ngen_113_, 1);
v_isSharedCheck_144_ = !lean_is_exclusive(v_ngen_113_);
if (v_isSharedCheck_144_ == 0)
{
v___x_117_ = v_ngen_113_;
v_isShared_118_ = v_isSharedCheck_144_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_idx_115_);
lean_inc(v_namePrefix_114_);
lean_dec(v_ngen_113_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_144_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; lean_object* v_env_120_; lean_object* v_nextMacroScope_121_; lean_object* v_auxDeclNGen_122_; lean_object* v_traceState_123_; lean_object* v_cache_124_; lean_object* v_messages_125_; lean_object* v_infoState_126_; lean_object* v_snapshotTasks_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_142_; 
v___x_119_ = lean_st_ref_take(v___y_110_);
v_env_120_ = lean_ctor_get(v___x_119_, 0);
v_nextMacroScope_121_ = lean_ctor_get(v___x_119_, 1);
v_auxDeclNGen_122_ = lean_ctor_get(v___x_119_, 3);
v_traceState_123_ = lean_ctor_get(v___x_119_, 4);
v_cache_124_ = lean_ctor_get(v___x_119_, 5);
v_messages_125_ = lean_ctor_get(v___x_119_, 6);
v_infoState_126_ = lean_ctor_get(v___x_119_, 7);
v_snapshotTasks_127_ = lean_ctor_get(v___x_119_, 8);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; 
v_unused_143_ = lean_ctor_get(v___x_119_, 2);
lean_dec(v_unused_143_);
v___x_129_ = v___x_119_;
v_isShared_130_ = v_isSharedCheck_142_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_snapshotTasks_127_);
lean_inc(v_infoState_126_);
lean_inc(v_messages_125_);
lean_inc(v_cache_124_);
lean_inc(v_traceState_123_);
lean_inc(v_auxDeclNGen_122_);
lean_inc(v_nextMacroScope_121_);
lean_inc(v_env_120_);
lean_dec(v___x_119_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_142_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v_r_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
lean_inc(v_idx_115_);
lean_inc(v_namePrefix_114_);
v_r_131_ = l_Lean_Name_num___override(v_namePrefix_114_, v_idx_115_);
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_nat_add(v_idx_115_, v___x_132_);
lean_dec(v_idx_115_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v___x_133_);
v___x_135_ = v___x_117_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_namePrefix_114_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v___x_133_);
v___x_135_ = v_reuseFailAlloc_141_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_137_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 2, v___x_135_);
v___x_137_ = v___x_129_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_env_120_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_nextMacroScope_121_);
lean_ctor_set(v_reuseFailAlloc_140_, 2, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_140_, 3, v_auxDeclNGen_122_);
lean_ctor_set(v_reuseFailAlloc_140_, 4, v_traceState_123_);
lean_ctor_set(v_reuseFailAlloc_140_, 5, v_cache_124_);
lean_ctor_set(v_reuseFailAlloc_140_, 6, v_messages_125_);
lean_ctor_set(v_reuseFailAlloc_140_, 7, v_infoState_126_);
lean_ctor_set(v_reuseFailAlloc_140_, 8, v_snapshotTasks_127_);
v___x_137_ = v_reuseFailAlloc_140_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_st_ref_set(v___y_110_, v___x_137_);
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v_r_131_);
return v___x_139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg___boxed(lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(v___y_145_);
lean_dec(v___y_145_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___x_154_; lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
v___x_154_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(v___y_152_);
v_a_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0___boxed(lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec_ref(v___y_163_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(lean_object* v_a_170_, lean_object* v_b_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_n_179_; lean_object* v_d_u2081_180_; lean_object* v_b_u2081_181_; uint8_t v_bi_182_; lean_object* v_d_u2082_183_; lean_object* v_b_u2082_184_; lean_object* v___y_185_; lean_object* v___y_186_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; uint8_t v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; uint8_t v___y_261_; uint8_t v___x_323_; 
v___x_323_ = l_Lean_Expr_isErased(v_a_170_);
if (v___x_323_ == 0)
{
uint8_t v___x_324_; 
v___x_324_ = l_Lean_Expr_isErased(v_b_171_);
v___y_261_ = v___x_324_;
goto v___jp_260_;
}
else
{
v___y_261_ = v___x_323_;
goto v___jp_260_;
}
v___jp_178_:
{
lean_object* v___x_190_; 
lean_inc_ref(v___y_185_);
lean_inc_ref(v_d_u2081_180_);
v___x_190_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_d_u2081_180_, v_d_u2082_183_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; uint8_t v___x_192_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_191_);
v___x_192_ = lean_unbox(v_a_191_);
lean_dec(v_a_191_);
if (v___x_192_ == 0)
{
lean_dec_ref(v___y_185_);
lean_dec_ref(v_b_u2082_184_);
lean_dec_ref(v_b_u2081_181_);
lean_dec_ref(v_d_u2081_180_);
lean_dec(v_n_179_);
return v___x_190_;
}
else
{
lean_object* v___x_193_; 
lean_dec_ref(v___x_190_);
v___x_193_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_a_194_);
lean_dec_ref(v___x_193_);
lean_inc(v_a_194_);
v___x_195_ = l_Lean_Expr_fvar___override(v_a_194_);
v___x_196_ = 0;
v___x_197_ = l_Lean_LocalContext_mkLocalDecl(v___y_185_, v_a_194_, v_n_179_, v_d_u2081_180_, v_bi_182_, v___x_196_);
v___x_198_ = lean_expr_instantiate1(v_b_u2081_181_, v___x_195_);
lean_dec_ref(v_b_u2081_181_);
v___x_199_ = lean_expr_instantiate1(v_b_u2082_184_, v___x_195_);
lean_dec_ref(v___x_195_);
lean_dec_ref(v_b_u2082_184_);
v_a_170_ = v___x_198_;
v_b_171_ = v___x_199_;
v_a_172_ = v___x_197_;
v_a_173_ = v___y_186_;
v_a_174_ = v___y_187_;
v_a_175_ = v___y_188_;
v_a_176_ = v___y_189_;
goto _start;
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec_ref(v___y_185_);
lean_dec_ref(v_b_u2082_184_);
lean_dec_ref(v_b_u2081_181_);
lean_dec_ref(v_d_u2081_180_);
lean_dec(v_n_179_);
v_a_201_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_193_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_193_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_185_);
lean_dec_ref(v_b_u2082_184_);
lean_dec_ref(v_b_u2081_181_);
lean_dec_ref(v_d_u2081_180_);
lean_dec(v_n_179_);
return v___x_190_;
}
}
v___jp_209_:
{
uint8_t v___x_216_; 
v___x_216_ = l_Lean_Expr_isLambda(v_a_170_);
if (v___x_216_ == 0)
{
uint8_t v___x_217_; 
v___x_217_ = l_Lean_Expr_isLambda(v_b_171_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec_ref(v___y_211_);
lean_dec_ref(v_b_171_);
lean_dec_ref(v_a_170_);
v___x_218_ = lean_box(v___x_217_);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
else
{
lean_object* v___x_220_; 
v___x_220_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_a_170_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_231_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_231_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_231_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_231_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
if (lean_obj_tag(v_a_221_) == 1)
{
lean_object* v_val_225_; 
lean_del_object(v___x_223_);
v_val_225_ = lean_ctor_get(v_a_221_, 0);
lean_inc(v_val_225_);
lean_dec_ref(v_a_221_);
v_a_170_ = v_val_225_;
v_a_172_ = v___y_211_;
v_a_173_ = v___y_212_;
v_a_174_ = v___y_213_;
v_a_175_ = v___y_214_;
v_a_176_ = v___y_215_;
goto _start;
}
else
{
lean_object* v___x_227_; lean_object* v___x_229_; 
lean_dec(v_a_221_);
lean_dec_ref(v___y_211_);
lean_dec_ref(v_b_171_);
v___x_227_ = lean_box(v___x_216_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_227_);
v___x_229_ = v___x_223_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
lean_dec_ref(v___y_211_);
lean_dec_ref(v_b_171_);
v_a_232_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_220_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_220_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
else
{
lean_object* v___x_240_; 
v___x_240_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_b_171_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_251_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_251_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_251_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_251_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
if (lean_obj_tag(v_a_241_) == 1)
{
lean_object* v_val_245_; 
lean_del_object(v___x_243_);
v_val_245_ = lean_ctor_get(v_a_241_, 0);
lean_inc(v_val_245_);
lean_dec_ref(v_a_241_);
v_b_171_ = v_val_245_;
v_a_172_ = v___y_211_;
v_a_173_ = v___y_212_;
v_a_174_ = v___y_213_;
v_a_175_ = v___y_214_;
v_a_176_ = v___y_215_;
goto _start;
}
else
{
lean_object* v___x_247_; lean_object* v___x_249_; 
lean_dec(v_a_241_);
lean_dec_ref(v___y_211_);
lean_dec_ref(v_a_170_);
v___x_247_ = lean_box(v___y_210_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_247_);
v___x_249_ = v___x_243_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
lean_dec_ref(v___y_211_);
lean_dec_ref(v_a_170_);
v_a_252_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_240_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_240_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
}
v___jp_260_:
{
uint8_t v___x_262_; 
v___x_262_ = 1;
if (v___y_261_ == 0)
{
lean_object* v_a_x27_263_; lean_object* v_b_x27_264_; uint8_t v___x_265_; 
lean_inc_ref(v_a_170_);
v_a_x27_263_ = l_Lean_Expr_headBeta(v_a_170_);
lean_inc_ref(v_b_171_);
v_b_x27_264_ = l_Lean_Expr_headBeta(v_b_171_);
v___x_265_ = lean_expr_eqv(v_a_170_, v_a_x27_263_);
if (v___x_265_ == 0)
{
lean_dec_ref(v_b_171_);
lean_dec_ref(v_a_170_);
v_a_170_ = v_a_x27_263_;
v_b_171_ = v_b_x27_264_;
goto _start;
}
else
{
uint8_t v___x_267_; 
v___x_267_ = lean_expr_eqv(v_b_171_, v_b_x27_264_);
if (v___x_267_ == 0)
{
lean_dec_ref(v_b_171_);
lean_dec_ref(v_a_170_);
v_a_170_ = v_a_x27_263_;
v_b_171_ = v_b_x27_264_;
goto _start;
}
else
{
uint8_t v___x_269_; 
lean_dec_ref(v_b_x27_264_);
lean_dec_ref(v_a_x27_263_);
v___x_269_ = lean_expr_eqv(v_a_170_, v_b_171_);
if (v___x_269_ == 0)
{
switch(lean_obj_tag(v_a_170_))
{
case 5:
{
switch(lean_obj_tag(v_b_171_))
{
case 5:
{
lean_object* v_fn_270_; lean_object* v_arg_271_; lean_object* v_fn_272_; lean_object* v_arg_273_; lean_object* v___x_274_; 
v_fn_270_ = lean_ctor_get(v_a_170_, 0);
lean_inc_ref(v_fn_270_);
v_arg_271_ = lean_ctor_get(v_a_170_, 1);
lean_inc_ref(v_arg_271_);
lean_dec_ref(v_a_170_);
v_fn_272_ = lean_ctor_get(v_b_171_, 0);
lean_inc_ref(v_fn_272_);
v_arg_273_ = lean_ctor_get(v_b_171_, 1);
lean_inc_ref(v_arg_273_);
lean_dec_ref(v_b_171_);
lean_inc_ref(v_a_172_);
v___x_274_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_fn_270_, v_fn_272_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; uint8_t v___x_276_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_a_275_);
v___x_276_ = lean_unbox(v_a_275_);
lean_dec(v_a_275_);
if (v___x_276_ == 0)
{
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_271_);
lean_dec_ref(v_a_172_);
return v___x_274_;
}
else
{
lean_dec_ref(v___x_274_);
v_a_170_ = v_arg_271_;
v_b_171_ = v_arg_273_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_arg_271_);
lean_dec_ref(v_a_172_);
return v___x_274_;
}
}
case 10:
{
lean_object* v_expr_278_; 
v_expr_278_ = lean_ctor_get(v_b_171_, 1);
lean_inc_ref(v_expr_278_);
lean_dec_ref(v_b_171_);
v_b_171_ = v_expr_278_;
goto _start;
}
default: 
{
v___y_210_ = v___x_269_;
v___y_211_ = v_a_172_;
v___y_212_ = v_a_173_;
v___y_213_ = v_a_174_;
v___y_214_ = v_a_175_;
v___y_215_ = v_a_176_;
goto v___jp_209_;
}
}
}
case 7:
{
switch(lean_obj_tag(v_b_171_))
{
case 7:
{
lean_object* v_binderName_280_; lean_object* v_binderType_281_; lean_object* v_body_282_; uint8_t v_binderInfo_283_; lean_object* v_binderType_284_; lean_object* v_body_285_; 
v_binderName_280_ = lean_ctor_get(v_a_170_, 0);
lean_inc(v_binderName_280_);
v_binderType_281_ = lean_ctor_get(v_a_170_, 1);
lean_inc_ref(v_binderType_281_);
v_body_282_ = lean_ctor_get(v_a_170_, 2);
lean_inc_ref(v_body_282_);
v_binderInfo_283_ = lean_ctor_get_uint8(v_a_170_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_170_);
v_binderType_284_ = lean_ctor_get(v_b_171_, 1);
lean_inc_ref(v_binderType_284_);
v_body_285_ = lean_ctor_get(v_b_171_, 2);
lean_inc_ref(v_body_285_);
lean_dec_ref(v_b_171_);
v_n_179_ = v_binderName_280_;
v_d_u2081_180_ = v_binderType_281_;
v_b_u2081_181_ = v_body_282_;
v_bi_182_ = v_binderInfo_283_;
v_d_u2082_183_ = v_binderType_284_;
v_b_u2082_184_ = v_body_285_;
v___y_185_ = v_a_172_;
v___y_186_ = v_a_173_;
v___y_187_ = v_a_174_;
v___y_188_ = v_a_175_;
v___y_189_ = v_a_176_;
goto v___jp_178_;
}
case 10:
{
lean_object* v_expr_286_; 
v_expr_286_ = lean_ctor_get(v_b_171_, 1);
lean_inc_ref(v_expr_286_);
lean_dec_ref(v_b_171_);
v_b_171_ = v_expr_286_;
goto _start;
}
default: 
{
v___y_210_ = v___x_269_;
v___y_211_ = v_a_172_;
v___y_212_ = v_a_173_;
v___y_213_ = v_a_174_;
v___y_214_ = v_a_175_;
v___y_215_ = v_a_176_;
goto v___jp_209_;
}
}
}
case 6:
{
switch(lean_obj_tag(v_b_171_))
{
case 6:
{
lean_object* v_binderName_288_; lean_object* v_binderType_289_; lean_object* v_body_290_; uint8_t v_binderInfo_291_; lean_object* v_binderType_292_; lean_object* v_body_293_; 
v_binderName_288_ = lean_ctor_get(v_a_170_, 0);
lean_inc(v_binderName_288_);
v_binderType_289_ = lean_ctor_get(v_a_170_, 1);
lean_inc_ref(v_binderType_289_);
v_body_290_ = lean_ctor_get(v_a_170_, 2);
lean_inc_ref(v_body_290_);
v_binderInfo_291_ = lean_ctor_get_uint8(v_a_170_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_170_);
v_binderType_292_ = lean_ctor_get(v_b_171_, 1);
lean_inc_ref(v_binderType_292_);
v_body_293_ = lean_ctor_get(v_b_171_, 2);
lean_inc_ref(v_body_293_);
lean_dec_ref(v_b_171_);
v_n_179_ = v_binderName_288_;
v_d_u2081_180_ = v_binderType_289_;
v_b_u2081_181_ = v_body_290_;
v_bi_182_ = v_binderInfo_291_;
v_d_u2082_183_ = v_binderType_292_;
v_b_u2082_184_ = v_body_293_;
v___y_185_ = v_a_172_;
v___y_186_ = v_a_173_;
v___y_187_ = v_a_174_;
v___y_188_ = v_a_175_;
v___y_189_ = v_a_176_;
goto v___jp_178_;
}
case 10:
{
lean_object* v_expr_294_; 
v_expr_294_ = lean_ctor_get(v_b_171_, 1);
lean_inc_ref(v_expr_294_);
lean_dec_ref(v_b_171_);
v_b_171_ = v_expr_294_;
goto _start;
}
default: 
{
v___y_210_ = v___x_269_;
v___y_211_ = v_a_172_;
v___y_212_ = v_a_173_;
v___y_213_ = v_a_174_;
v___y_214_ = v_a_175_;
v___y_215_ = v_a_176_;
goto v___jp_209_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_b_171_))
{
case 3:
{
lean_object* v_u_296_; lean_object* v_u_297_; uint8_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec_ref(v_a_172_);
v_u_296_ = lean_ctor_get(v_a_170_, 0);
lean_inc(v_u_296_);
lean_dec_ref(v_a_170_);
v_u_297_ = lean_ctor_get(v_b_171_, 0);
lean_inc(v_u_297_);
lean_dec_ref(v_b_171_);
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
v_expr_301_ = lean_ctor_get(v_b_171_, 1);
lean_inc_ref(v_expr_301_);
lean_dec_ref(v_b_171_);
v_b_171_ = v_expr_301_;
goto _start;
}
default: 
{
v___y_210_ = v___x_269_;
v___y_211_ = v_a_172_;
v___y_212_ = v_a_173_;
v___y_213_ = v_a_174_;
v___y_214_ = v_a_175_;
v___y_215_ = v_a_176_;
goto v___jp_209_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_b_171_))
{
case 4:
{
lean_object* v_declName_303_; lean_object* v_us_304_; lean_object* v_declName_305_; lean_object* v_us_306_; uint8_t v___x_307_; 
lean_dec_ref(v_a_172_);
v_declName_303_ = lean_ctor_get(v_a_170_, 0);
lean_inc(v_declName_303_);
v_us_304_ = lean_ctor_get(v_a_170_, 1);
lean_inc(v_us_304_);
lean_dec_ref(v_a_170_);
v_declName_305_ = lean_ctor_get(v_b_171_, 0);
lean_inc(v_declName_305_);
v_us_306_ = lean_ctor_get(v_b_171_, 1);
lean_inc(v_us_306_);
lean_dec_ref(v_b_171_);
v___x_307_ = lean_name_eq(v_declName_303_, v_declName_305_);
lean_dec(v_declName_305_);
lean_dec(v_declName_303_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec(v_us_306_);
lean_dec(v_us_304_);
v___x_308_ = lean_box(v___x_307_);
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
v_expr_313_ = lean_ctor_get(v_b_171_, 1);
lean_inc_ref(v_expr_313_);
lean_dec_ref(v_b_171_);
v_b_171_ = v_expr_313_;
goto _start;
}
default: 
{
v___y_210_ = v___x_269_;
v___y_211_ = v_a_172_;
v___y_212_ = v_a_173_;
v___y_213_ = v_a_174_;
v___y_214_ = v_a_175_;
v___y_215_ = v_a_176_;
goto v___jp_209_;
}
}
}
case 10:
{
lean_object* v_expr_315_; 
v_expr_315_ = lean_ctor_get(v_a_170_, 1);
lean_inc_ref(v_expr_315_);
lean_dec_ref(v_a_170_);
v_a_170_ = v_expr_315_;
goto _start;
}
default: 
{
if (lean_obj_tag(v_b_171_) == 10)
{
lean_object* v_expr_317_; 
v_expr_317_ = lean_ctor_get(v_b_171_, 1);
lean_inc_ref(v_expr_317_);
lean_dec_ref(v_b_171_);
v_b_171_ = v_expr_317_;
goto _start;
}
else
{
v___y_210_ = v___x_269_;
v___y_211_ = v_a_172_;
v___y_212_ = v_a_173_;
v___y_213_ = v_a_174_;
v___y_214_ = v_a_175_;
v___y_215_ = v_a_176_;
goto v___jp_209_;
}
}
}
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref(v_a_172_);
lean_dec_ref(v_b_171_);
lean_dec_ref(v_a_170_);
v___x_319_ = lean_box(v___x_262_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
}
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec_ref(v_a_172_);
lean_dec_ref(v_b_171_);
lean_dec_ref(v_a_170_);
v___x_321_ = lean_box(v___x_262_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull___boxed(lean_object* v_a_325_, lean_object* v_b_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_a_325_, v_b_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0(lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(v___y_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___boxed(lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0(v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(lean_object* v_a_348_, lean_object* v_b_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
uint8_t v___x_356_; 
lean_inc_ref(v_b_349_);
lean_inc_ref(v_a_348_);
v___x_356_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_a_348_, v_b_349_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
lean_inc_ref(v_a_350_);
v___x_357_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_a_348_, v_b_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
return v___x_357_;
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec_ref(v_b_349_);
lean_dec_ref(v_a_348_);
v___x_358_ = lean_box(v___x_356_);
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes___boxed(lean_object* v_a_360_, lean_object* v_b_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(v_a_360_, v_b_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec_ref(v_a_362_);
return v_res_368_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_CompatibleTypes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
