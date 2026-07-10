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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* v_d_u2081_19_; lean_object* v_b_u2081_20_; lean_object* v_d_u2082_21_; lean_object* v_b_u2082_22_; lean_object* v___y_26_; uint8_t v___y_27_; lean_object* v___y_28_; uint8_t v___y_29_; uint8_t v___y_56_; uint8_t v___x_64_; 
v___x_64_ = l_Lean_Expr_isErased(v_a_16_);
if (v___x_64_ == 0)
{
uint8_t v___x_65_; 
v___x_65_ = l_Lean_Expr_isErased(v_b_17_);
v___y_56_ = v___x_65_;
goto v___jp_55_;
}
else
{
v___y_56_ = v___x_64_;
goto v___jp_55_;
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
if (v___y_29_ == 0)
{
uint8_t v___x_30_; 
lean_dec_ref(v___y_28_);
lean_dec_ref(v___y_26_);
v___x_30_ = lean_expr_eqv(v_a_16_, v_b_17_);
if (v___x_30_ == 0)
{
switch(lean_obj_tag(v_a_16_))
{
case 5:
{
if (lean_obj_tag(v_b_17_) == 5)
{
lean_object* v_fn_31_; lean_object* v_arg_32_; lean_object* v_fn_33_; lean_object* v_arg_34_; uint8_t v___x_35_; 
v_fn_31_ = lean_ctor_get(v_a_16_, 0);
lean_inc_ref(v_fn_31_);
v_arg_32_ = lean_ctor_get(v_a_16_, 1);
lean_inc_ref(v_arg_32_);
lean_dec_ref_known(v_a_16_, 2);
v_fn_33_ = lean_ctor_get(v_b_17_, 0);
lean_inc_ref(v_fn_33_);
v_arg_34_ = lean_ctor_get(v_b_17_, 1);
lean_inc_ref(v_arg_34_);
lean_dec_ref_known(v_b_17_, 2);
v___x_35_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_fn_31_, v_fn_33_);
if (v___x_35_ == 0)
{
lean_dec_ref(v_arg_34_);
lean_dec_ref(v_arg_32_);
return v___x_35_;
}
else
{
v_a_16_ = v_arg_32_;
v_b_17_ = v_arg_34_;
goto _start;
}
}
else
{
lean_dec_ref_known(v_a_16_, 2);
lean_dec_ref(v_b_17_);
return v___x_30_;
}
}
case 7:
{
if (lean_obj_tag(v_b_17_) == 7)
{
lean_object* v_binderType_37_; lean_object* v_body_38_; lean_object* v_binderType_39_; lean_object* v_body_40_; 
v_binderType_37_ = lean_ctor_get(v_a_16_, 1);
lean_inc_ref(v_binderType_37_);
v_body_38_ = lean_ctor_get(v_a_16_, 2);
lean_inc_ref(v_body_38_);
lean_dec_ref_known(v_a_16_, 3);
v_binderType_39_ = lean_ctor_get(v_b_17_, 1);
lean_inc_ref(v_binderType_39_);
v_body_40_ = lean_ctor_get(v_b_17_, 2);
lean_inc_ref(v_body_40_);
lean_dec_ref_known(v_b_17_, 3);
v_d_u2081_19_ = v_binderType_37_;
v_b_u2081_20_ = v_body_38_;
v_d_u2082_21_ = v_binderType_39_;
v_b_u2082_22_ = v_body_40_;
goto v___jp_18_;
}
else
{
lean_dec_ref_known(v_a_16_, 3);
lean_dec_ref(v_b_17_);
return v___x_30_;
}
}
case 6:
{
if (lean_obj_tag(v_b_17_) == 6)
{
lean_object* v_binderType_41_; lean_object* v_body_42_; lean_object* v_binderType_43_; lean_object* v_body_44_; 
v_binderType_41_ = lean_ctor_get(v_a_16_, 1);
lean_inc_ref(v_binderType_41_);
v_body_42_ = lean_ctor_get(v_a_16_, 2);
lean_inc_ref(v_body_42_);
lean_dec_ref_known(v_a_16_, 3);
v_binderType_43_ = lean_ctor_get(v_b_17_, 1);
lean_inc_ref(v_binderType_43_);
v_body_44_ = lean_ctor_get(v_b_17_, 2);
lean_inc_ref(v_body_44_);
lean_dec_ref_known(v_b_17_, 3);
v_d_u2081_19_ = v_binderType_41_;
v_b_u2081_20_ = v_body_42_;
v_d_u2082_21_ = v_binderType_43_;
v_b_u2082_22_ = v_body_44_;
goto v___jp_18_;
}
else
{
lean_dec_ref_known(v_a_16_, 3);
lean_dec_ref(v_b_17_);
return v___x_30_;
}
}
case 3:
{
if (lean_obj_tag(v_b_17_) == 3)
{
lean_object* v_u_45_; lean_object* v_u_46_; uint8_t v___x_47_; 
v_u_45_ = lean_ctor_get(v_a_16_, 0);
lean_inc(v_u_45_);
lean_dec_ref_known(v_a_16_, 1);
v_u_46_ = lean_ctor_get(v_b_17_, 0);
lean_inc(v_u_46_);
lean_dec_ref_known(v_b_17_, 1);
v___x_47_ = l_Lean_Level_isEquiv(v_u_45_, v_u_46_);
lean_dec(v_u_46_);
lean_dec(v_u_45_);
return v___x_47_;
}
else
{
lean_dec_ref_known(v_a_16_, 1);
lean_dec_ref(v_b_17_);
return v___x_30_;
}
}
case 4:
{
if (lean_obj_tag(v_b_17_) == 4)
{
lean_object* v_declName_48_; lean_object* v_us_49_; lean_object* v_declName_50_; lean_object* v_us_51_; uint8_t v___x_52_; 
v_declName_48_ = lean_ctor_get(v_a_16_, 0);
lean_inc(v_declName_48_);
v_us_49_ = lean_ctor_get(v_a_16_, 1);
lean_inc(v_us_49_);
lean_dec_ref_known(v_a_16_, 2);
v_declName_50_ = lean_ctor_get(v_b_17_, 0);
lean_inc(v_declName_50_);
v_us_51_ = lean_ctor_get(v_b_17_, 1);
lean_inc(v_us_51_);
lean_dec_ref_known(v_b_17_, 2);
v___x_52_ = lean_name_eq(v_declName_48_, v_declName_50_);
lean_dec(v_declName_50_);
lean_dec(v_declName_48_);
if (v___x_52_ == 0)
{
lean_dec(v_us_51_);
lean_dec(v_us_49_);
return v___x_52_;
}
else
{
uint8_t v___x_53_; 
v___x_53_ = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(v_us_49_, v_us_51_);
lean_dec(v_us_51_);
lean_dec(v_us_49_);
return v___x_53_;
}
}
else
{
lean_dec_ref_known(v_a_16_, 2);
lean_dec_ref(v_b_17_);
return v___x_30_;
}
}
default: 
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
return v___x_30_;
}
}
}
else
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
return v___y_27_;
}
}
else
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
v_a_16_ = v___y_26_;
v_b_17_ = v___y_28_;
goto _start;
}
}
v___jp_55_:
{
uint8_t v___x_57_; 
v___x_57_ = 1;
if (v___y_56_ == 0)
{
lean_object* v_a_x27_58_; lean_object* v_b_x27_59_; uint8_t v___x_60_; uint8_t v___x_61_; 
lean_inc_ref(v_a_16_);
v_a_x27_58_ = l_Lean_Expr_headBeta(v_a_16_);
lean_inc_ref(v_b_17_);
v_b_x27_59_ = l_Lean_Expr_headBeta(v_b_17_);
v___x_60_ = lean_expr_eqv(v_a_16_, v_a_x27_58_);
v___x_61_ = lean_bool_not(v___x_60_);
if (v___x_61_ == 0)
{
uint8_t v___x_62_; uint8_t v___x_63_; 
v___x_62_ = lean_expr_eqv(v_b_17_, v_b_x27_59_);
v___x_63_ = lean_bool_not(v___x_62_);
v___y_26_ = v_a_x27_58_;
v___y_27_ = v___x_57_;
v___y_28_ = v_b_x27_59_;
v___y_29_ = v___x_63_;
goto v___jp_25_;
}
else
{
v___y_26_ = v_a_x27_58_;
v___y_27_ = v___x_57_;
v___y_28_ = v_b_x27_59_;
v___y_29_ = v___x_61_;
goto v___jp_25_;
}
}
else
{
lean_dec_ref(v_b_17_);
lean_dec_ref(v_a_16_);
return v___x_57_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compatibleTypesQuick___boxed(lean_object* v_a_66_, lean_object* v_b_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_a_66_, v_b_67_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = l_Lean_Expr_bvar___override(v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(lean_object* v_e_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___x_79_; 
lean_inc_ref(v_e_72_);
v___x_79_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_99_; 
v_a_80_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_99_ == 0)
{
v___x_82_ = v___x_79_;
v_isShared_83_ = v_isSharedCheck_99_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___x_79_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_99_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Expr_headBeta(v_a_80_);
if (lean_obj_tag(v___x_84_) == 7)
{
lean_object* v_binderName_85_; lean_object* v_binderType_86_; uint8_t v_binderInfo_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v_binderName_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_binderName_85_);
v_binderType_86_ = lean_ctor_get(v___x_84_, 1);
lean_inc_ref(v_binderType_86_);
v_binderInfo_87_ = lean_ctor_get_uint8(v___x_84_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_84_, 3);
v___x_88_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0, &l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0_once, _init_l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0);
v___x_89_ = l_Lean_Expr_app___override(v_e_72_, v___x_88_);
v___x_90_ = l_Lean_Expr_lam___override(v_binderName_85_, v_binderType_86_, v___x_89_, v_binderInfo_87_);
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v___x_91_);
v___x_93_ = v___x_82_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
else
{
lean_object* v___x_95_; lean_object* v___x_97_; 
lean_dec_ref(v___x_84_);
lean_dec_ref(v_e_72_);
v___x_95_ = lean_box(0);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v___x_95_);
v___x_97_ = v___x_82_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
else
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
lean_dec_ref(v_e_72_);
v_a_100_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_107_ == 0)
{
v___x_102_ = v___x_79_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_79_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_100_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___boxed(lean_object* v_e_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_e_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec_ref(v_a_109_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(lean_object* v___y_116_){
_start:
{
lean_object* v___x_118_; lean_object* v_ngen_119_; lean_object* v_namePrefix_120_; lean_object* v_idx_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_150_; 
v___x_118_ = lean_st_ref_get(v___y_116_);
v_ngen_119_ = lean_ctor_get(v___x_118_, 2);
lean_inc_ref(v_ngen_119_);
lean_dec(v___x_118_);
v_namePrefix_120_ = lean_ctor_get(v_ngen_119_, 0);
v_idx_121_ = lean_ctor_get(v_ngen_119_, 1);
v_isSharedCheck_150_ = !lean_is_exclusive(v_ngen_119_);
if (v_isSharedCheck_150_ == 0)
{
v___x_123_ = v_ngen_119_;
v_isShared_124_ = v_isSharedCheck_150_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_idx_121_);
lean_inc(v_namePrefix_120_);
lean_dec(v_ngen_119_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_150_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v_env_126_; lean_object* v_nextMacroScope_127_; lean_object* v_auxDeclNGen_128_; lean_object* v_traceState_129_; lean_object* v_cache_130_; lean_object* v_messages_131_; lean_object* v_infoState_132_; lean_object* v_snapshotTasks_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_148_; 
v___x_125_ = lean_st_ref_take(v___y_116_);
v_env_126_ = lean_ctor_get(v___x_125_, 0);
v_nextMacroScope_127_ = lean_ctor_get(v___x_125_, 1);
v_auxDeclNGen_128_ = lean_ctor_get(v___x_125_, 3);
v_traceState_129_ = lean_ctor_get(v___x_125_, 4);
v_cache_130_ = lean_ctor_get(v___x_125_, 5);
v_messages_131_ = lean_ctor_get(v___x_125_, 6);
v_infoState_132_ = lean_ctor_get(v___x_125_, 7);
v_snapshotTasks_133_ = lean_ctor_get(v___x_125_, 8);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_148_ == 0)
{
lean_object* v_unused_149_; 
v_unused_149_ = lean_ctor_get(v___x_125_, 2);
lean_dec(v_unused_149_);
v___x_135_ = v___x_125_;
v_isShared_136_ = v_isSharedCheck_148_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_snapshotTasks_133_);
lean_inc(v_infoState_132_);
lean_inc(v_messages_131_);
lean_inc(v_cache_130_);
lean_inc(v_traceState_129_);
lean_inc(v_auxDeclNGen_128_);
lean_inc(v_nextMacroScope_127_);
lean_inc(v_env_126_);
lean_dec(v___x_125_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_148_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v_r_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_141_; 
lean_inc(v_idx_121_);
lean_inc(v_namePrefix_120_);
v_r_137_ = l_Lean_Name_num___override(v_namePrefix_120_, v_idx_121_);
v___x_138_ = lean_unsigned_to_nat(1u);
v___x_139_ = lean_nat_add(v_idx_121_, v___x_138_);
lean_dec(v_idx_121_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v___x_139_);
v___x_141_ = v___x_123_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_namePrefix_120_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v___x_139_);
v___x_141_ = v_reuseFailAlloc_147_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_143_; 
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 2, v___x_141_);
v___x_143_ = v___x_135_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_env_126_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_nextMacroScope_127_);
lean_ctor_set(v_reuseFailAlloc_146_, 2, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_146_, 3, v_auxDeclNGen_128_);
lean_ctor_set(v_reuseFailAlloc_146_, 4, v_traceState_129_);
lean_ctor_set(v_reuseFailAlloc_146_, 5, v_cache_130_);
lean_ctor_set(v_reuseFailAlloc_146_, 6, v_messages_131_);
lean_ctor_set(v_reuseFailAlloc_146_, 7, v_infoState_132_);
lean_ctor_set(v_reuseFailAlloc_146_, 8, v_snapshotTasks_133_);
v___x_143_ = v_reuseFailAlloc_146_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_st_ref_set(v___y_116_, v___x_143_);
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v_r_137_);
return v___x_145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg___boxed(lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(v___y_151_);
lean_dec(v___y_151_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v___x_160_; lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_168_; 
v___x_160_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(v___y_158_);
v_a_161_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_168_ == 0)
{
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_161_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0___boxed(lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec_ref(v___y_169_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(lean_object* v_a_176_, lean_object* v_b_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_n_185_; lean_object* v_d_u2081_186_; lean_object* v_b_u2081_187_; uint8_t v_bi_188_; lean_object* v_d_u2082_189_; lean_object* v_b_u2082_190_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_193_; lean_object* v___y_194_; lean_object* v___y_195_; uint8_t v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_267_; lean_object* v___y_268_; uint8_t v___y_269_; uint8_t v___y_270_; uint8_t v___y_325_; uint8_t v___x_335_; 
v___x_335_ = l_Lean_Expr_isErased(v_a_176_);
if (v___x_335_ == 0)
{
uint8_t v___x_336_; 
v___x_336_ = l_Lean_Expr_isErased(v_b_177_);
v___y_325_ = v___x_336_;
goto v___jp_324_;
}
else
{
v___y_325_ = v___x_335_;
goto v___jp_324_;
}
v___jp_184_:
{
lean_object* v___x_196_; 
lean_inc_ref(v___y_191_);
lean_inc_ref(v_d_u2081_186_);
v___x_196_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_d_u2081_186_, v_d_u2082_189_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; uint8_t v___x_198_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_197_);
v___x_198_ = lean_unbox(v_a_197_);
lean_dec(v_a_197_);
if (v___x_198_ == 0)
{
lean_dec_ref(v___y_191_);
lean_dec_ref(v_b_u2082_190_);
lean_dec_ref(v_b_u2081_187_);
lean_dec_ref(v_d_u2081_186_);
lean_dec(v_n_185_);
return v___x_196_;
}
else
{
lean_object* v___x_199_; 
lean_dec_ref_known(v___x_196_, 1);
v___x_199_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; lean_object* v___x_201_; uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc_n(v_a_200_, 2);
lean_dec_ref_known(v___x_199_, 1);
v___x_201_ = l_Lean_Expr_fvar___override(v_a_200_);
v___x_202_ = 0;
v___x_203_ = l_Lean_LocalContext_mkLocalDecl(v___y_191_, v_a_200_, v_n_185_, v_d_u2081_186_, v_bi_188_, v___x_202_);
v___x_204_ = lean_expr_instantiate1(v_b_u2081_187_, v___x_201_);
lean_dec_ref(v_b_u2081_187_);
v___x_205_ = lean_expr_instantiate1(v_b_u2082_190_, v___x_201_);
lean_dec_ref(v___x_201_);
lean_dec_ref(v_b_u2082_190_);
v_a_176_ = v___x_204_;
v_b_177_ = v___x_205_;
v_a_178_ = v___x_203_;
v_a_179_ = v___y_192_;
v_a_180_ = v___y_193_;
v_a_181_ = v___y_194_;
v_a_182_ = v___y_195_;
goto _start;
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
lean_dec_ref(v___y_191_);
lean_dec_ref(v_b_u2082_190_);
lean_dec_ref(v_b_u2081_187_);
lean_dec_ref(v_d_u2081_186_);
lean_dec(v_n_185_);
v_a_207_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_199_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_199_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_191_);
lean_dec_ref(v_b_u2082_190_);
lean_dec_ref(v_b_u2081_187_);
lean_dec_ref(v_d_u2081_186_);
lean_dec(v_n_185_);
return v___x_196_;
}
}
v___jp_215_:
{
uint8_t v___x_222_; 
v___x_222_ = l_Lean_Expr_isLambda(v_a_176_);
if (v___x_222_ == 0)
{
uint8_t v___x_223_; 
v___x_223_ = l_Lean_Expr_isLambda(v_b_177_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec_ref(v___y_217_);
lean_dec_ref(v_b_177_);
lean_dec_ref(v_a_176_);
v___x_224_ = lean_box(v___x_223_);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; 
v___x_226_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_a_176_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_237_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_237_ == 0)
{
v___x_229_ = v___x_226_;
v_isShared_230_ = v_isSharedCheck_237_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_226_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_237_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
if (lean_obj_tag(v_a_227_) == 1)
{
lean_object* v_val_231_; 
lean_del_object(v___x_229_);
v_val_231_ = lean_ctor_get(v_a_227_, 0);
lean_inc(v_val_231_);
lean_dec_ref_known(v_a_227_, 1);
v_a_176_ = v_val_231_;
v_a_178_ = v___y_217_;
v_a_179_ = v___y_218_;
v_a_180_ = v___y_219_;
v_a_181_ = v___y_220_;
v_a_182_ = v___y_221_;
goto _start;
}
else
{
lean_object* v___x_233_; lean_object* v___x_235_; 
lean_dec(v_a_227_);
lean_dec_ref(v___y_217_);
lean_dec_ref(v_b_177_);
v___x_233_ = lean_box(v___x_222_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_233_);
v___x_235_ = v___x_229_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_dec_ref(v___y_217_);
lean_dec_ref(v_b_177_);
v_a_238_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_226_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_226_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
else
{
lean_object* v___x_246_; 
v___x_246_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_b_177_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_257_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_257_ == 0)
{
v___x_249_ = v___x_246_;
v_isShared_250_ = v_isSharedCheck_257_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_246_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_257_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
if (lean_obj_tag(v_a_247_) == 1)
{
lean_object* v_val_251_; 
lean_del_object(v___x_249_);
v_val_251_ = lean_ctor_get(v_a_247_, 0);
lean_inc(v_val_251_);
lean_dec_ref_known(v_a_247_, 1);
v_b_177_ = v_val_251_;
v_a_178_ = v___y_217_;
v_a_179_ = v___y_218_;
v_a_180_ = v___y_219_;
v_a_181_ = v___y_220_;
v_a_182_ = v___y_221_;
goto _start;
}
else
{
lean_object* v___x_253_; lean_object* v___x_255_; 
lean_dec(v_a_247_);
lean_dec_ref(v___y_217_);
lean_dec_ref(v_a_176_);
v___x_253_ = lean_box(v___y_216_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 0, v___x_253_);
v___x_255_ = v___x_249_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_253_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
else
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
lean_dec_ref(v___y_217_);
lean_dec_ref(v_a_176_);
v_a_258_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_246_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_246_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
v___jp_266_:
{
if (v___y_270_ == 0)
{
uint8_t v___x_271_; 
lean_dec_ref(v___y_268_);
lean_dec_ref(v___y_267_);
v___x_271_ = lean_expr_eqv(v_a_176_, v_b_177_);
if (v___x_271_ == 0)
{
switch(lean_obj_tag(v_a_176_))
{
case 5:
{
switch(lean_obj_tag(v_b_177_))
{
case 5:
{
lean_object* v_fn_272_; lean_object* v_arg_273_; lean_object* v_fn_274_; lean_object* v_arg_275_; lean_object* v___x_276_; 
v_fn_272_ = lean_ctor_get(v_a_176_, 0);
lean_inc_ref(v_fn_272_);
v_arg_273_ = lean_ctor_get(v_a_176_, 1);
lean_inc_ref(v_arg_273_);
lean_dec_ref_known(v_a_176_, 2);
v_fn_274_ = lean_ctor_get(v_b_177_, 0);
lean_inc_ref(v_fn_274_);
v_arg_275_ = lean_ctor_get(v_b_177_, 1);
lean_inc_ref(v_arg_275_);
lean_dec_ref_known(v_b_177_, 2);
lean_inc_ref(v_a_178_);
v___x_276_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_fn_272_, v_fn_274_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
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
lean_dec_ref(v_a_178_);
return v___x_276_;
}
else
{
lean_dec_ref_known(v___x_276_, 1);
v_a_176_ = v_arg_273_;
v_b_177_ = v_arg_275_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_275_);
lean_dec_ref(v_arg_273_);
lean_dec_ref(v_a_178_);
return v___x_276_;
}
}
case 10:
{
lean_object* v_expr_280_; 
v_expr_280_ = lean_ctor_get(v_b_177_, 1);
lean_inc_ref(v_expr_280_);
lean_dec_ref_known(v_b_177_, 2);
v_b_177_ = v_expr_280_;
goto _start;
}
default: 
{
v___y_216_ = v___x_271_;
v___y_217_ = v_a_178_;
v___y_218_ = v_a_179_;
v___y_219_ = v_a_180_;
v___y_220_ = v_a_181_;
v___y_221_ = v_a_182_;
goto v___jp_215_;
}
}
}
case 7:
{
switch(lean_obj_tag(v_b_177_))
{
case 7:
{
lean_object* v_binderName_282_; lean_object* v_binderType_283_; lean_object* v_body_284_; uint8_t v_binderInfo_285_; lean_object* v_binderType_286_; lean_object* v_body_287_; 
v_binderName_282_ = lean_ctor_get(v_a_176_, 0);
lean_inc(v_binderName_282_);
v_binderType_283_ = lean_ctor_get(v_a_176_, 1);
lean_inc_ref(v_binderType_283_);
v_body_284_ = lean_ctor_get(v_a_176_, 2);
lean_inc_ref(v_body_284_);
v_binderInfo_285_ = lean_ctor_get_uint8(v_a_176_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_176_, 3);
v_binderType_286_ = lean_ctor_get(v_b_177_, 1);
lean_inc_ref(v_binderType_286_);
v_body_287_ = lean_ctor_get(v_b_177_, 2);
lean_inc_ref(v_body_287_);
lean_dec_ref_known(v_b_177_, 3);
v_n_185_ = v_binderName_282_;
v_d_u2081_186_ = v_binderType_283_;
v_b_u2081_187_ = v_body_284_;
v_bi_188_ = v_binderInfo_285_;
v_d_u2082_189_ = v_binderType_286_;
v_b_u2082_190_ = v_body_287_;
v___y_191_ = v_a_178_;
v___y_192_ = v_a_179_;
v___y_193_ = v_a_180_;
v___y_194_ = v_a_181_;
v___y_195_ = v_a_182_;
goto v___jp_184_;
}
case 10:
{
lean_object* v_expr_288_; 
v_expr_288_ = lean_ctor_get(v_b_177_, 1);
lean_inc_ref(v_expr_288_);
lean_dec_ref_known(v_b_177_, 2);
v_b_177_ = v_expr_288_;
goto _start;
}
default: 
{
v___y_216_ = v___x_271_;
v___y_217_ = v_a_178_;
v___y_218_ = v_a_179_;
v___y_219_ = v_a_180_;
v___y_220_ = v_a_181_;
v___y_221_ = v_a_182_;
goto v___jp_215_;
}
}
}
case 6:
{
switch(lean_obj_tag(v_b_177_))
{
case 6:
{
lean_object* v_binderName_290_; lean_object* v_binderType_291_; lean_object* v_body_292_; uint8_t v_binderInfo_293_; lean_object* v_binderType_294_; lean_object* v_body_295_; 
v_binderName_290_ = lean_ctor_get(v_a_176_, 0);
lean_inc(v_binderName_290_);
v_binderType_291_ = lean_ctor_get(v_a_176_, 1);
lean_inc_ref(v_binderType_291_);
v_body_292_ = lean_ctor_get(v_a_176_, 2);
lean_inc_ref(v_body_292_);
v_binderInfo_293_ = lean_ctor_get_uint8(v_a_176_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_176_, 3);
v_binderType_294_ = lean_ctor_get(v_b_177_, 1);
lean_inc_ref(v_binderType_294_);
v_body_295_ = lean_ctor_get(v_b_177_, 2);
lean_inc_ref(v_body_295_);
lean_dec_ref_known(v_b_177_, 3);
v_n_185_ = v_binderName_290_;
v_d_u2081_186_ = v_binderType_291_;
v_b_u2081_187_ = v_body_292_;
v_bi_188_ = v_binderInfo_293_;
v_d_u2082_189_ = v_binderType_294_;
v_b_u2082_190_ = v_body_295_;
v___y_191_ = v_a_178_;
v___y_192_ = v_a_179_;
v___y_193_ = v_a_180_;
v___y_194_ = v_a_181_;
v___y_195_ = v_a_182_;
goto v___jp_184_;
}
case 10:
{
lean_object* v_expr_296_; 
v_expr_296_ = lean_ctor_get(v_b_177_, 1);
lean_inc_ref(v_expr_296_);
lean_dec_ref_known(v_b_177_, 2);
v_b_177_ = v_expr_296_;
goto _start;
}
default: 
{
v___y_216_ = v___x_271_;
v___y_217_ = v_a_178_;
v___y_218_ = v_a_179_;
v___y_219_ = v_a_180_;
v___y_220_ = v_a_181_;
v___y_221_ = v_a_182_;
goto v___jp_215_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_b_177_))
{
case 3:
{
lean_object* v_u_298_; lean_object* v_u_299_; uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec_ref(v_a_178_);
v_u_298_ = lean_ctor_get(v_a_176_, 0);
lean_inc(v_u_298_);
lean_dec_ref_known(v_a_176_, 1);
v_u_299_ = lean_ctor_get(v_b_177_, 0);
lean_inc(v_u_299_);
lean_dec_ref_known(v_b_177_, 1);
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
v_expr_303_ = lean_ctor_get(v_b_177_, 1);
lean_inc_ref(v_expr_303_);
lean_dec_ref_known(v_b_177_, 2);
v_b_177_ = v_expr_303_;
goto _start;
}
default: 
{
v___y_216_ = v___x_271_;
v___y_217_ = v_a_178_;
v___y_218_ = v_a_179_;
v___y_219_ = v_a_180_;
v___y_220_ = v_a_181_;
v___y_221_ = v_a_182_;
goto v___jp_215_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_b_177_))
{
case 4:
{
lean_object* v_declName_305_; lean_object* v_us_306_; lean_object* v_declName_307_; lean_object* v_us_308_; uint8_t v___x_309_; 
lean_dec_ref(v_a_178_);
v_declName_305_ = lean_ctor_get(v_a_176_, 0);
lean_inc(v_declName_305_);
v_us_306_ = lean_ctor_get(v_a_176_, 1);
lean_inc(v_us_306_);
lean_dec_ref_known(v_a_176_, 2);
v_declName_307_ = lean_ctor_get(v_b_177_, 0);
lean_inc(v_declName_307_);
v_us_308_ = lean_ctor_get(v_b_177_, 1);
lean_inc(v_us_308_);
lean_dec_ref_known(v_b_177_, 2);
v___x_309_ = lean_name_eq(v_declName_305_, v_declName_307_);
lean_dec(v_declName_307_);
lean_dec(v_declName_305_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec(v_us_308_);
lean_dec(v_us_306_);
v___x_310_ = lean_box(v___x_309_);
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
v_expr_315_ = lean_ctor_get(v_b_177_, 1);
lean_inc_ref(v_expr_315_);
lean_dec_ref_known(v_b_177_, 2);
v_b_177_ = v_expr_315_;
goto _start;
}
default: 
{
v___y_216_ = v___x_271_;
v___y_217_ = v_a_178_;
v___y_218_ = v_a_179_;
v___y_219_ = v_a_180_;
v___y_220_ = v_a_181_;
v___y_221_ = v_a_182_;
goto v___jp_215_;
}
}
}
case 10:
{
lean_object* v_expr_317_; 
v_expr_317_ = lean_ctor_get(v_a_176_, 1);
lean_inc_ref(v_expr_317_);
lean_dec_ref_known(v_a_176_, 2);
v_a_176_ = v_expr_317_;
goto _start;
}
default: 
{
if (lean_obj_tag(v_b_177_) == 10)
{
lean_object* v_expr_319_; 
v_expr_319_ = lean_ctor_get(v_b_177_, 1);
lean_inc_ref(v_expr_319_);
lean_dec_ref_known(v_b_177_, 2);
v_b_177_ = v_expr_319_;
goto _start;
}
else
{
v___y_216_ = v___x_271_;
v___y_217_ = v_a_178_;
v___y_218_ = v_a_179_;
v___y_219_ = v_a_180_;
v___y_220_ = v_a_181_;
v___y_221_ = v_a_182_;
goto v___jp_215_;
}
}
}
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec_ref(v_a_178_);
lean_dec_ref(v_b_177_);
lean_dec_ref(v_a_176_);
v___x_321_ = lean_box(v___y_269_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
else
{
lean_dec_ref(v_b_177_);
lean_dec_ref(v_a_176_);
v_a_176_ = v___y_268_;
v_b_177_ = v___y_267_;
goto _start;
}
}
v___jp_324_:
{
uint8_t v___x_326_; 
v___x_326_ = 1;
if (v___y_325_ == 0)
{
lean_object* v_a_x27_327_; lean_object* v_b_x27_328_; uint8_t v___x_329_; uint8_t v___x_330_; 
lean_inc_ref(v_a_176_);
v_a_x27_327_ = l_Lean_Expr_headBeta(v_a_176_);
lean_inc_ref(v_b_177_);
v_b_x27_328_ = l_Lean_Expr_headBeta(v_b_177_);
v___x_329_ = lean_expr_eqv(v_a_176_, v_a_x27_327_);
v___x_330_ = lean_bool_not(v___x_329_);
if (v___x_330_ == 0)
{
uint8_t v___x_331_; uint8_t v___x_332_; 
v___x_331_ = lean_expr_eqv(v_b_177_, v_b_x27_328_);
v___x_332_ = lean_bool_not(v___x_331_);
v___y_267_ = v_b_x27_328_;
v___y_268_ = v_a_x27_327_;
v___y_269_ = v___x_326_;
v___y_270_ = v___x_332_;
goto v___jp_266_;
}
else
{
v___y_267_ = v_b_x27_328_;
v___y_268_ = v_a_x27_327_;
v___y_269_ = v___x_326_;
v___y_270_ = v___x_330_;
goto v___jp_266_;
}
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec_ref(v_a_178_);
lean_dec_ref(v_b_177_);
lean_dec_ref(v_a_176_);
v___x_333_ = lean_box(v___x_326_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull___boxed(lean_object* v_a_337_, lean_object* v_b_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_a_337_, v_b_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0(lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(v___y_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___boxed(lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0(v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(lean_object* v_a_360_, lean_object* v_b_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
uint8_t v___x_368_; 
lean_inc_ref(v_b_361_);
lean_inc_ref(v_a_360_);
v___x_368_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_a_360_, v_b_361_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
lean_inc_ref(v_a_362_);
v___x_369_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_a_360_, v_b_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
return v___x_369_;
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec_ref(v_b_361_);
lean_dec_ref(v_a_360_);
v___x_370_ = lean_box(v___x_368_);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes___boxed(lean_object* v_a_372_, lean_object* v_b_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(v_a_372_, v_b_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec_ref(v_a_374_);
return v_res_380_;
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
