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
uint8_t l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_12_;
v_res_12_ = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(v_x_1_, v_x_2_);
stack->m_num = v_res_12_;
}
LEAN_EXPORT lean_object* l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0___boxed(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(v_x_13_, v_x_14_);
lean_dec(v_x_14_);
lean_dec(v_x_13_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
uint8_t l_Lean_Compiler_LCNF_compatibleTypesQuick(lean_object* v_a_17_, lean_object* v_b_18_){
_start:
{
uint8_t v___y_20_; lean_object* v_d_u2081_21_; lean_object* v_b_u2081_22_; lean_object* v_d_u2082_23_; lean_object* v_b_u2082_24_; uint8_t v___y_28_; uint8_t v___x_60_; 
v___x_60_ = l_Lean_Expr_isErased(v_a_17_);
if (v___x_60_ == 0)
{
uint8_t v___x_61_; 
v___x_61_ = l_Lean_Expr_isErased(v_b_18_);
v___y_28_ = v___x_61_;
goto v___jp_27_;
}
else
{
v___y_28_ = v___x_60_;
goto v___jp_27_;
}
v___jp_19_:
{
uint8_t v___x_25_; 
v___x_25_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_d_u2081_21_, v_d_u2082_23_);
if (v___x_25_ == 0)
{
lean_dec_ref(v_b_u2082_24_);
lean_dec_ref(v_b_u2081_22_);
return v___y_20_;
}
else
{
v_a_17_ = v_b_u2081_22_;
v_b_18_ = v_b_u2082_24_;
goto _start;
}
}
v___jp_27_:
{
uint8_t v___x_29_; 
v___x_29_ = 1;
if (v___y_28_ == 0)
{
lean_object* v_a_x27_30_; lean_object* v_b_x27_31_; uint8_t v___x_32_; 
lean_inc_ref(v_a_17_);
v_a_x27_30_ = l_Lean_Expr_headBeta(v_a_17_);
lean_inc_ref(v_b_18_);
v_b_x27_31_ = l_Lean_Expr_headBeta(v_b_18_);
v___x_32_ = lean_expr_eqv(v_a_17_, v_a_x27_30_);
if (v___x_32_ == 0)
{
lean_dec_ref(v_b_18_);
lean_dec_ref(v_a_17_);
v_a_17_ = v_a_x27_30_;
v_b_18_ = v_b_x27_31_;
goto _start;
}
else
{
uint8_t v___x_34_; 
v___x_34_ = lean_expr_eqv(v_b_18_, v_b_x27_31_);
if (v___x_34_ == 0)
{
lean_dec_ref(v_b_18_);
lean_dec_ref(v_a_17_);
v_a_17_ = v_a_x27_30_;
v_b_18_ = v_b_x27_31_;
goto _start;
}
else
{
uint8_t v___x_36_; 
lean_dec_ref(v_b_x27_31_);
lean_dec_ref(v_a_x27_30_);
v___x_36_ = lean_expr_eqv(v_a_17_, v_b_18_);
if (v___x_36_ == 0)
{
switch(lean_obj_tag(v_a_17_))
{
case 5:
{
if (lean_obj_tag(v_b_18_) == 5)
{
lean_object* v_fn_37_; lean_object* v_arg_38_; lean_object* v_fn_39_; lean_object* v_arg_40_; uint8_t v___x_41_; 
v_fn_37_ = lean_ctor_get(v_a_17_, 0);
lean_inc_ref(v_fn_37_);
v_arg_38_ = lean_ctor_get(v_a_17_, 1);
lean_inc_ref(v_arg_38_);
lean_dec_ref_known(v_a_17_, 2);
v_fn_39_ = lean_ctor_get(v_b_18_, 0);
lean_inc_ref(v_fn_39_);
v_arg_40_ = lean_ctor_get(v_b_18_, 1);
lean_inc_ref(v_arg_40_);
lean_dec_ref_known(v_b_18_, 2);
v___x_41_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_fn_37_, v_fn_39_);
if (v___x_41_ == 0)
{
lean_dec_ref(v_arg_40_);
lean_dec_ref(v_arg_38_);
return v___x_36_;
}
else
{
v_a_17_ = v_arg_38_;
v_b_18_ = v_arg_40_;
goto _start;
}
}
else
{
lean_dec_ref_known(v_a_17_, 2);
lean_dec_ref(v_b_18_);
return v___x_36_;
}
}
case 7:
{
if (lean_obj_tag(v_b_18_) == 7)
{
lean_object* v_binderType_43_; lean_object* v_body_44_; lean_object* v_binderType_45_; lean_object* v_body_46_; 
v_binderType_43_ = lean_ctor_get(v_a_17_, 1);
lean_inc_ref(v_binderType_43_);
v_body_44_ = lean_ctor_get(v_a_17_, 2);
lean_inc_ref(v_body_44_);
lean_dec_ref_known(v_a_17_, 3);
v_binderType_45_ = lean_ctor_get(v_b_18_, 1);
lean_inc_ref(v_binderType_45_);
v_body_46_ = lean_ctor_get(v_b_18_, 2);
lean_inc_ref(v_body_46_);
lean_dec_ref_known(v_b_18_, 3);
v___y_20_ = v___x_36_;
v_d_u2081_21_ = v_binderType_43_;
v_b_u2081_22_ = v_body_44_;
v_d_u2082_23_ = v_binderType_45_;
v_b_u2082_24_ = v_body_46_;
goto v___jp_19_;
}
else
{
lean_dec_ref_known(v_a_17_, 3);
lean_dec_ref(v_b_18_);
return v___x_36_;
}
}
case 6:
{
if (lean_obj_tag(v_b_18_) == 6)
{
lean_object* v_binderType_47_; lean_object* v_body_48_; lean_object* v_binderType_49_; lean_object* v_body_50_; 
v_binderType_47_ = lean_ctor_get(v_a_17_, 1);
lean_inc_ref(v_binderType_47_);
v_body_48_ = lean_ctor_get(v_a_17_, 2);
lean_inc_ref(v_body_48_);
lean_dec_ref_known(v_a_17_, 3);
v_binderType_49_ = lean_ctor_get(v_b_18_, 1);
lean_inc_ref(v_binderType_49_);
v_body_50_ = lean_ctor_get(v_b_18_, 2);
lean_inc_ref(v_body_50_);
lean_dec_ref_known(v_b_18_, 3);
v___y_20_ = v___x_36_;
v_d_u2081_21_ = v_binderType_47_;
v_b_u2081_22_ = v_body_48_;
v_d_u2082_23_ = v_binderType_49_;
v_b_u2082_24_ = v_body_50_;
goto v___jp_19_;
}
else
{
lean_dec_ref_known(v_a_17_, 3);
lean_dec_ref(v_b_18_);
return v___x_36_;
}
}
case 3:
{
if (lean_obj_tag(v_b_18_) == 3)
{
lean_object* v_u_51_; lean_object* v_u_52_; uint8_t v___x_53_; 
v_u_51_ = lean_ctor_get(v_a_17_, 0);
lean_inc(v_u_51_);
lean_dec_ref_known(v_a_17_, 1);
v_u_52_ = lean_ctor_get(v_b_18_, 0);
lean_inc(v_u_52_);
lean_dec_ref_known(v_b_18_, 1);
v___x_53_ = l_Lean_Level_isEquiv(v_u_51_, v_u_52_);
lean_dec(v_u_52_);
lean_dec(v_u_51_);
return v___x_53_;
}
else
{
lean_dec_ref_known(v_a_17_, 1);
lean_dec_ref(v_b_18_);
return v___x_36_;
}
}
case 4:
{
if (lean_obj_tag(v_b_18_) == 4)
{
lean_object* v_declName_54_; lean_object* v_us_55_; lean_object* v_declName_56_; lean_object* v_us_57_; uint8_t v___x_58_; 
v_declName_54_ = lean_ctor_get(v_a_17_, 0);
lean_inc(v_declName_54_);
v_us_55_ = lean_ctor_get(v_a_17_, 1);
lean_inc(v_us_55_);
lean_dec_ref_known(v_a_17_, 2);
v_declName_56_ = lean_ctor_get(v_b_18_, 0);
lean_inc(v_declName_56_);
v_us_57_ = lean_ctor_get(v_b_18_, 1);
lean_inc(v_us_57_);
lean_dec_ref_known(v_b_18_, 2);
v___x_58_ = lean_name_eq(v_declName_54_, v_declName_56_);
lean_dec(v_declName_56_);
lean_dec(v_declName_54_);
if (v___x_58_ == 0)
{
lean_dec(v_us_57_);
lean_dec(v_us_55_);
return v___x_36_;
}
else
{
uint8_t v___x_59_; 
v___x_59_ = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(v_us_55_, v_us_57_);
lean_dec(v_us_57_);
lean_dec(v_us_55_);
return v___x_59_;
}
}
else
{
lean_dec_ref_known(v_a_17_, 2);
lean_dec_ref(v_b_18_);
return v___x_36_;
}
}
default: 
{
lean_dec_ref(v_b_18_);
lean_dec_ref(v_a_17_);
return v___x_36_;
}
}
}
else
{
lean_dec_ref(v_b_18_);
lean_dec_ref(v_a_17_);
return v___x_29_;
}
}
}
}
else
{
lean_dec_ref(v_b_18_);
lean_dec_ref(v_a_17_);
return v___x_29_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_compatibleTypesQuick_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_17_ = stack[0].m_obj;
lean_object* v_b_18_ = stack[1].m_obj;
uint8_t v_res_62_;
v_res_62_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_a_17_, v_b_18_);
stack->m_num = v_res_62_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compatibleTypesQuick___boxed(lean_object* v_a_63_, lean_object* v_b_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_a_63_, v_b_64_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = l_Lean_Expr_bvar___override(v___x_67_);
return v___x_68_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(lean_object* v_e_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v___x_76_; 
lean_inc_ref(v_e_69_);
v___x_76_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(v_e_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_96_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_96_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_96_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_96_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_Expr_headBeta(v_a_77_);
if (lean_obj_tag(v___x_81_) == 7)
{
lean_object* v_binderName_82_; lean_object* v_binderType_83_; uint8_t v_binderInfo_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_90_; 
v_binderName_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_binderName_82_);
v_binderType_83_ = lean_ctor_get(v___x_81_, 1);
lean_inc_ref(v_binderType_83_);
v_binderInfo_84_ = lean_ctor_get_uint8(v___x_81_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_81_, 3);
v___x_85_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0, &l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0_once, _init_l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___closed__0);
v___x_86_ = l_Lean_Expr_app___override(v_e_69_, v___x_85_);
v___x_87_ = l_Lean_Expr_lam___override(v_binderName_82_, v_binderType_83_, v___x_86_, v_binderInfo_84_);
v___x_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_88_);
v___x_90_ = v___x_79_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_88_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
else
{
lean_object* v___x_92_; lean_object* v___x_94_; 
lean_dec_ref(v___x_81_);
lean_dec_ref(v_e_69_);
v___x_92_ = lean_box(0);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_92_);
v___x_94_ = v___x_79_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
else
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
lean_dec_ref(v_e_69_);
v_a_97_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_104_ == 0)
{
v___x_99_ = v___x_76_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_76_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_97_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_69_ = stack[0].m_obj;
lean_object* v_a_70_ = stack[1].m_obj;
lean_object* v_a_71_ = stack[2].m_obj;
lean_object* v_a_72_ = stack[3].m_obj;
lean_object* v_a_73_ = stack[4].m_obj;
lean_object* v_a_74_ = stack[5].m_obj;
lean_object* v_res_105_;
v_res_105_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_e_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
stack->m_obj
 = v_res_105_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f___boxed(lean_object* v_e_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_e_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec_ref(v_a_107_);
return v_res_113_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(lean_object* v___y_114_){
_start:
{
lean_object* v___x_116_; lean_object* v_ngen_117_; lean_object* v_namePrefix_118_; lean_object* v_idx_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_149_; 
v___x_116_ = lean_st_ref_get(v___y_114_);
v_ngen_117_ = lean_ctor_get(v___x_116_, 2);
lean_inc_ref(v_ngen_117_);
lean_dec(v___x_116_);
v_namePrefix_118_ = lean_ctor_get(v_ngen_117_, 0);
v_idx_119_ = lean_ctor_get(v_ngen_117_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_ngen_117_);
if (v_isSharedCheck_149_ == 0)
{
v___x_121_ = v_ngen_117_;
v_isShared_122_ = v_isSharedCheck_149_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_idx_119_);
lean_inc(v_namePrefix_118_);
lean_dec(v_ngen_117_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_149_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v_r_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
lean_inc(v_idx_119_);
lean_inc(v_namePrefix_118_);
v_r_123_ = l_Lean_Name_num___override(v_namePrefix_118_, v_idx_119_);
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_nat_add(v_idx_119_, v___x_124_);
lean_dec(v_idx_119_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v___x_125_);
v___x_127_ = v___x_121_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_namePrefix_118_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_125_);
v___x_127_ = v_reuseFailAlloc_148_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_128_; lean_object* v_env_129_; lean_object* v_nextMacroScope_130_; lean_object* v_auxDeclNGen_131_; lean_object* v_traceState_132_; lean_object* v_cache_133_; lean_object* v_recordedDeps_134_; lean_object* v_messages_135_; lean_object* v_infoState_136_; lean_object* v_snapshotTasks_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_146_; 
v___x_128_ = lean_st_ref_take(v___y_114_);
v_env_129_ = lean_ctor_get(v___x_128_, 0);
v_nextMacroScope_130_ = lean_ctor_get(v___x_128_, 1);
v_auxDeclNGen_131_ = lean_ctor_get(v___x_128_, 3);
v_traceState_132_ = lean_ctor_get(v___x_128_, 4);
v_cache_133_ = lean_ctor_get(v___x_128_, 5);
v_recordedDeps_134_ = lean_ctor_get(v___x_128_, 6);
v_messages_135_ = lean_ctor_get(v___x_128_, 7);
v_infoState_136_ = lean_ctor_get(v___x_128_, 8);
v_snapshotTasks_137_ = lean_ctor_get(v___x_128_, 9);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_146_ == 0)
{
lean_object* v_unused_147_; 
v_unused_147_ = lean_ctor_get(v___x_128_, 2);
lean_dec(v_unused_147_);
v___x_139_ = v___x_128_;
v_isShared_140_ = v_isSharedCheck_146_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_snapshotTasks_137_);
lean_inc(v_infoState_136_);
lean_inc(v_messages_135_);
lean_inc(v_recordedDeps_134_);
lean_inc(v_cache_133_);
lean_inc(v_traceState_132_);
lean_inc(v_auxDeclNGen_131_);
lean_inc(v_nextMacroScope_130_);
lean_inc(v_env_129_);
lean_dec(v___x_128_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_146_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 2, v___x_127_);
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_env_129_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_nextMacroScope_130_);
lean_ctor_set(v_reuseFailAlloc_145_, 2, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_145_, 3, v_auxDeclNGen_131_);
lean_ctor_set(v_reuseFailAlloc_145_, 4, v_traceState_132_);
lean_ctor_set(v_reuseFailAlloc_145_, 5, v_cache_133_);
lean_ctor_set(v_reuseFailAlloc_145_, 6, v_recordedDeps_134_);
lean_ctor_set(v_reuseFailAlloc_145_, 7, v_messages_135_);
lean_ctor_set(v_reuseFailAlloc_145_, 8, v_infoState_136_);
lean_ctor_set(v_reuseFailAlloc_145_, 9, v_snapshotTasks_137_);
v___x_142_ = v_reuseFailAlloc_145_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_st_ref_put(v___y_114_, v___x_142_);
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v_r_123_);
return v___x_144_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_114_ = stack[0].m_obj;
lean_object* v_res_150_;
v_res_150_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(v___y_114_);
stack->m_obj
 = v_res_150_;
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
lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
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
LEAN_EXPORT void l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_154_ = stack[0].m_obj;
lean_object* v___y_155_ = stack[1].m_obj;
lean_object* v___y_156_ = stack[2].m_obj;
lean_object* v___y_157_ = stack[3].m_obj;
lean_object* v___y_158_ = stack[4].m_obj;
lean_object* v_res_169_;
v_res_169_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
stack->m_obj
 = v_res_169_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0___boxed(lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec_ref(v___y_170_);
return v_res_176_;
}
}
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(lean_object* v_a_177_, lean_object* v_b_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_n_186_; lean_object* v_d_u2081_187_; lean_object* v_b_u2081_188_; uint8_t v_bi_189_; lean_object* v_d_u2082_190_; lean_object* v_b_u2082_191_; lean_object* v___y_192_; lean_object* v___y_193_; lean_object* v___y_194_; lean_object* v___y_195_; lean_object* v___y_196_; uint8_t v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; uint8_t v___y_268_; uint8_t v___x_330_; 
v___x_330_ = l_Lean_Expr_isErased(v_a_177_);
if (v___x_330_ == 0)
{
uint8_t v___x_331_; 
v___x_331_ = l_Lean_Expr_isErased(v_b_178_);
v___y_268_ = v___x_331_;
goto v___jp_267_;
}
else
{
v___y_268_ = v___x_330_;
goto v___jp_267_;
}
v___jp_185_:
{
lean_object* v___x_197_; 
lean_inc_ref(v___y_192_);
lean_inc_ref(v_d_u2081_187_);
v___x_197_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_d_u2081_187_, v_d_u2082_190_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; uint8_t v___x_199_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
v___x_199_ = lean_unbox(v_a_198_);
if (v___x_199_ == 0)
{
lean_dec_ref(v___y_192_);
lean_dec_ref(v_b_u2082_191_);
lean_dec_ref(v_b_u2081_188_);
lean_dec_ref(v_d_u2081_187_);
lean_dec(v_n_186_);
return v___x_197_;
}
else
{
lean_object* v___x_200_; 
lean_dec_ref_known(v___x_197_, 1);
v___x_200_ = l_Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0(v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_202_; uint8_t v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc_n(v_a_201_, 2);
lean_dec_ref_known(v___x_200_, 1);
v___x_202_ = l_Lean_Expr_fvar___override(v_a_201_);
v___x_203_ = 0;
v___x_204_ = l_Lean_LocalContext_mkLocalDecl(v___y_192_, v_a_201_, v_n_186_, v_d_u2081_187_, v_bi_189_, v___x_203_);
v___x_205_ = lean_expr_instantiate1(v_b_u2081_188_, v___x_202_);
lean_dec_ref(v_b_u2081_188_);
v___x_206_ = lean_expr_instantiate1(v_b_u2082_191_, v___x_202_);
lean_dec_ref(v___x_202_);
lean_dec_ref(v_b_u2082_191_);
v_a_177_ = v___x_205_;
v_b_178_ = v___x_206_;
v_a_179_ = v___x_204_;
v_a_180_ = v___y_193_;
v_a_181_ = v___y_194_;
v_a_182_ = v___y_195_;
v_a_183_ = v___y_196_;
goto _start;
}
else
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
lean_dec_ref(v___y_192_);
lean_dec_ref(v_b_u2082_191_);
lean_dec_ref(v_b_u2081_188_);
lean_dec_ref(v_d_u2081_187_);
lean_dec(v_n_186_);
v_a_208_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_200_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_200_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_192_);
lean_dec_ref(v_b_u2082_191_);
lean_dec_ref(v_b_u2081_188_);
lean_dec_ref(v_d_u2081_187_);
lean_dec(v_n_186_);
return v___x_197_;
}
}
v___jp_216_:
{
uint8_t v___x_223_; 
v___x_223_ = l_Lean_Expr_isLambda(v_a_177_);
if (v___x_223_ == 0)
{
uint8_t v___x_224_; 
v___x_224_ = l_Lean_Expr_isLambda(v_b_178_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec_ref(v___y_218_);
lean_dec_ref(v_b_178_);
lean_dec_ref(v_a_177_);
v___x_225_ = lean_box(v___x_224_);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
else
{
lean_object* v___x_227_; 
v___x_227_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_a_177_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_238_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_238_ == 0)
{
v___x_230_ = v___x_227_;
v_isShared_231_ = v_isSharedCheck_238_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_238_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
if (lean_obj_tag(v_a_228_) == 1)
{
lean_object* v_val_232_; 
lean_del_object(v___x_230_);
v_val_232_ = lean_ctor_get(v_a_228_, 0);
lean_inc(v_val_232_);
lean_dec_ref_known(v_a_228_, 1);
v_a_177_ = v_val_232_;
v_a_179_ = v___y_218_;
v_a_180_ = v___y_219_;
v_a_181_ = v___y_220_;
v_a_182_ = v___y_221_;
v_a_183_ = v___y_222_;
goto _start;
}
else
{
lean_object* v___x_234_; lean_object* v___x_236_; 
lean_dec(v_a_228_);
lean_dec_ref(v___y_218_);
lean_dec_ref(v_b_178_);
v___x_234_ = lean_box(v___x_223_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_234_);
v___x_236_ = v___x_230_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_dec_ref(v___y_218_);
lean_dec_ref(v_b_178_);
v_a_239_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_227_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_227_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
}
else
{
lean_object* v___x_247_; 
v___x_247_ = l___private_Lean_Compiler_LCNF_CompatibleTypes_0__Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_etaExpand_x3f(v_b_178_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_258_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_258_ == 0)
{
v___x_250_ = v___x_247_;
v_isShared_251_ = v_isSharedCheck_258_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_247_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_258_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
if (lean_obj_tag(v_a_248_) == 1)
{
lean_object* v_val_252_; 
lean_del_object(v___x_250_);
v_val_252_ = lean_ctor_get(v_a_248_, 0);
lean_inc(v_val_252_);
lean_dec_ref_known(v_a_248_, 1);
v_b_178_ = v_val_252_;
v_a_179_ = v___y_218_;
v_a_180_ = v___y_219_;
v_a_181_ = v___y_220_;
v_a_182_ = v___y_221_;
v_a_183_ = v___y_222_;
goto _start;
}
else
{
lean_object* v___x_254_; lean_object* v___x_256_; 
lean_dec(v_a_248_);
lean_dec_ref(v___y_218_);
lean_dec_ref(v_a_177_);
v___x_254_ = lean_box(v___y_217_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v___x_254_);
v___x_256_ = v___x_250_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_254_);
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
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_dec_ref(v___y_218_);
lean_dec_ref(v_a_177_);
v_a_259_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_247_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_247_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
v___jp_267_:
{
uint8_t v___x_269_; 
v___x_269_ = 1;
if (v___y_268_ == 0)
{
lean_object* v_a_x27_270_; lean_object* v_b_x27_271_; uint8_t v___x_272_; 
lean_inc_ref(v_a_177_);
v_a_x27_270_ = l_Lean_Expr_headBeta(v_a_177_);
lean_inc_ref(v_b_178_);
v_b_x27_271_ = l_Lean_Expr_headBeta(v_b_178_);
v___x_272_ = lean_expr_eqv(v_a_177_, v_a_x27_270_);
if (v___x_272_ == 0)
{
lean_dec_ref(v_b_178_);
lean_dec_ref(v_a_177_);
v_a_177_ = v_a_x27_270_;
v_b_178_ = v_b_x27_271_;
goto _start;
}
else
{
uint8_t v___x_274_; 
v___x_274_ = lean_expr_eqv(v_b_178_, v_b_x27_271_);
if (v___x_274_ == 0)
{
lean_dec_ref(v_b_178_);
lean_dec_ref(v_a_177_);
v_a_177_ = v_a_x27_270_;
v_b_178_ = v_b_x27_271_;
goto _start;
}
else
{
uint8_t v___x_276_; 
lean_dec_ref(v_b_x27_271_);
lean_dec_ref(v_a_x27_270_);
v___x_276_ = lean_expr_eqv(v_a_177_, v_b_178_);
if (v___x_276_ == 0)
{
switch(lean_obj_tag(v_a_177_))
{
case 5:
{
switch(lean_obj_tag(v_b_178_))
{
case 5:
{
lean_object* v_fn_277_; lean_object* v_arg_278_; lean_object* v_fn_279_; lean_object* v_arg_280_; lean_object* v___x_281_; 
v_fn_277_ = lean_ctor_get(v_a_177_, 0);
lean_inc_ref(v_fn_277_);
v_arg_278_ = lean_ctor_get(v_a_177_, 1);
lean_inc_ref(v_arg_278_);
lean_dec_ref_known(v_a_177_, 2);
v_fn_279_ = lean_ctor_get(v_b_178_, 0);
lean_inc_ref(v_fn_279_);
v_arg_280_ = lean_ctor_get(v_b_178_, 1);
lean_inc_ref(v_arg_280_);
lean_dec_ref_known(v_b_178_, 2);
lean_inc_ref(v_a_179_);
v___x_281_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_fn_277_, v_fn_279_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; uint8_t v___x_283_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
v___x_283_ = lean_unbox(v_a_282_);
if (v___x_283_ == 0)
{
lean_dec_ref(v_arg_280_);
lean_dec_ref(v_arg_278_);
lean_dec_ref(v_a_179_);
return v___x_281_;
}
else
{
lean_dec_ref_known(v___x_281_, 1);
v_a_177_ = v_arg_278_;
v_b_178_ = v_arg_280_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_280_);
lean_dec_ref(v_arg_278_);
lean_dec_ref(v_a_179_);
return v___x_281_;
}
}
case 10:
{
lean_object* v_expr_285_; 
v_expr_285_ = lean_ctor_get(v_b_178_, 1);
lean_inc_ref(v_expr_285_);
lean_dec_ref_known(v_b_178_, 2);
v_b_178_ = v_expr_285_;
goto _start;
}
default: 
{
v___y_217_ = v___x_276_;
v___y_218_ = v_a_179_;
v___y_219_ = v_a_180_;
v___y_220_ = v_a_181_;
v___y_221_ = v_a_182_;
v___y_222_ = v_a_183_;
goto v___jp_216_;
}
}
}
case 7:
{
switch(lean_obj_tag(v_b_178_))
{
case 7:
{
lean_object* v_binderName_287_; lean_object* v_binderType_288_; lean_object* v_body_289_; uint8_t v_binderInfo_290_; lean_object* v_binderType_291_; lean_object* v_body_292_; 
v_binderName_287_ = lean_ctor_get(v_a_177_, 0);
lean_inc(v_binderName_287_);
v_binderType_288_ = lean_ctor_get(v_a_177_, 1);
lean_inc_ref(v_binderType_288_);
v_body_289_ = lean_ctor_get(v_a_177_, 2);
lean_inc_ref(v_body_289_);
v_binderInfo_290_ = lean_ctor_get_uint8(v_a_177_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_177_, 3);
v_binderType_291_ = lean_ctor_get(v_b_178_, 1);
lean_inc_ref(v_binderType_291_);
v_body_292_ = lean_ctor_get(v_b_178_, 2);
lean_inc_ref(v_body_292_);
lean_dec_ref_known(v_b_178_, 3);
v_n_186_ = v_binderName_287_;
v_d_u2081_187_ = v_binderType_288_;
v_b_u2081_188_ = v_body_289_;
v_bi_189_ = v_binderInfo_290_;
v_d_u2082_190_ = v_binderType_291_;
v_b_u2082_191_ = v_body_292_;
v___y_192_ = v_a_179_;
v___y_193_ = v_a_180_;
v___y_194_ = v_a_181_;
v___y_195_ = v_a_182_;
v___y_196_ = v_a_183_;
goto v___jp_185_;
}
case 10:
{
lean_object* v_expr_293_; 
v_expr_293_ = lean_ctor_get(v_b_178_, 1);
lean_inc_ref(v_expr_293_);
lean_dec_ref_known(v_b_178_, 2);
v_b_178_ = v_expr_293_;
goto _start;
}
default: 
{
v___y_217_ = v___x_276_;
v___y_218_ = v_a_179_;
v___y_219_ = v_a_180_;
v___y_220_ = v_a_181_;
v___y_221_ = v_a_182_;
v___y_222_ = v_a_183_;
goto v___jp_216_;
}
}
}
case 6:
{
switch(lean_obj_tag(v_b_178_))
{
case 6:
{
lean_object* v_binderName_295_; lean_object* v_binderType_296_; lean_object* v_body_297_; uint8_t v_binderInfo_298_; lean_object* v_binderType_299_; lean_object* v_body_300_; 
v_binderName_295_ = lean_ctor_get(v_a_177_, 0);
lean_inc(v_binderName_295_);
v_binderType_296_ = lean_ctor_get(v_a_177_, 1);
lean_inc_ref(v_binderType_296_);
v_body_297_ = lean_ctor_get(v_a_177_, 2);
lean_inc_ref(v_body_297_);
v_binderInfo_298_ = lean_ctor_get_uint8(v_a_177_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_177_, 3);
v_binderType_299_ = lean_ctor_get(v_b_178_, 1);
lean_inc_ref(v_binderType_299_);
v_body_300_ = lean_ctor_get(v_b_178_, 2);
lean_inc_ref(v_body_300_);
lean_dec_ref_known(v_b_178_, 3);
v_n_186_ = v_binderName_295_;
v_d_u2081_187_ = v_binderType_296_;
v_b_u2081_188_ = v_body_297_;
v_bi_189_ = v_binderInfo_298_;
v_d_u2082_190_ = v_binderType_299_;
v_b_u2082_191_ = v_body_300_;
v___y_192_ = v_a_179_;
v___y_193_ = v_a_180_;
v___y_194_ = v_a_181_;
v___y_195_ = v_a_182_;
v___y_196_ = v_a_183_;
goto v___jp_185_;
}
case 10:
{
lean_object* v_expr_301_; 
v_expr_301_ = lean_ctor_get(v_b_178_, 1);
lean_inc_ref(v_expr_301_);
lean_dec_ref_known(v_b_178_, 2);
v_b_178_ = v_expr_301_;
goto _start;
}
default: 
{
v___y_217_ = v___x_276_;
v___y_218_ = v_a_179_;
v___y_219_ = v_a_180_;
v___y_220_ = v_a_181_;
v___y_221_ = v_a_182_;
v___y_222_ = v_a_183_;
goto v___jp_216_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_b_178_))
{
case 3:
{
lean_object* v_u_303_; lean_object* v_u_304_; uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec_ref(v_a_179_);
v_u_303_ = lean_ctor_get(v_a_177_, 0);
lean_inc(v_u_303_);
lean_dec_ref_known(v_a_177_, 1);
v_u_304_ = lean_ctor_get(v_b_178_, 0);
lean_inc(v_u_304_);
lean_dec_ref_known(v_b_178_, 1);
v___x_305_ = l_Lean_Level_isEquiv(v_u_303_, v_u_304_);
lean_dec(v_u_304_);
lean_dec(v_u_303_);
v___x_306_ = lean_box(v___x_305_);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
case 10:
{
lean_object* v_expr_308_; 
v_expr_308_ = lean_ctor_get(v_b_178_, 1);
lean_inc_ref(v_expr_308_);
lean_dec_ref_known(v_b_178_, 2);
v_b_178_ = v_expr_308_;
goto _start;
}
default: 
{
v___y_217_ = v___x_276_;
v___y_218_ = v_a_179_;
v___y_219_ = v_a_180_;
v___y_220_ = v_a_181_;
v___y_221_ = v_a_182_;
v___y_222_ = v_a_183_;
goto v___jp_216_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_b_178_))
{
case 4:
{
lean_object* v_declName_310_; lean_object* v_us_311_; lean_object* v_declName_312_; lean_object* v_us_313_; uint8_t v___x_314_; 
lean_dec_ref(v_a_179_);
v_declName_310_ = lean_ctor_get(v_a_177_, 0);
lean_inc(v_declName_310_);
v_us_311_ = lean_ctor_get(v_a_177_, 1);
lean_inc(v_us_311_);
lean_dec_ref_known(v_a_177_, 2);
v_declName_312_ = lean_ctor_get(v_b_178_, 0);
lean_inc(v_declName_312_);
v_us_313_ = lean_ctor_get(v_b_178_, 1);
lean_inc(v_us_313_);
lean_dec_ref_known(v_b_178_, 2);
v___x_314_ = lean_name_eq(v_declName_310_, v_declName_312_);
lean_dec(v_declName_312_);
lean_dec(v_declName_310_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec(v_us_313_);
lean_dec(v_us_311_);
v___x_315_ = lean_box(v___x_276_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
else
{
uint8_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = l_List_isEqv___at___00Lean_Compiler_LCNF_compatibleTypesQuick_spec__0(v_us_311_, v_us_313_);
lean_dec(v_us_313_);
lean_dec(v_us_311_);
v___x_318_ = lean_box(v___x_317_);
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
}
case 10:
{
lean_object* v_expr_320_; 
v_expr_320_ = lean_ctor_get(v_b_178_, 1);
lean_inc_ref(v_expr_320_);
lean_dec_ref_known(v_b_178_, 2);
v_b_178_ = v_expr_320_;
goto _start;
}
default: 
{
v___y_217_ = v___x_276_;
v___y_218_ = v_a_179_;
v___y_219_ = v_a_180_;
v___y_220_ = v_a_181_;
v___y_221_ = v_a_182_;
v___y_222_ = v_a_183_;
goto v___jp_216_;
}
}
}
case 10:
{
lean_object* v_expr_322_; 
v_expr_322_ = lean_ctor_get(v_a_177_, 1);
lean_inc_ref(v_expr_322_);
lean_dec_ref_known(v_a_177_, 2);
v_a_177_ = v_expr_322_;
goto _start;
}
default: 
{
if (lean_obj_tag(v_b_178_) == 10)
{
lean_object* v_expr_324_; 
v_expr_324_ = lean_ctor_get(v_b_178_, 1);
lean_inc_ref(v_expr_324_);
lean_dec_ref_known(v_b_178_, 2);
v_b_178_ = v_expr_324_;
goto _start;
}
else
{
v___y_217_ = v___x_276_;
v___y_218_ = v_a_179_;
v___y_219_ = v_a_180_;
v___y_220_ = v_a_181_;
v___y_221_ = v_a_182_;
v___y_222_ = v_a_183_;
goto v___jp_216_;
}
}
}
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; 
lean_dec_ref(v_a_179_);
lean_dec_ref(v_b_178_);
lean_dec_ref(v_a_177_);
v___x_326_ = lean_box(v___x_269_);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec_ref(v_a_179_);
lean_dec_ref(v_b_178_);
lean_dec_ref(v_a_177_);
v___x_328_ = lean_box(v___x_269_);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_177_ = stack[0].m_obj;
lean_object* v_b_178_ = stack[1].m_obj;
lean_object* v_a_179_ = stack[2].m_obj;
lean_object* v_a_180_ = stack[3].m_obj;
lean_object* v_a_181_ = stack[4].m_obj;
lean_object* v_a_182_ = stack[5].m_obj;
lean_object* v_a_183_ = stack[6].m_obj;
lean_object* v_res_332_;
v_res_332_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_a_177_, v_b_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
stack->m_obj
 = v_res_332_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull___boxed(lean_object* v_a_333_, lean_object* v_b_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_a_333_, v_b_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
return v_res_341_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0(lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___redArg(v___y_346_);
return v___x_348_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_342_ = stack[0].m_obj;
lean_object* v___y_343_ = stack[1].m_obj;
lean_object* v___y_344_ = stack[2].m_obj;
lean_object* v___y_345_ = stack[3].m_obj;
lean_object* v___y_346_ = stack[4].m_obj;
lean_object* v_res_349_;
v_res_349_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0(v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
stack->m_obj
 = v_res_349_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0___boxed(lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull_spec__0_spec__0(v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec_ref(v___y_350_);
return v_res_356_;
}
}
lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(lean_object* v_a_357_, lean_object* v_b_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
uint8_t v___x_365_; 
lean_inc_ref(v_b_358_);
lean_inc_ref(v_a_357_);
v___x_365_ = l_Lean_Compiler_LCNF_compatibleTypesQuick(v_a_357_, v_b_358_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
lean_inc_ref(v_a_359_);
v___x_366_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypesFull(v_a_357_, v_b_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
return v___x_366_;
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; 
lean_dec_ref(v_b_358_);
lean_dec_ref(v_a_357_);
v___x_367_ = lean_box(v___x_365_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_357_ = stack[0].m_obj;
lean_object* v_b_358_ = stack[1].m_obj;
lean_object* v_a_359_ = stack[2].m_obj;
lean_object* v_a_360_ = stack[3].m_obj;
lean_object* v_a_361_ = stack[4].m_obj;
lean_object* v_a_362_ = stack[5].m_obj;
lean_object* v_a_363_ = stack[6].m_obj;
lean_object* v_res_369_;
v_res_369_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(v_a_357_, v_b_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
stack->m_obj
 = v_res_369_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes___boxed(lean_object* v_a_370_, lean_object* v_b_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Compiler_LCNF_InferType_Pure_compatibleTypes(v_a_370_, v_b_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec_ref(v_a_372_);
return v_res_378_;
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
