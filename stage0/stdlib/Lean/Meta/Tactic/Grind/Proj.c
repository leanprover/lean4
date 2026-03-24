// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Proj
// Imports: public import Lean.Meta.Tactic.Grind.Types
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCongrRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateProjEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_propagateProjEq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateProjEq___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateProjEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_Grind_propagateProjEq___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateProjEq___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_propagateProjEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_Lean_Meta_Grind_propagateProjEq___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateProjEq___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateProjEq___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateProjEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateProjEq___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateProjEq___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateProjEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateProjEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateProjEq___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateProjEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(76, 196, 184, 102, 66, 127, 118, 164)}};
static const lean_object* l_Lean_Meta_Grind_propagateProjEq___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateProjEq___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateProjEq___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateProjEq___closed__4;
static const lean_array_object l_Lean_Meta_Grind_propagateProjEq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_propagateProjEq___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateProjEq___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateProjEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateProjEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg(lean_object* v_declName_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_env_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = lean_st_ref_get(v___y_2_);
v_env_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_env_5_);
lean_dec(v___x_4_);
v___x_6_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_5_, v_declName_1_);
v___x_7_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg___boxed(lean_object* v_declName_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg(v_declName_8_, v___y_9_);
lean_dec(v___y_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0(lean_object* v_declName_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg(v_declName_12_, v___y_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___boxed(lean_object* v_declName_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0(v_declName_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
lean_dec(v___y_27_);
lean_dec(v___y_26_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(lean_object* v_cls_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_options_44_; uint8_t v_hasTrace_45_; 
v_options_44_ = lean_ctor_get(v___y_42_, 2);
v_hasTrace_45_ = lean_ctor_get_uint8(v_options_44_, sizeof(void*)*1);
if (v_hasTrace_45_ == 0)
{
lean_object* v___x_46_; lean_object* v___x_47_; 
lean_dec(v_cls_41_);
v___x_46_ = lean_box(v_hasTrace_45_);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
else
{
lean_object* v_inheritedTraceOptions_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v_inheritedTraceOptions_48_ = lean_ctor_get(v___y_42_, 13);
v___x_49_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__1));
v___x_50_ = l_Lean_Name_append(v___x_49_, v_cls_41_);
v___x_51_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_48_, v_options_44_, v___x_50_);
lean_dec(v___x_50_);
v___x_52_ = lean_box(v___x_51_);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___boxed(lean_object* v_cls_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v_cls_54_, v___y_55_);
lean_dec_ref(v___y_55_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1(lean_object* v_cls_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v_cls_58_, v___y_67_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1___boxed(lean_object* v_cls_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1(v_cls_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec(v___y_72_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__3___redArg(lean_object* v_a_84_, lean_object* v_b_85_){
_start:
{
lean_object* v_array_86_; lean_object* v_start_87_; lean_object* v_stop_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_101_; 
v_array_86_ = lean_ctor_get(v_a_84_, 0);
v_start_87_ = lean_ctor_get(v_a_84_, 1);
v_stop_88_ = lean_ctor_get(v_a_84_, 2);
v_isSharedCheck_101_ = !lean_is_exclusive(v_a_84_);
if (v_isSharedCheck_101_ == 0)
{
v___x_90_ = v_a_84_;
v_isShared_91_ = v_isSharedCheck_101_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_stop_88_);
lean_inc(v_start_87_);
lean_inc(v_array_86_);
lean_dec(v_a_84_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_101_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
uint8_t v___x_92_; 
v___x_92_ = lean_nat_dec_lt(v_start_87_, v_stop_88_);
if (v___x_92_ == 0)
{
lean_del_object(v___x_90_);
lean_dec(v_stop_88_);
lean_dec(v_start_87_);
lean_dec_ref(v_array_86_);
return v_b_85_;
}
else
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
v___x_93_ = lean_unsigned_to_nat(1u);
v___x_94_ = lean_nat_add(v_start_87_, v___x_93_);
lean_inc_ref(v_array_86_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v___x_94_);
v___x_96_ = v___x_90_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_array_86_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v___x_94_);
lean_ctor_set(v_reuseFailAlloc_100_, 2, v_stop_88_);
v___x_96_ = v_reuseFailAlloc_100_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_array_fget(v_array_86_, v_start_87_);
lean_dec(v_start_87_);
lean_dec_ref(v_array_86_);
v___x_98_ = lean_array_push(v_b_85_, v___x_97_);
v_a_84_ = v___x_96_;
v_b_85_ = v___x_98_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2_spec__2(lean_object* v_msgData_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___x_108_; lean_object* v_env_109_; lean_object* v___x_110_; lean_object* v_mctx_111_; lean_object* v_lctx_112_; lean_object* v_options_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_108_ = lean_st_ref_get(v___y_106_);
v_env_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc_ref(v_env_109_);
lean_dec(v___x_108_);
v___x_110_ = lean_st_ref_get(v___y_104_);
v_mctx_111_ = lean_ctor_get(v___x_110_, 0);
lean_inc_ref(v_mctx_111_);
lean_dec(v___x_110_);
v_lctx_112_ = lean_ctor_get(v___y_103_, 2);
v_options_113_ = lean_ctor_get(v___y_105_, 2);
lean_inc_ref(v_options_113_);
lean_inc_ref(v_lctx_112_);
v___x_114_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_114_, 0, v_env_109_);
lean_ctor_set(v___x_114_, 1, v_mctx_111_);
lean_ctor_set(v___x_114_, 2, v_lctx_112_);
lean_ctor_set(v___x_114_, 3, v_options_113_);
v___x_115_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v_msgData_102_);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2_spec__2___boxed(lean_object* v_msgData_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2_spec__2(v_msgData_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
return v_res_123_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_124_; double v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_float_of_nat(v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(lean_object* v_cls_129_, lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_ref_136_; lean_object* v___x_137_; lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_182_; 
v_ref_136_ = lean_ctor_get(v___y_133_, 5);
v___x_137_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2_spec__2(v_msg_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
v_a_138_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_182_ == 0)
{
v___x_140_ = v___x_137_;
v_isShared_141_ = v_isSharedCheck_182_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_182_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v_traceState_143_; lean_object* v_env_144_; lean_object* v_nextMacroScope_145_; lean_object* v_ngen_146_; lean_object* v_auxDeclNGen_147_; lean_object* v_cache_148_; lean_object* v_messages_149_; lean_object* v_infoState_150_; lean_object* v_snapshotTasks_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_181_; 
v___x_142_ = lean_st_ref_take(v___y_134_);
v_traceState_143_ = lean_ctor_get(v___x_142_, 4);
v_env_144_ = lean_ctor_get(v___x_142_, 0);
v_nextMacroScope_145_ = lean_ctor_get(v___x_142_, 1);
v_ngen_146_ = lean_ctor_get(v___x_142_, 2);
v_auxDeclNGen_147_ = lean_ctor_get(v___x_142_, 3);
v_cache_148_ = lean_ctor_get(v___x_142_, 5);
v_messages_149_ = lean_ctor_get(v___x_142_, 6);
v_infoState_150_ = lean_ctor_get(v___x_142_, 7);
v_snapshotTasks_151_ = lean_ctor_get(v___x_142_, 8);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_181_ == 0)
{
v___x_153_ = v___x_142_;
v_isShared_154_ = v_isSharedCheck_181_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_snapshotTasks_151_);
lean_inc(v_infoState_150_);
lean_inc(v_messages_149_);
lean_inc(v_cache_148_);
lean_inc(v_traceState_143_);
lean_inc(v_auxDeclNGen_147_);
lean_inc(v_ngen_146_);
lean_inc(v_nextMacroScope_145_);
lean_inc(v_env_144_);
lean_dec(v___x_142_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_181_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
uint64_t v_tid_155_; lean_object* v_traces_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_180_; 
v_tid_155_ = lean_ctor_get_uint64(v_traceState_143_, sizeof(void*)*1);
v_traces_156_ = lean_ctor_get(v_traceState_143_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v_traceState_143_);
if (v_isSharedCheck_180_ == 0)
{
v___x_158_ = v_traceState_143_;
v_isShared_159_ = v_isSharedCheck_180_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_traces_156_);
lean_dec(v_traceState_143_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_180_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; double v___x_161_; uint8_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_160_ = lean_box(0);
v___x_161_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg___closed__0);
v___x_162_ = 0;
v___x_163_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg___closed__1));
v___x_164_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_164_, 0, v_cls_129_);
lean_ctor_set(v___x_164_, 1, v___x_160_);
lean_ctor_set(v___x_164_, 2, v___x_163_);
lean_ctor_set_float(v___x_164_, sizeof(void*)*3, v___x_161_);
lean_ctor_set_float(v___x_164_, sizeof(void*)*3 + 8, v___x_161_);
lean_ctor_set_uint8(v___x_164_, sizeof(void*)*3 + 16, v___x_162_);
v___x_165_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg___closed__2));
v___x_166_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v_a_138_);
lean_ctor_set(v___x_166_, 2, v___x_165_);
lean_inc(v_ref_136_);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v_ref_136_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = l_Lean_PersistentArray_push___redArg(v_traces_156_, v___x_167_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_168_);
v___x_170_ = v___x_158_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_168_);
lean_ctor_set_uint64(v_reuseFailAlloc_179_, sizeof(void*)*1, v_tid_155_);
v___x_170_ = v_reuseFailAlloc_179_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_172_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 4, v___x_170_);
v___x_172_ = v___x_153_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_env_144_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_nextMacroScope_145_);
lean_ctor_set(v_reuseFailAlloc_178_, 2, v_ngen_146_);
lean_ctor_set(v_reuseFailAlloc_178_, 3, v_auxDeclNGen_147_);
lean_ctor_set(v_reuseFailAlloc_178_, 4, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_178_, 5, v_cache_148_);
lean_ctor_set(v_reuseFailAlloc_178_, 6, v_messages_149_);
lean_ctor_set(v_reuseFailAlloc_178_, 7, v_infoState_150_);
lean_ctor_set(v_reuseFailAlloc_178_, 8, v_snapshotTasks_151_);
v___x_172_ = v_reuseFailAlloc_178_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_173_ = lean_st_ref_set(v___y_134_, v___x_172_);
v___x_174_ = lean_box(0);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_174_);
v___x_176_ = v___x_140_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg___boxed(lean_object* v_cls_183_, lean_object* v_msg_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(v_cls_183_, v_msg_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
return v_res_190_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateProjEq___closed__4(void){
_start:
{
lean_object* v___x_198_; lean_object* v_dummy_199_; 
v___x_198_ = lean_box(0);
v_dummy_199_ = l_Lean_Expr_sort___override(v___x_198_);
return v_dummy_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateProjEq(lean_object* v_parent_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_projFn_214_; 
v_projFn_214_ = l_Lean_Expr_getAppFn(v_parent_202_);
if (lean_obj_tag(v_projFn_214_) == 4)
{
lean_object* v_declName_215_; lean_object* v___x_216_; lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_385_; 
v_declName_215_ = lean_ctor_get(v_projFn_214_, 0);
lean_inc(v_declName_215_);
v___x_216_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg(v_declName_215_, v_a_212_);
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_385_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_385_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_385_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
if (lean_obj_tag(v_a_217_) == 1)
{
lean_object* v_val_221_; lean_object* v_ctorName_222_; lean_object* v_numParams_223_; lean_object* v_i_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v_val_221_ = lean_ctor_get(v_a_217_, 0);
lean_inc(v_val_221_);
lean_dec_ref(v_a_217_);
v_ctorName_222_ = lean_ctor_get(v_val_221_, 0);
lean_inc(v_ctorName_222_);
v_numParams_223_ = lean_ctor_get(v_val_221_, 1);
lean_inc(v_numParams_223_);
v_i_224_ = lean_ctor_get(v_val_221_, 2);
lean_inc(v_i_224_);
lean_dec(v_val_221_);
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = lean_nat_add(v_numParams_223_, v___x_225_);
v___x_227_ = l_Lean_Expr_getAppNumArgs(v_parent_202_);
v___x_228_ = lean_nat_dec_eq(v___x_226_, v___x_227_);
lean_dec(v___x_227_);
lean_dec(v___x_226_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_231_; 
lean_dec(v_i_224_);
lean_dec(v_numParams_223_);
lean_dec(v_ctorName_222_);
lean_dec_ref(v_projFn_214_);
lean_dec_ref(v_parent_202_);
v___x_229_ = lean_box(0);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_229_);
v___x_231_ = v___x_219_;
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
else
{
lean_object* v___x_233_; 
lean_del_object(v___x_219_);
lean_inc_ref(v_parent_202_);
v___x_233_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_parent_202_, v_a_203_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_372_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_372_ == 0)
{
v___x_236_ = v___x_233_;
v_isShared_237_ = v_isSharedCheck_372_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_233_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_372_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
uint8_t v___x_238_; 
v___x_238_ = lean_unbox(v_a_234_);
lean_dec(v_a_234_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_241_; 
lean_dec(v_i_224_);
lean_dec(v_numParams_223_);
lean_dec(v_ctorName_222_);
lean_dec_ref(v_projFn_214_);
lean_dec_ref(v_parent_202_);
v___x_239_ = lean_box(0);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_239_);
v___x_241_ = v___x_236_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = l_Lean_Expr_appArg_x21(v_parent_202_);
lean_inc_ref(v___x_243_);
v___x_244_ = l_Lean_Meta_Grind_getRootENode___redArg(v___x_243_, v_a_203_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_363_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_363_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_363_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_363_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v_self_249_; uint8_t v_heqProofs_250_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v_parentNew_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v_parentNew_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; uint8_t v___x_324_; 
v_self_249_ = lean_ctor_get(v_a_245_, 0);
lean_inc_ref(v_self_249_);
v_heqProofs_250_ = lean_ctor_get_uint8(v_a_245_, sizeof(void*)*11 + 4);
lean_dec(v_a_245_);
v___x_324_ = l_Lean_Expr_isAppOf(v_self_249_, v_ctorName_222_);
lean_dec(v_ctorName_222_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_327_; 
lean_dec_ref(v_self_249_);
lean_del_object(v___x_247_);
lean_dec_ref(v___x_243_);
lean_dec(v_i_224_);
lean_dec(v_numParams_223_);
lean_dec_ref(v_projFn_214_);
lean_dec_ref(v_parent_202_);
v___x_325_ = lean_box(0);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_325_);
v___x_327_ = v___x_236_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
else
{
uint8_t v___x_329_; 
lean_del_object(v___x_236_);
v___x_329_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_243_, v_self_249_);
lean_dec_ref(v___x_243_);
if (v___x_329_ == 0)
{
if (v_heqProofs_250_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec_ref(v_projFn_214_);
v___x_330_ = l_Lean_Expr_appFn_x21(v_parent_202_);
lean_inc_ref(v_self_249_);
v___x_331_ = l_Lean_Expr_app___override(v___x_330_, v_self_249_);
v___x_332_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_331_, v_a_208_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_333_);
lean_dec_ref(v___x_332_);
v_parentNew_301_ = v_a_333_;
v___y_302_ = v_a_203_;
v___y_303_ = v_a_204_;
v___y_304_ = v_a_205_;
v___y_305_ = v_a_206_;
v___y_306_ = v_a_207_;
v___y_307_ = v_a_208_;
v___y_308_ = v_a_209_;
v___y_309_ = v_a_210_;
v___y_310_ = v_a_211_;
v___y_311_ = v_a_212_;
goto v___jp_300_;
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_dec_ref(v_self_249_);
lean_del_object(v___x_247_);
lean_dec(v_i_224_);
lean_dec(v_numParams_223_);
lean_dec_ref(v_parent_202_);
v_a_334_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_332_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_332_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
else
{
lean_object* v_dummy_342_; lean_object* v_nargs_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v_dummy_342_ = lean_obj_once(&l_Lean_Meta_Grind_propagateProjEq___closed__4, &l_Lean_Meta_Grind_propagateProjEq___closed__4_once, _init_l_Lean_Meta_Grind_propagateProjEq___closed__4);
v_nargs_343_ = l_Lean_Expr_getAppNumArgs(v_self_249_);
lean_inc(v_nargs_343_);
v___x_344_ = lean_mk_array(v_nargs_343_, v_dummy_342_);
v___x_345_ = lean_nat_sub(v_nargs_343_, v___x_225_);
lean_dec(v_nargs_343_);
lean_inc_ref(v_self_249_);
v___x_346_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_249_, v___x_344_, v___x_345_);
v___x_347_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_223_);
v___x_348_ = l_Array_toSubarray___redArg(v___x_346_, v___x_347_, v_numParams_223_);
v___x_349_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__5));
v___x_350_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__3___redArg(v___x_348_, v___x_349_);
v___x_351_ = l_Lean_mkAppN(v_projFn_214_, v___x_350_);
lean_dec_ref(v___x_350_);
lean_inc_ref(v_self_249_);
v___x_352_ = l_Lean_Expr_app___override(v___x_351_, v_self_249_);
v___x_353_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_352_, v_a_208_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_354_);
lean_dec_ref(v___x_353_);
v_parentNew_301_ = v_a_354_;
v___y_302_ = v_a_203_;
v___y_303_ = v_a_204_;
v___y_304_ = v_a_205_;
v___y_305_ = v_a_206_;
v___y_306_ = v_a_207_;
v___y_307_ = v_a_208_;
v___y_308_ = v_a_209_;
v___y_309_ = v_a_210_;
v___y_310_ = v_a_211_;
v___y_311_ = v_a_212_;
goto v___jp_300_;
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec_ref(v_self_249_);
lean_del_object(v___x_247_);
lean_dec(v_i_224_);
lean_dec(v_numParams_223_);
lean_dec_ref(v_parent_202_);
v_a_355_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_353_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_353_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
else
{
lean_dec_ref(v_projFn_214_);
v_parentNew_282_ = v_parent_202_;
v___y_283_ = v_a_203_;
v___y_284_ = v_a_204_;
v___y_285_ = v_a_205_;
v___y_286_ = v_a_206_;
v___y_287_ = v_a_207_;
v___y_288_ = v_a_208_;
v___y_289_ = v_a_209_;
v___y_290_ = v_a_210_;
v___y_291_ = v_a_211_;
v___y_292_ = v_a_212_;
goto v___jp_281_;
}
}
v___jp_251_:
{
lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_259_ = lean_nat_add(v_numParams_223_, v_i_224_);
lean_dec(v_i_224_);
lean_dec(v_numParams_223_);
v___x_260_ = l_Lean_Expr_getAppNumArgs(v_self_249_);
v___x_261_ = lean_nat_dec_lt(v___x_259_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_264_; 
lean_dec(v___x_260_);
lean_dec(v___x_259_);
lean_dec_ref(v___y_252_);
lean_dec_ref(v_self_249_);
v___x_262_ = lean_box(0);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_262_);
v___x_264_ = v___x_247_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
lean_del_object(v___x_247_);
v___x_266_ = lean_nat_sub(v___x_260_, v___x_259_);
lean_dec(v___x_259_);
lean_dec(v___x_260_);
v___x_267_ = lean_nat_sub(v___x_266_, v___x_225_);
lean_dec(v___x_266_);
v___x_268_ = l_Lean_Expr_getRevArg_x21(v_self_249_, v___x_267_);
lean_dec_ref(v_self_249_);
lean_inc_ref(v___x_268_);
v___x_269_ = l_Lean_Meta_mkEqRefl(v___x_268_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; uint8_t v___x_271_; lean_object* v___x_272_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_a_270_);
lean_dec_ref(v___x_269_);
v___x_271_ = 0;
v___x_272_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___y_252_, v___x_268_, v_a_270_, v___x_271_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
return v___x_272_;
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_dec_ref(v___x_268_);
lean_dec_ref(v___y_252_);
v_a_273_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_269_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_269_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
v___jp_281_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v_a_295_; uint8_t v___x_296_; 
v___x_293_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__3));
v___x_294_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v___x_293_, v___y_291_);
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref(v___x_294_);
v___x_296_ = lean_unbox(v_a_295_);
lean_dec(v_a_295_);
if (v___x_296_ == 0)
{
v___y_252_ = v_parentNew_282_;
v___y_253_ = v___y_283_;
v___y_254_ = v___y_285_;
v___y_255_ = v___y_289_;
v___y_256_ = v___y_290_;
v___y_257_ = v___y_291_;
v___y_258_ = v___y_292_;
goto v___jp_251_;
}
else
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_Meta_Grind_updateLastTag(v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec_ref(v___x_297_);
lean_inc_ref(v_parentNew_282_);
v___x_298_ = l_Lean_MessageData_ofExpr(v_parentNew_282_);
v___x_299_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(v___x_293_, v___x_298_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_dec_ref(v___x_299_);
v___y_252_ = v_parentNew_282_;
v___y_253_ = v___y_283_;
v___y_254_ = v___y_285_;
v___y_255_ = v___y_289_;
v___y_256_ = v___y_290_;
v___y_257_ = v___y_291_;
v___y_258_ = v___y_292_;
goto v___jp_251_;
}
else
{
lean_dec_ref(v_parentNew_282_);
lean_dec_ref(v_self_249_);
lean_del_object(v___x_247_);
lean_dec(v_i_224_);
lean_dec(v_numParams_223_);
return v___x_299_;
}
}
else
{
lean_dec_ref(v_parentNew_282_);
lean_dec_ref(v_self_249_);
lean_del_object(v___x_247_);
lean_dec(v_i_224_);
lean_dec(v_numParams_223_);
return v___x_297_;
}
}
}
v___jp_300_:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_Meta_Grind_getGeneration___redArg(v_parent_202_, v___y_302_);
lean_dec_ref(v_parent_202_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref(v___x_312_);
v___x_314_ = lean_box(0);
lean_inc(v___y_311_);
lean_inc_ref(v___y_310_);
lean_inc(v___y_309_);
lean_inc_ref(v___y_308_);
lean_inc(v___y_307_);
lean_inc_ref(v___y_306_);
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v___y_303_);
lean_inc(v___y_302_);
lean_inc_ref(v_parentNew_301_);
v___x_315_ = lean_grind_internalize(v_parentNew_301_, v_a_313_, v___x_314_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_dec_ref(v___x_315_);
v_parentNew_282_ = v_parentNew_301_;
v___y_283_ = v___y_302_;
v___y_284_ = v___y_303_;
v___y_285_ = v___y_304_;
v___y_286_ = v___y_305_;
v___y_287_ = v___y_306_;
v___y_288_ = v___y_307_;
v___y_289_ = v___y_308_;
v___y_290_ = v___y_309_;
v___y_291_ = v___y_310_;
v___y_292_ = v___y_311_;
goto v___jp_281_;
}
else
{
lean_dec_ref(v_parentNew_301_);
lean_dec_ref(v_self_249_);
lean_del_object(v___x_247_);
lean_dec(v_i_224_);
lean_dec(v_numParams_223_);
return v___x_315_;
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec_ref(v_parentNew_301_);
lean_dec_ref(v_self_249_);
lean_del_object(v___x_247_);
lean_dec(v_i_224_);
lean_dec(v_numParams_223_);
v_a_316_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_312_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_312_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec_ref(v___x_243_);
lean_del_object(v___x_236_);
lean_dec(v_i_224_);
lean_dec(v_numParams_223_);
lean_dec(v_ctorName_222_);
lean_dec_ref(v_projFn_214_);
lean_dec_ref(v_parent_202_);
v_a_364_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_244_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_244_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec(v_i_224_);
lean_dec(v_numParams_223_);
lean_dec(v_ctorName_222_);
lean_dec_ref(v_projFn_214_);
lean_dec_ref(v_parent_202_);
v_a_373_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_233_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_233_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
else
{
lean_object* v___x_381_; lean_object* v___x_383_; 
lean_dec(v_a_217_);
lean_dec_ref(v_projFn_214_);
lean_dec_ref(v_parent_202_);
v___x_381_ = lean_box(0);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_381_);
v___x_383_ = v___x_219_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; 
lean_dec_ref(v_projFn_214_);
lean_dec_ref(v_parent_202_);
v___x_386_ = lean_box(0);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateProjEq___boxed(lean_object* v_parent_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Meta_Grind_propagateProjEq(v_parent_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec(v_a_389_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2(lean_object* v_cls_401_, lean_object* v_msg_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(v_cls_401_, v_msg_402_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2___boxed(lean_object* v_cls_415_, lean_object* v_msg_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__2(v_cls_415_, v_msg_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec(v___y_417_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__3(lean_object* v_inst_429_, lean_object* v_R_430_, lean_object* v_a_431_, lean_object* v_b_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__3___redArg(v_a_431_, v_b_432_);
return v___x_433_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Proj(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Proj(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Proj(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Proj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Proj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Proj(builtin);
}
#ifdef __cplusplus
}
#endif
