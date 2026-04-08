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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
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
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_propagateProjEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_propagateProjEq___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateProjEq___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateProjEq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateProjEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_propagateProjEq___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateProjEq___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateProjEq___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateProjEq___closed__6;
static lean_once_cell_t l_Lean_Meta_Grind_propagateProjEq___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateProjEq___closed__7;
static const lean_array_object l_Lean_Meta_Grind_propagateProjEq___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_propagateProjEq___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateProjEq___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateProjEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateProjEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(lean_object* v_a_38_, lean_object* v_b_39_){
_start:
{
lean_object* v_array_40_; lean_object* v_start_41_; lean_object* v_stop_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_55_; 
v_array_40_ = lean_ctor_get(v_a_38_, 0);
v_start_41_ = lean_ctor_get(v_a_38_, 1);
v_stop_42_ = lean_ctor_get(v_a_38_, 2);
v_isSharedCheck_55_ = !lean_is_exclusive(v_a_38_);
if (v_isSharedCheck_55_ == 0)
{
v___x_44_ = v_a_38_;
v_isShared_45_ = v_isSharedCheck_55_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_stop_42_);
lean_inc(v_start_41_);
lean_inc(v_array_40_);
lean_dec(v_a_38_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_55_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
uint8_t v___x_46_; 
v___x_46_ = lean_nat_dec_lt(v_start_41_, v_stop_42_);
if (v___x_46_ == 0)
{
lean_del_object(v___x_44_);
lean_dec(v_stop_42_);
lean_dec(v_start_41_);
lean_dec_ref(v_array_40_);
return v_b_39_;
}
else
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_50_; 
v___x_47_ = lean_unsigned_to_nat(1u);
v___x_48_ = lean_nat_add(v_start_41_, v___x_47_);
lean_inc_ref(v_array_40_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 1, v___x_48_);
v___x_50_ = v___x_44_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_array_40_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v___x_48_);
lean_ctor_set(v_reuseFailAlloc_54_, 2, v_stop_42_);
v___x_50_ = v_reuseFailAlloc_54_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_array_fget(v_array_40_, v_start_41_);
lean_dec(v_start_41_);
lean_dec_ref(v_array_40_);
v___x_52_ = lean_array_push(v_b_39_, v___x_51_);
v_a_38_ = v___x_50_;
v_b_39_ = v___x_52_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1(lean_object* v_msgData_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v___x_62_; lean_object* v_env_63_; lean_object* v___x_64_; lean_object* v_mctx_65_; lean_object* v_lctx_66_; lean_object* v_options_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_62_ = lean_st_ref_get(v___y_60_);
v_env_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc_ref(v_env_63_);
lean_dec(v___x_62_);
v___x_64_ = lean_st_ref_get(v___y_58_);
v_mctx_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc_ref(v_mctx_65_);
lean_dec(v___x_64_);
v_lctx_66_ = lean_ctor_get(v___y_57_, 2);
v_options_67_ = lean_ctor_get(v___y_59_, 2);
lean_inc_ref(v_options_67_);
lean_inc_ref(v_lctx_66_);
v___x_68_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_68_, 0, v_env_63_);
lean_ctor_set(v___x_68_, 1, v_mctx_65_);
lean_ctor_set(v___x_68_, 2, v_lctx_66_);
lean_ctor_set(v___x_68_, 3, v_options_67_);
v___x_69_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v_msgData_56_);
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1___boxed(lean_object* v_msgData_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1(v_msgData_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
return v_res_77_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_78_; double v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = lean_float_of_nat(v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(lean_object* v_cls_83_, lean_object* v_msg_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_ref_90_; lean_object* v___x_91_; lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_136_; 
v_ref_90_ = lean_ctor_get(v___y_87_, 5);
v___x_91_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1(v_msg_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
v_a_92_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_136_ == 0)
{
v___x_94_ = v___x_91_;
v_isShared_95_ = v_isSharedCheck_136_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_91_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_136_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v_traceState_97_; lean_object* v_env_98_; lean_object* v_nextMacroScope_99_; lean_object* v_ngen_100_; lean_object* v_auxDeclNGen_101_; lean_object* v_cache_102_; lean_object* v_messages_103_; lean_object* v_infoState_104_; lean_object* v_snapshotTasks_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_135_; 
v___x_96_ = lean_st_ref_take(v___y_88_);
v_traceState_97_ = lean_ctor_get(v___x_96_, 4);
v_env_98_ = lean_ctor_get(v___x_96_, 0);
v_nextMacroScope_99_ = lean_ctor_get(v___x_96_, 1);
v_ngen_100_ = lean_ctor_get(v___x_96_, 2);
v_auxDeclNGen_101_ = lean_ctor_get(v___x_96_, 3);
v_cache_102_ = lean_ctor_get(v___x_96_, 5);
v_messages_103_ = lean_ctor_get(v___x_96_, 6);
v_infoState_104_ = lean_ctor_get(v___x_96_, 7);
v_snapshotTasks_105_ = lean_ctor_get(v___x_96_, 8);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_135_ == 0)
{
v___x_107_ = v___x_96_;
v_isShared_108_ = v_isSharedCheck_135_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_snapshotTasks_105_);
lean_inc(v_infoState_104_);
lean_inc(v_messages_103_);
lean_inc(v_cache_102_);
lean_inc(v_traceState_97_);
lean_inc(v_auxDeclNGen_101_);
lean_inc(v_ngen_100_);
lean_inc(v_nextMacroScope_99_);
lean_inc(v_env_98_);
lean_dec(v___x_96_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_135_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
uint64_t v_tid_109_; lean_object* v_traces_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_134_; 
v_tid_109_ = lean_ctor_get_uint64(v_traceState_97_, sizeof(void*)*1);
v_traces_110_ = lean_ctor_get(v_traceState_97_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v_traceState_97_);
if (v_isSharedCheck_134_ == 0)
{
v___x_112_ = v_traceState_97_;
v_isShared_113_ = v_isSharedCheck_134_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_traces_110_);
lean_dec(v_traceState_97_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_134_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_114_; double v___x_115_; uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_114_ = lean_box(0);
v___x_115_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0);
v___x_116_ = 0;
v___x_117_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__1));
v___x_118_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_118_, 0, v_cls_83_);
lean_ctor_set(v___x_118_, 1, v___x_114_);
lean_ctor_set(v___x_118_, 2, v___x_117_);
lean_ctor_set_float(v___x_118_, sizeof(void*)*3, v___x_115_);
lean_ctor_set_float(v___x_118_, sizeof(void*)*3 + 8, v___x_115_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*3 + 16, v___x_116_);
v___x_119_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__2));
v___x_120_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_120_, 0, v___x_118_);
lean_ctor_set(v___x_120_, 1, v_a_92_);
lean_ctor_set(v___x_120_, 2, v___x_119_);
lean_inc(v_ref_90_);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v_ref_90_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = l_Lean_PersistentArray_push___redArg(v_traces_110_, v___x_121_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_122_);
v___x_124_ = v___x_112_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_122_);
lean_ctor_set_uint64(v_reuseFailAlloc_133_, sizeof(void*)*1, v_tid_109_);
v___x_124_ = v_reuseFailAlloc_133_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_126_; 
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 4, v___x_124_);
v___x_126_ = v___x_107_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_env_98_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_nextMacroScope_99_);
lean_ctor_set(v_reuseFailAlloc_132_, 2, v_ngen_100_);
lean_ctor_set(v_reuseFailAlloc_132_, 3, v_auxDeclNGen_101_);
lean_ctor_set(v_reuseFailAlloc_132_, 4, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_132_, 5, v_cache_102_);
lean_ctor_set(v_reuseFailAlloc_132_, 6, v_messages_103_);
lean_ctor_set(v_reuseFailAlloc_132_, 7, v_infoState_104_);
lean_ctor_set(v_reuseFailAlloc_132_, 8, v_snapshotTasks_105_);
v___x_126_ = v_reuseFailAlloc_132_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_127_ = lean_st_ref_set(v___y_88_, v___x_126_);
v___x_128_ = lean_box(0);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_128_);
v___x_130_ = v___x_94_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___boxed(lean_object* v_cls_137_, lean_object* v_msg_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v_cls_137_, v_msg_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
return v_res_144_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateProjEq___closed__6(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__3));
v___x_156_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__5));
v___x_157_ = l_Lean_Name_append(v___x_156_, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateProjEq___closed__7(void){
_start:
{
lean_object* v___x_158_; lean_object* v_dummy_159_; 
v___x_158_ = lean_box(0);
v_dummy_159_ = l_Lean_Expr_sort___override(v___x_158_);
return v_dummy_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateProjEq(lean_object* v_parent_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_projFn_174_; 
v_projFn_174_ = l_Lean_Expr_getAppFn(v_parent_162_);
if (lean_obj_tag(v_projFn_174_) == 4)
{
lean_object* v_declName_175_; lean_object* v___x_176_; lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_347_; 
v_declName_175_ = lean_ctor_get(v_projFn_174_, 0);
lean_inc(v_declName_175_);
v___x_176_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg(v_declName_175_, v_a_172_);
v_a_177_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_347_ == 0)
{
v___x_179_ = v___x_176_;
v_isShared_180_ = v_isSharedCheck_347_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_176_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_347_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
if (lean_obj_tag(v_a_177_) == 1)
{
lean_object* v_val_181_; lean_object* v_ctorName_182_; lean_object* v_numParams_183_; lean_object* v_i_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v_val_181_ = lean_ctor_get(v_a_177_, 0);
lean_inc(v_val_181_);
lean_dec_ref(v_a_177_);
v_ctorName_182_ = lean_ctor_get(v_val_181_, 0);
lean_inc(v_ctorName_182_);
v_numParams_183_ = lean_ctor_get(v_val_181_, 1);
lean_inc(v_numParams_183_);
v_i_184_ = lean_ctor_get(v_val_181_, 2);
lean_inc(v_i_184_);
lean_dec(v_val_181_);
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_nat_add(v_numParams_183_, v___x_185_);
v___x_187_ = l_Lean_Expr_getAppNumArgs(v_parent_162_);
v___x_188_ = lean_nat_dec_eq(v___x_186_, v___x_187_);
lean_dec(v___x_187_);
lean_dec(v___x_186_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_191_; 
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
lean_dec(v_ctorName_182_);
lean_dec_ref(v_projFn_174_);
lean_dec_ref(v_parent_162_);
v___x_189_ = lean_box(0);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_189_);
v___x_191_ = v___x_179_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
else
{
lean_object* v___x_193_; 
lean_del_object(v___x_179_);
lean_inc_ref(v_parent_162_);
v___x_193_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_parent_162_, v_a_163_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_334_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_334_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_334_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_334_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
uint8_t v___x_198_; 
v___x_198_ = lean_unbox(v_a_194_);
lean_dec(v_a_194_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_201_; 
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
lean_dec(v_ctorName_182_);
lean_dec_ref(v_projFn_174_);
lean_dec_ref(v_parent_162_);
v___x_199_ = lean_box(0);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_199_);
v___x_201_ = v___x_196_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = l_Lean_Expr_appArg_x21(v_parent_162_);
lean_inc_ref(v___x_203_);
v___x_204_ = l_Lean_Meta_Grind_getRootENode___redArg(v___x_203_, v_a_163_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_325_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_325_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_325_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_325_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v_self_209_; uint8_t v_heqProofs_210_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v_parentNew_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v_parentNew_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; uint8_t v___x_286_; 
v_self_209_ = lean_ctor_get(v_a_205_, 0);
lean_inc_ref(v_self_209_);
v_heqProofs_210_ = lean_ctor_get_uint8(v_a_205_, sizeof(void*)*11 + 4);
lean_dec(v_a_205_);
v___x_286_ = l_Lean_Expr_isAppOf(v_self_209_, v_ctorName_182_);
lean_dec(v_ctorName_182_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_289_; 
lean_dec_ref(v_self_209_);
lean_del_object(v___x_207_);
lean_dec_ref(v___x_203_);
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
lean_dec_ref(v_projFn_174_);
lean_dec_ref(v_parent_162_);
v___x_287_ = lean_box(0);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_287_);
v___x_289_ = v___x_196_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_287_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
else
{
uint8_t v___x_291_; 
lean_del_object(v___x_196_);
v___x_291_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_203_, v_self_209_);
lean_dec_ref(v___x_203_);
if (v___x_291_ == 0)
{
if (v_heqProofs_210_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
lean_dec_ref(v_projFn_174_);
v___x_292_ = l_Lean_Expr_appFn_x21(v_parent_162_);
lean_inc_ref(v_self_209_);
v___x_293_ = l_Lean_Expr_app___override(v___x_292_, v_self_209_);
v___x_294_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_293_, v_a_168_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref(v___x_294_);
v_parentNew_263_ = v_a_295_;
v___y_264_ = v_a_163_;
v___y_265_ = v_a_164_;
v___y_266_ = v_a_165_;
v___y_267_ = v_a_166_;
v___y_268_ = v_a_167_;
v___y_269_ = v_a_168_;
v___y_270_ = v_a_169_;
v___y_271_ = v_a_170_;
v___y_272_ = v_a_171_;
v___y_273_ = v_a_172_;
goto v___jp_262_;
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec_ref(v_self_209_);
lean_del_object(v___x_207_);
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
lean_dec_ref(v_parent_162_);
v_a_296_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_294_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_294_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
else
{
lean_object* v_dummy_304_; lean_object* v_nargs_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_dummy_304_ = lean_obj_once(&l_Lean_Meta_Grind_propagateProjEq___closed__7, &l_Lean_Meta_Grind_propagateProjEq___closed__7_once, _init_l_Lean_Meta_Grind_propagateProjEq___closed__7);
v_nargs_305_ = l_Lean_Expr_getAppNumArgs(v_self_209_);
lean_inc(v_nargs_305_);
v___x_306_ = lean_mk_array(v_nargs_305_, v_dummy_304_);
v___x_307_ = lean_nat_sub(v_nargs_305_, v___x_185_);
lean_dec(v_nargs_305_);
lean_inc_ref_n(v_self_209_, 2);
v___x_308_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_209_, v___x_306_, v___x_307_);
v___x_309_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_183_);
v___x_310_ = l_Array_toSubarray___redArg(v___x_308_, v___x_309_, v_numParams_183_);
v___x_311_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__8));
v___x_312_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(v___x_310_, v___x_311_);
v___x_313_ = l_Lean_mkAppN(v_projFn_174_, v___x_312_);
lean_dec_ref(v___x_312_);
v___x_314_ = l_Lean_Expr_app___override(v___x_313_, v_self_209_);
v___x_315_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_314_, v_a_168_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_a_316_);
lean_dec_ref(v___x_315_);
v_parentNew_263_ = v_a_316_;
v___y_264_ = v_a_163_;
v___y_265_ = v_a_164_;
v___y_266_ = v_a_165_;
v___y_267_ = v_a_166_;
v___y_268_ = v_a_167_;
v___y_269_ = v_a_168_;
v___y_270_ = v_a_169_;
v___y_271_ = v_a_170_;
v___y_272_ = v_a_171_;
v___y_273_ = v_a_172_;
goto v___jp_262_;
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec_ref(v_self_209_);
lean_del_object(v___x_207_);
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
lean_dec_ref(v_parent_162_);
v_a_317_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_315_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_315_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
else
{
lean_dec_ref(v_projFn_174_);
v_parentNew_242_ = v_parent_162_;
v___y_243_ = v_a_163_;
v___y_244_ = v_a_164_;
v___y_245_ = v_a_165_;
v___y_246_ = v_a_166_;
v___y_247_ = v_a_167_;
v___y_248_ = v_a_168_;
v___y_249_ = v_a_169_;
v___y_250_ = v_a_170_;
v___y_251_ = v_a_171_;
v___y_252_ = v_a_172_;
goto v___jp_241_;
}
}
v___jp_211_:
{
lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_219_ = lean_nat_add(v_numParams_183_, v_i_184_);
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
v___x_220_ = l_Lean_Expr_getAppNumArgs(v_self_209_);
v___x_221_ = lean_nat_dec_lt(v___x_219_, v___x_220_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; lean_object* v___x_224_; 
lean_dec(v___x_220_);
lean_dec(v___x_219_);
lean_dec_ref(v___y_212_);
lean_dec_ref(v_self_209_);
v___x_222_ = lean_box(0);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_222_);
v___x_224_ = v___x_207_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
lean_del_object(v___x_207_);
v___x_226_ = lean_nat_sub(v___x_220_, v___x_219_);
lean_dec(v___x_219_);
lean_dec(v___x_220_);
v___x_227_ = lean_nat_sub(v___x_226_, v___x_185_);
lean_dec(v___x_226_);
v___x_228_ = l_Lean_Expr_getRevArg_x21(v_self_209_, v___x_227_);
lean_dec_ref(v_self_209_);
lean_inc_ref(v___x_228_);
v___x_229_ = l_Lean_Meta_mkEqRefl(v___x_228_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; uint8_t v___x_231_; lean_object* v___x_232_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_230_);
lean_dec_ref(v___x_229_);
v___x_231_ = 0;
v___x_232_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___y_212_, v___x_228_, v_a_230_, v___x_231_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
return v___x_232_;
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec_ref(v___x_228_);
lean_dec_ref(v___y_212_);
v_a_233_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_229_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_229_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
v___jp_241_:
{
lean_object* v_options_253_; uint8_t v_hasTrace_254_; 
v_options_253_ = lean_ctor_get(v___y_251_, 2);
v_hasTrace_254_ = lean_ctor_get_uint8(v_options_253_, sizeof(void*)*1);
if (v_hasTrace_254_ == 0)
{
v___y_212_ = v_parentNew_242_;
v___y_213_ = v___y_243_;
v___y_214_ = v___y_245_;
v___y_215_ = v___y_249_;
v___y_216_ = v___y_250_;
v___y_217_ = v___y_251_;
v___y_218_ = v___y_252_;
goto v___jp_211_;
}
else
{
lean_object* v_inheritedTraceOptions_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v_inheritedTraceOptions_255_ = lean_ctor_get(v___y_251_, 13);
v___x_256_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__3));
v___x_257_ = lean_obj_once(&l_Lean_Meta_Grind_propagateProjEq___closed__6, &l_Lean_Meta_Grind_propagateProjEq___closed__6_once, _init_l_Lean_Meta_Grind_propagateProjEq___closed__6);
v___x_258_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_255_, v_options_253_, v___x_257_);
if (v___x_258_ == 0)
{
v___y_212_ = v_parentNew_242_;
v___y_213_ = v___y_243_;
v___y_214_ = v___y_245_;
v___y_215_ = v___y_249_;
v___y_216_ = v___y_250_;
v___y_217_ = v___y_251_;
v___y_218_ = v___y_252_;
goto v___jp_211_;
}
else
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_Meta_Grind_updateLastTag(v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec_ref(v___x_259_);
lean_inc_ref(v_parentNew_242_);
v___x_260_ = l_Lean_MessageData_ofExpr(v_parentNew_242_);
v___x_261_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v___x_256_, v___x_260_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_dec_ref(v___x_261_);
v___y_212_ = v_parentNew_242_;
v___y_213_ = v___y_243_;
v___y_214_ = v___y_245_;
v___y_215_ = v___y_249_;
v___y_216_ = v___y_250_;
v___y_217_ = v___y_251_;
v___y_218_ = v___y_252_;
goto v___jp_211_;
}
else
{
lean_dec_ref(v_parentNew_242_);
lean_dec_ref(v_self_209_);
lean_del_object(v___x_207_);
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
return v___x_261_;
}
}
else
{
lean_dec_ref(v_parentNew_242_);
lean_dec_ref(v_self_209_);
lean_del_object(v___x_207_);
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
return v___x_259_;
}
}
}
}
v___jp_262_:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Meta_Grind_getGeneration___redArg(v_parent_162_, v___y_264_);
lean_dec_ref(v_parent_162_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_a_275_);
lean_dec_ref(v___x_274_);
v___x_276_ = lean_box(0);
lean_inc(v___y_273_);
lean_inc_ref(v___y_272_);
lean_inc(v___y_271_);
lean_inc_ref(v___y_270_);
lean_inc(v___y_269_);
lean_inc_ref(v___y_268_);
lean_inc(v___y_267_);
lean_inc_ref(v___y_266_);
lean_inc(v___y_265_);
lean_inc(v___y_264_);
lean_inc_ref(v_parentNew_263_);
v___x_277_ = lean_grind_internalize(v_parentNew_263_, v_a_275_, v___x_276_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_dec_ref(v___x_277_);
v_parentNew_242_ = v_parentNew_263_;
v___y_243_ = v___y_264_;
v___y_244_ = v___y_265_;
v___y_245_ = v___y_266_;
v___y_246_ = v___y_267_;
v___y_247_ = v___y_268_;
v___y_248_ = v___y_269_;
v___y_249_ = v___y_270_;
v___y_250_ = v___y_271_;
v___y_251_ = v___y_272_;
v___y_252_ = v___y_273_;
goto v___jp_241_;
}
else
{
lean_dec_ref(v_parentNew_263_);
lean_dec_ref(v_self_209_);
lean_del_object(v___x_207_);
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
return v___x_277_;
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref(v_parentNew_263_);
lean_dec_ref(v_self_209_);
lean_del_object(v___x_207_);
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
v_a_278_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_274_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_274_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec_ref(v___x_203_);
lean_del_object(v___x_196_);
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
lean_dec(v_ctorName_182_);
lean_dec_ref(v_projFn_174_);
lean_dec_ref(v_parent_162_);
v_a_326_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_204_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_204_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
lean_dec(v_ctorName_182_);
lean_dec_ref(v_projFn_174_);
lean_dec_ref(v_parent_162_);
v_a_335_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_193_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_193_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
else
{
lean_object* v___x_343_; lean_object* v___x_345_; 
lean_dec(v_a_177_);
lean_dec_ref(v_projFn_174_);
lean_dec_ref(v_parent_162_);
v___x_343_ = lean_box(0);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_343_);
v___x_345_ = v___x_179_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
else
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec_ref(v_projFn_174_);
lean_dec_ref(v_parent_162_);
v___x_348_ = lean_box(0);
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateProjEq___boxed(lean_object* v_parent_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Meta_Grind_propagateProjEq(v_parent_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_a_352_);
lean_dec(v_a_351_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1(lean_object* v_cls_363_, lean_object* v_msg_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v_cls_363_, v_msg_364_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___boxed(lean_object* v_cls_377_, lean_object* v_msg_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1(v_cls_377_, v_msg_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec(v___y_379_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2(lean_object* v_inst_391_, lean_object* v_R_392_, lean_object* v_a_393_, lean_object* v_b_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(v_a_393_, v_b_394_);
return v___x_395_;
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
