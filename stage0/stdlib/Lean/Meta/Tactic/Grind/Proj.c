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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg(lean_object* v_declName_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_8_;
v_res_8_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg(v_declName_1_, v___y_2_);
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg___boxed(lean_object* v_declName_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg(v_declName_9_, v___y_10_);
lean_dec(v___y_10_);
return v_res_12_;
}
}
lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0(lean_object* v_declName_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg(v_declName_13_, v___y_23_);
return v___x_25_;
}
}
LEAN_EXPORT void l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_13_ = stack[0].m_obj;
lean_object* v___y_14_ = stack[1].m_obj;
lean_object* v___y_15_ = stack[2].m_obj;
lean_object* v___y_16_ = stack[3].m_obj;
lean_object* v___y_17_ = stack[4].m_obj;
lean_object* v___y_18_ = stack[5].m_obj;
lean_object* v___y_19_ = stack[6].m_obj;
lean_object* v___y_20_ = stack[7].m_obj;
lean_object* v___y_21_ = stack[8].m_obj;
lean_object* v___y_22_ = stack[9].m_obj;
lean_object* v___y_23_ = stack[10].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0(v_declName_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___boxed(lean_object* v_declName_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0(v_declName_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_29_);
lean_dec(v___y_28_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(lean_object* v_a_40_, lean_object* v_b_41_){
_start:
{
lean_object* v_array_42_; lean_object* v_start_43_; lean_object* v_stop_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_57_; 
v_array_42_ = lean_ctor_get(v_a_40_, 0);
v_start_43_ = lean_ctor_get(v_a_40_, 1);
v_stop_44_ = lean_ctor_get(v_a_40_, 2);
v_isSharedCheck_57_ = !lean_is_exclusive(v_a_40_);
if (v_isSharedCheck_57_ == 0)
{
v___x_46_ = v_a_40_;
v_isShared_47_ = v_isSharedCheck_57_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_stop_44_);
lean_inc(v_start_43_);
lean_inc(v_array_42_);
lean_dec(v_a_40_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_57_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
uint8_t v___x_48_; 
v___x_48_ = lean_nat_dec_lt(v_start_43_, v_stop_44_);
if (v___x_48_ == 0)
{
lean_del_object(v___x_46_);
lean_dec(v_stop_44_);
lean_dec(v_start_43_);
lean_dec_ref(v_array_42_);
return v_b_41_;
}
else
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_52_; 
v___x_49_ = lean_unsigned_to_nat(1u);
v___x_50_ = lean_nat_add(v_start_43_, v___x_49_);
lean_inc_ref(v_array_42_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 1, v___x_50_);
v___x_52_ = v___x_46_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_array_42_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v___x_50_);
lean_ctor_set(v_reuseFailAlloc_56_, 2, v_stop_44_);
v___x_52_ = v_reuseFailAlloc_56_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_array_fget(v_array_42_, v_start_43_);
lean_dec(v_start_43_);
lean_dec_ref(v_array_42_);
v___x_54_ = lean_array_push(v_b_41_, v___x_53_);
v_a_40_ = v___x_52_;
v_b_41_ = v___x_54_;
goto _start;
}
}
}
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1(lean_object* v_msgData_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v___x_64_; lean_object* v_env_65_; uint8_t v___x_66_; lean_object* v_env_67_; lean_object* v___x_68_; lean_object* v_toCold_69_; lean_object* v_mctx_70_; lean_object* v_lctx_71_; lean_object* v_options_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_64_ = lean_st_ref_get(v___y_62_);
v_env_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc_ref(v_env_65_);
lean_dec(v___x_64_);
v___x_66_ = 0;
v_env_67_ = l_Lean_Environment_setRecordingDeps(v_env_65_, v___x_66_);
v___x_68_ = lean_st_ref_get(v___y_60_);
v_toCold_69_ = lean_ctor_get(v___y_61_, 0);
v_mctx_70_ = lean_ctor_get(v___x_68_, 0);
lean_inc_ref(v_mctx_70_);
lean_dec(v___x_68_);
v_lctx_71_ = lean_ctor_get(v___y_59_, 2);
v_options_72_ = lean_ctor_get(v_toCold_69_, 2);
lean_inc_ref(v_options_72_);
lean_inc_ref(v_lctx_71_);
v___x_73_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_73_, 0, v_env_67_);
lean_ctor_set(v___x_73_, 1, v_mctx_70_);
lean_ctor_set(v___x_73_, 2, v_lctx_71_);
lean_ctor_set(v___x_73_, 3, v_options_72_);
v___x_74_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v_msgData_58_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_58_ = stack[0].m_obj;
lean_object* v___y_59_ = stack[1].m_obj;
lean_object* v___y_60_ = stack[2].m_obj;
lean_object* v___y_61_ = stack[3].m_obj;
lean_object* v___y_62_ = stack[4].m_obj;
lean_object* v_res_76_;
v_res_76_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1(v_msgData_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
stack->m_obj
 = v_res_76_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1___boxed(lean_object* v_msgData_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1(v_msgData_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_83_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_84_; double v___x_85_; 
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = lean_float_of_nat(v___x_84_);
return v___x_85_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(lean_object* v_cls_89_, lean_object* v_msg_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_ref_96_; lean_object* v___x_97_; lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_143_; 
v_ref_96_ = lean_ctor_get(v___y_93_, 2);
v___x_97_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1(v_msg_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
v_a_98_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_143_ == 0)
{
v___x_100_ = v___x_97_;
v_isShared_101_ = v_isSharedCheck_143_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_143_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v_traceState_103_; lean_object* v_env_104_; lean_object* v_nextMacroScope_105_; lean_object* v_ngen_106_; lean_object* v_auxDeclNGen_107_; lean_object* v_cache_108_; lean_object* v_recordedDeps_109_; lean_object* v_messages_110_; lean_object* v_infoState_111_; lean_object* v_snapshotTasks_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_142_; 
v___x_102_ = lean_st_ref_take(v___y_94_);
v_traceState_103_ = lean_ctor_get(v___x_102_, 4);
v_env_104_ = lean_ctor_get(v___x_102_, 0);
v_nextMacroScope_105_ = lean_ctor_get(v___x_102_, 1);
v_ngen_106_ = lean_ctor_get(v___x_102_, 2);
v_auxDeclNGen_107_ = lean_ctor_get(v___x_102_, 3);
v_cache_108_ = lean_ctor_get(v___x_102_, 5);
v_recordedDeps_109_ = lean_ctor_get(v___x_102_, 6);
v_messages_110_ = lean_ctor_get(v___x_102_, 7);
v_infoState_111_ = lean_ctor_get(v___x_102_, 8);
v_snapshotTasks_112_ = lean_ctor_get(v___x_102_, 9);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_142_ == 0)
{
v___x_114_ = v___x_102_;
v_isShared_115_ = v_isSharedCheck_142_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_snapshotTasks_112_);
lean_inc(v_infoState_111_);
lean_inc(v_messages_110_);
lean_inc(v_recordedDeps_109_);
lean_inc(v_cache_108_);
lean_inc(v_traceState_103_);
lean_inc(v_auxDeclNGen_107_);
lean_inc(v_ngen_106_);
lean_inc(v_nextMacroScope_105_);
lean_inc(v_env_104_);
lean_dec(v___x_102_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_142_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
uint64_t v_tid_116_; lean_object* v_traces_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_141_; 
v_tid_116_ = lean_ctor_get_uint64(v_traceState_103_, sizeof(void*)*1);
v_traces_117_ = lean_ctor_get(v_traceState_103_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v_traceState_103_);
if (v_isSharedCheck_141_ == 0)
{
v___x_119_ = v_traceState_103_;
v_isShared_120_ = v_isSharedCheck_141_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_traces_117_);
lean_dec(v_traceState_103_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_141_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; lean_object* v___x_122_; double v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_121_ = lean_box(0);
v___x_122_ = lean_box(0);
v___x_123_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0);
v___x_124_ = 0;
v___x_125_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__1));
v___x_126_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_126_, 0, v_cls_89_);
lean_ctor_set(v___x_126_, 1, v___x_122_);
lean_ctor_set(v___x_126_, 2, v___x_125_);
lean_ctor_set_float(v___x_126_, sizeof(void*)*3, v___x_123_);
lean_ctor_set_float(v___x_126_, sizeof(void*)*3 + 8, v___x_123_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*3 + 16, v___x_124_);
v___x_127_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__2));
v___x_128_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set(v___x_128_, 1, v_a_98_);
lean_ctor_set(v___x_128_, 2, v___x_127_);
lean_inc(v_ref_96_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v_ref_96_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = l_Lean_PersistentArray_push___redArg(v_traces_117_, v___x_129_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v___x_130_);
v___x_132_ = v___x_119_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_130_);
lean_ctor_set_uint64(v_reuseFailAlloc_140_, sizeof(void*)*1, v_tid_116_);
v___x_132_ = v_reuseFailAlloc_140_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_134_; 
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 4, v___x_132_);
v___x_134_ = v___x_114_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_env_104_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_nextMacroScope_105_);
lean_ctor_set(v_reuseFailAlloc_139_, 2, v_ngen_106_);
lean_ctor_set(v_reuseFailAlloc_139_, 3, v_auxDeclNGen_107_);
lean_ctor_set(v_reuseFailAlloc_139_, 4, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_139_, 5, v_cache_108_);
lean_ctor_set(v_reuseFailAlloc_139_, 6, v_recordedDeps_109_);
lean_ctor_set(v_reuseFailAlloc_139_, 7, v_messages_110_);
lean_ctor_set(v_reuseFailAlloc_139_, 8, v_infoState_111_);
lean_ctor_set(v_reuseFailAlloc_139_, 9, v_snapshotTasks_112_);
v___x_134_ = v_reuseFailAlloc_139_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_135_ = lean_st_ref_put(v___y_94_, v___x_134_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_121_);
v___x_137_ = v___x_100_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_121_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_89_ = stack[0].m_obj;
lean_object* v_msg_90_ = stack[1].m_obj;
lean_object* v___y_91_ = stack[2].m_obj;
lean_object* v___y_92_ = stack[3].m_obj;
lean_object* v___y_93_ = stack[4].m_obj;
lean_object* v___y_94_ = stack[5].m_obj;
lean_object* v_res_144_;
v_res_144_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v_cls_89_, v_msg_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
stack->m_obj
 = v_res_144_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___boxed(lean_object* v_cls_145_, lean_object* v_msg_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v_cls_145_, v_msg_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
return v_res_152_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateProjEq___closed__6(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__3));
v___x_164_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__5));
v___x_165_ = l_Lean_Name_append(v___x_164_, v___x_163_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateProjEq___closed__7(void){
_start:
{
lean_object* v___x_166_; lean_object* v_dummy_167_; 
v___x_166_ = lean_box(0);
v_dummy_167_ = l_Lean_Expr_sort___override(v___x_166_);
return v_dummy_167_;
}
}
lean_object* l_Lean_Meta_Grind_propagateProjEq(lean_object* v_parent_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_Expr_getAppFn(v_parent_170_);
if (lean_obj_tag(v___x_182_) == 4)
{
lean_object* v_declName_183_; lean_object* v___x_184_; lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_369_; 
v_declName_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_declName_183_);
v___x_184_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg(v_declName_183_, v_a_180_);
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_369_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_369_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_369_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
if (lean_obj_tag(v_a_185_) == 1)
{
lean_object* v_val_189_; lean_object* v_ctorName_190_; lean_object* v_numParams_191_; lean_object* v_i_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_val_189_ = lean_ctor_get(v_a_185_, 0);
lean_inc(v_val_189_);
lean_dec_ref_known(v_a_185_, 1);
v_ctorName_190_ = lean_ctor_get(v_val_189_, 0);
lean_inc(v_ctorName_190_);
v_numParams_191_ = lean_ctor_get(v_val_189_, 1);
lean_inc(v_numParams_191_);
v_i_192_ = lean_ctor_get(v_val_189_, 2);
lean_inc(v_i_192_);
lean_dec(v_val_189_);
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = lean_nat_add(v_numParams_191_, v___x_193_);
v___x_195_ = l_Lean_Expr_getAppNumArgs(v_parent_170_);
v___x_196_ = lean_nat_dec_eq(v___x_194_, v___x_195_);
lean_dec(v___x_195_);
lean_dec(v___x_194_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_199_; 
lean_dec(v_i_192_);
lean_dec(v_numParams_191_);
lean_dec(v_ctorName_190_);
lean_dec_ref_known(v___x_182_, 2);
lean_dec_ref(v_parent_170_);
v___x_197_ = lean_box(0);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_197_);
v___x_199_ = v___x_187_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
else
{
lean_object* v___x_201_; 
lean_del_object(v___x_187_);
lean_inc_ref(v_parent_170_);
v___x_201_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_parent_170_, v_a_171_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_356_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_356_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_356_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_356_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
uint8_t v___x_206_; 
v___x_206_ = lean_unbox(v_a_202_);
lean_dec(v_a_202_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_209_; 
lean_dec(v_i_192_);
lean_dec(v_numParams_191_);
lean_dec(v_ctorName_190_);
lean_dec_ref_known(v___x_182_, 2);
lean_dec_ref(v_parent_170_);
v___x_207_ = lean_box(0);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_207_);
v___x_209_ = v___x_204_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = l_Lean_Expr_appArg_x21(v_parent_170_);
lean_inc_ref(v___x_211_);
v___x_212_ = l_Lean_Meta_Grind_getRootENode___redArg(v___x_211_, v_a_171_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_347_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_347_ == 0)
{
v___x_215_ = v___x_212_;
v_isShared_216_ = v_isSharedCheck_347_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_212_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_347_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_self_217_; uint8_t v_heqProofs_218_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; lean_object* v_parentNew_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v_parentNew_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; uint8_t v___x_306_; 
v_self_217_ = lean_ctor_get(v_a_213_, 0);
lean_inc_ref(v_self_217_);
v_heqProofs_218_ = lean_ctor_get_uint8(v_a_213_, sizeof(void*)*12 + 4);
lean_dec(v_a_213_);
v___x_306_ = l_Lean_Expr_isAppOf(v_self_217_, v_ctorName_190_);
lean_dec(v_ctorName_190_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_309_; 
lean_dec_ref(v_self_217_);
lean_del_object(v___x_215_);
lean_dec_ref(v___x_211_);
lean_dec(v_i_192_);
lean_dec(v_numParams_191_);
lean_dec_ref_known(v___x_182_, 2);
lean_dec_ref(v_parent_170_);
v___x_307_ = lean_box(0);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_307_);
v___x_309_ = v___x_204_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
else
{
size_t v___x_311_; size_t v___x_312_; uint8_t v___x_313_; 
lean_del_object(v___x_204_);
v___x_311_ = lean_ptr_addr(v___x_211_);
lean_dec_ref(v___x_211_);
v___x_312_ = lean_ptr_addr(v_self_217_);
v___x_313_ = lean_usize_dec_eq(v___x_311_, v___x_312_);
if (v___x_313_ == 0)
{
if (v_heqProofs_218_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec_ref_known(v___x_182_, 2);
v___x_314_ = l_Lean_Expr_appFn_x21(v_parent_170_);
lean_inc_ref(v_self_217_);
v___x_315_ = l_Lean_Expr_app___override(v___x_314_, v_self_217_);
v___x_316_ = l_Lean_Meta_Sym_shareCommon(v___x_315_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
lean_dec_ref_known(v___x_316_, 1);
v_parentNew_283_ = v_a_317_;
v___y_284_ = v_a_171_;
v___y_285_ = v_a_172_;
v___y_286_ = v_a_173_;
v___y_287_ = v_a_174_;
v___y_288_ = v_a_175_;
v___y_289_ = v_a_176_;
v___y_290_ = v_a_177_;
v___y_291_ = v_a_178_;
v___y_292_ = v_a_179_;
v___y_293_ = v_a_180_;
goto v___jp_282_;
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec_ref(v_self_217_);
lean_del_object(v___x_215_);
lean_dec(v_i_192_);
lean_dec(v_numParams_191_);
lean_dec_ref(v_parent_170_);
v_a_318_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_316_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_316_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_object* v_dummy_326_; lean_object* v_nargs_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_dummy_326_ = lean_obj_once(&l_Lean_Meta_Grind_propagateProjEq___closed__7, &l_Lean_Meta_Grind_propagateProjEq___closed__7_once, _init_l_Lean_Meta_Grind_propagateProjEq___closed__7);
v_nargs_327_ = l_Lean_Expr_getAppNumArgs(v_self_217_);
lean_inc(v_nargs_327_);
v___x_328_ = lean_mk_array(v_nargs_327_, v_dummy_326_);
v___x_329_ = lean_nat_sub(v_nargs_327_, v___x_193_);
lean_dec(v_nargs_327_);
lean_inc_ref_n(v_self_217_, 2);
v___x_330_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_217_, v___x_328_, v___x_329_);
v___x_331_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_191_);
v___x_332_ = l_Array_toSubarray___redArg(v___x_330_, v___x_331_, v_numParams_191_);
v___x_333_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__8));
v___x_334_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(v___x_332_, v___x_333_);
v___x_335_ = l_Lean_mkAppN(v___x_182_, v___x_334_);
lean_dec_ref(v___x_334_);
v___x_336_ = l_Lean_Expr_app___override(v___x_335_, v_self_217_);
v___x_337_ = l_Lean_Meta_Sym_shareCommon(v___x_336_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
v_parentNew_283_ = v_a_338_;
v___y_284_ = v_a_171_;
v___y_285_ = v_a_172_;
v___y_286_ = v_a_173_;
v___y_287_ = v_a_174_;
v___y_288_ = v_a_175_;
v___y_289_ = v_a_176_;
v___y_290_ = v_a_177_;
v___y_291_ = v_a_178_;
v___y_292_ = v_a_179_;
v___y_293_ = v_a_180_;
goto v___jp_282_;
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec_ref(v_self_217_);
lean_del_object(v___x_215_);
lean_dec(v_i_192_);
lean_dec(v_numParams_191_);
lean_dec_ref(v_parent_170_);
v_a_339_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_337_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_337_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_182_, 2);
v_parentNew_261_ = v_parent_170_;
v___y_262_ = v_a_171_;
v___y_263_ = v_a_172_;
v___y_264_ = v_a_173_;
v___y_265_ = v_a_174_;
v___y_266_ = v_a_175_;
v___y_267_ = v_a_176_;
v___y_268_ = v_a_177_;
v___y_269_ = v_a_178_;
v___y_270_ = v_a_179_;
v___y_271_ = v_a_180_;
goto v___jp_260_;
}
}
v___jp_219_:
{
lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_227_ = lean_nat_add(v_numParams_191_, v_i_192_);
lean_dec(v_i_192_);
lean_dec(v_numParams_191_);
v___x_228_ = l_Lean_Expr_getAppNumArgs(v_self_217_);
v___x_229_ = lean_nat_dec_lt(v___x_227_, v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_232_; 
lean_dec(v___x_228_);
lean_dec(v___x_227_);
lean_dec_ref(v___y_220_);
lean_dec_ref(v_self_217_);
v___x_230_ = lean_box(0);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_230_);
v___x_232_ = v___x_215_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
lean_del_object(v___x_215_);
v___x_234_ = lean_nat_sub(v___x_228_, v___x_227_);
lean_dec(v___x_227_);
lean_dec(v___x_228_);
v___x_235_ = lean_nat_sub(v___x_234_, v___x_193_);
lean_dec(v___x_234_);
v___x_236_ = l_Lean_Expr_getRevArg_x21(v_self_217_, v___x_235_);
lean_dec_ref(v_self_217_);
lean_inc_ref(v___x_236_);
v___x_237_ = l_Lean_Meta_mkEqRefl(v___x_236_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_239_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v___x_237_, 1);
lean_inc_ref(v___x_236_);
lean_inc_ref(v___y_220_);
v___x_239_ = l_Lean_Meta_mkEq(v___y_220_, v___x_236_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_241_; uint8_t v___x_242_; lean_object* v___x_243_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_a_240_);
lean_dec_ref_known(v___x_239_, 1);
v___x_241_ = l_Lean_Meta_mkExpectedPropHint(v_a_238_, v_a_240_);
v___x_242_ = 0;
v___x_243_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___y_220_, v___x_236_, v___x_241_, v___x_242_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
return v___x_243_;
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec(v_a_238_);
lean_dec_ref(v___x_236_);
lean_dec_ref(v___y_220_);
v_a_244_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_239_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_239_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
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
lean_dec_ref(v___x_236_);
lean_dec_ref(v___y_220_);
v_a_252_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_237_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_237_);
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
lean_object* v_toCold_272_; lean_object* v_options_273_; uint8_t v_hasTrace_274_; 
v_toCold_272_ = lean_ctor_get(v___y_270_, 0);
v_options_273_ = lean_ctor_get(v_toCold_272_, 2);
v_hasTrace_274_ = lean_ctor_get_uint8(v_options_273_, sizeof(void*)*1);
if (v_hasTrace_274_ == 0)
{
v___y_220_ = v_parentNew_261_;
v___y_221_ = v___y_262_;
v___y_222_ = v___y_264_;
v___y_223_ = v___y_268_;
v___y_224_ = v___y_269_;
v___y_225_ = v___y_270_;
v___y_226_ = v___y_271_;
goto v___jp_219_;
}
else
{
lean_object* v_inheritedTraceOptions_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v_inheritedTraceOptions_275_ = lean_ctor_get(v_toCold_272_, 11);
v___x_276_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__3));
v___x_277_ = lean_obj_once(&l_Lean_Meta_Grind_propagateProjEq___closed__6, &l_Lean_Meta_Grind_propagateProjEq___closed__6_once, _init_l_Lean_Meta_Grind_propagateProjEq___closed__6);
v___x_278_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_275_, v_options_273_, v___x_277_);
if (v___x_278_ == 0)
{
v___y_220_ = v_parentNew_261_;
v___y_221_ = v___y_262_;
v___y_222_ = v___y_264_;
v___y_223_ = v___y_268_;
v___y_224_ = v___y_269_;
v___y_225_ = v___y_270_;
v___y_226_ = v___y_271_;
goto v___jp_219_;
}
else
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_Meta_Grind_updateLastTag(v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec_ref_known(v___x_279_, 1);
lean_inc_ref(v_parentNew_261_);
v___x_280_ = l_Lean_MessageData_ofExpr(v_parentNew_261_);
v___x_281_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v___x_276_, v___x_280_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_dec_ref_known(v___x_281_, 1);
v___y_220_ = v_parentNew_261_;
v___y_221_ = v___y_262_;
v___y_222_ = v___y_264_;
v___y_223_ = v___y_268_;
v___y_224_ = v___y_269_;
v___y_225_ = v___y_270_;
v___y_226_ = v___y_271_;
goto v___jp_219_;
}
else
{
lean_dec_ref(v_parentNew_261_);
lean_dec_ref(v_self_217_);
lean_del_object(v___x_215_);
lean_dec(v_i_192_);
lean_dec(v_numParams_191_);
return v___x_281_;
}
}
else
{
lean_dec_ref(v_parentNew_261_);
lean_dec_ref(v_self_217_);
lean_del_object(v___x_215_);
lean_dec(v_i_192_);
lean_dec(v_numParams_191_);
return v___x_279_;
}
}
}
}
v___jp_282_:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Meta_Grind_getGeneration___redArg(v_parent_170_, v___y_284_);
lean_dec_ref(v_parent_170_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref_known(v___x_294_, 1);
v___x_296_ = lean_box(0);
lean_inc(v___y_293_);
lean_inc_ref(v___y_292_);
lean_inc(v___y_291_);
lean_inc_ref(v___y_290_);
lean_inc(v___y_289_);
lean_inc_ref(v___y_288_);
lean_inc(v___y_287_);
lean_inc_ref(v___y_286_);
lean_inc(v___y_285_);
lean_inc(v___y_284_);
lean_inc_ref(v_parentNew_283_);
v___x_297_ = lean_grind_internalize(v_parentNew_283_, v_a_295_, v___x_296_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_dec_ref_known(v___x_297_, 1);
v_parentNew_261_ = v_parentNew_283_;
v___y_262_ = v___y_284_;
v___y_263_ = v___y_285_;
v___y_264_ = v___y_286_;
v___y_265_ = v___y_287_;
v___y_266_ = v___y_288_;
v___y_267_ = v___y_289_;
v___y_268_ = v___y_290_;
v___y_269_ = v___y_291_;
v___y_270_ = v___y_292_;
v___y_271_ = v___y_293_;
goto v___jp_260_;
}
else
{
lean_dec_ref(v_parentNew_283_);
lean_dec_ref(v_self_217_);
lean_del_object(v___x_215_);
lean_dec(v_i_192_);
lean_dec(v_numParams_191_);
return v___x_297_;
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec_ref(v_parentNew_283_);
lean_dec_ref(v_self_217_);
lean_del_object(v___x_215_);
lean_dec(v_i_192_);
lean_dec(v_numParams_191_);
v_a_298_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_294_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_294_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec_ref(v___x_211_);
lean_del_object(v___x_204_);
lean_dec(v_i_192_);
lean_dec(v_numParams_191_);
lean_dec(v_ctorName_190_);
lean_dec_ref_known(v___x_182_, 2);
lean_dec_ref(v_parent_170_);
v_a_348_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_212_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_212_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
}
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec(v_i_192_);
lean_dec(v_numParams_191_);
lean_dec(v_ctorName_190_);
lean_dec_ref_known(v___x_182_, 2);
lean_dec_ref(v_parent_170_);
v_a_357_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_201_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_201_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
else
{
lean_object* v___x_365_; lean_object* v___x_367_; 
lean_dec(v_a_185_);
lean_dec_ref_known(v___x_182_, 2);
lean_dec_ref(v_parent_170_);
v___x_365_ = lean_box(0);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_365_);
v___x_367_ = v___x_187_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec_ref(v___x_182_);
lean_dec_ref(v_parent_170_);
v___x_370_ = lean_box(0);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateProjEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_parent_170_ = stack[0].m_obj;
lean_object* v_a_171_ = stack[1].m_obj;
lean_object* v_a_172_ = stack[2].m_obj;
lean_object* v_a_173_ = stack[3].m_obj;
lean_object* v_a_174_ = stack[4].m_obj;
lean_object* v_a_175_ = stack[5].m_obj;
lean_object* v_a_176_ = stack[6].m_obj;
lean_object* v_a_177_ = stack[7].m_obj;
lean_object* v_a_178_ = stack[8].m_obj;
lean_object* v_a_179_ = stack[9].m_obj;
lean_object* v_a_180_ = stack[10].m_obj;
lean_object* v_res_372_;
v_res_372_ = l_Lean_Meta_Grind_propagateProjEq(v_parent_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
stack->m_obj
 = v_res_372_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateProjEq___boxed(lean_object* v_parent_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Meta_Grind_propagateProjEq(v_parent_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec(v_a_374_);
return v_res_385_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1(lean_object* v_cls_386_, lean_object* v_msg_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v_cls_386_, v_msg_387_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
return v___x_399_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_386_ = stack[0].m_obj;
lean_object* v_msg_387_ = stack[1].m_obj;
lean_object* v___y_388_ = stack[2].m_obj;
lean_object* v___y_389_ = stack[3].m_obj;
lean_object* v___y_390_ = stack[4].m_obj;
lean_object* v___y_391_ = stack[5].m_obj;
lean_object* v___y_392_ = stack[6].m_obj;
lean_object* v___y_393_ = stack[7].m_obj;
lean_object* v___y_394_ = stack[8].m_obj;
lean_object* v___y_395_ = stack[9].m_obj;
lean_object* v___y_396_ = stack[10].m_obj;
lean_object* v___y_397_ = stack[11].m_obj;
lean_object* v_res_400_;
v_res_400_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1(v_cls_386_, v_msg_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
stack->m_obj
 = v_res_400_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___boxed(lean_object* v_cls_401_, lean_object* v_msg_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1(v_cls_401_, v_msg_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec(v___y_403_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2(lean_object* v_inst_415_, lean_object* v_R_416_, lean_object* v_a_417_, lean_object* v_b_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(v_a_417_, v_b_418_);
return v___x_419_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Proj(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
