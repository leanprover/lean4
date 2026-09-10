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
lean_object* v___x_62_; lean_object* v_env_63_; lean_object* v___x_64_; lean_object* v_toCold_65_; lean_object* v_mctx_66_; lean_object* v_lctx_67_; lean_object* v_options_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_62_ = lean_st_ref_get(v___y_60_);
v_env_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc_ref(v_env_63_);
lean_dec(v___x_62_);
v___x_64_ = lean_st_ref_get(v___y_58_);
v_toCold_65_ = lean_ctor_get(v___y_59_, 0);
v_mctx_66_ = lean_ctor_get(v___x_64_, 0);
lean_inc_ref(v_mctx_66_);
lean_dec(v___x_64_);
v_lctx_67_ = lean_ctor_get(v___y_57_, 2);
v_options_68_ = lean_ctor_get(v_toCold_65_, 2);
lean_inc_ref(v_options_68_);
lean_inc_ref(v_lctx_67_);
v___x_69_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_69_, 0, v_env_63_);
lean_ctor_set(v___x_69_, 1, v_mctx_66_);
lean_ctor_set(v___x_69_, 2, v_lctx_67_);
lean_ctor_set(v___x_69_, 3, v_options_68_);
v___x_70_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v_msgData_56_);
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1___boxed(lean_object* v_msgData_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1(v_msgData_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
return v_res_78_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_79_; double v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_float_of_nat(v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(lean_object* v_cls_84_, lean_object* v_msg_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_ref_91_; lean_object* v___x_92_; lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_137_; 
v_ref_91_ = lean_ctor_get(v___y_88_, 2);
v___x_92_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1(v_msg_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_137_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_137_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_137_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; lean_object* v_traceState_98_; lean_object* v_env_99_; lean_object* v_nextMacroScope_100_; lean_object* v_ngen_101_; lean_object* v_auxDeclNGen_102_; lean_object* v_cache_103_; lean_object* v_messages_104_; lean_object* v_infoState_105_; lean_object* v_snapshotTasks_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_136_; 
v___x_97_ = lean_st_ref_take(v___y_89_);
v_traceState_98_ = lean_ctor_get(v___x_97_, 4);
v_env_99_ = lean_ctor_get(v___x_97_, 0);
v_nextMacroScope_100_ = lean_ctor_get(v___x_97_, 1);
v_ngen_101_ = lean_ctor_get(v___x_97_, 2);
v_auxDeclNGen_102_ = lean_ctor_get(v___x_97_, 3);
v_cache_103_ = lean_ctor_get(v___x_97_, 5);
v_messages_104_ = lean_ctor_get(v___x_97_, 6);
v_infoState_105_ = lean_ctor_get(v___x_97_, 7);
v_snapshotTasks_106_ = lean_ctor_get(v___x_97_, 8);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_136_ == 0)
{
v___x_108_ = v___x_97_;
v_isShared_109_ = v_isSharedCheck_136_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_snapshotTasks_106_);
lean_inc(v_infoState_105_);
lean_inc(v_messages_104_);
lean_inc(v_cache_103_);
lean_inc(v_traceState_98_);
lean_inc(v_auxDeclNGen_102_);
lean_inc(v_ngen_101_);
lean_inc(v_nextMacroScope_100_);
lean_inc(v_env_99_);
lean_dec(v___x_97_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_136_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
uint64_t v_tid_110_; lean_object* v_traces_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_135_; 
v_tid_110_ = lean_ctor_get_uint64(v_traceState_98_, sizeof(void*)*1);
v_traces_111_ = lean_ctor_get(v_traceState_98_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v_traceState_98_);
if (v_isSharedCheck_135_ == 0)
{
v___x_113_ = v_traceState_98_;
v_isShared_114_ = v_isSharedCheck_135_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_traces_111_);
lean_dec(v_traceState_98_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_135_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; double v___x_116_; uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_115_ = lean_box(0);
v___x_116_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0);
v___x_117_ = 0;
v___x_118_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__1));
v___x_119_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_119_, 0, v_cls_84_);
lean_ctor_set(v___x_119_, 1, v___x_115_);
lean_ctor_set(v___x_119_, 2, v___x_118_);
lean_ctor_set_float(v___x_119_, sizeof(void*)*3, v___x_116_);
lean_ctor_set_float(v___x_119_, sizeof(void*)*3 + 8, v___x_116_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*3 + 16, v___x_117_);
v___x_120_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__2));
v___x_121_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_121_, 0, v___x_119_);
lean_ctor_set(v___x_121_, 1, v_a_93_);
lean_ctor_set(v___x_121_, 2, v___x_120_);
lean_inc(v_ref_91_);
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v_ref_91_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = l_Lean_PersistentArray_push___redArg(v_traces_111_, v___x_122_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_123_);
v___x_125_ = v___x_113_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_123_);
lean_ctor_set_uint64(v_reuseFailAlloc_134_, sizeof(void*)*1, v_tid_110_);
v___x_125_ = v_reuseFailAlloc_134_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_127_; 
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 4, v___x_125_);
v___x_127_ = v___x_108_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_env_99_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_nextMacroScope_100_);
lean_ctor_set(v_reuseFailAlloc_133_, 2, v_ngen_101_);
lean_ctor_set(v_reuseFailAlloc_133_, 3, v_auxDeclNGen_102_);
lean_ctor_set(v_reuseFailAlloc_133_, 4, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_133_, 5, v_cache_103_);
lean_ctor_set(v_reuseFailAlloc_133_, 6, v_messages_104_);
lean_ctor_set(v_reuseFailAlloc_133_, 7, v_infoState_105_);
lean_ctor_set(v_reuseFailAlloc_133_, 8, v_snapshotTasks_106_);
v___x_127_ = v_reuseFailAlloc_133_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_128_ = lean_st_ref_put(v___y_89_, v___x_127_);
v___x_129_ = lean_box(0);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_129_);
v___x_131_ = v___x_95_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___boxed(lean_object* v_cls_138_, lean_object* v_msg_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v_cls_138_, v_msg_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
return v_res_145_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateProjEq___closed__6(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__3));
v___x_157_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__5));
v___x_158_ = l_Lean_Name_append(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateProjEq___closed__7(void){
_start:
{
lean_object* v___x_159_; lean_object* v_dummy_160_; 
v___x_159_ = lean_box(0);
v_dummy_160_ = l_Lean_Expr_sort___override(v___x_159_);
return v_dummy_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateProjEq(lean_object* v_parent_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
lean_object* v_projFn_175_; 
v_projFn_175_ = l_Lean_Expr_getAppFn(v_parent_163_);
if (lean_obj_tag(v_projFn_175_) == 4)
{
lean_object* v_declName_176_; lean_object* v___x_177_; lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_362_; 
v_declName_176_ = lean_ctor_get(v_projFn_175_, 0);
lean_inc(v_declName_176_);
v___x_177_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg(v_declName_176_, v_a_173_);
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_362_ == 0)
{
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_362_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_362_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
if (lean_obj_tag(v_a_178_) == 1)
{
lean_object* v_val_182_; lean_object* v_ctorName_183_; lean_object* v_numParams_184_; lean_object* v_i_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v_val_182_ = lean_ctor_get(v_a_178_, 0);
lean_inc(v_val_182_);
lean_dec_ref_known(v_a_178_, 1);
v_ctorName_183_ = lean_ctor_get(v_val_182_, 0);
lean_inc(v_ctorName_183_);
v_numParams_184_ = lean_ctor_get(v_val_182_, 1);
lean_inc(v_numParams_184_);
v_i_185_ = lean_ctor_get(v_val_182_, 2);
lean_inc(v_i_185_);
lean_dec(v_val_182_);
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_add(v_numParams_184_, v___x_186_);
v___x_188_ = l_Lean_Expr_getAppNumArgs(v_parent_163_);
v___x_189_ = lean_nat_dec_eq(v___x_187_, v___x_188_);
lean_dec(v___x_188_);
lean_dec(v___x_187_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; lean_object* v___x_192_; 
lean_dec(v_i_185_);
lean_dec(v_numParams_184_);
lean_dec(v_ctorName_183_);
lean_dec_ref_known(v_projFn_175_, 2);
lean_dec_ref(v_parent_163_);
v___x_190_ = lean_box(0);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_190_);
v___x_192_ = v___x_180_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
else
{
lean_object* v___x_194_; 
lean_del_object(v___x_180_);
lean_inc_ref(v_parent_163_);
v___x_194_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_parent_163_, v_a_164_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_349_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_349_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_349_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_349_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
uint8_t v___x_199_; 
v___x_199_ = lean_unbox(v_a_195_);
lean_dec(v_a_195_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_202_; 
lean_dec(v_i_185_);
lean_dec(v_numParams_184_);
lean_dec(v_ctorName_183_);
lean_dec_ref_known(v_projFn_175_, 2);
lean_dec_ref(v_parent_163_);
v___x_200_ = lean_box(0);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_200_);
v___x_202_ = v___x_197_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
else
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = l_Lean_Expr_appArg_x21(v_parent_163_);
lean_inc_ref(v___x_204_);
v___x_205_ = l_Lean_Meta_Grind_getRootENode___redArg(v___x_204_, v_a_164_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_340_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_340_ == 0)
{
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_340_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_340_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v_self_210_; uint8_t v_heqProofs_211_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v_parentNew_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v_parentNew_276_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; uint8_t v___x_299_; 
v_self_210_ = lean_ctor_get(v_a_206_, 0);
lean_inc_ref(v_self_210_);
v_heqProofs_211_ = lean_ctor_get_uint8(v_a_206_, sizeof(void*)*12 + 4);
lean_dec(v_a_206_);
v___x_299_ = l_Lean_Expr_isAppOf(v_self_210_, v_ctorName_183_);
lean_dec(v_ctorName_183_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_302_; 
lean_dec_ref(v_self_210_);
lean_del_object(v___x_208_);
lean_dec_ref(v___x_204_);
lean_dec(v_i_185_);
lean_dec(v_numParams_184_);
lean_dec_ref_known(v_projFn_175_, 2);
lean_dec_ref(v_parent_163_);
v___x_300_ = lean_box(0);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_300_);
v___x_302_ = v___x_197_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_300_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
else
{
size_t v___x_304_; size_t v___x_305_; uint8_t v___x_306_; 
lean_del_object(v___x_197_);
v___x_304_ = lean_ptr_addr(v___x_204_);
lean_dec_ref(v___x_204_);
v___x_305_ = lean_ptr_addr(v_self_210_);
v___x_306_ = lean_usize_dec_eq(v___x_304_, v___x_305_);
if (v___x_306_ == 0)
{
if (v_heqProofs_211_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec_ref_known(v_projFn_175_, 2);
v___x_307_ = l_Lean_Expr_appFn_x21(v_parent_163_);
lean_inc_ref(v_self_210_);
v___x_308_ = l_Lean_Expr_app___override(v___x_307_, v_self_210_);
v___x_309_ = l_Lean_Meta_Sym_shareCommon(v___x_308_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_309_, 1);
v_parentNew_276_ = v_a_310_;
v___y_277_ = v_a_164_;
v___y_278_ = v_a_165_;
v___y_279_ = v_a_166_;
v___y_280_ = v_a_167_;
v___y_281_ = v_a_168_;
v___y_282_ = v_a_169_;
v___y_283_ = v_a_170_;
v___y_284_ = v_a_171_;
v___y_285_ = v_a_172_;
v___y_286_ = v_a_173_;
goto v___jp_275_;
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_dec_ref(v_self_210_);
lean_del_object(v___x_208_);
lean_dec(v_i_185_);
lean_dec(v_numParams_184_);
lean_dec_ref(v_parent_163_);
v_a_311_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_309_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_309_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
else
{
lean_object* v_dummy_319_; lean_object* v_nargs_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_dummy_319_ = lean_obj_once(&l_Lean_Meta_Grind_propagateProjEq___closed__7, &l_Lean_Meta_Grind_propagateProjEq___closed__7_once, _init_l_Lean_Meta_Grind_propagateProjEq___closed__7);
v_nargs_320_ = l_Lean_Expr_getAppNumArgs(v_self_210_);
lean_inc(v_nargs_320_);
v___x_321_ = lean_mk_array(v_nargs_320_, v_dummy_319_);
v___x_322_ = lean_nat_sub(v_nargs_320_, v___x_186_);
lean_dec(v_nargs_320_);
lean_inc_ref_n(v_self_210_, 2);
v___x_323_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_210_, v___x_321_, v___x_322_);
v___x_324_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_184_);
v___x_325_ = l_Array_toSubarray___redArg(v___x_323_, v___x_324_, v_numParams_184_);
v___x_326_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__8));
v___x_327_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(v___x_325_, v___x_326_);
v___x_328_ = l_Lean_mkAppN(v_projFn_175_, v___x_327_);
lean_dec_ref(v___x_327_);
v___x_329_ = l_Lean_Expr_app___override(v___x_328_, v_self_210_);
v___x_330_ = l_Lean_Meta_Sym_shareCommon(v___x_329_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_330_, 1);
v_parentNew_276_ = v_a_331_;
v___y_277_ = v_a_164_;
v___y_278_ = v_a_165_;
v___y_279_ = v_a_166_;
v___y_280_ = v_a_167_;
v___y_281_ = v_a_168_;
v___y_282_ = v_a_169_;
v___y_283_ = v_a_170_;
v___y_284_ = v_a_171_;
v___y_285_ = v_a_172_;
v___y_286_ = v_a_173_;
goto v___jp_275_;
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_dec_ref(v_self_210_);
lean_del_object(v___x_208_);
lean_dec(v_i_185_);
lean_dec(v_numParams_184_);
lean_dec_ref(v_parent_163_);
v_a_332_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_330_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_330_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_projFn_175_, 2);
v_parentNew_254_ = v_parent_163_;
v___y_255_ = v_a_164_;
v___y_256_ = v_a_165_;
v___y_257_ = v_a_166_;
v___y_258_ = v_a_167_;
v___y_259_ = v_a_168_;
v___y_260_ = v_a_169_;
v___y_261_ = v_a_170_;
v___y_262_ = v_a_171_;
v___y_263_ = v_a_172_;
v___y_264_ = v_a_173_;
goto v___jp_253_;
}
}
v___jp_212_:
{
lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_220_ = lean_nat_add(v_numParams_184_, v_i_185_);
lean_dec(v_i_185_);
lean_dec(v_numParams_184_);
v___x_221_ = l_Lean_Expr_getAppNumArgs(v_self_210_);
v___x_222_ = lean_nat_dec_lt(v___x_220_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; lean_object* v___x_225_; 
lean_dec(v___x_221_);
lean_dec(v___x_220_);
lean_dec_ref(v___y_213_);
lean_dec_ref(v_self_210_);
v___x_223_ = lean_box(0);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_223_);
v___x_225_ = v___x_208_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
else
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
lean_del_object(v___x_208_);
v___x_227_ = lean_nat_sub(v___x_221_, v___x_220_);
lean_dec(v___x_220_);
lean_dec(v___x_221_);
v___x_228_ = lean_nat_sub(v___x_227_, v___x_186_);
lean_dec(v___x_227_);
v___x_229_ = l_Lean_Expr_getRevArg_x21(v_self_210_, v___x_228_);
lean_dec_ref(v_self_210_);
lean_inc_ref(v___x_229_);
v___x_230_ = l_Lean_Meta_mkEqRefl(v___x_229_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_232_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_230_, 1);
lean_inc_ref(v___x_229_);
lean_inc_ref(v___y_213_);
v___x_232_ = l_Lean_Meta_mkEq(v___y_213_, v___x_229_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_234_; uint8_t v___x_235_; lean_object* v___x_236_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_a_233_);
lean_dec_ref_known(v___x_232_, 1);
v___x_234_ = l_Lean_Meta_mkExpectedPropHint(v_a_231_, v_a_233_);
v___x_235_ = 0;
v___x_236_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___y_213_, v___x_229_, v___x_234_, v___x_235_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
return v___x_236_;
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
lean_dec(v_a_231_);
lean_dec_ref(v___x_229_);
lean_dec_ref(v___y_213_);
v_a_237_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_232_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_232_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec_ref(v___x_229_);
lean_dec_ref(v___y_213_);
v_a_245_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_230_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_230_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
v___jp_253_:
{
lean_object* v_toCold_265_; lean_object* v_options_266_; uint8_t v_hasTrace_267_; 
v_toCold_265_ = lean_ctor_get(v___y_263_, 0);
v_options_266_ = lean_ctor_get(v_toCold_265_, 2);
v_hasTrace_267_ = lean_ctor_get_uint8(v_options_266_, sizeof(void*)*1);
if (v_hasTrace_267_ == 0)
{
v___y_213_ = v_parentNew_254_;
v___y_214_ = v___y_255_;
v___y_215_ = v___y_257_;
v___y_216_ = v___y_261_;
v___y_217_ = v___y_262_;
v___y_218_ = v___y_263_;
v___y_219_ = v___y_264_;
goto v___jp_212_;
}
else
{
lean_object* v_inheritedTraceOptions_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v_inheritedTraceOptions_268_ = lean_ctor_get(v_toCold_265_, 11);
v___x_269_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__3));
v___x_270_ = lean_obj_once(&l_Lean_Meta_Grind_propagateProjEq___closed__6, &l_Lean_Meta_Grind_propagateProjEq___closed__6_once, _init_l_Lean_Meta_Grind_propagateProjEq___closed__6);
v___x_271_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_268_, v_options_266_, v___x_270_);
if (v___x_271_ == 0)
{
v___y_213_ = v_parentNew_254_;
v___y_214_ = v___y_255_;
v___y_215_ = v___y_257_;
v___y_216_ = v___y_261_;
v___y_217_ = v___y_262_;
v___y_218_ = v___y_263_;
v___y_219_ = v___y_264_;
goto v___jp_212_;
}
else
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_Meta_Grind_updateLastTag(v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
lean_dec_ref_known(v___x_272_, 1);
lean_inc_ref(v_parentNew_254_);
v___x_273_ = l_Lean_MessageData_ofExpr(v_parentNew_254_);
v___x_274_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v___x_269_, v___x_273_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_dec_ref_known(v___x_274_, 1);
v___y_213_ = v_parentNew_254_;
v___y_214_ = v___y_255_;
v___y_215_ = v___y_257_;
v___y_216_ = v___y_261_;
v___y_217_ = v___y_262_;
v___y_218_ = v___y_263_;
v___y_219_ = v___y_264_;
goto v___jp_212_;
}
else
{
lean_dec_ref(v_parentNew_254_);
lean_dec_ref(v_self_210_);
lean_del_object(v___x_208_);
lean_dec(v_i_185_);
lean_dec(v_numParams_184_);
return v___x_274_;
}
}
else
{
lean_dec_ref(v_parentNew_254_);
lean_dec_ref(v_self_210_);
lean_del_object(v___x_208_);
lean_dec(v_i_185_);
lean_dec(v_numParams_184_);
return v___x_272_;
}
}
}
}
v___jp_275_:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Meta_Grind_getGeneration___redArg(v_parent_163_, v___y_277_);
lean_dec_ref(v_parent_163_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_288_);
lean_dec_ref_known(v___x_287_, 1);
v___x_289_ = lean_box(0);
lean_inc(v___y_286_);
lean_inc_ref(v___y_285_);
lean_inc(v___y_284_);
lean_inc_ref(v___y_283_);
lean_inc(v___y_282_);
lean_inc_ref(v___y_281_);
lean_inc(v___y_280_);
lean_inc_ref(v___y_279_);
lean_inc(v___y_278_);
lean_inc(v___y_277_);
lean_inc_ref(v_parentNew_276_);
v___x_290_ = lean_grind_internalize(v_parentNew_276_, v_a_288_, v___x_289_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_dec_ref_known(v___x_290_, 1);
v_parentNew_254_ = v_parentNew_276_;
v___y_255_ = v___y_277_;
v___y_256_ = v___y_278_;
v___y_257_ = v___y_279_;
v___y_258_ = v___y_280_;
v___y_259_ = v___y_281_;
v___y_260_ = v___y_282_;
v___y_261_ = v___y_283_;
v___y_262_ = v___y_284_;
v___y_263_ = v___y_285_;
v___y_264_ = v___y_286_;
goto v___jp_253_;
}
else
{
lean_dec_ref(v_parentNew_276_);
lean_dec_ref(v_self_210_);
lean_del_object(v___x_208_);
lean_dec(v_i_185_);
lean_dec(v_numParams_184_);
return v___x_290_;
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec_ref(v_parentNew_276_);
lean_dec_ref(v_self_210_);
lean_del_object(v___x_208_);
lean_dec(v_i_185_);
lean_dec(v_numParams_184_);
v_a_291_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_287_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_287_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec_ref(v___x_204_);
lean_del_object(v___x_197_);
lean_dec(v_i_185_);
lean_dec(v_numParams_184_);
lean_dec(v_ctorName_183_);
lean_dec_ref_known(v_projFn_175_, 2);
lean_dec_ref(v_parent_163_);
v_a_341_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_205_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_205_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec(v_i_185_);
lean_dec(v_numParams_184_);
lean_dec(v_ctorName_183_);
lean_dec_ref_known(v_projFn_175_, 2);
lean_dec_ref(v_parent_163_);
v_a_350_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_194_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_194_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
else
{
lean_object* v___x_358_; lean_object* v___x_360_; 
lean_dec(v_a_178_);
lean_dec_ref_known(v_projFn_175_, 2);
lean_dec_ref(v_parent_163_);
v___x_358_ = lean_box(0);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_358_);
v___x_360_ = v___x_180_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_358_);
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
else
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec_ref(v_projFn_175_);
lean_dec_ref(v_parent_163_);
v___x_363_ = lean_box(0);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateProjEq___boxed(lean_object* v_parent_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Meta_Grind_propagateProjEq(v_parent_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec(v_a_366_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1(lean_object* v_cls_378_, lean_object* v_msg_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v_cls_378_, v_msg_379_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___boxed(lean_object* v_cls_392_, lean_object* v_msg_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1(v_cls_392_, v_msg_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec(v___y_394_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2(lean_object* v_inst_406_, lean_object* v_R_407_, lean_object* v_a_408_, lean_object* v_b_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(v_a_408_, v_b_409_);
return v___x_410_;
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
