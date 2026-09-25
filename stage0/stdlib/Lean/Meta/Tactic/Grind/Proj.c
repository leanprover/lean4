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
lean_object* v_ref_91_; lean_object* v___x_92_; lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_138_; 
v_ref_91_ = lean_ctor_get(v___y_88_, 2);
v___x_92_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1(v_msg_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_138_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_138_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_138_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; lean_object* v_traceState_98_; lean_object* v_env_99_; lean_object* v_nextMacroScope_100_; lean_object* v_ngen_101_; lean_object* v_auxDeclNGen_102_; lean_object* v_cache_103_; lean_object* v_recordedDeps_104_; lean_object* v_messages_105_; lean_object* v_infoState_106_; lean_object* v_snapshotTasks_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_137_; 
v___x_97_ = lean_st_ref_take(v___y_89_);
v_traceState_98_ = lean_ctor_get(v___x_97_, 4);
v_env_99_ = lean_ctor_get(v___x_97_, 0);
v_nextMacroScope_100_ = lean_ctor_get(v___x_97_, 1);
v_ngen_101_ = lean_ctor_get(v___x_97_, 2);
v_auxDeclNGen_102_ = lean_ctor_get(v___x_97_, 3);
v_cache_103_ = lean_ctor_get(v___x_97_, 5);
v_recordedDeps_104_ = lean_ctor_get(v___x_97_, 6);
v_messages_105_ = lean_ctor_get(v___x_97_, 7);
v_infoState_106_ = lean_ctor_get(v___x_97_, 8);
v_snapshotTasks_107_ = lean_ctor_get(v___x_97_, 9);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_137_ == 0)
{
v___x_109_ = v___x_97_;
v_isShared_110_ = v_isSharedCheck_137_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_snapshotTasks_107_);
lean_inc(v_infoState_106_);
lean_inc(v_messages_105_);
lean_inc(v_recordedDeps_104_);
lean_inc(v_cache_103_);
lean_inc(v_traceState_98_);
lean_inc(v_auxDeclNGen_102_);
lean_inc(v_ngen_101_);
lean_inc(v_nextMacroScope_100_);
lean_inc(v_env_99_);
lean_dec(v___x_97_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_137_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
uint64_t v_tid_111_; lean_object* v_traces_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_136_; 
v_tid_111_ = lean_ctor_get_uint64(v_traceState_98_, sizeof(void*)*1);
v_traces_112_ = lean_ctor_get(v_traceState_98_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v_traceState_98_);
if (v_isSharedCheck_136_ == 0)
{
v___x_114_ = v_traceState_98_;
v_isShared_115_ = v_isSharedCheck_136_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_traces_112_);
lean_dec(v_traceState_98_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_136_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_117_; double v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_116_ = lean_box(0);
v___x_117_ = lean_box(0);
v___x_118_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0);
v___x_119_ = 0;
v___x_120_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__1));
v___x_121_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_121_, 0, v_cls_84_);
lean_ctor_set(v___x_121_, 1, v___x_117_);
lean_ctor_set(v___x_121_, 2, v___x_120_);
lean_ctor_set_float(v___x_121_, sizeof(void*)*3, v___x_118_);
lean_ctor_set_float(v___x_121_, sizeof(void*)*3 + 8, v___x_118_);
lean_ctor_set_uint8(v___x_121_, sizeof(void*)*3 + 16, v___x_119_);
v___x_122_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__2));
v___x_123_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_123_, 0, v___x_121_);
lean_ctor_set(v___x_123_, 1, v_a_93_);
lean_ctor_set(v___x_123_, 2, v___x_122_);
lean_inc(v_ref_91_);
v___x_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_124_, 0, v_ref_91_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
v___x_125_ = l_Lean_PersistentArray_push___redArg(v_traces_112_, v___x_124_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_125_);
v___x_127_ = v___x_114_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_125_);
lean_ctor_set_uint64(v_reuseFailAlloc_135_, sizeof(void*)*1, v_tid_111_);
v___x_127_ = v_reuseFailAlloc_135_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 4, v___x_127_);
v___x_129_ = v___x_109_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_env_99_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_nextMacroScope_100_);
lean_ctor_set(v_reuseFailAlloc_134_, 2, v_ngen_101_);
lean_ctor_set(v_reuseFailAlloc_134_, 3, v_auxDeclNGen_102_);
lean_ctor_set(v_reuseFailAlloc_134_, 4, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_134_, 5, v_cache_103_);
lean_ctor_set(v_reuseFailAlloc_134_, 6, v_recordedDeps_104_);
lean_ctor_set(v_reuseFailAlloc_134_, 7, v_messages_105_);
lean_ctor_set(v_reuseFailAlloc_134_, 8, v_infoState_106_);
lean_ctor_set(v_reuseFailAlloc_134_, 9, v_snapshotTasks_107_);
v___x_129_ = v_reuseFailAlloc_134_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_130_ = lean_st_ref_put(v___y_89_, v___x_129_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_116_);
v___x_132_ = v___x_95_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_116_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___boxed(lean_object* v_cls_139_, lean_object* v_msg_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v_cls_139_, v_msg_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
return v_res_146_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateProjEq___closed__6(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__3));
v___x_158_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__5));
v___x_159_ = l_Lean_Name_append(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateProjEq___closed__7(void){
_start:
{
lean_object* v___x_160_; lean_object* v_dummy_161_; 
v___x_160_ = lean_box(0);
v_dummy_161_ = l_Lean_Expr_sort___override(v___x_160_);
return v_dummy_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateProjEq(lean_object* v_parent_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_projFn_176_; 
v_projFn_176_ = l_Lean_Expr_getAppFn(v_parent_164_);
if (lean_obj_tag(v_projFn_176_) == 4)
{
lean_object* v_declName_177_; lean_object* v___x_178_; lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_363_; 
v_declName_177_ = lean_ctor_get(v_projFn_176_, 0);
lean_inc(v_declName_177_);
v___x_178_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg(v_declName_177_, v_a_174_);
v_a_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_363_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_363_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_363_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
if (lean_obj_tag(v_a_179_) == 1)
{
lean_object* v_val_183_; lean_object* v_ctorName_184_; lean_object* v_numParams_185_; lean_object* v_i_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v_val_183_ = lean_ctor_get(v_a_179_, 0);
lean_inc(v_val_183_);
lean_dec_ref_known(v_a_179_, 1);
v_ctorName_184_ = lean_ctor_get(v_val_183_, 0);
lean_inc(v_ctorName_184_);
v_numParams_185_ = lean_ctor_get(v_val_183_, 1);
lean_inc(v_numParams_185_);
v_i_186_ = lean_ctor_get(v_val_183_, 2);
lean_inc(v_i_186_);
lean_dec(v_val_183_);
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_nat_add(v_numParams_185_, v___x_187_);
v___x_189_ = l_Lean_Expr_getAppNumArgs(v_parent_164_);
v___x_190_ = lean_nat_dec_eq(v___x_188_, v___x_189_);
lean_dec(v___x_189_);
lean_dec(v___x_188_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; lean_object* v___x_193_; 
lean_dec(v_i_186_);
lean_dec(v_numParams_185_);
lean_dec(v_ctorName_184_);
lean_dec_ref_known(v_projFn_176_, 2);
lean_dec_ref(v_parent_164_);
v___x_191_ = lean_box(0);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_191_);
v___x_193_ = v___x_181_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
else
{
lean_object* v___x_195_; 
lean_del_object(v___x_181_);
lean_inc_ref(v_parent_164_);
v___x_195_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_parent_164_, v_a_165_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_350_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_350_ == 0)
{
v___x_198_ = v___x_195_;
v_isShared_199_ = v_isSharedCheck_350_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_350_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
uint8_t v___x_200_; 
v___x_200_ = lean_unbox(v_a_196_);
lean_dec(v_a_196_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_203_; 
lean_dec(v_i_186_);
lean_dec(v_numParams_185_);
lean_dec(v_ctorName_184_);
lean_dec_ref_known(v_projFn_176_, 2);
lean_dec_ref(v_parent_164_);
v___x_201_ = lean_box(0);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_201_);
v___x_203_ = v___x_198_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
else
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = l_Lean_Expr_appArg_x21(v_parent_164_);
lean_inc_ref(v___x_205_);
v___x_206_ = l_Lean_Meta_Grind_getRootENode___redArg(v___x_205_, v_a_165_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_341_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_341_ == 0)
{
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_341_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_341_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v_self_211_; uint8_t v_heqProofs_212_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v_parentNew_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v_parentNew_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; uint8_t v___x_300_; 
v_self_211_ = lean_ctor_get(v_a_207_, 0);
lean_inc_ref(v_self_211_);
v_heqProofs_212_ = lean_ctor_get_uint8(v_a_207_, sizeof(void*)*12 + 4);
lean_dec(v_a_207_);
v___x_300_ = l_Lean_Expr_isAppOf(v_self_211_, v_ctorName_184_);
lean_dec(v_ctorName_184_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_303_; 
lean_dec_ref(v_self_211_);
lean_del_object(v___x_209_);
lean_dec_ref(v___x_205_);
lean_dec(v_i_186_);
lean_dec(v_numParams_185_);
lean_dec_ref_known(v_projFn_176_, 2);
lean_dec_ref(v_parent_164_);
v___x_301_ = lean_box(0);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_301_);
v___x_303_ = v___x_198_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
else
{
size_t v___x_305_; size_t v___x_306_; uint8_t v___x_307_; 
lean_del_object(v___x_198_);
v___x_305_ = lean_ptr_addr(v___x_205_);
lean_dec_ref(v___x_205_);
v___x_306_ = lean_ptr_addr(v_self_211_);
v___x_307_ = lean_usize_dec_eq(v___x_305_, v___x_306_);
if (v___x_307_ == 0)
{
if (v_heqProofs_212_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec_ref_known(v_projFn_176_, 2);
v___x_308_ = l_Lean_Expr_appFn_x21(v_parent_164_);
lean_inc_ref(v_self_211_);
v___x_309_ = l_Lean_Expr_app___override(v___x_308_, v_self_211_);
v___x_310_ = l_Lean_Meta_Sym_shareCommon(v___x_309_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref_known(v___x_310_, 1);
v_parentNew_277_ = v_a_311_;
v___y_278_ = v_a_165_;
v___y_279_ = v_a_166_;
v___y_280_ = v_a_167_;
v___y_281_ = v_a_168_;
v___y_282_ = v_a_169_;
v___y_283_ = v_a_170_;
v___y_284_ = v_a_171_;
v___y_285_ = v_a_172_;
v___y_286_ = v_a_173_;
v___y_287_ = v_a_174_;
goto v___jp_276_;
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_dec_ref(v_self_211_);
lean_del_object(v___x_209_);
lean_dec(v_i_186_);
lean_dec(v_numParams_185_);
lean_dec_ref(v_parent_164_);
v_a_312_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_310_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_310_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
else
{
lean_object* v_dummy_320_; lean_object* v_nargs_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_dummy_320_ = lean_obj_once(&l_Lean_Meta_Grind_propagateProjEq___closed__7, &l_Lean_Meta_Grind_propagateProjEq___closed__7_once, _init_l_Lean_Meta_Grind_propagateProjEq___closed__7);
v_nargs_321_ = l_Lean_Expr_getAppNumArgs(v_self_211_);
lean_inc(v_nargs_321_);
v___x_322_ = lean_mk_array(v_nargs_321_, v_dummy_320_);
v___x_323_ = lean_nat_sub(v_nargs_321_, v___x_187_);
lean_dec(v_nargs_321_);
lean_inc_ref_n(v_self_211_, 2);
v___x_324_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_211_, v___x_322_, v___x_323_);
v___x_325_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_185_);
v___x_326_ = l_Array_toSubarray___redArg(v___x_324_, v___x_325_, v_numParams_185_);
v___x_327_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__8));
v___x_328_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(v___x_326_, v___x_327_);
v___x_329_ = l_Lean_mkAppN(v_projFn_176_, v___x_328_);
lean_dec_ref(v___x_328_);
v___x_330_ = l_Lean_Expr_app___override(v___x_329_, v_self_211_);
v___x_331_ = l_Lean_Meta_Sym_shareCommon(v___x_330_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
v_parentNew_277_ = v_a_332_;
v___y_278_ = v_a_165_;
v___y_279_ = v_a_166_;
v___y_280_ = v_a_167_;
v___y_281_ = v_a_168_;
v___y_282_ = v_a_169_;
v___y_283_ = v_a_170_;
v___y_284_ = v_a_171_;
v___y_285_ = v_a_172_;
v___y_286_ = v_a_173_;
v___y_287_ = v_a_174_;
goto v___jp_276_;
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_dec_ref(v_self_211_);
lean_del_object(v___x_209_);
lean_dec(v_i_186_);
lean_dec(v_numParams_185_);
lean_dec_ref(v_parent_164_);
v_a_333_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_331_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_331_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_projFn_176_, 2);
v_parentNew_255_ = v_parent_164_;
v___y_256_ = v_a_165_;
v___y_257_ = v_a_166_;
v___y_258_ = v_a_167_;
v___y_259_ = v_a_168_;
v___y_260_ = v_a_169_;
v___y_261_ = v_a_170_;
v___y_262_ = v_a_171_;
v___y_263_ = v_a_172_;
v___y_264_ = v_a_173_;
v___y_265_ = v_a_174_;
goto v___jp_254_;
}
}
v___jp_213_:
{
lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_221_ = lean_nat_add(v_numParams_185_, v_i_186_);
lean_dec(v_i_186_);
lean_dec(v_numParams_185_);
v___x_222_ = l_Lean_Expr_getAppNumArgs(v_self_211_);
v___x_223_ = lean_nat_dec_lt(v___x_221_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_226_; 
lean_dec(v___x_222_);
lean_dec(v___x_221_);
lean_dec_ref(v___y_214_);
lean_dec_ref(v_self_211_);
v___x_224_ = lean_box(0);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_224_);
v___x_226_ = v___x_209_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
lean_del_object(v___x_209_);
v___x_228_ = lean_nat_sub(v___x_222_, v___x_221_);
lean_dec(v___x_221_);
lean_dec(v___x_222_);
v___x_229_ = lean_nat_sub(v___x_228_, v___x_187_);
lean_dec(v___x_228_);
v___x_230_ = l_Lean_Expr_getRevArg_x21(v_self_211_, v___x_229_);
lean_dec_ref(v_self_211_);
lean_inc_ref(v___x_230_);
v___x_231_ = l_Lean_Meta_mkEqRefl(v___x_230_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_233_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref_known(v___x_231_, 1);
lean_inc_ref(v___x_230_);
lean_inc_ref(v___y_214_);
v___x_233_ = l_Lean_Meta_mkEq(v___y_214_, v___x_230_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_235_; uint8_t v___x_236_; lean_object* v___x_237_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
lean_dec_ref_known(v___x_233_, 1);
v___x_235_ = l_Lean_Meta_mkExpectedPropHint(v_a_232_, v_a_234_);
v___x_236_ = 0;
v___x_237_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___y_214_, v___x_230_, v___x_235_, v___x_236_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
return v___x_237_;
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_dec(v_a_232_);
lean_dec_ref(v___x_230_);
lean_dec_ref(v___y_214_);
v_a_238_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_233_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_233_);
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
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec_ref(v___x_230_);
lean_dec_ref(v___y_214_);
v_a_246_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_231_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_231_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
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
}
v___jp_254_:
{
lean_object* v_toCold_266_; lean_object* v_options_267_; uint8_t v_hasTrace_268_; 
v_toCold_266_ = lean_ctor_get(v___y_264_, 0);
v_options_267_ = lean_ctor_get(v_toCold_266_, 2);
v_hasTrace_268_ = lean_ctor_get_uint8(v_options_267_, sizeof(void*)*1);
if (v_hasTrace_268_ == 0)
{
v___y_214_ = v_parentNew_255_;
v___y_215_ = v___y_256_;
v___y_216_ = v___y_258_;
v___y_217_ = v___y_262_;
v___y_218_ = v___y_263_;
v___y_219_ = v___y_264_;
v___y_220_ = v___y_265_;
goto v___jp_213_;
}
else
{
lean_object* v_inheritedTraceOptions_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_inheritedTraceOptions_269_ = lean_ctor_get(v_toCold_266_, 11);
v___x_270_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__3));
v___x_271_ = lean_obj_once(&l_Lean_Meta_Grind_propagateProjEq___closed__6, &l_Lean_Meta_Grind_propagateProjEq___closed__6_once, _init_l_Lean_Meta_Grind_propagateProjEq___closed__6);
v___x_272_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_269_, v_options_267_, v___x_271_);
if (v___x_272_ == 0)
{
v___y_214_ = v_parentNew_255_;
v___y_215_ = v___y_256_;
v___y_216_ = v___y_258_;
v___y_217_ = v___y_262_;
v___y_218_ = v___y_263_;
v___y_219_ = v___y_264_;
v___y_220_ = v___y_265_;
goto v___jp_213_;
}
else
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_Meta_Grind_updateLastTag(v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec_ref_known(v___x_273_, 1);
lean_inc_ref(v_parentNew_255_);
v___x_274_ = l_Lean_MessageData_ofExpr(v_parentNew_255_);
v___x_275_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v___x_270_, v___x_274_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_dec_ref_known(v___x_275_, 1);
v___y_214_ = v_parentNew_255_;
v___y_215_ = v___y_256_;
v___y_216_ = v___y_258_;
v___y_217_ = v___y_262_;
v___y_218_ = v___y_263_;
v___y_219_ = v___y_264_;
v___y_220_ = v___y_265_;
goto v___jp_213_;
}
else
{
lean_dec_ref(v_parentNew_255_);
lean_dec_ref(v_self_211_);
lean_del_object(v___x_209_);
lean_dec(v_i_186_);
lean_dec(v_numParams_185_);
return v___x_275_;
}
}
else
{
lean_dec_ref(v_parentNew_255_);
lean_dec_ref(v_self_211_);
lean_del_object(v___x_209_);
lean_dec(v_i_186_);
lean_dec(v_numParams_185_);
return v___x_273_;
}
}
}
}
v___jp_276_:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Meta_Grind_getGeneration___redArg(v_parent_164_, v___y_278_);
lean_dec_ref(v_parent_164_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_a_289_);
lean_dec_ref_known(v___x_288_, 1);
v___x_290_ = lean_box(0);
lean_inc(v___y_287_);
lean_inc_ref(v___y_286_);
lean_inc(v___y_285_);
lean_inc_ref(v___y_284_);
lean_inc(v___y_283_);
lean_inc_ref(v___y_282_);
lean_inc(v___y_281_);
lean_inc_ref(v___y_280_);
lean_inc(v___y_279_);
lean_inc(v___y_278_);
lean_inc_ref(v_parentNew_277_);
v___x_291_ = lean_grind_internalize(v_parentNew_277_, v_a_289_, v___x_290_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_dec_ref_known(v___x_291_, 1);
v_parentNew_255_ = v_parentNew_277_;
v___y_256_ = v___y_278_;
v___y_257_ = v___y_279_;
v___y_258_ = v___y_280_;
v___y_259_ = v___y_281_;
v___y_260_ = v___y_282_;
v___y_261_ = v___y_283_;
v___y_262_ = v___y_284_;
v___y_263_ = v___y_285_;
v___y_264_ = v___y_286_;
v___y_265_ = v___y_287_;
goto v___jp_254_;
}
else
{
lean_dec_ref(v_parentNew_277_);
lean_dec_ref(v_self_211_);
lean_del_object(v___x_209_);
lean_dec(v_i_186_);
lean_dec(v_numParams_185_);
return v___x_291_;
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec_ref(v_parentNew_277_);
lean_dec_ref(v_self_211_);
lean_del_object(v___x_209_);
lean_dec(v_i_186_);
lean_dec(v_numParams_185_);
v_a_292_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_288_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_288_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec_ref(v___x_205_);
lean_del_object(v___x_198_);
lean_dec(v_i_186_);
lean_dec(v_numParams_185_);
lean_dec(v_ctorName_184_);
lean_dec_ref_known(v_projFn_176_, 2);
lean_dec_ref(v_parent_164_);
v_a_342_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_206_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_206_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec(v_i_186_);
lean_dec(v_numParams_185_);
lean_dec(v_ctorName_184_);
lean_dec_ref_known(v_projFn_176_, 2);
lean_dec_ref(v_parent_164_);
v_a_351_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_195_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_195_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
else
{
lean_object* v___x_359_; lean_object* v___x_361_; 
lean_dec(v_a_179_);
lean_dec_ref_known(v_projFn_176_, 2);
lean_dec_ref(v_parent_164_);
v___x_359_ = lean_box(0);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_359_);
v___x_361_ = v___x_181_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec_ref(v_projFn_176_);
lean_dec_ref(v_parent_164_);
v___x_364_ = lean_box(0);
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateProjEq___boxed(lean_object* v_parent_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Meta_Grind_propagateProjEq(v_parent_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec(v_a_367_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1(lean_object* v_cls_379_, lean_object* v_msg_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v_cls_379_, v_msg_380_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___boxed(lean_object* v_cls_393_, lean_object* v_msg_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1(v_cls_393_, v_msg_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec(v___y_395_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2(lean_object* v_inst_407_, lean_object* v_R_408_, lean_object* v_a_409_, lean_object* v_b_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(v_a_409_, v_b_410_);
return v___x_411_;
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
