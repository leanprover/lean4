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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1(lean_object* v_msgData_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v___x_44_; lean_object* v_env_45_; lean_object* v___x_46_; lean_object* v_mctx_47_; lean_object* v_lctx_48_; lean_object* v_options_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_44_ = lean_st_ref_get(v___y_42_);
v_env_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc_ref(v_env_45_);
lean_dec(v___x_44_);
v___x_46_ = lean_st_ref_get(v___y_40_);
v_mctx_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc_ref(v_mctx_47_);
lean_dec(v___x_46_);
v_lctx_48_ = lean_ctor_get(v___y_39_, 2);
v_options_49_ = lean_ctor_get(v___y_41_, 2);
lean_inc_ref(v_options_49_);
lean_inc_ref(v_lctx_48_);
v___x_50_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_50_, 0, v_env_45_);
lean_ctor_set(v___x_50_, 1, v_mctx_47_);
lean_ctor_set(v___x_50_, 2, v_lctx_48_);
lean_ctor_set(v___x_50_, 3, v_options_49_);
v___x_51_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v_msgData_38_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1___boxed(lean_object* v_msgData_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1(v_msgData_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
return v_res_59_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_60_; double v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = lean_float_of_nat(v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(lean_object* v_cls_65_, lean_object* v_msg_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v_ref_72_; lean_object* v___x_73_; lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_118_; 
v_ref_72_ = lean_ctor_get(v___y_69_, 5);
v___x_73_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1(v_msg_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
v_a_74_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_118_ == 0)
{
v___x_76_ = v___x_73_;
v_isShared_77_ = v_isSharedCheck_118_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_dec(v___x_73_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_118_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; lean_object* v_traceState_79_; lean_object* v_env_80_; lean_object* v_nextMacroScope_81_; lean_object* v_ngen_82_; lean_object* v_auxDeclNGen_83_; lean_object* v_cache_84_; lean_object* v_messages_85_; lean_object* v_infoState_86_; lean_object* v_snapshotTasks_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_117_; 
v___x_78_ = lean_st_ref_take(v___y_70_);
v_traceState_79_ = lean_ctor_get(v___x_78_, 4);
v_env_80_ = lean_ctor_get(v___x_78_, 0);
v_nextMacroScope_81_ = lean_ctor_get(v___x_78_, 1);
v_ngen_82_ = lean_ctor_get(v___x_78_, 2);
v_auxDeclNGen_83_ = lean_ctor_get(v___x_78_, 3);
v_cache_84_ = lean_ctor_get(v___x_78_, 5);
v_messages_85_ = lean_ctor_get(v___x_78_, 6);
v_infoState_86_ = lean_ctor_get(v___x_78_, 7);
v_snapshotTasks_87_ = lean_ctor_get(v___x_78_, 8);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_117_ == 0)
{
v___x_89_ = v___x_78_;
v_isShared_90_ = v_isSharedCheck_117_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_snapshotTasks_87_);
lean_inc(v_infoState_86_);
lean_inc(v_messages_85_);
lean_inc(v_cache_84_);
lean_inc(v_traceState_79_);
lean_inc(v_auxDeclNGen_83_);
lean_inc(v_ngen_82_);
lean_inc(v_nextMacroScope_81_);
lean_inc(v_env_80_);
lean_dec(v___x_78_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_117_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
uint64_t v_tid_91_; lean_object* v_traces_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_116_; 
v_tid_91_ = lean_ctor_get_uint64(v_traceState_79_, sizeof(void*)*1);
v_traces_92_ = lean_ctor_get(v_traceState_79_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v_traceState_79_);
if (v_isSharedCheck_116_ == 0)
{
v___x_94_ = v_traceState_79_;
v_isShared_95_ = v_isSharedCheck_116_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_traces_92_);
lean_dec(v_traceState_79_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_116_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; double v___x_97_; uint8_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_96_ = lean_box(0);
v___x_97_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0);
v___x_98_ = 0;
v___x_99_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__1));
v___x_100_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_100_, 0, v_cls_65_);
lean_ctor_set(v___x_100_, 1, v___x_96_);
lean_ctor_set(v___x_100_, 2, v___x_99_);
lean_ctor_set_float(v___x_100_, sizeof(void*)*3, v___x_97_);
lean_ctor_set_float(v___x_100_, sizeof(void*)*3 + 8, v___x_97_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*3 + 16, v___x_98_);
v___x_101_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__2));
v___x_102_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set(v___x_102_, 1, v_a_74_);
lean_ctor_set(v___x_102_, 2, v___x_101_);
lean_inc(v_ref_72_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v_ref_72_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = l_Lean_PersistentArray_push___redArg(v_traces_92_, v___x_103_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_104_);
v___x_106_ = v___x_94_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_104_);
lean_ctor_set_uint64(v_reuseFailAlloc_115_, sizeof(void*)*1, v_tid_91_);
v___x_106_ = v_reuseFailAlloc_115_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_108_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 4, v___x_106_);
v___x_108_ = v___x_89_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_env_80_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_nextMacroScope_81_);
lean_ctor_set(v_reuseFailAlloc_114_, 2, v_ngen_82_);
lean_ctor_set(v_reuseFailAlloc_114_, 3, v_auxDeclNGen_83_);
lean_ctor_set(v_reuseFailAlloc_114_, 4, v___x_106_);
lean_ctor_set(v_reuseFailAlloc_114_, 5, v_cache_84_);
lean_ctor_set(v_reuseFailAlloc_114_, 6, v_messages_85_);
lean_ctor_set(v_reuseFailAlloc_114_, 7, v_infoState_86_);
lean_ctor_set(v_reuseFailAlloc_114_, 8, v_snapshotTasks_87_);
v___x_108_ = v_reuseFailAlloc_114_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_109_ = lean_st_ref_put(v___y_70_, v___x_108_);
v___x_110_ = lean_box(0);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 0, v___x_110_);
v___x_112_ = v___x_76_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___boxed(lean_object* v_cls_119_, lean_object* v_msg_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v_cls_119_, v_msg_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(lean_object* v_a_127_, lean_object* v_b_128_){
_start:
{
lean_object* v_array_129_; lean_object* v_start_130_; lean_object* v_stop_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_144_; 
v_array_129_ = lean_ctor_get(v_a_127_, 0);
v_start_130_ = lean_ctor_get(v_a_127_, 1);
v_stop_131_ = lean_ctor_get(v_a_127_, 2);
v_isSharedCheck_144_ = !lean_is_exclusive(v_a_127_);
if (v_isSharedCheck_144_ == 0)
{
v___x_133_ = v_a_127_;
v_isShared_134_ = v_isSharedCheck_144_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_stop_131_);
lean_inc(v_start_130_);
lean_inc(v_array_129_);
lean_dec(v_a_127_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_144_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
uint8_t v___x_135_; 
v___x_135_ = lean_nat_dec_lt(v_start_130_, v_stop_131_);
if (v___x_135_ == 0)
{
lean_del_object(v___x_133_);
lean_dec(v_stop_131_);
lean_dec(v_start_130_);
lean_dec_ref(v_array_129_);
return v_b_128_;
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_add(v_start_130_, v___x_136_);
lean_inc_ref(v_array_129_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___x_137_);
v___x_139_ = v___x_133_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_array_129_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v_stop_131_);
v___x_139_ = v_reuseFailAlloc_143_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_array_fget(v_array_129_, v_start_130_);
lean_dec(v_start_130_);
lean_dec_ref(v_array_129_);
v___x_141_ = lean_array_push(v_b_128_, v___x_140_);
v_a_127_ = v___x_139_;
v_b_128_ = v___x_141_;
goto _start;
}
}
}
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
lean_object* v_declName_175_; lean_object* v___x_176_; lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_360_; 
v_declName_175_ = lean_ctor_get(v_projFn_174_, 0);
lean_inc(v_declName_175_);
v___x_176_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg(v_declName_175_, v_a_172_);
v_a_177_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_360_ == 0)
{
v___x_179_ = v___x_176_;
v_isShared_180_ = v_isSharedCheck_360_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_176_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_360_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
if (lean_obj_tag(v_a_177_) == 1)
{
lean_object* v_val_181_; lean_object* v_ctorName_182_; lean_object* v_numParams_183_; lean_object* v_i_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v_val_181_ = lean_ctor_get(v_a_177_, 0);
lean_inc(v_val_181_);
lean_dec_ref_known(v_a_177_, 1);
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
lean_dec_ref_known(v_projFn_174_, 2);
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
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_347_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_347_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_347_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_347_;
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
lean_dec_ref_known(v_projFn_174_, 2);
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
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_338_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_338_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_338_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_338_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v_self_209_; uint8_t v_heqProofs_210_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v_parentNew_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v_parentNew_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; uint8_t v___x_297_; 
v_self_209_ = lean_ctor_get(v_a_205_, 0);
lean_inc_ref(v_self_209_);
v_heqProofs_210_ = lean_ctor_get_uint8(v_a_205_, sizeof(void*)*12 + 4);
lean_dec(v_a_205_);
v___x_297_ = l_Lean_Expr_isAppOf(v_self_209_, v_ctorName_182_);
lean_dec(v_ctorName_182_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_300_; 
lean_dec_ref(v_self_209_);
lean_del_object(v___x_207_);
lean_dec_ref(v___x_203_);
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
lean_dec_ref_known(v_projFn_174_, 2);
lean_dec_ref(v_parent_162_);
v___x_298_ = lean_box(0);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_298_);
v___x_300_ = v___x_196_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
else
{
size_t v___x_302_; size_t v___x_303_; uint8_t v___x_304_; 
lean_del_object(v___x_196_);
v___x_302_ = lean_ptr_addr(v___x_203_);
lean_dec_ref(v___x_203_);
v___x_303_ = lean_ptr_addr(v_self_209_);
v___x_304_ = lean_usize_dec_eq(v___x_302_, v___x_303_);
if (v___x_304_ == 0)
{
if (v_heqProofs_210_ == 0)
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec_ref_known(v_projFn_174_, 2);
v___x_305_ = l_Lean_Expr_appFn_x21(v_parent_162_);
lean_inc_ref(v_self_209_);
v___x_306_ = l_Lean_Expr_app___override(v___x_305_, v_self_209_);
v___x_307_ = l_Lean_Meta_Sym_shareCommon(v___x_306_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref_known(v___x_307_, 1);
v_parentNew_274_ = v_a_308_;
v___y_275_ = v_a_163_;
v___y_276_ = v_a_164_;
v___y_277_ = v_a_165_;
v___y_278_ = v_a_166_;
v___y_279_ = v_a_167_;
v___y_280_ = v_a_168_;
v___y_281_ = v_a_169_;
v___y_282_ = v_a_170_;
v___y_283_ = v_a_171_;
v___y_284_ = v_a_172_;
goto v___jp_273_;
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
lean_dec_ref(v_self_209_);
lean_del_object(v___x_207_);
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
lean_dec_ref(v_parent_162_);
v_a_309_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_307_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_307_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
else
{
lean_object* v_dummy_317_; lean_object* v_nargs_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_dummy_317_ = lean_obj_once(&l_Lean_Meta_Grind_propagateProjEq___closed__7, &l_Lean_Meta_Grind_propagateProjEq___closed__7_once, _init_l_Lean_Meta_Grind_propagateProjEq___closed__7);
v_nargs_318_ = l_Lean_Expr_getAppNumArgs(v_self_209_);
lean_inc(v_nargs_318_);
v___x_319_ = lean_mk_array(v_nargs_318_, v_dummy_317_);
v___x_320_ = lean_nat_sub(v_nargs_318_, v___x_185_);
lean_dec(v_nargs_318_);
lean_inc_ref_n(v_self_209_, 2);
v___x_321_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_self_209_, v___x_319_, v___x_320_);
v___x_322_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_183_);
v___x_323_ = l_Array_toSubarray___redArg(v___x_321_, v___x_322_, v_numParams_183_);
v___x_324_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__8));
v___x_325_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(v___x_323_, v___x_324_);
v___x_326_ = l_Lean_mkAppN(v_projFn_174_, v___x_325_);
lean_dec_ref(v___x_325_);
v___x_327_ = l_Lean_Expr_app___override(v___x_326_, v_self_209_);
v___x_328_ = l_Lean_Meta_Sym_shareCommon(v___x_327_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref_known(v___x_328_, 1);
v_parentNew_274_ = v_a_329_;
v___y_275_ = v_a_163_;
v___y_276_ = v_a_164_;
v___y_277_ = v_a_165_;
v___y_278_ = v_a_166_;
v___y_279_ = v_a_167_;
v___y_280_ = v_a_168_;
v___y_281_ = v_a_169_;
v___y_282_ = v_a_170_;
v___y_283_ = v_a_171_;
v___y_284_ = v_a_172_;
goto v___jp_273_;
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec_ref(v_self_209_);
lean_del_object(v___x_207_);
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
lean_dec_ref(v_parent_162_);
v_a_330_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_328_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_328_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_projFn_174_, 2);
v_parentNew_253_ = v_parent_162_;
v___y_254_ = v_a_163_;
v___y_255_ = v_a_164_;
v___y_256_ = v_a_165_;
v___y_257_ = v_a_166_;
v___y_258_ = v_a_167_;
v___y_259_ = v_a_168_;
v___y_260_ = v_a_169_;
v___y_261_ = v_a_170_;
v___y_262_ = v_a_171_;
v___y_263_ = v_a_172_;
goto v___jp_252_;
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
lean_object* v_a_230_; lean_object* v___x_231_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v___x_229_, 1);
lean_inc_ref(v___x_228_);
lean_inc_ref(v___y_212_);
v___x_231_ = l_Lean_Meta_mkEq(v___y_212_, v___x_228_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_233_; uint8_t v___x_234_; lean_object* v___x_235_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref_known(v___x_231_, 1);
v___x_233_ = l_Lean_Meta_mkExpectedPropHint(v_a_230_, v_a_232_);
v___x_234_ = 0;
v___x_235_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___y_212_, v___x_228_, v___x_233_, v___x_234_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
return v___x_235_;
}
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
lean_dec(v_a_230_);
lean_dec_ref(v___x_228_);
lean_dec_ref(v___y_212_);
v_a_236_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_231_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_231_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec_ref(v___x_228_);
lean_dec_ref(v___y_212_);
v_a_244_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_229_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_229_);
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
}
v___jp_252_:
{
lean_object* v_options_264_; uint8_t v_hasTrace_265_; 
v_options_264_ = lean_ctor_get(v___y_262_, 2);
v_hasTrace_265_ = lean_ctor_get_uint8(v_options_264_, sizeof(void*)*1);
if (v_hasTrace_265_ == 0)
{
v___y_212_ = v_parentNew_253_;
v___y_213_ = v___y_254_;
v___y_214_ = v___y_256_;
v___y_215_ = v___y_260_;
v___y_216_ = v___y_261_;
v___y_217_ = v___y_262_;
v___y_218_ = v___y_263_;
goto v___jp_211_;
}
else
{
lean_object* v_inheritedTraceOptions_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v_inheritedTraceOptions_266_ = lean_ctor_get(v___y_262_, 13);
v___x_267_ = ((lean_object*)(l_Lean_Meta_Grind_propagateProjEq___closed__3));
v___x_268_ = lean_obj_once(&l_Lean_Meta_Grind_propagateProjEq___closed__6, &l_Lean_Meta_Grind_propagateProjEq___closed__6_once, _init_l_Lean_Meta_Grind_propagateProjEq___closed__6);
v___x_269_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_266_, v_options_264_, v___x_268_);
if (v___x_269_ == 0)
{
v___y_212_ = v_parentNew_253_;
v___y_213_ = v___y_254_;
v___y_214_ = v___y_256_;
v___y_215_ = v___y_260_;
v___y_216_ = v___y_261_;
v___y_217_ = v___y_262_;
v___y_218_ = v___y_263_;
goto v___jp_211_;
}
else
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Meta_Grind_updateLastTag(v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec_ref_known(v___x_270_, 1);
lean_inc_ref(v_parentNew_253_);
v___x_271_ = l_Lean_MessageData_ofExpr(v_parentNew_253_);
v___x_272_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v___x_267_, v___x_271_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_dec_ref_known(v___x_272_, 1);
v___y_212_ = v_parentNew_253_;
v___y_213_ = v___y_254_;
v___y_214_ = v___y_256_;
v___y_215_ = v___y_260_;
v___y_216_ = v___y_261_;
v___y_217_ = v___y_262_;
v___y_218_ = v___y_263_;
goto v___jp_211_;
}
else
{
lean_dec_ref(v_parentNew_253_);
lean_dec_ref(v_self_209_);
lean_del_object(v___x_207_);
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
return v___x_272_;
}
}
else
{
lean_dec_ref(v_parentNew_253_);
lean_dec_ref(v_self_209_);
lean_del_object(v___x_207_);
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
return v___x_270_;
}
}
}
}
v___jp_273_:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_Meta_Grind_getGeneration___redArg(v_parent_162_, v___y_275_);
lean_dec_ref(v_parent_162_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_a_286_);
lean_dec_ref_known(v___x_285_, 1);
v___x_287_ = lean_box(0);
lean_inc(v___y_284_);
lean_inc_ref(v___y_283_);
lean_inc(v___y_282_);
lean_inc_ref(v___y_281_);
lean_inc(v___y_280_);
lean_inc_ref(v___y_279_);
lean_inc(v___y_278_);
lean_inc_ref(v___y_277_);
lean_inc(v___y_276_);
lean_inc(v___y_275_);
lean_inc_ref(v_parentNew_274_);
v___x_288_ = lean_grind_internalize(v_parentNew_274_, v_a_286_, v___x_287_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_dec_ref_known(v___x_288_, 1);
v_parentNew_253_ = v_parentNew_274_;
v___y_254_ = v___y_275_;
v___y_255_ = v___y_276_;
v___y_256_ = v___y_277_;
v___y_257_ = v___y_278_;
v___y_258_ = v___y_279_;
v___y_259_ = v___y_280_;
v___y_260_ = v___y_281_;
v___y_261_ = v___y_282_;
v___y_262_ = v___y_283_;
v___y_263_ = v___y_284_;
goto v___jp_252_;
}
else
{
lean_dec_ref(v_parentNew_274_);
lean_dec_ref(v_self_209_);
lean_del_object(v___x_207_);
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
return v___x_288_;
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec_ref(v_parentNew_274_);
lean_dec_ref(v_self_209_);
lean_del_object(v___x_207_);
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
v_a_289_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_285_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_285_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec_ref(v___x_203_);
lean_del_object(v___x_196_);
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
lean_dec(v_ctorName_182_);
lean_dec_ref_known(v_projFn_174_, 2);
lean_dec_ref(v_parent_162_);
v_a_339_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_204_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_204_);
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
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec(v_i_184_);
lean_dec(v_numParams_183_);
lean_dec(v_ctorName_182_);
lean_dec_ref_known(v_projFn_174_, 2);
lean_dec_ref(v_parent_162_);
v_a_348_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_193_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_193_);
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
else
{
lean_object* v___x_356_; lean_object* v___x_358_; 
lean_dec(v_a_177_);
lean_dec_ref_known(v_projFn_174_, 2);
lean_dec_ref(v_parent_162_);
v___x_356_ = lean_box(0);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_356_);
v___x_358_ = v___x_179_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec_ref(v_projFn_174_);
lean_dec_ref(v_parent_162_);
v___x_361_ = lean_box(0);
v___x_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateProjEq___boxed(lean_object* v_parent_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Meta_Grind_propagateProjEq(v_parent_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
lean_dec(v_a_364_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1(lean_object* v_cls_376_, lean_object* v_msg_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v_cls_376_, v_msg_377_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___boxed(lean_object* v_cls_390_, lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1(v_cls_390_, v_msg_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec(v___y_392_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2(lean_object* v_inst_404_, lean_object* v_R_405_, lean_object* v_a_406_, lean_object* v_b_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(v_a_406_, v_b_407_);
return v___x_408_;
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
