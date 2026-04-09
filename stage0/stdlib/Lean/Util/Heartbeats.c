// Lean compiler output
// Module: Lean.Util.Heartbeats
// Imports: public import Lean.CoreM
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_IO_getNumHeartbeats___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_withHeartbeats___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_getNumHeartbeats___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_withHeartbeats___redArg___closed__0 = (const lean_object*)&l_Lean_withHeartbeats___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxHeartbeats___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxHeartbeats___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxHeartbeats(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxHeartbeats___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getInitHeartbeats___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getInitHeartbeats___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getInitHeartbeats(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getInitHeartbeats___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRemainingHeartbeats___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRemainingHeartbeats___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRemainingHeartbeats(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRemainingHeartbeats___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_heartbeatsPercent___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_heartbeatsPercent___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_heartbeatsPercent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_heartbeatsPercent___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_reportOutOfHeartbeats___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_reportOutOfHeartbeats___closed__0 = (const lean_object*)&l_Lean_reportOutOfHeartbeats___closed__0_value;
static const lean_string_object l_Lean_reportOutOfHeartbeats___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 109, .m_capacity = 109, .m_length = 108, .m_data = "` stopped because it was running out of time.\nYou may get better results using `set_option maxHeartbeats 0`."};
static const lean_object* l_Lean_reportOutOfHeartbeats___closed__1 = (const lean_object*)&l_Lean_reportOutOfHeartbeats___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_reportOutOfHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportOutOfHeartbeats___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___redArg___lam__0(lean_object* v_start_1_, lean_object* v_r_2_, lean_object* v_toPure_3_, lean_object* v_finish_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_5_ = lean_nat_sub(v_finish_4_, v_start_1_);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v_r_2_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
v___x_7_ = lean_apply_2(v_toPure_3_, lean_box(0), v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___redArg___lam__0___boxed(lean_object* v_start_8_, lean_object* v_r_9_, lean_object* v_toPure_10_, lean_object* v_finish_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_withHeartbeats___redArg___lam__0(v_start_8_, v_r_9_, v_toPure_10_, v_finish_11_);
lean_dec(v_finish_11_);
lean_dec(v_start_8_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___redArg___lam__1(lean_object* v_start_13_, lean_object* v_toPure_14_, lean_object* v_toBind_15_, lean_object* v___x_16_, lean_object* v_r_17_){
_start:
{
lean_object* v___f_18_; lean_object* v___x_19_; 
v___f_18_ = lean_alloc_closure((void*)(l_Lean_withHeartbeats___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_18_, 0, v_start_13_);
lean_closure_set(v___f_18_, 1, v_r_17_);
lean_closure_set(v___f_18_, 2, v_toPure_14_);
v___x_19_ = lean_apply_4(v_toBind_15_, lean_box(0), lean_box(0), v___x_16_, v___f_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___redArg___lam__2(lean_object* v_toPure_20_, lean_object* v_toBind_21_, lean_object* v___x_22_, lean_object* v_x_23_, lean_object* v_start_24_){
_start:
{
lean_object* v___f_25_; lean_object* v___x_26_; 
lean_inc(v_toBind_21_);
v___f_25_ = lean_alloc_closure((void*)(l_Lean_withHeartbeats___redArg___lam__1), 5, 4);
lean_closure_set(v___f_25_, 0, v_start_24_);
lean_closure_set(v___f_25_, 1, v_toPure_20_);
lean_closure_set(v___f_25_, 2, v_toBind_21_);
lean_closure_set(v___f_25_, 3, v___x_22_);
v___x_26_ = lean_apply_4(v_toBind_21_, lean_box(0), lean_box(0), v_x_23_, v___f_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeartbeats___redArg(lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_x_30_){
_start:
{
lean_object* v_toApplicative_31_; lean_object* v_toBind_32_; lean_object* v_toPure_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___f_36_; lean_object* v___x_37_; 
v_toApplicative_31_ = lean_ctor_get(v_inst_28_, 0);
lean_inc_ref(v_toApplicative_31_);
v_toBind_32_ = lean_ctor_get(v_inst_28_, 1);
lean_inc_n(v_toBind_32_, 2);
lean_dec_ref(v_inst_28_);
v_toPure_33_ = lean_ctor_get(v_toApplicative_31_, 1);
lean_inc(v_toPure_33_);
lean_dec_ref(v_toApplicative_31_);
v___x_34_ = ((lean_object*)(l_Lean_withHeartbeats___redArg___closed__0));
v___x_35_ = lean_apply_2(v_inst_29_, lean_box(0), v___x_34_);
lean_inc(v___x_35_);
v___f_36_ = lean_alloc_closure((void*)(l_Lean_withHeartbeats___redArg___lam__2), 5, 4);
lean_closure_set(v___f_36_, 0, v_toPure_33_);
lean_closure_set(v___f_36_, 1, v_toBind_32_);
lean_closure_set(v___f_36_, 2, v___x_35_);
lean_closure_set(v___f_36_, 3, v_x_30_);
v___x_37_ = lean_apply_4(v_toBind_32_, lean_box(0), lean_box(0), v___x_35_, v___f_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeartbeats(lean_object* v_m_38_, lean_object* v_00_u03b1_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_x_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_withHeartbeats___redArg(v_inst_40_, v_inst_41_, v_x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMaxHeartbeats___redArg(lean_object* v_a_44_){
_start:
{
lean_object* v_maxHeartbeats_46_; lean_object* v___x_47_; 
v_maxHeartbeats_46_ = lean_ctor_get(v_a_44_, 9);
lean_inc(v_maxHeartbeats_46_);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v_maxHeartbeats_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMaxHeartbeats___redArg___boxed(lean_object* v_a_48_, lean_object* v_a_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_getMaxHeartbeats___redArg(v_a_48_);
lean_dec_ref(v_a_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMaxHeartbeats(lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lean_getMaxHeartbeats___redArg(v_a_51_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMaxHeartbeats___boxed(lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_getMaxHeartbeats(v_a_55_, v_a_56_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_getInitHeartbeats___redArg(lean_object* v_a_59_){
_start:
{
lean_object* v_initHeartbeats_61_; lean_object* v___x_62_; 
v_initHeartbeats_61_ = lean_ctor_get(v_a_59_, 8);
lean_inc(v_initHeartbeats_61_);
v___x_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_62_, 0, v_initHeartbeats_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_getInitHeartbeats___redArg___boxed(lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_getInitHeartbeats___redArg(v_a_63_);
lean_dec_ref(v_a_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_getInitHeartbeats(lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_getInitHeartbeats___redArg(v_a_66_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_getInitHeartbeats___boxed(lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_getInitHeartbeats(v_a_70_, v_a_71_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRemainingHeartbeats___redArg(lean_object* v_a_74_){
_start:
{
lean_object* v___x_76_; lean_object* v_a_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_89_; 
v___x_76_ = l_Lean_getMaxHeartbeats___redArg(v_a_74_);
v_a_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_a_77_);
lean_dec_ref(v___x_76_);
v___x_78_ = lean_io_get_num_heartbeats();
v___x_79_ = l_Lean_getInitHeartbeats___redArg(v_a_74_);
v_a_80_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_89_ == 0)
{
v___x_82_ = v___x_79_;
v_isShared_83_ = v_isSharedCheck_89_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___x_79_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_89_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_84_ = lean_nat_sub(v___x_78_, v_a_80_);
lean_dec(v_a_80_);
lean_dec(v___x_78_);
v___x_85_ = lean_nat_sub(v_a_77_, v___x_84_);
lean_dec(v___x_84_);
lean_dec(v_a_77_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v___x_85_);
v___x_87_ = v___x_82_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_getRemainingHeartbeats___redArg___boxed(lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_getRemainingHeartbeats___redArg(v_a_90_);
lean_dec_ref(v_a_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRemainingHeartbeats(lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_getRemainingHeartbeats___redArg(v_a_93_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRemainingHeartbeats___boxed(lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_getRemainingHeartbeats(v_a_97_, v_a_98_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_heartbeatsPercent___redArg(lean_object* v_a_101_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v_a_105_; lean_object* v___x_106_; lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_118_; 
v___x_103_ = lean_io_get_num_heartbeats();
v___x_104_ = l_Lean_getInitHeartbeats___redArg(v_a_101_);
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref(v___x_104_);
v___x_106_ = l_Lean_getMaxHeartbeats___redArg(v_a_101_);
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_118_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_118_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_118_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_111_ = lean_nat_sub(v___x_103_, v_a_105_);
lean_dec(v_a_105_);
lean_dec(v___x_103_);
v___x_112_ = lean_unsigned_to_nat(100u);
v___x_113_ = lean_nat_mul(v___x_111_, v___x_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_nat_div(v___x_113_, v_a_107_);
lean_dec(v_a_107_);
lean_dec(v___x_113_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_114_);
v___x_116_ = v___x_109_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_heartbeatsPercent___redArg___boxed(lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_heartbeatsPercent___redArg(v_a_119_);
lean_dec_ref(v_a_119_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_heartbeatsPercent(lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_heartbeatsPercent___redArg(v_a_122_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_heartbeatsPercent___boxed(lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_heartbeatsPercent(v_a_126_, v_a_127_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
return v_res_129_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0(uint8_t v___y_138_, uint8_t v_suppressElabErrors_139_, lean_object* v_x_140_){
_start:
{
if (lean_obj_tag(v_x_140_) == 1)
{
lean_object* v_pre_141_; 
v_pre_141_ = lean_ctor_get(v_x_140_, 0);
switch(lean_obj_tag(v_pre_141_))
{
case 1:
{
lean_object* v_pre_142_; 
v_pre_142_ = lean_ctor_get(v_pre_141_, 0);
switch(lean_obj_tag(v_pre_142_))
{
case 0:
{
lean_object* v_str_143_; lean_object* v_str_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v_str_143_ = lean_ctor_get(v_x_140_, 1);
v_str_144_ = lean_ctor_get(v_pre_141_, 1);
v___x_145_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__0));
v___x_146_ = lean_string_dec_eq(v_str_144_, v___x_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_147_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__1));
v___x_148_ = lean_string_dec_eq(v_str_144_, v___x_147_);
if (v___x_148_ == 0)
{
return v___y_138_;
}
else
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__2));
v___x_150_ = lean_string_dec_eq(v_str_143_, v___x_149_);
if (v___x_150_ == 0)
{
return v___y_138_;
}
else
{
return v_suppressElabErrors_139_;
}
}
}
else
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__3));
v___x_152_ = lean_string_dec_eq(v_str_143_, v___x_151_);
if (v___x_152_ == 0)
{
return v___y_138_;
}
else
{
return v_suppressElabErrors_139_;
}
}
}
case 1:
{
lean_object* v_pre_153_; 
v_pre_153_ = lean_ctor_get(v_pre_142_, 0);
if (lean_obj_tag(v_pre_153_) == 0)
{
lean_object* v_str_154_; lean_object* v_str_155_; lean_object* v_str_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v_str_154_ = lean_ctor_get(v_x_140_, 1);
v_str_155_ = lean_ctor_get(v_pre_141_, 1);
v_str_156_ = lean_ctor_get(v_pre_142_, 1);
v___x_157_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__4));
v___x_158_ = lean_string_dec_eq(v_str_156_, v___x_157_);
if (v___x_158_ == 0)
{
return v___y_138_;
}
else
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__5));
v___x_160_ = lean_string_dec_eq(v_str_155_, v___x_159_);
if (v___x_160_ == 0)
{
return v___y_138_;
}
else
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__6));
v___x_162_ = lean_string_dec_eq(v_str_154_, v___x_161_);
if (v___x_162_ == 0)
{
return v___y_138_;
}
else
{
return v_suppressElabErrors_139_;
}
}
}
}
else
{
return v___y_138_;
}
}
default: 
{
return v___y_138_;
}
}
}
case 0:
{
lean_object* v_str_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v_str_163_ = lean_ctor_get(v_x_140_, 1);
v___x_164_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__7));
v___x_165_ = lean_string_dec_eq(v_str_163_, v___x_164_);
if (v___x_165_ == 0)
{
return v___y_138_;
}
else
{
return v_suppressElabErrors_139_;
}
}
default: 
{
return v___y_138_;
}
}
}
else
{
return v___y_138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___boxed(lean_object* v___y_166_, lean_object* v_suppressElabErrors_167_, lean_object* v_x_168_){
_start:
{
uint8_t v___y_2451__boxed_169_; uint8_t v_suppressElabErrors_boxed_170_; uint8_t v_res_171_; lean_object* v_r_172_; 
v___y_2451__boxed_169_ = lean_unbox(v___y_166_);
v_suppressElabErrors_boxed_170_ = lean_unbox(v_suppressElabErrors_167_);
v_res_171_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0(v___y_2451__boxed_169_, v_suppressElabErrors_boxed_170_, v_x_168_);
lean_dec(v_x_168_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(lean_object* v_opts_173_, lean_object* v_opt_174_){
_start:
{
lean_object* v_name_175_; lean_object* v_defValue_176_; lean_object* v_map_177_; lean_object* v___x_178_; 
v_name_175_ = lean_ctor_get(v_opt_174_, 0);
v_defValue_176_ = lean_ctor_get(v_opt_174_, 1);
v_map_177_ = lean_ctor_get(v_opts_173_, 0);
v___x_178_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_177_, v_name_175_);
if (lean_obj_tag(v___x_178_) == 0)
{
uint8_t v___x_179_; 
v___x_179_ = lean_unbox(v_defValue_176_);
return v___x_179_;
}
else
{
lean_object* v_val_180_; 
v_val_180_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_val_180_);
lean_dec_ref(v___x_178_);
if (lean_obj_tag(v_val_180_) == 1)
{
uint8_t v_v_181_; 
v_v_181_ = lean_ctor_get_uint8(v_val_180_, 0);
lean_dec_ref(v_val_180_);
return v_v_181_;
}
else
{
uint8_t v___x_182_; 
lean_dec(v_val_180_);
v___x_182_ = lean_unbox(v_defValue_176_);
return v___x_182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2___boxed(lean_object* v_opts_183_, lean_object* v_opt_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(v_opts_183_, v_opt_184_);
lean_dec_ref(v_opt_184_);
lean_dec_ref(v_opts_183_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_187_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0);
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1);
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
lean_ctor_set(v___x_192_, 2, v___x_191_);
lean_ctor_set(v___x_192_, 3, v___x_191_);
lean_ctor_set(v___x_192_, 4, v___x_190_);
lean_ctor_set(v___x_192_, 5, v___x_190_);
lean_ctor_set(v___x_192_, 6, v___x_190_);
lean_ctor_set(v___x_192_, 7, v___x_190_);
lean_ctor_set(v___x_192_, 8, v___x_190_);
lean_ctor_set(v___x_192_, 9, v___x_190_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_unsigned_to_nat(32u);
v___x_194_ = lean_mk_empty_array_with_capacity(v___x_193_);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_196_ = ((size_t)5ULL);
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_unsigned_to_nat(32u);
v___x_199_ = lean_mk_empty_array_with_capacity(v___x_198_);
v___x_200_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3);
v___x_201_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___x_199_);
lean_ctor_set(v___x_201_, 2, v___x_197_);
lean_ctor_set(v___x_201_, 3, v___x_197_);
lean_ctor_set_usize(v___x_201_, 4, v___x_196_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_202_ = lean_box(1);
v___x_203_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4);
v___x_204_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1);
v___x_205_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
lean_ctor_set(v___x_205_, 2, v___x_202_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(lean_object* v_msgData_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; lean_object* v_env_211_; lean_object* v_options_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_210_ = lean_st_ref_get(v___y_208_);
v_env_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc_ref(v_env_211_);
lean_dec(v___x_210_);
v_options_212_ = lean_ctor_get(v___y_207_, 2);
v___x_213_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2);
v___x_214_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_212_);
v___x_215_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_215_, 0, v_env_211_);
lean_ctor_set(v___x_215_, 1, v___x_213_);
lean_ctor_set(v___x_215_, 2, v___x_214_);
lean_ctor_set(v___x_215_, 3, v_options_212_);
v___x_216_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v_msgData_206_);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(v_msgData_218_, v___y_219_, v___y_220_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(lean_object* v_ref_224_, lean_object* v_msgData_225_, uint8_t v_severity_226_, uint8_t v_isSilent_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v___y_232_; uint8_t v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; uint8_t v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; uint8_t v___y_271_; uint8_t v___y_272_; lean_object* v___y_273_; uint8_t v___y_274_; lean_object* v___y_275_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; uint8_t v___y_296_; uint8_t v___y_297_; uint8_t v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; uint8_t v___y_307_; uint8_t v___y_308_; lean_object* v___y_309_; uint8_t v___y_310_; uint8_t v___x_315_; lean_object* v___y_317_; lean_object* v___y_318_; uint8_t v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; uint8_t v___y_322_; uint8_t v___y_323_; uint8_t v___y_325_; uint8_t v___x_340_; 
v___x_315_ = 2;
v___x_340_ = l_Lean_instBEqMessageSeverity_beq(v_severity_226_, v___x_315_);
if (v___x_340_ == 0)
{
v___y_325_ = v___x_340_;
goto v___jp_324_;
}
else
{
uint8_t v___x_341_; 
lean_inc_ref(v_msgData_225_);
v___x_341_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_225_);
v___y_325_ = v___x_341_;
goto v___jp_324_;
}
v___jp_231_:
{
lean_object* v___x_241_; lean_object* v_currNamespace_242_; lean_object* v_openDecls_243_; lean_object* v_env_244_; lean_object* v_nextMacroScope_245_; lean_object* v_ngen_246_; lean_object* v_auxDeclNGen_247_; lean_object* v_traceState_248_; lean_object* v_cache_249_; lean_object* v_messages_250_; lean_object* v_infoState_251_; lean_object* v_snapshotTasks_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_266_; 
v___x_241_ = lean_st_ref_take(v___y_240_);
v_currNamespace_242_ = lean_ctor_get(v___y_239_, 6);
v_openDecls_243_ = lean_ctor_get(v___y_239_, 7);
v_env_244_ = lean_ctor_get(v___x_241_, 0);
v_nextMacroScope_245_ = lean_ctor_get(v___x_241_, 1);
v_ngen_246_ = lean_ctor_get(v___x_241_, 2);
v_auxDeclNGen_247_ = lean_ctor_get(v___x_241_, 3);
v_traceState_248_ = lean_ctor_get(v___x_241_, 4);
v_cache_249_ = lean_ctor_get(v___x_241_, 5);
v_messages_250_ = lean_ctor_get(v___x_241_, 6);
v_infoState_251_ = lean_ctor_get(v___x_241_, 7);
v_snapshotTasks_252_ = lean_ctor_get(v___x_241_, 8);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_266_ == 0)
{
v___x_254_ = v___x_241_;
v_isShared_255_ = v_isSharedCheck_266_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_snapshotTasks_252_);
lean_inc(v_infoState_251_);
lean_inc(v_messages_250_);
lean_inc(v_cache_249_);
lean_inc(v_traceState_248_);
lean_inc(v_auxDeclNGen_247_);
lean_inc(v_ngen_246_);
lean_inc(v_nextMacroScope_245_);
lean_inc(v_env_244_);
lean_dec(v___x_241_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_266_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
lean_inc(v_openDecls_243_);
lean_inc(v_currNamespace_242_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v_currNamespace_242_);
lean_ctor_set(v___x_256_, 1, v_openDecls_243_);
v___x_257_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___y_236_);
lean_inc_ref(v___y_235_);
lean_inc_ref(v___y_232_);
v___x_258_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_258_, 0, v___y_232_);
lean_ctor_set(v___x_258_, 1, v___y_234_);
lean_ctor_set(v___x_258_, 2, v___y_238_);
lean_ctor_set(v___x_258_, 3, v___y_235_);
lean_ctor_set(v___x_258_, 4, v___x_257_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*5, v___y_233_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*5 + 1, v___y_237_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*5 + 2, v_isSilent_227_);
v___x_259_ = l_Lean_MessageLog_add(v___x_258_, v_messages_250_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 6, v___x_259_);
v___x_261_ = v___x_254_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_env_244_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_nextMacroScope_245_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v_ngen_246_);
lean_ctor_set(v_reuseFailAlloc_265_, 3, v_auxDeclNGen_247_);
lean_ctor_set(v_reuseFailAlloc_265_, 4, v_traceState_248_);
lean_ctor_set(v_reuseFailAlloc_265_, 5, v_cache_249_);
lean_ctor_set(v_reuseFailAlloc_265_, 6, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_265_, 7, v_infoState_251_);
lean_ctor_set(v_reuseFailAlloc_265_, 8, v_snapshotTasks_252_);
v___x_261_ = v_reuseFailAlloc_265_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = lean_st_ref_set(v___y_240_, v___x_261_);
v___x_263_ = lean_box(0);
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
}
v___jp_267_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_291_; 
v___x_276_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_225_);
v___x_277_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(v___x_276_, v___y_228_, v___y_229_);
v_a_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_291_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_291_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_291_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
lean_inc_ref_n(v___y_269_, 2);
v___x_282_ = l_Lean_FileMap_toPosition(v___y_269_, v___y_273_);
lean_dec(v___y_273_);
v___x_283_ = l_Lean_FileMap_toPosition(v___y_269_, v___y_275_);
lean_dec(v___y_275_);
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
v___x_285_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___closed__0));
if (v___y_272_ == 0)
{
lean_del_object(v___x_280_);
lean_dec_ref(v___y_268_);
v___y_232_ = v___y_270_;
v___y_233_ = v___y_271_;
v___y_234_ = v___x_282_;
v___y_235_ = v___x_285_;
v___y_236_ = v_a_278_;
v___y_237_ = v___y_274_;
v___y_238_ = v___x_284_;
v___y_239_ = v___y_228_;
v___y_240_ = v___y_229_;
goto v___jp_231_;
}
else
{
uint8_t v___x_286_; 
lean_inc(v_a_278_);
v___x_286_ = l_Lean_MessageData_hasTag(v___y_268_, v_a_278_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_289_; 
lean_dec_ref(v___x_284_);
lean_dec_ref(v___x_282_);
lean_dec(v_a_278_);
v___x_287_ = lean_box(0);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_287_);
v___x_289_ = v___x_280_;
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
lean_del_object(v___x_280_);
v___y_232_ = v___y_270_;
v___y_233_ = v___y_271_;
v___y_234_ = v___x_282_;
v___y_235_ = v___x_285_;
v___y_236_ = v_a_278_;
v___y_237_ = v___y_274_;
v___y_238_ = v___x_284_;
v___y_239_ = v___y_228_;
v___y_240_ = v___y_229_;
goto v___jp_231_;
}
}
}
}
v___jp_292_:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Syntax_getTailPos_x3f(v___y_299_, v___y_296_);
lean_dec(v___y_299_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_inc(v___y_300_);
v___y_268_ = v___y_293_;
v___y_269_ = v___y_294_;
v___y_270_ = v___y_295_;
v___y_271_ = v___y_296_;
v___y_272_ = v___y_297_;
v___y_273_ = v___y_300_;
v___y_274_ = v___y_298_;
v___y_275_ = v___y_300_;
goto v___jp_267_;
}
else
{
lean_object* v_val_302_; 
v_val_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_val_302_);
lean_dec_ref(v___x_301_);
v___y_268_ = v___y_293_;
v___y_269_ = v___y_294_;
v___y_270_ = v___y_295_;
v___y_271_ = v___y_296_;
v___y_272_ = v___y_297_;
v___y_273_ = v___y_300_;
v___y_274_ = v___y_298_;
v___y_275_ = v_val_302_;
goto v___jp_267_;
}
}
v___jp_303_:
{
lean_object* v_ref_311_; lean_object* v___x_312_; 
v_ref_311_ = l_Lean_replaceRef(v_ref_224_, v___y_309_);
v___x_312_ = l_Lean_Syntax_getPos_x3f(v_ref_311_, v___y_307_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v___x_313_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___y_293_ = v___y_304_;
v___y_294_ = v___y_305_;
v___y_295_ = v___y_306_;
v___y_296_ = v___y_307_;
v___y_297_ = v___y_308_;
v___y_298_ = v___y_310_;
v___y_299_ = v_ref_311_;
v___y_300_ = v___x_313_;
goto v___jp_292_;
}
else
{
lean_object* v_val_314_; 
v_val_314_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_val_314_);
lean_dec_ref(v___x_312_);
v___y_293_ = v___y_304_;
v___y_294_ = v___y_305_;
v___y_295_ = v___y_306_;
v___y_296_ = v___y_307_;
v___y_297_ = v___y_308_;
v___y_298_ = v___y_310_;
v___y_299_ = v_ref_311_;
v___y_300_ = v_val_314_;
goto v___jp_292_;
}
}
v___jp_316_:
{
if (v___y_323_ == 0)
{
v___y_304_ = v___y_320_;
v___y_305_ = v___y_317_;
v___y_306_ = v___y_318_;
v___y_307_ = v___y_322_;
v___y_308_ = v___y_319_;
v___y_309_ = v___y_321_;
v___y_310_ = v_severity_226_;
goto v___jp_303_;
}
else
{
v___y_304_ = v___y_320_;
v___y_305_ = v___y_317_;
v___y_306_ = v___y_318_;
v___y_307_ = v___y_322_;
v___y_308_ = v___y_319_;
v___y_309_ = v___y_321_;
v___y_310_ = v___x_315_;
goto v___jp_303_;
}
}
v___jp_324_:
{
if (v___y_325_ == 0)
{
lean_object* v_fileName_326_; lean_object* v_fileMap_327_; lean_object* v_options_328_; lean_object* v_ref_329_; uint8_t v_suppressElabErrors_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___f_333_; uint8_t v___x_334_; uint8_t v___x_335_; 
v_fileName_326_ = lean_ctor_get(v___y_228_, 0);
v_fileMap_327_ = lean_ctor_get(v___y_228_, 1);
v_options_328_ = lean_ctor_get(v___y_228_, 2);
v_ref_329_ = lean_ctor_get(v___y_228_, 5);
v_suppressElabErrors_330_ = lean_ctor_get_uint8(v___y_228_, sizeof(void*)*14 + 1);
v___x_331_ = lean_box(v___y_325_);
v___x_332_ = lean_box(v_suppressElabErrors_330_);
v___f_333_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_333_, 0, v___x_331_);
lean_closure_set(v___f_333_, 1, v___x_332_);
v___x_334_ = 1;
v___x_335_ = l_Lean_instBEqMessageSeverity_beq(v_severity_226_, v___x_334_);
if (v___x_335_ == 0)
{
v___y_317_ = v_fileMap_327_;
v___y_318_ = v_fileName_326_;
v___y_319_ = v_suppressElabErrors_330_;
v___y_320_ = v___f_333_;
v___y_321_ = v_ref_329_;
v___y_322_ = v___y_325_;
v___y_323_ = v___x_335_;
goto v___jp_316_;
}
else
{
lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = l_Lean_warningAsError;
v___x_337_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(v_options_328_, v___x_336_);
v___y_317_ = v_fileMap_327_;
v___y_318_ = v_fileName_326_;
v___y_319_ = v_suppressElabErrors_330_;
v___y_320_ = v___f_333_;
v___y_321_ = v_ref_329_;
v___y_322_ = v___y_325_;
v___y_323_ = v___x_337_;
goto v___jp_316_;
}
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec_ref(v_msgData_225_);
v___x_338_ = lean_box(0);
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___boxed(lean_object* v_ref_342_, lean_object* v_msgData_343_, lean_object* v_severity_344_, lean_object* v_isSilent_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
uint8_t v_severity_boxed_349_; uint8_t v_isSilent_boxed_350_; lean_object* v_res_351_; 
v_severity_boxed_349_ = lean_unbox(v_severity_344_);
v_isSilent_boxed_350_ = lean_unbox(v_isSilent_345_);
v_res_351_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(v_ref_342_, v_msgData_343_, v_severity_boxed_349_, v_isSilent_boxed_350_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v_ref_342_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(lean_object* v_ref_352_, lean_object* v_msgData_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
uint8_t v___x_357_; uint8_t v___x_358_; lean_object* v___x_359_; 
v___x_357_ = 0;
v___x_358_ = 0;
v___x_359_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(v_ref_352_, v_msgData_353_, v___x_357_, v___x_358_, v___y_354_, v___y_355_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0___boxed(lean_object* v_ref_360_, lean_object* v_msgData_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(v_ref_360_, v_msgData_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v_ref_360_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportOutOfHeartbeats(lean_object* v_tac_368_, lean_object* v_stx_369_, lean_object* v_threshold_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v___x_374_; lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_392_; 
v___x_374_ = l_Lean_heartbeatsPercent___redArg(v_a_371_);
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_392_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_392_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_392_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
uint8_t v___x_379_; 
v___x_379_ = lean_nat_dec_le(v_threshold_370_, v_a_375_);
lean_dec(v_a_375_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_382_; 
lean_dec(v_tac_368_);
v___x_380_ = lean_box(0);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_380_);
v___x_382_ = v___x_377_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
lean_del_object(v___x_377_);
v___x_384_ = ((lean_object*)(l_Lean_reportOutOfHeartbeats___closed__0));
v___x_385_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_tac_368_, v___x_379_);
v___x_386_ = lean_string_append(v___x_384_, v___x_385_);
lean_dec_ref(v___x_385_);
v___x_387_ = ((lean_object*)(l_Lean_reportOutOfHeartbeats___closed__1));
v___x_388_ = lean_string_append(v___x_386_, v___x_387_);
v___x_389_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
v___x_390_ = l_Lean_MessageData_ofFormat(v___x_389_);
v___x_391_ = l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(v_stx_369_, v___x_390_, v_a_371_, v_a_372_);
return v___x_391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportOutOfHeartbeats___boxed(lean_object* v_tac_393_, lean_object* v_stx_394_, lean_object* v_threshold_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_reportOutOfHeartbeats(v_tac_393_, v_stx_394_, v_threshold_395_, v_a_396_, v_a_397_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_threshold_395_);
lean_dec(v_stx_394_);
return v_res_399_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Heartbeats(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_Heartbeats(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_CoreM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Heartbeats(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Heartbeats(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_Heartbeats(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_Heartbeats(builtin);
}
#ifdef __cplusplus
}
#endif
