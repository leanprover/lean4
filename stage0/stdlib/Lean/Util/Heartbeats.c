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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
lean_object* v_toCold_46_; lean_object* v_maxHeartbeats_47_; lean_object* v___x_48_; 
v_toCold_46_ = lean_ctor_get(v_a_44_, 0);
v_maxHeartbeats_47_ = lean_ctor_get(v_toCold_46_, 7);
lean_inc(v_maxHeartbeats_47_);
v___x_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_48_, 0, v_maxHeartbeats_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMaxHeartbeats___redArg___boxed(lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_getMaxHeartbeats___redArg(v_a_49_);
lean_dec_ref(v_a_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMaxHeartbeats(lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_getMaxHeartbeats___redArg(v_a_52_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMaxHeartbeats___boxed(lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_getMaxHeartbeats(v_a_56_, v_a_57_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_getInitHeartbeats___redArg(lean_object* v_a_60_){
_start:
{
lean_object* v_toCold_62_; lean_object* v_initHeartbeats_63_; lean_object* v___x_64_; 
v_toCold_62_ = lean_ctor_get(v_a_60_, 0);
v_initHeartbeats_63_ = lean_ctor_get(v_toCold_62_, 6);
lean_inc(v_initHeartbeats_63_);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v_initHeartbeats_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_getInitHeartbeats___redArg___boxed(lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_getInitHeartbeats___redArg(v_a_65_);
lean_dec_ref(v_a_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_getInitHeartbeats(lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_getInitHeartbeats___redArg(v_a_68_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_getInitHeartbeats___boxed(lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_getInitHeartbeats(v_a_72_, v_a_73_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRemainingHeartbeats___redArg(lean_object* v_a_76_){
_start:
{
lean_object* v___x_78_; lean_object* v_a_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_91_; 
v___x_78_ = l_Lean_getMaxHeartbeats___redArg(v_a_76_);
v_a_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_a_79_);
lean_dec_ref(v___x_78_);
v___x_80_ = lean_io_get_num_heartbeats();
v___x_81_ = l_Lean_getInitHeartbeats___redArg(v_a_76_);
v_a_82_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_91_ == 0)
{
v___x_84_ = v___x_81_;
v_isShared_85_ = v_isSharedCheck_91_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_81_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_91_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_86_ = lean_nat_sub(v___x_80_, v_a_82_);
lean_dec(v_a_82_);
lean_dec(v___x_80_);
v___x_87_ = lean_nat_sub(v_a_79_, v___x_86_);
lean_dec(v___x_86_);
lean_dec(v_a_79_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v___x_87_);
v___x_89_ = v___x_84_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRemainingHeartbeats___redArg___boxed(lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_getRemainingHeartbeats___redArg(v_a_92_);
lean_dec_ref(v_a_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRemainingHeartbeats(lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_getRemainingHeartbeats___redArg(v_a_95_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRemainingHeartbeats___boxed(lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_getRemainingHeartbeats(v_a_99_, v_a_100_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_heartbeatsPercent___redArg(lean_object* v_a_103_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v_a_107_; lean_object* v___x_108_; lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_120_; 
v___x_105_ = lean_io_get_num_heartbeats();
v___x_106_ = l_Lean_getInitHeartbeats___redArg(v_a_103_);
v_a_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_a_107_);
lean_dec_ref(v___x_106_);
v___x_108_ = l_Lean_getMaxHeartbeats___redArg(v_a_103_);
v_a_109_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_120_ == 0)
{
v___x_111_ = v___x_108_;
v_isShared_112_ = v_isSharedCheck_120_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_108_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_120_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_113_ = lean_nat_sub(v___x_105_, v_a_107_);
lean_dec(v_a_107_);
lean_dec(v___x_105_);
v___x_114_ = lean_unsigned_to_nat(100u);
v___x_115_ = lean_nat_mul(v___x_113_, v___x_114_);
lean_dec(v___x_113_);
v___x_116_ = lean_nat_div(v___x_115_, v_a_109_);
lean_dec(v_a_109_);
lean_dec(v___x_115_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_116_);
v___x_118_ = v___x_111_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_heartbeatsPercent___redArg___boxed(lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_heartbeatsPercent___redArg(v_a_121_);
lean_dec_ref(v_a_121_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_heartbeatsPercent(lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_heartbeatsPercent___redArg(v_a_124_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_heartbeatsPercent___boxed(lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_heartbeatsPercent(v_a_128_, v_a_129_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
return v_res_131_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_140_, uint8_t v___y_141_, lean_object* v_x_142_){
_start:
{
if (lean_obj_tag(v_x_142_) == 1)
{
lean_object* v_pre_143_; 
v_pre_143_ = lean_ctor_get(v_x_142_, 0);
switch(lean_obj_tag(v_pre_143_))
{
case 1:
{
lean_object* v_pre_144_; 
v_pre_144_ = lean_ctor_get(v_pre_143_, 0);
switch(lean_obj_tag(v_pre_144_))
{
case 0:
{
lean_object* v_str_145_; lean_object* v_str_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v_str_145_ = lean_ctor_get(v_x_142_, 1);
v_str_146_ = lean_ctor_get(v_pre_143_, 1);
v___x_147_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__0));
v___x_148_ = lean_string_dec_eq(v_str_146_, v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__1));
v___x_150_ = lean_string_dec_eq(v_str_146_, v___x_149_);
if (v___x_150_ == 0)
{
return v___x_150_;
}
else
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__2));
v___x_152_ = lean_string_dec_eq(v_str_145_, v___x_151_);
if (v___x_152_ == 0)
{
return v___x_152_;
}
else
{
return v_suppressElabErrors_140_;
}
}
}
else
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__3));
v___x_154_ = lean_string_dec_eq(v_str_145_, v___x_153_);
if (v___x_154_ == 0)
{
return v___x_154_;
}
else
{
return v_suppressElabErrors_140_;
}
}
}
case 1:
{
lean_object* v_pre_155_; 
v_pre_155_ = lean_ctor_get(v_pre_144_, 0);
if (lean_obj_tag(v_pre_155_) == 0)
{
lean_object* v_str_156_; lean_object* v_str_157_; lean_object* v_str_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v_str_156_ = lean_ctor_get(v_x_142_, 1);
v_str_157_ = lean_ctor_get(v_pre_143_, 1);
v_str_158_ = lean_ctor_get(v_pre_144_, 1);
v___x_159_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__4));
v___x_160_ = lean_string_dec_eq(v_str_158_, v___x_159_);
if (v___x_160_ == 0)
{
return v___x_160_;
}
else
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__5));
v___x_162_ = lean_string_dec_eq(v_str_157_, v___x_161_);
if (v___x_162_ == 0)
{
return v___x_162_;
}
else
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__6));
v___x_164_ = lean_string_dec_eq(v_str_156_, v___x_163_);
if (v___x_164_ == 0)
{
return v___x_164_;
}
else
{
return v_suppressElabErrors_140_;
}
}
}
}
else
{
return v___y_141_;
}
}
default: 
{
return v___y_141_;
}
}
}
case 0:
{
lean_object* v_str_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v_str_165_ = lean_ctor_get(v_x_142_, 1);
v___x_166_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__7));
v___x_167_ = lean_string_dec_eq(v_str_165_, v___x_166_);
if (v___x_167_ == 0)
{
return v___x_167_;
}
else
{
return v_suppressElabErrors_140_;
}
}
default: 
{
return v___y_141_;
}
}
}
else
{
return v___y_141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_168_, lean_object* v___y_169_, lean_object* v_x_170_){
_start:
{
uint8_t v_suppressElabErrors_boxed_171_; uint8_t v___y_2759__boxed_172_; uint8_t v_res_173_; lean_object* v_r_174_; 
v_suppressElabErrors_boxed_171_ = lean_unbox(v_suppressElabErrors_168_);
v___y_2759__boxed_172_ = lean_unbox(v___y_169_);
v_res_173_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_171_, v___y_2759__boxed_172_, v_x_170_);
lean_dec(v_x_170_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(lean_object* v_opts_175_, lean_object* v_opt_176_){
_start:
{
lean_object* v_name_177_; lean_object* v_defValue_178_; lean_object* v_map_179_; lean_object* v___x_180_; 
v_name_177_ = lean_ctor_get(v_opt_176_, 0);
v_defValue_178_ = lean_ctor_get(v_opt_176_, 1);
v_map_179_ = lean_ctor_get(v_opts_175_, 0);
v___x_180_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_179_, v_name_177_);
if (lean_obj_tag(v___x_180_) == 0)
{
uint8_t v___x_181_; 
v___x_181_ = lean_unbox(v_defValue_178_);
return v___x_181_;
}
else
{
lean_object* v_val_182_; 
v_val_182_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_val_182_);
lean_dec_ref_known(v___x_180_, 1);
if (lean_obj_tag(v_val_182_) == 1)
{
uint8_t v_v_183_; 
v_v_183_ = lean_ctor_get_uint8(v_val_182_, 0);
lean_dec_ref_known(v_val_182_, 0);
return v_v_183_;
}
else
{
uint8_t v___x_184_; 
lean_dec(v_val_182_);
v___x_184_ = lean_unbox(v_defValue_178_);
return v___x_184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2___boxed(lean_object* v_opts_185_, lean_object* v_opt_186_){
_start:
{
uint8_t v_res_187_; lean_object* v_r_188_; 
v_res_187_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(v_opts_185_, v_opt_186_);
lean_dec_ref(v_opt_186_);
lean_dec_ref(v_opts_185_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_189_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0);
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_192_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_193_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1);
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
lean_ctor_set(v___x_195_, 2, v___x_194_);
lean_ctor_set(v___x_195_, 3, v___x_194_);
lean_ctor_set(v___x_195_, 4, v___x_193_);
lean_ctor_set(v___x_195_, 5, v___x_193_);
lean_ctor_set(v___x_195_, 6, v___x_193_);
lean_ctor_set(v___x_195_, 7, v___x_193_);
lean_ctor_set(v___x_195_, 8, v___x_193_);
lean_ctor_set(v___x_195_, 9, v___x_193_);
lean_ctor_set(v___x_195_, 10, v___x_193_);
lean_ctor_set(v___x_195_, 11, v___x_192_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = lean_unsigned_to_nat(32u);
v___x_197_ = lean_mk_empty_array_with_capacity(v___x_196_);
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_199_ = ((size_t)5ULL);
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_unsigned_to_nat(32u);
v___x_202_ = lean_mk_empty_array_with_capacity(v___x_201_);
v___x_203_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3);
v___x_204_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v___x_202_);
lean_ctor_set(v___x_204_, 2, v___x_200_);
lean_ctor_set(v___x_204_, 3, v___x_200_);
lean_ctor_set_usize(v___x_204_, 4, v___x_199_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_205_ = lean_box(1);
v___x_206_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4);
v___x_207_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1);
v___x_208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___x_206_);
lean_ctor_set(v___x_208_, 2, v___x_205_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(lean_object* v_msgData_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; lean_object* v_toCold_214_; lean_object* v_env_215_; lean_object* v_options_216_; uint8_t v___x_217_; lean_object* v_env_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_213_ = lean_st_ref_get(v___y_211_);
v_toCold_214_ = lean_ctor_get(v___y_210_, 0);
v_env_215_ = lean_ctor_get(v___x_213_, 0);
lean_inc_ref(v_env_215_);
lean_dec(v___x_213_);
v_options_216_ = lean_ctor_get(v_toCold_214_, 2);
v___x_217_ = 0;
v_env_218_ = l_Lean_Environment_setRecordingDeps(v_env_215_, v___x_217_);
v___x_219_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2);
v___x_220_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_216_);
v___x_221_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_221_, 0, v_env_218_);
lean_ctor_set(v___x_221_, 1, v___x_219_);
lean_ctor_set(v___x_221_, 2, v___x_220_);
lean_ctor_set(v___x_221_, 3, v_options_216_);
v___x_222_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v_msgData_209_);
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(v_msgData_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(lean_object* v_ref_230_, lean_object* v_msgData_231_, uint8_t v_severity_232_, uint8_t v_isSilent_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___y_238_; lean_object* v___y_239_; uint8_t v___y_240_; lean_object* v___y_241_; uint8_t v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v_toCold_245_; lean_object* v___y_246_; lean_object* v___y_275_; lean_object* v___y_276_; uint8_t v___y_277_; uint8_t v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; uint8_t v___y_281_; lean_object* v___y_282_; uint8_t v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; uint8_t v___y_305_; lean_object* v___y_306_; uint8_t v___y_307_; lean_object* v___y_308_; uint8_t v___y_312_; uint8_t v___y_313_; uint8_t v___y_314_; uint8_t v___x_325_; uint8_t v___y_327_; uint8_t v___y_328_; uint8_t v___y_329_; uint8_t v___y_331_; uint8_t v___x_339_; 
v___x_325_ = 2;
v___x_339_ = l_Lean_instBEqMessageSeverity_beq(v_severity_232_, v___x_325_);
if (v___x_339_ == 0)
{
v___y_331_ = v___x_339_;
goto v___jp_330_;
}
else
{
uint8_t v___x_340_; 
lean_inc_ref(v_msgData_231_);
v___x_340_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_231_);
v___y_331_ = v___x_340_;
goto v___jp_330_;
}
v___jp_237_:
{
lean_object* v_currNamespace_247_; lean_object* v_openDecls_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v_env_253_; lean_object* v_nextMacroScope_254_; lean_object* v_ngen_255_; lean_object* v_auxDeclNGen_256_; lean_object* v_traceState_257_; lean_object* v_cache_258_; lean_object* v_recordedDeps_259_; lean_object* v_messages_260_; lean_object* v_infoState_261_; lean_object* v_snapshotTasks_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_273_; 
v_currNamespace_247_ = lean_ctor_get(v_toCold_245_, 4);
v_openDecls_248_ = lean_ctor_get(v_toCold_245_, 5);
lean_inc(v_openDecls_248_);
lean_inc(v_currNamespace_247_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v_currNamespace_247_);
lean_ctor_set(v___x_249_, 1, v_openDecls_248_);
v___x_250_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___y_244_);
lean_inc_ref(v___y_239_);
lean_inc_ref(v___y_238_);
v___x_251_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_251_, 0, v___y_238_);
lean_ctor_set(v___x_251_, 1, v___y_241_);
lean_ctor_set(v___x_251_, 2, v___y_243_);
lean_ctor_set(v___x_251_, 3, v___y_239_);
lean_ctor_set(v___x_251_, 4, v___x_250_);
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*5, v___y_242_);
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*5 + 1, v___y_240_);
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*5 + 2, v_isSilent_233_);
v___x_252_ = lean_st_ref_take(v___y_246_);
v_env_253_ = lean_ctor_get(v___x_252_, 0);
v_nextMacroScope_254_ = lean_ctor_get(v___x_252_, 1);
v_ngen_255_ = lean_ctor_get(v___x_252_, 2);
v_auxDeclNGen_256_ = lean_ctor_get(v___x_252_, 3);
v_traceState_257_ = lean_ctor_get(v___x_252_, 4);
v_cache_258_ = lean_ctor_get(v___x_252_, 5);
v_recordedDeps_259_ = lean_ctor_get(v___x_252_, 6);
v_messages_260_ = lean_ctor_get(v___x_252_, 7);
v_infoState_261_ = lean_ctor_get(v___x_252_, 8);
v_snapshotTasks_262_ = lean_ctor_get(v___x_252_, 9);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_273_ == 0)
{
v___x_264_ = v___x_252_;
v_isShared_265_ = v_isSharedCheck_273_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_snapshotTasks_262_);
lean_inc(v_infoState_261_);
lean_inc(v_messages_260_);
lean_inc(v_recordedDeps_259_);
lean_inc(v_cache_258_);
lean_inc(v_traceState_257_);
lean_inc(v_auxDeclNGen_256_);
lean_inc(v_ngen_255_);
lean_inc(v_nextMacroScope_254_);
lean_inc(v_env_253_);
lean_dec(v___x_252_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_273_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_266_ = lean_box(0);
v___x_267_ = l_Lean_MessageLog_add(v___x_251_, v_messages_260_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 7, v___x_267_);
v___x_269_ = v___x_264_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_env_253_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_nextMacroScope_254_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_ngen_255_);
lean_ctor_set(v_reuseFailAlloc_272_, 3, v_auxDeclNGen_256_);
lean_ctor_set(v_reuseFailAlloc_272_, 4, v_traceState_257_);
lean_ctor_set(v_reuseFailAlloc_272_, 5, v_cache_258_);
lean_ctor_set(v_reuseFailAlloc_272_, 6, v_recordedDeps_259_);
lean_ctor_set(v_reuseFailAlloc_272_, 7, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_272_, 8, v_infoState_261_);
lean_ctor_set(v_reuseFailAlloc_272_, 9, v_snapshotTasks_262_);
v___x_269_ = v_reuseFailAlloc_272_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_st_ref_put(v___y_246_, v___x_269_);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_266_);
return v___x_271_;
}
}
}
v___jp_274_:
{
lean_object* v_fileName_283_; lean_object* v_fileMap_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_300_; 
v_fileName_283_ = lean_ctor_get(v___y_279_, 0);
v_fileMap_284_ = lean_ctor_get(v___y_279_, 1);
v___x_285_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_231_);
v___x_286_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(v___x_285_, v___y_234_, v___y_235_);
v_a_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_300_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_300_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_300_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
lean_inc_ref_n(v_fileMap_284_, 2);
v___x_291_ = l_Lean_FileMap_toPosition(v_fileMap_284_, v___y_280_);
lean_dec(v___y_280_);
v___x_292_ = l_Lean_FileMap_toPosition(v_fileMap_284_, v___y_282_);
lean_dec(v___y_282_);
v___x_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
v___x_294_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___closed__0));
if (v___y_277_ == 0)
{
lean_del_object(v___x_289_);
lean_dec_ref(v___y_275_);
v___y_238_ = v_fileName_283_;
v___y_239_ = v___x_294_;
v___y_240_ = v___y_278_;
v___y_241_ = v___x_291_;
v___y_242_ = v___y_281_;
v___y_243_ = v___x_293_;
v___y_244_ = v_a_287_;
v_toCold_245_ = v___y_276_;
v___y_246_ = v___y_235_;
goto v___jp_237_;
}
else
{
uint8_t v___x_295_; 
lean_inc(v_a_287_);
v___x_295_ = l_Lean_MessageData_hasTag(v___y_275_, v_a_287_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_298_; 
lean_dec_ref_known(v___x_293_, 1);
lean_dec_ref(v___x_291_);
lean_dec(v_a_287_);
v___x_296_ = lean_box(0);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_296_);
v___x_298_ = v___x_289_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
else
{
lean_del_object(v___x_289_);
v___y_238_ = v_fileName_283_;
v___y_239_ = v___x_294_;
v___y_240_ = v___y_278_;
v___y_241_ = v___x_291_;
v___y_242_ = v___y_281_;
v___y_243_ = v___x_293_;
v___y_244_ = v_a_287_;
v_toCold_245_ = v___y_276_;
v___y_246_ = v___y_235_;
goto v___jp_237_;
}
}
}
}
v___jp_301_:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Syntax_getTailPos_x3f(v___y_306_, v___y_307_);
lean_dec(v___y_306_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_inc(v___y_308_);
v___y_275_ = v___y_303_;
v___y_276_ = v___y_304_;
v___y_277_ = v___y_302_;
v___y_278_ = v___y_305_;
v___y_279_ = v___y_304_;
v___y_280_ = v___y_308_;
v___y_281_ = v___y_307_;
v___y_282_ = v___y_308_;
goto v___jp_274_;
}
else
{
lean_object* v_val_310_; 
v_val_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_val_310_);
lean_dec_ref_known(v___x_309_, 1);
v___y_275_ = v___y_303_;
v___y_276_ = v___y_304_;
v___y_277_ = v___y_302_;
v___y_278_ = v___y_305_;
v___y_279_ = v___y_304_;
v___y_280_ = v___y_308_;
v___y_281_ = v___y_307_;
v___y_282_ = v_val_310_;
goto v___jp_274_;
}
}
v___jp_311_:
{
lean_object* v_toCold_315_; lean_object* v_ref_316_; uint8_t v_suppressElabErrors_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___f_320_; lean_object* v_ref_321_; lean_object* v___x_322_; 
v_toCold_315_ = lean_ctor_get(v___y_234_, 0);
v_ref_316_ = lean_ctor_get(v___y_234_, 2);
v_suppressElabErrors_317_ = lean_ctor_get_uint8(v___y_234_, sizeof(void*)*3 + 2);
v___x_318_ = lean_box(v_suppressElabErrors_317_);
v___x_319_ = lean_box(v___y_312_);
v___f_320_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_320_, 0, v___x_318_);
lean_closure_set(v___f_320_, 1, v___x_319_);
v_ref_321_ = l_Lean_replaceRef(v_ref_230_, v_ref_316_);
v___x_322_ = l_Lean_Syntax_getPos_x3f(v_ref_321_, v___y_313_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v___x_323_; 
v___x_323_ = lean_unsigned_to_nat(0u);
v___y_302_ = v_suppressElabErrors_317_;
v___y_303_ = v___f_320_;
v___y_304_ = v_toCold_315_;
v___y_305_ = v___y_314_;
v___y_306_ = v_ref_321_;
v___y_307_ = v___y_313_;
v___y_308_ = v___x_323_;
goto v___jp_301_;
}
else
{
lean_object* v_val_324_; 
v_val_324_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_val_324_);
lean_dec_ref_known(v___x_322_, 1);
v___y_302_ = v_suppressElabErrors_317_;
v___y_303_ = v___f_320_;
v___y_304_ = v_toCold_315_;
v___y_305_ = v___y_314_;
v___y_306_ = v_ref_321_;
v___y_307_ = v___y_313_;
v___y_308_ = v_val_324_;
goto v___jp_301_;
}
}
v___jp_326_:
{
if (v___y_329_ == 0)
{
v___y_312_ = v___y_327_;
v___y_313_ = v___y_328_;
v___y_314_ = v_severity_232_;
goto v___jp_311_;
}
else
{
v___y_312_ = v___y_327_;
v___y_313_ = v___y_328_;
v___y_314_ = v___x_325_;
goto v___jp_311_;
}
}
v___jp_330_:
{
if (v___y_331_ == 0)
{
uint8_t v___x_332_; uint8_t v___x_333_; 
v___x_332_ = 1;
v___x_333_ = l_Lean_instBEqMessageSeverity_beq(v_severity_232_, v___x_332_);
if (v___x_333_ == 0)
{
v___y_327_ = v___y_331_;
v___y_328_ = v___y_331_;
v___y_329_ = v___x_333_;
goto v___jp_326_;
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_334_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_234_);
v___x_335_ = l_Lean_warningAsError;
v___x_336_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(v___x_334_, v___x_335_);
lean_dec_ref(v___x_334_);
v___y_327_ = v___y_331_;
v___y_328_ = v___y_331_;
v___y_329_ = v___x_336_;
goto v___jp_326_;
}
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec_ref(v_msgData_231_);
v___x_337_ = lean_box(0);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___boxed(lean_object* v_ref_341_, lean_object* v_msgData_342_, lean_object* v_severity_343_, lean_object* v_isSilent_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
uint8_t v_severity_boxed_348_; uint8_t v_isSilent_boxed_349_; lean_object* v_res_350_; 
v_severity_boxed_348_ = lean_unbox(v_severity_343_);
v_isSilent_boxed_349_ = lean_unbox(v_isSilent_344_);
v_res_350_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(v_ref_341_, v_msgData_342_, v_severity_boxed_348_, v_isSilent_boxed_349_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v_ref_341_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(lean_object* v_ref_351_, lean_object* v_msgData_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
uint8_t v___x_356_; uint8_t v___x_357_; lean_object* v___x_358_; 
v___x_356_ = 0;
v___x_357_ = 0;
v___x_358_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(v_ref_351_, v_msgData_352_, v___x_356_, v___x_357_, v___y_353_, v___y_354_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0___boxed(lean_object* v_ref_359_, lean_object* v_msgData_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(v_ref_359_, v_msgData_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v_ref_359_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportOutOfHeartbeats(lean_object* v_tac_367_, lean_object* v_stx_368_, lean_object* v_threshold_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v___x_373_; lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_391_; 
v___x_373_ = l_Lean_heartbeatsPercent___redArg(v_a_370_);
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_391_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_391_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_391_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
uint8_t v___x_378_; 
v___x_378_ = lean_nat_dec_le(v_threshold_369_, v_a_374_);
lean_dec(v_a_374_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_381_; 
lean_dec(v_tac_367_);
v___x_379_ = lean_box(0);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_379_);
v___x_381_ = v___x_376_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
lean_del_object(v___x_376_);
v___x_383_ = ((lean_object*)(l_Lean_reportOutOfHeartbeats___closed__0));
v___x_384_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_tac_367_, v___x_378_);
v___x_385_ = lean_string_append(v___x_383_, v___x_384_);
lean_dec_ref(v___x_384_);
v___x_386_ = ((lean_object*)(l_Lean_reportOutOfHeartbeats___closed__1));
v___x_387_ = lean_string_append(v___x_385_, v___x_386_);
v___x_388_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
v___x_389_ = l_Lean_MessageData_ofFormat(v___x_388_);
v___x_390_ = l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(v_stx_368_, v___x_389_, v_a_370_, v_a_371_);
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportOutOfHeartbeats___boxed(lean_object* v_tac_392_, lean_object* v_stx_393_, lean_object* v_threshold_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_reportOutOfHeartbeats(v_tac_392_, v_stx_393_, v_threshold_394_, v_a_395_, v_a_396_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_threshold_394_);
lean_dec(v_stx_393_);
return v_res_398_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Heartbeats(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
