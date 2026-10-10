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
lean_object* l_Lean_getMaxHeartbeats___redArg(lean_object* v_a_44_){
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
LEAN_EXPORT void l_Lean_getMaxHeartbeats___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_44_ = stack[0].m_obj;
lean_object* v_res_49_;
v_res_49_ = l_Lean_getMaxHeartbeats___redArg(v_a_44_);
stack->m_obj
 = v_res_49_;
}
LEAN_EXPORT lean_object* l_Lean_getMaxHeartbeats___redArg___boxed(lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_getMaxHeartbeats___redArg(v_a_50_);
lean_dec_ref(v_a_50_);
return v_res_52_;
}
}
lean_object* l_Lean_getMaxHeartbeats(lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_getMaxHeartbeats___redArg(v_a_53_);
return v___x_56_;
}
}
LEAN_EXPORT void l_Lean_getMaxHeartbeats_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_53_ = stack[0].m_obj;
lean_object* v_a_54_ = stack[1].m_obj;
lean_object* v_res_57_;
v_res_57_ = l_Lean_getMaxHeartbeats(v_a_53_, v_a_54_);
stack->m_obj
 = v_res_57_;
}
LEAN_EXPORT lean_object* l_Lean_getMaxHeartbeats___boxed(lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_getMaxHeartbeats(v_a_58_, v_a_59_);
lean_dec(v_a_59_);
lean_dec_ref(v_a_58_);
return v_res_61_;
}
}
lean_object* l_Lean_getInitHeartbeats___redArg(lean_object* v_a_62_){
_start:
{
lean_object* v_toCold_64_; lean_object* v_initHeartbeats_65_; lean_object* v___x_66_; 
v_toCold_64_ = lean_ctor_get(v_a_62_, 0);
v_initHeartbeats_65_ = lean_ctor_get(v_toCold_64_, 6);
lean_inc(v_initHeartbeats_65_);
v___x_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_66_, 0, v_initHeartbeats_65_);
return v___x_66_;
}
}
LEAN_EXPORT void l_Lean_getInitHeartbeats___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_62_ = stack[0].m_obj;
lean_object* v_res_67_;
v_res_67_ = l_Lean_getInitHeartbeats___redArg(v_a_62_);
stack->m_obj
 = v_res_67_;
}
LEAN_EXPORT lean_object* l_Lean_getInitHeartbeats___redArg___boxed(lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_getInitHeartbeats___redArg(v_a_68_);
lean_dec_ref(v_a_68_);
return v_res_70_;
}
}
lean_object* l_Lean_getInitHeartbeats(lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_getInitHeartbeats___redArg(v_a_71_);
return v___x_74_;
}
}
LEAN_EXPORT void l_Lean_getInitHeartbeats_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_71_ = stack[0].m_obj;
lean_object* v_a_72_ = stack[1].m_obj;
lean_object* v_res_75_;
v_res_75_ = l_Lean_getInitHeartbeats(v_a_71_, v_a_72_);
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Lean_getInitHeartbeats___boxed(lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_getInitHeartbeats(v_a_76_, v_a_77_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
return v_res_79_;
}
}
lean_object* l_Lean_getRemainingHeartbeats___redArg(lean_object* v_a_80_){
_start:
{
lean_object* v___x_82_; lean_object* v_a_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_95_; 
v___x_82_ = l_Lean_getMaxHeartbeats___redArg(v_a_80_);
v_a_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_a_83_);
lean_dec_ref(v___x_82_);
v___x_84_ = lean_io_get_num_heartbeats();
v___x_85_ = l_Lean_getInitHeartbeats___redArg(v_a_80_);
v_a_86_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_95_ == 0)
{
v___x_88_ = v___x_85_;
v_isShared_89_ = v_isSharedCheck_95_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_95_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_90_ = lean_nat_sub(v___x_84_, v_a_86_);
lean_dec(v_a_86_);
lean_dec(v___x_84_);
v___x_91_ = lean_nat_sub(v_a_83_, v___x_90_);
lean_dec(v___x_90_);
lean_dec(v_a_83_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v___x_91_);
v___x_93_ = v___x_88_;
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
}
}
LEAN_EXPORT void l_Lean_getRemainingHeartbeats___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_80_ = stack[0].m_obj;
lean_object* v_res_96_;
v_res_96_ = l_Lean_getRemainingHeartbeats___redArg(v_a_80_);
stack->m_obj
 = v_res_96_;
}
LEAN_EXPORT lean_object* l_Lean_getRemainingHeartbeats___redArg___boxed(lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_getRemainingHeartbeats___redArg(v_a_97_);
lean_dec_ref(v_a_97_);
return v_res_99_;
}
}
lean_object* l_Lean_getRemainingHeartbeats(lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_getRemainingHeartbeats___redArg(v_a_100_);
return v___x_103_;
}
}
LEAN_EXPORT void l_Lean_getRemainingHeartbeats_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_100_ = stack[0].m_obj;
lean_object* v_a_101_ = stack[1].m_obj;
lean_object* v_res_104_;
v_res_104_ = l_Lean_getRemainingHeartbeats(v_a_100_, v_a_101_);
stack->m_obj
 = v_res_104_;
}
LEAN_EXPORT lean_object* l_Lean_getRemainingHeartbeats___boxed(lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_getRemainingHeartbeats(v_a_105_, v_a_106_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
return v_res_108_;
}
}
lean_object* l_Lean_heartbeatsPercent___redArg(lean_object* v_a_109_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v_a_113_; lean_object* v___x_114_; lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_126_; 
v___x_111_ = lean_io_get_num_heartbeats();
v___x_112_ = l_Lean_getInitHeartbeats___redArg(v_a_109_);
v_a_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_a_113_);
lean_dec_ref(v___x_112_);
v___x_114_ = l_Lean_getMaxHeartbeats___redArg(v_a_109_);
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_126_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_126_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_126_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_119_ = lean_nat_sub(v___x_111_, v_a_113_);
lean_dec(v_a_113_);
lean_dec(v___x_111_);
v___x_120_ = lean_unsigned_to_nat(100u);
v___x_121_ = lean_nat_mul(v___x_119_, v___x_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_nat_div(v___x_121_, v_a_115_);
lean_dec(v_a_115_);
lean_dec(v___x_121_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_122_);
v___x_124_ = v___x_117_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
LEAN_EXPORT void l_Lean_heartbeatsPercent___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_109_ = stack[0].m_obj;
lean_object* v_res_127_;
v_res_127_ = l_Lean_heartbeatsPercent___redArg(v_a_109_);
stack->m_obj
 = v_res_127_;
}
LEAN_EXPORT lean_object* l_Lean_heartbeatsPercent___redArg___boxed(lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_heartbeatsPercent___redArg(v_a_128_);
lean_dec_ref(v_a_128_);
return v_res_130_;
}
}
lean_object* l_Lean_heartbeatsPercent(lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_heartbeatsPercent___redArg(v_a_131_);
return v___x_134_;
}
}
LEAN_EXPORT void l_Lean_heartbeatsPercent_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_131_ = stack[0].m_obj;
lean_object* v_a_132_ = stack[1].m_obj;
lean_object* v_res_135_;
v_res_135_ = l_Lean_heartbeatsPercent(v_a_131_, v_a_132_);
stack->m_obj
 = v_res_135_;
}
LEAN_EXPORT lean_object* l_Lean_heartbeatsPercent___boxed(lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_heartbeatsPercent(v_a_136_, v_a_137_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
return v_res_139_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_148_, uint8_t v___y_149_, lean_object* v_x_150_){
_start:
{
if (lean_obj_tag(v_x_150_) == 1)
{
lean_object* v_pre_151_; 
v_pre_151_ = lean_ctor_get(v_x_150_, 0);
switch(lean_obj_tag(v_pre_151_))
{
case 1:
{
lean_object* v_pre_152_; 
v_pre_152_ = lean_ctor_get(v_pre_151_, 0);
switch(lean_obj_tag(v_pre_152_))
{
case 0:
{
lean_object* v_str_153_; lean_object* v_str_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v_str_153_ = lean_ctor_get(v_x_150_, 1);
v_str_154_ = lean_ctor_get(v_pre_151_, 1);
v___x_155_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__0));
v___x_156_ = lean_string_dec_eq(v_str_154_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__1));
v___x_158_ = lean_string_dec_eq(v_str_154_, v___x_157_);
if (v___x_158_ == 0)
{
return v___x_158_;
}
else
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__2));
v___x_160_ = lean_string_dec_eq(v_str_153_, v___x_159_);
if (v___x_160_ == 0)
{
return v___x_160_;
}
else
{
return v_suppressElabErrors_148_;
}
}
}
else
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__3));
v___x_162_ = lean_string_dec_eq(v_str_153_, v___x_161_);
if (v___x_162_ == 0)
{
return v___x_162_;
}
else
{
return v_suppressElabErrors_148_;
}
}
}
case 1:
{
lean_object* v_pre_163_; 
v_pre_163_ = lean_ctor_get(v_pre_152_, 0);
if (lean_obj_tag(v_pre_163_) == 0)
{
lean_object* v_str_164_; lean_object* v_str_165_; lean_object* v_str_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_str_164_ = lean_ctor_get(v_x_150_, 1);
v_str_165_ = lean_ctor_get(v_pre_151_, 1);
v_str_166_ = lean_ctor_get(v_pre_152_, 1);
v___x_167_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__4));
v___x_168_ = lean_string_dec_eq(v_str_166_, v___x_167_);
if (v___x_168_ == 0)
{
return v___x_168_;
}
else
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__5));
v___x_170_ = lean_string_dec_eq(v_str_165_, v___x_169_);
if (v___x_170_ == 0)
{
return v___x_170_;
}
else
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__6));
v___x_172_ = lean_string_dec_eq(v_str_164_, v___x_171_);
if (v___x_172_ == 0)
{
return v___x_172_;
}
else
{
return v_suppressElabErrors_148_;
}
}
}
}
else
{
return v___y_149_;
}
}
default: 
{
return v___y_149_;
}
}
}
case 0:
{
lean_object* v_str_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v_str_173_ = lean_ctor_get(v_x_150_, 1);
v___x_174_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__7));
v___x_175_ = lean_string_dec_eq(v_str_173_, v___x_174_);
if (v___x_175_ == 0)
{
return v___x_175_;
}
else
{
return v_suppressElabErrors_148_;
}
}
default: 
{
return v___y_149_;
}
}
}
else
{
return v___y_149_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_148_ = stack[0].m_num;
uint8_t v___y_149_ = stack[1].m_num;
lean_object* v_x_150_ = stack[2].m_obj;
uint8_t v_res_176_;
v_res_176_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0(v_suppressElabErrors_148_, v___y_149_, v_x_150_);
stack->m_num = v_res_176_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_177_, lean_object* v___y_178_, lean_object* v_x_179_){
_start:
{
uint8_t v_suppressElabErrors_boxed_180_; uint8_t v___y_2759__boxed_181_; uint8_t v_res_182_; lean_object* v_r_183_; 
v_suppressElabErrors_boxed_180_ = lean_unbox(v_suppressElabErrors_177_);
v___y_2759__boxed_181_ = lean_unbox(v___y_178_);
v_res_182_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_180_, v___y_2759__boxed_181_, v_x_179_);
lean_dec(v_x_179_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(lean_object* v_opts_184_, lean_object* v_opt_185_){
_start:
{
lean_object* v_name_186_; lean_object* v_defValue_187_; lean_object* v_map_188_; lean_object* v___x_189_; 
v_name_186_ = lean_ctor_get(v_opt_185_, 0);
v_defValue_187_ = lean_ctor_get(v_opt_185_, 1);
v_map_188_ = lean_ctor_get(v_opts_184_, 0);
v___x_189_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_188_, v_name_186_);
if (lean_obj_tag(v___x_189_) == 0)
{
uint8_t v___x_190_; 
v___x_190_ = lean_unbox(v_defValue_187_);
return v___x_190_;
}
else
{
lean_object* v_val_191_; 
v_val_191_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_val_191_);
lean_dec_ref_known(v___x_189_, 1);
if (lean_obj_tag(v_val_191_) == 1)
{
uint8_t v_v_192_; 
v_v_192_ = lean_ctor_get_uint8(v_val_191_, 0);
lean_dec_ref_known(v_val_191_, 0);
return v_v_192_;
}
else
{
uint8_t v___x_193_; 
lean_dec(v_val_191_);
v___x_193_ = lean_unbox(v_defValue_187_);
return v___x_193_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_184_ = stack[0].m_obj;
lean_object* v_opt_185_ = stack[1].m_obj;
uint8_t v_res_194_;
v_res_194_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(v_opts_184_, v_opt_185_);
stack->m_num = v_res_194_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2___boxed(lean_object* v_opts_195_, lean_object* v_opt_196_){
_start:
{
uint8_t v_res_197_; lean_object* v_r_198_; 
v_res_197_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(v_opts_195_, v_opt_196_);
lean_dec_ref(v_opt_196_);
lean_dec_ref(v_opts_195_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_199_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0);
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_202_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_203_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
lean_ctor_set(v___x_205_, 2, v___x_204_);
lean_ctor_set(v___x_205_, 3, v___x_204_);
lean_ctor_set(v___x_205_, 4, v___x_203_);
lean_ctor_set(v___x_205_, 5, v___x_203_);
lean_ctor_set(v___x_205_, 6, v___x_203_);
lean_ctor_set(v___x_205_, 7, v___x_203_);
lean_ctor_set(v___x_205_, 8, v___x_203_);
lean_ctor_set(v___x_205_, 9, v___x_203_);
lean_ctor_set(v___x_205_, 10, v___x_203_);
lean_ctor_set(v___x_205_, 11, v___x_202_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lean_unsigned_to_nat(32u);
v___x_207_ = lean_mk_empty_array_with_capacity(v___x_206_);
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_209_ = ((size_t)5ULL);
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = lean_unsigned_to_nat(32u);
v___x_212_ = lean_mk_empty_array_with_capacity(v___x_211_);
v___x_213_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3);
v___x_214_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v___x_212_);
lean_ctor_set(v___x_214_, 2, v___x_210_);
lean_ctor_set(v___x_214_, 3, v___x_210_);
lean_ctor_set_usize(v___x_214_, 4, v___x_209_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_215_ = lean_box(1);
v___x_216_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4);
v___x_217_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1);
v___x_218_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v___x_216_);
lean_ctor_set(v___x_218_, 2, v___x_215_);
return v___x_218_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(lean_object* v_msgData_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___x_223_; lean_object* v_toCold_224_; lean_object* v_env_225_; lean_object* v_options_226_; uint8_t v___x_227_; lean_object* v_env_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_223_ = lean_st_ref_get(v___y_221_);
v_toCold_224_ = lean_ctor_get(v___y_220_, 0);
v_env_225_ = lean_ctor_get(v___x_223_, 0);
lean_inc_ref(v_env_225_);
lean_dec(v___x_223_);
v_options_226_ = lean_ctor_get(v_toCold_224_, 2);
v___x_227_ = 0;
v_env_228_ = l_Lean_Environment_setRecordingDeps(v_env_225_, v___x_227_);
v___x_229_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2);
v___x_230_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_226_);
v___x_231_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_231_, 0, v_env_228_);
lean_ctor_set(v___x_231_, 1, v___x_229_);
lean_ctor_set(v___x_231_, 2, v___x_230_);
lean_ctor_set(v___x_231_, 3, v_options_226_);
v___x_232_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v_msgData_219_);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_219_ = stack[0].m_obj;
lean_object* v___y_220_ = stack[1].m_obj;
lean_object* v___y_221_ = stack[2].m_obj;
lean_object* v_res_234_;
v_res_234_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(v_msgData_219_, v___y_220_, v___y_221_);
stack->m_obj
 = v_res_234_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(v_msgData_235_, v___y_236_, v___y_237_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
return v_res_239_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(lean_object* v_ref_241_, lean_object* v_msgData_242_, uint8_t v_severity_243_, uint8_t v_isSilent_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v___y_249_; lean_object* v___y_250_; uint8_t v___y_251_; lean_object* v___y_252_; uint8_t v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v_toCold_256_; lean_object* v___y_257_; lean_object* v___y_286_; lean_object* v___y_287_; uint8_t v___y_288_; uint8_t v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; uint8_t v___y_292_; lean_object* v___y_293_; uint8_t v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; uint8_t v___y_316_; lean_object* v___y_317_; uint8_t v___y_318_; lean_object* v___y_319_; uint8_t v___y_323_; uint8_t v___y_324_; uint8_t v___y_325_; uint8_t v___x_336_; uint8_t v___y_338_; uint8_t v___y_339_; uint8_t v___y_340_; uint8_t v___y_342_; uint8_t v___x_350_; 
v___x_336_ = 2;
v___x_350_ = l_Lean_instBEqMessageSeverity_beq(v_severity_243_, v___x_336_);
if (v___x_350_ == 0)
{
v___y_342_ = v___x_350_;
goto v___jp_341_;
}
else
{
uint8_t v___x_351_; 
lean_inc_ref(v_msgData_242_);
v___x_351_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_242_);
v___y_342_ = v___x_351_;
goto v___jp_341_;
}
v___jp_248_:
{
lean_object* v_currNamespace_258_; lean_object* v_openDecls_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v_env_264_; lean_object* v_nextMacroScope_265_; lean_object* v_ngen_266_; lean_object* v_auxDeclNGen_267_; lean_object* v_traceState_268_; lean_object* v_cache_269_; lean_object* v_recordedDeps_270_; lean_object* v_messages_271_; lean_object* v_infoState_272_; lean_object* v_snapshotTasks_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_284_; 
v_currNamespace_258_ = lean_ctor_get(v_toCold_256_, 4);
v_openDecls_259_ = lean_ctor_get(v_toCold_256_, 5);
lean_inc(v_openDecls_259_);
lean_inc(v_currNamespace_258_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v_currNamespace_258_);
lean_ctor_set(v___x_260_, 1, v_openDecls_259_);
v___x_261_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___y_255_);
lean_inc_ref(v___y_250_);
lean_inc_ref(v___y_249_);
v___x_262_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_262_, 0, v___y_249_);
lean_ctor_set(v___x_262_, 1, v___y_252_);
lean_ctor_set(v___x_262_, 2, v___y_254_);
lean_ctor_set(v___x_262_, 3, v___y_250_);
lean_ctor_set(v___x_262_, 4, v___x_261_);
lean_ctor_set_uint8(v___x_262_, sizeof(void*)*5, v___y_253_);
lean_ctor_set_uint8(v___x_262_, sizeof(void*)*5 + 1, v___y_251_);
lean_ctor_set_uint8(v___x_262_, sizeof(void*)*5 + 2, v_isSilent_244_);
v___x_263_ = lean_st_ref_take(v___y_257_);
v_env_264_ = lean_ctor_get(v___x_263_, 0);
v_nextMacroScope_265_ = lean_ctor_get(v___x_263_, 1);
v_ngen_266_ = lean_ctor_get(v___x_263_, 2);
v_auxDeclNGen_267_ = lean_ctor_get(v___x_263_, 3);
v_traceState_268_ = lean_ctor_get(v___x_263_, 4);
v_cache_269_ = lean_ctor_get(v___x_263_, 5);
v_recordedDeps_270_ = lean_ctor_get(v___x_263_, 6);
v_messages_271_ = lean_ctor_get(v___x_263_, 7);
v_infoState_272_ = lean_ctor_get(v___x_263_, 8);
v_snapshotTasks_273_ = lean_ctor_get(v___x_263_, 9);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_284_ == 0)
{
v___x_275_ = v___x_263_;
v_isShared_276_ = v_isSharedCheck_284_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_snapshotTasks_273_);
lean_inc(v_infoState_272_);
lean_inc(v_messages_271_);
lean_inc(v_recordedDeps_270_);
lean_inc(v_cache_269_);
lean_inc(v_traceState_268_);
lean_inc(v_auxDeclNGen_267_);
lean_inc(v_ngen_266_);
lean_inc(v_nextMacroScope_265_);
lean_inc(v_env_264_);
lean_dec(v___x_263_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_284_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_277_ = lean_box(0);
v___x_278_ = l_Lean_MessageLog_add(v___x_262_, v_messages_271_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 7, v___x_278_);
v___x_280_ = v___x_275_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_env_264_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_nextMacroScope_265_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_ngen_266_);
lean_ctor_set(v_reuseFailAlloc_283_, 3, v_auxDeclNGen_267_);
lean_ctor_set(v_reuseFailAlloc_283_, 4, v_traceState_268_);
lean_ctor_set(v_reuseFailAlloc_283_, 5, v_cache_269_);
lean_ctor_set(v_reuseFailAlloc_283_, 6, v_recordedDeps_270_);
lean_ctor_set(v_reuseFailAlloc_283_, 7, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_283_, 8, v_infoState_272_);
lean_ctor_set(v_reuseFailAlloc_283_, 9, v_snapshotTasks_273_);
v___x_280_ = v_reuseFailAlloc_283_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_st_ref_put(v___y_257_, v___x_280_);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_277_);
return v___x_282_;
}
}
}
v___jp_285_:
{
lean_object* v_fileName_294_; lean_object* v_fileMap_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_311_; 
v_fileName_294_ = lean_ctor_get(v___y_290_, 0);
v_fileMap_295_ = lean_ctor_get(v___y_290_, 1);
v___x_296_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_242_);
v___x_297_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(v___x_296_, v___y_245_, v___y_246_);
v_a_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_311_ == 0)
{
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_311_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_311_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
lean_inc_ref_n(v_fileMap_295_, 2);
v___x_302_ = l_Lean_FileMap_toPosition(v_fileMap_295_, v___y_291_);
lean_dec(v___y_291_);
v___x_303_ = l_Lean_FileMap_toPosition(v_fileMap_295_, v___y_293_);
lean_dec(v___y_293_);
v___x_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
v___x_305_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___closed__0));
if (v___y_288_ == 0)
{
lean_del_object(v___x_300_);
lean_dec_ref(v___y_286_);
v___y_249_ = v_fileName_294_;
v___y_250_ = v___x_305_;
v___y_251_ = v___y_289_;
v___y_252_ = v___x_302_;
v___y_253_ = v___y_292_;
v___y_254_ = v___x_304_;
v___y_255_ = v_a_298_;
v_toCold_256_ = v___y_287_;
v___y_257_ = v___y_246_;
goto v___jp_248_;
}
else
{
uint8_t v___x_306_; 
lean_inc(v_a_298_);
v___x_306_ = l_Lean_MessageData_hasTag(v___y_286_, v_a_298_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_309_; 
lean_dec_ref_known(v___x_304_, 1);
lean_dec_ref(v___x_302_);
lean_dec(v_a_298_);
v___x_307_ = lean_box(0);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_307_);
v___x_309_ = v___x_300_;
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
lean_del_object(v___x_300_);
v___y_249_ = v_fileName_294_;
v___y_250_ = v___x_305_;
v___y_251_ = v___y_289_;
v___y_252_ = v___x_302_;
v___y_253_ = v___y_292_;
v___y_254_ = v___x_304_;
v___y_255_ = v_a_298_;
v_toCold_256_ = v___y_287_;
v___y_257_ = v___y_246_;
goto v___jp_248_;
}
}
}
}
v___jp_312_:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Syntax_getTailPos_x3f(v___y_317_, v___y_318_);
lean_dec(v___y_317_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_inc(v___y_319_);
v___y_286_ = v___y_314_;
v___y_287_ = v___y_315_;
v___y_288_ = v___y_313_;
v___y_289_ = v___y_316_;
v___y_290_ = v___y_315_;
v___y_291_ = v___y_319_;
v___y_292_ = v___y_318_;
v___y_293_ = v___y_319_;
goto v___jp_285_;
}
else
{
lean_object* v_val_321_; 
v_val_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_val_321_);
lean_dec_ref_known(v___x_320_, 1);
v___y_286_ = v___y_314_;
v___y_287_ = v___y_315_;
v___y_288_ = v___y_313_;
v___y_289_ = v___y_316_;
v___y_290_ = v___y_315_;
v___y_291_ = v___y_319_;
v___y_292_ = v___y_318_;
v___y_293_ = v_val_321_;
goto v___jp_285_;
}
}
v___jp_322_:
{
lean_object* v_toCold_326_; lean_object* v_ref_327_; uint8_t v_suppressElabErrors_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___f_331_; lean_object* v_ref_332_; lean_object* v___x_333_; 
v_toCold_326_ = lean_ctor_get(v___y_245_, 0);
v_ref_327_ = lean_ctor_get(v___y_245_, 2);
v_suppressElabErrors_328_ = lean_ctor_get_uint8(v___y_245_, sizeof(void*)*3 + 2);
v___x_329_ = lean_box(v_suppressElabErrors_328_);
v___x_330_ = lean_box(v___y_323_);
v___f_331_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_331_, 0, v___x_329_);
lean_closure_set(v___f_331_, 1, v___x_330_);
v_ref_332_ = l_Lean_replaceRef(v_ref_241_, v_ref_327_);
v___x_333_ = l_Lean_Syntax_getPos_x3f(v_ref_332_, v___y_324_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v___x_334_; 
v___x_334_ = lean_unsigned_to_nat(0u);
v___y_313_ = v_suppressElabErrors_328_;
v___y_314_ = v___f_331_;
v___y_315_ = v_toCold_326_;
v___y_316_ = v___y_325_;
v___y_317_ = v_ref_332_;
v___y_318_ = v___y_324_;
v___y_319_ = v___x_334_;
goto v___jp_312_;
}
else
{
lean_object* v_val_335_; 
v_val_335_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_val_335_);
lean_dec_ref_known(v___x_333_, 1);
v___y_313_ = v_suppressElabErrors_328_;
v___y_314_ = v___f_331_;
v___y_315_ = v_toCold_326_;
v___y_316_ = v___y_325_;
v___y_317_ = v_ref_332_;
v___y_318_ = v___y_324_;
v___y_319_ = v_val_335_;
goto v___jp_312_;
}
}
v___jp_337_:
{
if (v___y_340_ == 0)
{
v___y_323_ = v___y_338_;
v___y_324_ = v___y_339_;
v___y_325_ = v_severity_243_;
goto v___jp_322_;
}
else
{
v___y_323_ = v___y_338_;
v___y_324_ = v___y_339_;
v___y_325_ = v___x_336_;
goto v___jp_322_;
}
}
v___jp_341_:
{
if (v___y_342_ == 0)
{
uint8_t v___x_343_; uint8_t v___x_344_; 
v___x_343_ = 1;
v___x_344_ = l_Lean_instBEqMessageSeverity_beq(v_severity_243_, v___x_343_);
if (v___x_344_ == 0)
{
v___y_338_ = v___y_342_;
v___y_339_ = v___y_342_;
v___y_340_ = v___x_344_;
goto v___jp_337_;
}
else
{
lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_345_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_245_);
v___x_346_ = l_Lean_warningAsError;
v___x_347_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(v___x_345_, v___x_346_);
lean_dec_ref(v___x_345_);
v___y_338_ = v___y_342_;
v___y_339_ = v___y_342_;
v___y_340_ = v___x_347_;
goto v___jp_337_;
}
}
else
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec_ref(v_msgData_242_);
v___x_348_ = lean_box(0);
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_241_ = stack[0].m_obj;
lean_object* v_msgData_242_ = stack[1].m_obj;
uint8_t v_severity_243_ = stack[2].m_num;
uint8_t v_isSilent_244_ = stack[3].m_num;
lean_object* v___y_245_ = stack[4].m_obj;
lean_object* v___y_246_ = stack[5].m_obj;
lean_object* v_res_352_;
v_res_352_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(v_ref_241_, v_msgData_242_, v_severity_243_, v_isSilent_244_, v___y_245_, v___y_246_);
stack->m_obj
 = v_res_352_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___boxed(lean_object* v_ref_353_, lean_object* v_msgData_354_, lean_object* v_severity_355_, lean_object* v_isSilent_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
uint8_t v_severity_boxed_360_; uint8_t v_isSilent_boxed_361_; lean_object* v_res_362_; 
v_severity_boxed_360_ = lean_unbox(v_severity_355_);
v_isSilent_boxed_361_ = lean_unbox(v_isSilent_356_);
v_res_362_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(v_ref_353_, v_msgData_354_, v_severity_boxed_360_, v_isSilent_boxed_361_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v_ref_353_);
return v_res_362_;
}
}
lean_object* l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(lean_object* v_ref_363_, lean_object* v_msgData_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
uint8_t v___x_368_; uint8_t v___x_369_; lean_object* v___x_370_; 
v___x_368_ = 0;
v___x_369_ = 0;
v___x_370_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(v_ref_363_, v_msgData_364_, v___x_368_, v___x_369_, v___y_365_, v___y_366_);
return v___x_370_;
}
}
LEAN_EXPORT void l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_363_ = stack[0].m_obj;
lean_object* v_msgData_364_ = stack[1].m_obj;
lean_object* v___y_365_ = stack[2].m_obj;
lean_object* v___y_366_ = stack[3].m_obj;
lean_object* v_res_371_;
v_res_371_ = l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(v_ref_363_, v_msgData_364_, v___y_365_, v___y_366_);
stack->m_obj
 = v_res_371_;
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0___boxed(lean_object* v_ref_372_, lean_object* v_msgData_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(v_ref_372_, v_msgData_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v_ref_372_);
return v_res_377_;
}
}
lean_object* l_Lean_reportOutOfHeartbeats(lean_object* v_tac_380_, lean_object* v_stx_381_, lean_object* v_threshold_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v___x_386_; lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_404_; 
v___x_386_ = l_Lean_heartbeatsPercent___redArg(v_a_383_);
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_404_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_404_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_404_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
uint8_t v___x_391_; 
v___x_391_ = lean_nat_dec_le(v_threshold_382_, v_a_387_);
lean_dec(v_a_387_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_394_; 
lean_dec(v_tac_380_);
v___x_392_ = lean_box(0);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_392_);
v___x_394_ = v___x_389_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
lean_del_object(v___x_389_);
v___x_396_ = ((lean_object*)(l_Lean_reportOutOfHeartbeats___closed__0));
v___x_397_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_tac_380_, v___x_391_);
v___x_398_ = lean_string_append(v___x_396_, v___x_397_);
lean_dec_ref(v___x_397_);
v___x_399_ = ((lean_object*)(l_Lean_reportOutOfHeartbeats___closed__1));
v___x_400_ = lean_string_append(v___x_398_, v___x_399_);
v___x_401_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
v___x_402_ = l_Lean_MessageData_ofFormat(v___x_401_);
v___x_403_ = l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(v_stx_381_, v___x_402_, v_a_383_, v_a_384_);
return v___x_403_;
}
}
}
}
LEAN_EXPORT void l_Lean_reportOutOfHeartbeats_0interp(lean_interpreter_value* stack)
{
lean_object* v_tac_380_ = stack[0].m_obj;
lean_object* v_stx_381_ = stack[1].m_obj;
lean_object* v_threshold_382_ = stack[2].m_obj;
lean_object* v_a_383_ = stack[3].m_obj;
lean_object* v_a_384_ = stack[4].m_obj;
lean_object* v_res_405_;
v_res_405_ = l_Lean_reportOutOfHeartbeats(v_tac_380_, v_stx_381_, v_threshold_382_, v_a_383_, v_a_384_);
stack->m_obj
 = v_res_405_;
}
LEAN_EXPORT lean_object* l_Lean_reportOutOfHeartbeats___boxed(lean_object* v_tac_406_, lean_object* v_stx_407_, lean_object* v_threshold_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_reportOutOfHeartbeats(v_tac_406_, v_stx_407_, v_threshold_408_, v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_threshold_408_);
lean_dec(v_stx_407_);
return v_res_412_;
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
