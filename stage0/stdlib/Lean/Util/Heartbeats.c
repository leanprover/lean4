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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_140_, lean_object* v_x_141_){
_start:
{
if (lean_obj_tag(v_x_141_) == 1)
{
lean_object* v_pre_142_; 
v_pre_142_ = lean_ctor_get(v_x_141_, 0);
switch(lean_obj_tag(v_pre_142_))
{
case 1:
{
lean_object* v_pre_143_; 
v_pre_143_ = lean_ctor_get(v_pre_142_, 0);
switch(lean_obj_tag(v_pre_143_))
{
case 0:
{
lean_object* v_str_144_; lean_object* v_str_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v_str_144_ = lean_ctor_get(v_x_141_, 1);
v_str_145_ = lean_ctor_get(v_pre_142_, 1);
v___x_146_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__0));
v___x_147_ = lean_string_dec_eq(v_str_145_, v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_148_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__1));
v___x_149_ = lean_string_dec_eq(v_str_145_, v___x_148_);
if (v___x_149_ == 0)
{
return v___x_149_;
}
else
{
lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_150_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__2));
v___x_151_ = lean_string_dec_eq(v_str_144_, v___x_150_);
if (v___x_151_ == 0)
{
return v___x_151_;
}
else
{
return v_suppressElabErrors_140_;
}
}
}
else
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__3));
v___x_153_ = lean_string_dec_eq(v_str_144_, v___x_152_);
if (v___x_153_ == 0)
{
return v___x_153_;
}
else
{
return v_suppressElabErrors_140_;
}
}
}
case 1:
{
lean_object* v_pre_154_; 
v_pre_154_ = lean_ctor_get(v_pre_143_, 0);
if (lean_obj_tag(v_pre_154_) == 0)
{
lean_object* v_str_155_; lean_object* v_str_156_; lean_object* v_str_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v_str_155_ = lean_ctor_get(v_x_141_, 1);
v_str_156_ = lean_ctor_get(v_pre_142_, 1);
v_str_157_ = lean_ctor_get(v_pre_143_, 1);
v___x_158_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__4));
v___x_159_ = lean_string_dec_eq(v_str_157_, v___x_158_);
if (v___x_159_ == 0)
{
return v___x_159_;
}
else
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__5));
v___x_161_ = lean_string_dec_eq(v_str_156_, v___x_160_);
if (v___x_161_ == 0)
{
return v___x_161_;
}
else
{
lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__6));
v___x_163_ = lean_string_dec_eq(v_str_155_, v___x_162_);
if (v___x_163_ == 0)
{
return v___x_163_;
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
uint8_t v___x_164_; 
v___x_164_ = 0;
return v___x_164_;
}
}
default: 
{
uint8_t v___x_165_; 
v___x_165_ = 0;
return v___x_165_;
}
}
}
case 0:
{
lean_object* v_str_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_str_166_ = lean_ctor_get(v_x_141_, 1);
v___x_167_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__7));
v___x_168_ = lean_string_dec_eq(v_str_166_, v___x_167_);
if (v___x_168_ == 0)
{
return v___x_168_;
}
else
{
return v_suppressElabErrors_140_;
}
}
default: 
{
uint8_t v___x_169_; 
v___x_169_ = 0;
return v___x_169_;
}
}
}
else
{
uint8_t v___x_170_; 
v___x_170_ = 0;
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_171_, lean_object* v_x_172_){
_start:
{
uint8_t v_suppressElabErrors_boxed_173_; uint8_t v_res_174_; lean_object* v_r_175_; 
v_suppressElabErrors_boxed_173_ = lean_unbox(v_suppressElabErrors_171_);
v_res_174_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_173_, v_x_172_);
lean_dec(v_x_172_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(lean_object* v_opts_176_, lean_object* v_opt_177_){
_start:
{
lean_object* v_name_178_; lean_object* v_defValue_179_; lean_object* v_map_180_; lean_object* v___x_181_; 
v_name_178_ = lean_ctor_get(v_opt_177_, 0);
v_defValue_179_ = lean_ctor_get(v_opt_177_, 1);
v_map_180_ = lean_ctor_get(v_opts_176_, 0);
v___x_181_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_180_, v_name_178_);
if (lean_obj_tag(v___x_181_) == 0)
{
uint8_t v___x_182_; 
v___x_182_ = lean_unbox(v_defValue_179_);
return v___x_182_;
}
else
{
lean_object* v_val_183_; 
v_val_183_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_val_183_);
lean_dec_ref_known(v___x_181_, 1);
if (lean_obj_tag(v_val_183_) == 1)
{
uint8_t v_v_184_; 
v_v_184_ = lean_ctor_get_uint8(v_val_183_, 0);
lean_dec_ref_known(v_val_183_, 0);
return v_v_184_;
}
else
{
uint8_t v___x_185_; 
lean_dec(v_val_183_);
v___x_185_ = lean_unbox(v_defValue_179_);
return v___x_185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2___boxed(lean_object* v_opts_186_, lean_object* v_opt_187_){
_start:
{
uint8_t v_res_188_; lean_object* v_r_189_; 
v_res_188_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(v_opts_186_, v_opt_187_);
lean_dec_ref(v_opt_187_);
lean_dec_ref(v_opts_186_);
v_r_189_ = lean_box(v_res_188_);
return v_r_189_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_190_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0);
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_193_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_194_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
lean_ctor_set(v___x_196_, 2, v___x_195_);
lean_ctor_set(v___x_196_, 3, v___x_195_);
lean_ctor_set(v___x_196_, 4, v___x_194_);
lean_ctor_set(v___x_196_, 5, v___x_194_);
lean_ctor_set(v___x_196_, 6, v___x_194_);
lean_ctor_set(v___x_196_, 7, v___x_194_);
lean_ctor_set(v___x_196_, 8, v___x_194_);
lean_ctor_set(v___x_196_, 9, v___x_194_);
lean_ctor_set(v___x_196_, 10, v___x_194_);
lean_ctor_set(v___x_196_, 11, v___x_193_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = lean_unsigned_to_nat(32u);
v___x_198_ = lean_mk_empty_array_with_capacity(v___x_197_);
v___x_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_200_ = ((size_t)5ULL);
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = lean_unsigned_to_nat(32u);
v___x_203_ = lean_mk_empty_array_with_capacity(v___x_202_);
v___x_204_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3);
v___x_205_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
lean_ctor_set(v___x_205_, 2, v___x_201_);
lean_ctor_set(v___x_205_, 3, v___x_201_);
lean_ctor_set_usize(v___x_205_, 4, v___x_200_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_206_ = lean_box(1);
v___x_207_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4);
v___x_208_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1);
v___x_209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v___x_207_);
lean_ctor_set(v___x_209_, 2, v___x_206_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(lean_object* v_msgData_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___x_214_; lean_object* v_toCold_215_; lean_object* v_env_216_; lean_object* v_options_217_; uint8_t v___x_218_; lean_object* v_env_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_214_ = lean_st_ref_get(v___y_212_);
v_toCold_215_ = lean_ctor_get(v___y_211_, 0);
v_env_216_ = lean_ctor_get(v___x_214_, 0);
lean_inc_ref(v_env_216_);
lean_dec(v___x_214_);
v_options_217_ = lean_ctor_get(v_toCold_215_, 2);
v___x_218_ = 0;
v_env_219_ = l_Lean_Environment_setRecordingDeps(v_env_216_, v___x_218_);
v___x_220_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2);
v___x_221_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_217_);
v___x_222_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_222_, 0, v_env_219_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
lean_ctor_set(v___x_222_, 2, v___x_221_);
lean_ctor_set(v___x_222_, 3, v_options_217_);
v___x_223_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v_msgData_210_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(v_msgData_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(lean_object* v_ref_231_, lean_object* v_msgData_232_, uint8_t v_severity_233_, uint8_t v_isSilent_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_242_; uint8_t v___y_243_; uint8_t v___y_244_; lean_object* v___y_245_; lean_object* v_toCold_246_; lean_object* v___y_247_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; uint8_t v___y_279_; uint8_t v___y_280_; uint8_t v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; uint8_t v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; uint8_t v___y_307_; uint8_t v___y_308_; lean_object* v___y_309_; uint8_t v___y_313_; uint8_t v___y_314_; uint8_t v___x_324_; uint8_t v___y_326_; uint8_t v___x_332_; 
v___x_324_ = 2;
v___x_332_ = l_Lean_instBEqMessageSeverity_beq(v_severity_233_, v___x_324_);
if (v___x_332_ == 0)
{
v___y_326_ = v___x_332_;
goto v___jp_325_;
}
else
{
uint8_t v___x_333_; 
lean_inc_ref(v_msgData_232_);
v___x_333_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_232_);
if (v___x_333_ == 0)
{
v___y_326_ = v___x_333_;
goto v___jp_325_;
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; 
lean_dec_ref(v_msgData_232_);
v___x_334_ = lean_box(0);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
v___jp_238_:
{
lean_object* v_currNamespace_248_; lean_object* v_openDecls_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v_env_254_; lean_object* v_nextMacroScope_255_; lean_object* v_ngen_256_; lean_object* v_auxDeclNGen_257_; lean_object* v_traceState_258_; lean_object* v_cache_259_; lean_object* v_recordedDeps_260_; lean_object* v_messages_261_; lean_object* v_infoState_262_; lean_object* v_snapshotTasks_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_274_; 
v_currNamespace_248_ = lean_ctor_get(v_toCold_246_, 4);
v_openDecls_249_ = lean_ctor_get(v_toCold_246_, 5);
lean_inc(v_openDecls_249_);
lean_inc(v_currNamespace_248_);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v_currNamespace_248_);
lean_ctor_set(v___x_250_, 1, v_openDecls_249_);
v___x_251_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___y_241_);
lean_inc_ref(v___y_240_);
lean_inc_ref(v___y_242_);
v___x_252_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_252_, 0, v___y_242_);
lean_ctor_set(v___x_252_, 1, v___y_245_);
lean_ctor_set(v___x_252_, 2, v___y_239_);
lean_ctor_set(v___x_252_, 3, v___y_240_);
lean_ctor_set(v___x_252_, 4, v___x_251_);
lean_ctor_set_uint8(v___x_252_, sizeof(void*)*5, v___y_244_);
lean_ctor_set_uint8(v___x_252_, sizeof(void*)*5 + 1, v___y_243_);
lean_ctor_set_uint8(v___x_252_, sizeof(void*)*5 + 2, v_isSilent_234_);
v___x_253_ = lean_st_ref_take(v___y_247_);
v_env_254_ = lean_ctor_get(v___x_253_, 0);
v_nextMacroScope_255_ = lean_ctor_get(v___x_253_, 1);
v_ngen_256_ = lean_ctor_get(v___x_253_, 2);
v_auxDeclNGen_257_ = lean_ctor_get(v___x_253_, 3);
v_traceState_258_ = lean_ctor_get(v___x_253_, 4);
v_cache_259_ = lean_ctor_get(v___x_253_, 5);
v_recordedDeps_260_ = lean_ctor_get(v___x_253_, 6);
v_messages_261_ = lean_ctor_get(v___x_253_, 7);
v_infoState_262_ = lean_ctor_get(v___x_253_, 8);
v_snapshotTasks_263_ = lean_ctor_get(v___x_253_, 9);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_274_ == 0)
{
v___x_265_ = v___x_253_;
v_isShared_266_ = v_isSharedCheck_274_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_snapshotTasks_263_);
lean_inc(v_infoState_262_);
lean_inc(v_messages_261_);
lean_inc(v_recordedDeps_260_);
lean_inc(v_cache_259_);
lean_inc(v_traceState_258_);
lean_inc(v_auxDeclNGen_257_);
lean_inc(v_ngen_256_);
lean_inc(v_nextMacroScope_255_);
lean_inc(v_env_254_);
lean_dec(v___x_253_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_274_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_267_ = lean_box(0);
v___x_268_ = l_Lean_MessageLog_add(v___x_252_, v_messages_261_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 7, v___x_268_);
v___x_270_ = v___x_265_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_env_254_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_nextMacroScope_255_);
lean_ctor_set(v_reuseFailAlloc_273_, 2, v_ngen_256_);
lean_ctor_set(v_reuseFailAlloc_273_, 3, v_auxDeclNGen_257_);
lean_ctor_set(v_reuseFailAlloc_273_, 4, v_traceState_258_);
lean_ctor_set(v_reuseFailAlloc_273_, 5, v_cache_259_);
lean_ctor_set(v_reuseFailAlloc_273_, 6, v_recordedDeps_260_);
lean_ctor_set(v_reuseFailAlloc_273_, 7, v___x_268_);
lean_ctor_set(v_reuseFailAlloc_273_, 8, v_infoState_262_);
lean_ctor_set(v_reuseFailAlloc_273_, 9, v_snapshotTasks_263_);
v___x_270_ = v_reuseFailAlloc_273_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_st_ref_put(v___y_247_, v___x_270_);
v___x_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_267_);
return v___x_272_;
}
}
}
v___jp_275_:
{
lean_object* v_fileName_284_; lean_object* v_fileMap_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_301_; 
v_fileName_284_ = lean_ctor_get(v___y_282_, 0);
v_fileMap_285_ = lean_ctor_get(v___y_282_, 1);
v___x_286_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_232_);
v___x_287_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(v___x_286_, v___y_235_, v___y_236_);
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_301_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_301_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_301_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
lean_inc_ref_n(v_fileMap_285_, 2);
v___x_292_ = l_Lean_FileMap_toPosition(v_fileMap_285_, v___y_278_);
lean_dec(v___y_278_);
v___x_293_ = l_Lean_FileMap_toPosition(v_fileMap_285_, v___y_283_);
lean_dec(v___y_283_);
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
v___x_295_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___closed__0));
if (v___y_279_ == 0)
{
lean_del_object(v___x_290_);
lean_dec_ref(v___y_276_);
v___y_239_ = v___x_294_;
v___y_240_ = v___x_295_;
v___y_241_ = v_a_288_;
v___y_242_ = v_fileName_284_;
v___y_243_ = v___y_281_;
v___y_244_ = v___y_280_;
v___y_245_ = v___x_292_;
v_toCold_246_ = v___y_277_;
v___y_247_ = v___y_236_;
goto v___jp_238_;
}
else
{
uint8_t v___x_296_; 
lean_inc(v_a_288_);
v___x_296_ = l_Lean_MessageData_hasTag(v___y_276_, v_a_288_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_299_; 
lean_dec_ref_known(v___x_294_, 1);
lean_dec_ref(v___x_292_);
lean_dec(v_a_288_);
v___x_297_ = lean_box(0);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_297_);
v___x_299_ = v___x_290_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
else
{
lean_del_object(v___x_290_);
v___y_239_ = v___x_294_;
v___y_240_ = v___x_295_;
v___y_241_ = v_a_288_;
v___y_242_ = v_fileName_284_;
v___y_243_ = v___y_281_;
v___y_244_ = v___y_280_;
v___y_245_ = v___x_292_;
v_toCold_246_ = v___y_277_;
v___y_247_ = v___y_236_;
goto v___jp_238_;
}
}
}
}
v___jp_302_:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Syntax_getTailPos_x3f(v___y_306_, v___y_308_);
lean_dec(v___y_306_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_inc(v___y_309_);
v___y_276_ = v___y_304_;
v___y_277_ = v___y_305_;
v___y_278_ = v___y_309_;
v___y_279_ = v___y_303_;
v___y_280_ = v___y_308_;
v___y_281_ = v___y_307_;
v___y_282_ = v___y_305_;
v___y_283_ = v___y_309_;
goto v___jp_275_;
}
else
{
lean_object* v_val_311_; 
v_val_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_val_311_);
lean_dec_ref_known(v___x_310_, 1);
v___y_276_ = v___y_304_;
v___y_277_ = v___y_305_;
v___y_278_ = v___y_309_;
v___y_279_ = v___y_303_;
v___y_280_ = v___y_308_;
v___y_281_ = v___y_307_;
v___y_282_ = v___y_305_;
v___y_283_ = v_val_311_;
goto v___jp_275_;
}
}
v___jp_312_:
{
lean_object* v_toCold_315_; lean_object* v_ref_316_; uint8_t v_suppressElabErrors_317_; lean_object* v___x_318_; lean_object* v___f_319_; lean_object* v_ref_320_; lean_object* v___x_321_; 
v_toCold_315_ = lean_ctor_get(v___y_235_, 0);
v_ref_316_ = lean_ctor_get(v___y_235_, 2);
v_suppressElabErrors_317_ = lean_ctor_get_uint8(v___y_235_, sizeof(void*)*3 + 2);
v___x_318_ = lean_box(v_suppressElabErrors_317_);
v___f_319_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_319_, 0, v___x_318_);
v_ref_320_ = l_Lean_replaceRef(v_ref_231_, v_ref_316_);
v___x_321_ = l_Lean_Syntax_getPos_x3f(v_ref_320_, v___y_313_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v___x_322_; 
v___x_322_ = lean_unsigned_to_nat(0u);
v___y_303_ = v_suppressElabErrors_317_;
v___y_304_ = v___f_319_;
v___y_305_ = v_toCold_315_;
v___y_306_ = v_ref_320_;
v___y_307_ = v___y_314_;
v___y_308_ = v___y_313_;
v___y_309_ = v___x_322_;
goto v___jp_302_;
}
else
{
lean_object* v_val_323_; 
v_val_323_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_val_323_);
lean_dec_ref_known(v___x_321_, 1);
v___y_303_ = v_suppressElabErrors_317_;
v___y_304_ = v___f_319_;
v___y_305_ = v_toCold_315_;
v___y_306_ = v_ref_320_;
v___y_307_ = v___y_314_;
v___y_308_ = v___y_313_;
v___y_309_ = v_val_323_;
goto v___jp_302_;
}
}
v___jp_325_:
{
uint8_t v___x_327_; uint8_t v___x_328_; 
v___x_327_ = 1;
v___x_328_ = l_Lean_instBEqMessageSeverity_beq(v_severity_233_, v___x_327_);
if (v___x_328_ == 0)
{
v___y_313_ = v___y_326_;
v___y_314_ = v_severity_233_;
goto v___jp_312_;
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_329_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_235_);
v___x_330_ = l_Lean_warningAsError;
v___x_331_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(v___x_329_, v___x_330_);
lean_dec_ref(v___x_329_);
if (v___x_331_ == 0)
{
v___y_313_ = v___y_326_;
v___y_314_ = v_severity_233_;
goto v___jp_312_;
}
else
{
v___y_313_ = v___y_326_;
v___y_314_ = v___x_324_;
goto v___jp_312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___boxed(lean_object* v_ref_336_, lean_object* v_msgData_337_, lean_object* v_severity_338_, lean_object* v_isSilent_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
uint8_t v_severity_boxed_343_; uint8_t v_isSilent_boxed_344_; lean_object* v_res_345_; 
v_severity_boxed_343_ = lean_unbox(v_severity_338_);
v_isSilent_boxed_344_ = lean_unbox(v_isSilent_339_);
v_res_345_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(v_ref_336_, v_msgData_337_, v_severity_boxed_343_, v_isSilent_boxed_344_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v_ref_336_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(lean_object* v_ref_346_, lean_object* v_msgData_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
uint8_t v___x_351_; uint8_t v___x_352_; lean_object* v___x_353_; 
v___x_351_ = 0;
v___x_352_ = 0;
v___x_353_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(v_ref_346_, v_msgData_347_, v___x_351_, v___x_352_, v___y_348_, v___y_349_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0___boxed(lean_object* v_ref_354_, lean_object* v_msgData_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(v_ref_354_, v_msgData_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v_ref_354_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportOutOfHeartbeats(lean_object* v_tac_362_, lean_object* v_stx_363_, lean_object* v_threshold_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v___x_368_; lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_386_; 
v___x_368_ = l_Lean_heartbeatsPercent___redArg(v_a_365_);
v_a_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_386_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_386_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_386_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
uint8_t v___x_373_; 
v___x_373_ = lean_nat_dec_le(v_threshold_364_, v_a_369_);
lean_dec(v_a_369_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v___x_376_; 
lean_dec(v_tac_362_);
v___x_374_ = lean_box(0);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_374_);
v___x_376_ = v___x_371_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
lean_del_object(v___x_371_);
v___x_378_ = ((lean_object*)(l_Lean_reportOutOfHeartbeats___closed__0));
v___x_379_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_tac_362_, v___x_373_);
v___x_380_ = lean_string_append(v___x_378_, v___x_379_);
lean_dec_ref(v___x_379_);
v___x_381_ = ((lean_object*)(l_Lean_reportOutOfHeartbeats___closed__1));
v___x_382_ = lean_string_append(v___x_380_, v___x_381_);
v___x_383_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
v___x_384_ = l_Lean_MessageData_ofFormat(v___x_383_);
v___x_385_ = l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(v_stx_363_, v___x_384_, v_a_365_, v_a_366_);
return v___x_385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportOutOfHeartbeats___boxed(lean_object* v_tac_387_, lean_object* v_stx_388_, lean_object* v_threshold_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_reportOutOfHeartbeats(v_tac_387_, v_stx_388_, v_threshold_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_threshold_389_);
lean_dec(v_stx_388_);
return v_res_393_;
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
