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
uint8_t v_suppressElabErrors_boxed_171_; uint8_t v___y_2698__boxed_172_; uint8_t v_res_173_; lean_object* v_r_174_; 
v_suppressElabErrors_boxed_171_ = lean_unbox(v_suppressElabErrors_168_);
v___y_2698__boxed_172_ = lean_unbox(v___y_169_);
v_res_173_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_171_, v___y_2698__boxed_172_, v_x_170_);
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
v___x_189_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1);
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
lean_ctor_set(v___x_194_, 2, v___x_193_);
lean_ctor_set(v___x_194_, 3, v___x_193_);
lean_ctor_set(v___x_194_, 4, v___x_192_);
lean_ctor_set(v___x_194_, 5, v___x_192_);
lean_ctor_set(v___x_194_, 6, v___x_192_);
lean_ctor_set(v___x_194_, 7, v___x_192_);
lean_ctor_set(v___x_194_, 8, v___x_192_);
lean_ctor_set(v___x_194_, 9, v___x_192_);
lean_ctor_set(v___x_194_, 10, v___x_192_);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_unsigned_to_nat(32u);
v___x_196_ = lean_mk_empty_array_with_capacity(v___x_195_);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_198_ = ((size_t)5ULL);
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = lean_unsigned_to_nat(32u);
v___x_201_ = lean_mk_empty_array_with_capacity(v___x_200_);
v___x_202_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3);
v___x_203_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v___x_201_);
lean_ctor_set(v___x_203_, 2, v___x_199_);
lean_ctor_set(v___x_203_, 3, v___x_199_);
lean_ctor_set_usize(v___x_203_, 4, v___x_198_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_204_ = lean_box(1);
v___x_205_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4);
v___x_206_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1);
v___x_207_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_205_);
lean_ctor_set(v___x_207_, 2, v___x_204_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(lean_object* v_msgData_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v_toCold_213_; lean_object* v_env_214_; lean_object* v_options_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_212_ = lean_st_ref_get(v___y_210_);
v_toCold_213_ = lean_ctor_get(v___y_209_, 0);
v_env_214_ = lean_ctor_get(v___x_212_, 0);
lean_inc_ref(v_env_214_);
lean_dec(v___x_212_);
v_options_215_ = lean_ctor_get(v_toCold_213_, 2);
v___x_216_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2);
v___x_217_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_215_);
v___x_218_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_218_, 0, v_env_214_);
lean_ctor_set(v___x_218_, 1, v___x_216_);
lean_ctor_set(v___x_218_, 2, v___x_217_);
lean_ctor_set(v___x_218_, 3, v_options_215_);
v___x_219_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v_msgData_208_);
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(v_msgData_221_, v___y_222_, v___y_223_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(lean_object* v_ref_227_, lean_object* v_msgData_228_, uint8_t v_severity_229_, uint8_t v_isSilent_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
uint8_t v___y_235_; uint8_t v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_272_; uint8_t v___y_273_; uint8_t v___y_274_; uint8_t v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_297_; uint8_t v___y_298_; uint8_t v___y_299_; uint8_t v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_308_; lean_object* v___y_309_; uint8_t v___y_310_; uint8_t v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; uint8_t v___y_314_; uint8_t v___x_319_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; uint8_t v___y_325_; uint8_t v___y_326_; uint8_t v___y_327_; uint8_t v___y_329_; uint8_t v___x_345_; 
v___x_319_ = 2;
v___x_345_ = l_Lean_instBEqMessageSeverity_beq(v_severity_229_, v___x_319_);
if (v___x_345_ == 0)
{
v___y_329_ = v___x_345_;
goto v___jp_328_;
}
else
{
uint8_t v___x_346_; 
lean_inc_ref(v_msgData_228_);
v___x_346_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_228_);
v___y_329_ = v___x_346_;
goto v___jp_328_;
}
v___jp_234_:
{
lean_object* v___x_244_; lean_object* v_toCold_245_; lean_object* v_currNamespace_246_; lean_object* v_openDecls_247_; lean_object* v_env_248_; lean_object* v_nextMacroScope_249_; lean_object* v_ngen_250_; lean_object* v_auxDeclNGen_251_; lean_object* v_traceState_252_; lean_object* v_cache_253_; lean_object* v_messages_254_; lean_object* v_infoState_255_; lean_object* v_snapshotTasks_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_270_; 
v___x_244_ = lean_st_ref_take(v___y_243_);
v_toCold_245_ = lean_ctor_get(v___y_242_, 0);
v_currNamespace_246_ = lean_ctor_get(v_toCold_245_, 4);
v_openDecls_247_ = lean_ctor_get(v_toCold_245_, 5);
v_env_248_ = lean_ctor_get(v___x_244_, 0);
v_nextMacroScope_249_ = lean_ctor_get(v___x_244_, 1);
v_ngen_250_ = lean_ctor_get(v___x_244_, 2);
v_auxDeclNGen_251_ = lean_ctor_get(v___x_244_, 3);
v_traceState_252_ = lean_ctor_get(v___x_244_, 4);
v_cache_253_ = lean_ctor_get(v___x_244_, 5);
v_messages_254_ = lean_ctor_get(v___x_244_, 6);
v_infoState_255_ = lean_ctor_get(v___x_244_, 7);
v_snapshotTasks_256_ = lean_ctor_get(v___x_244_, 8);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_270_ == 0)
{
v___x_258_ = v___x_244_;
v_isShared_259_ = v_isSharedCheck_270_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_snapshotTasks_256_);
lean_inc(v_infoState_255_);
lean_inc(v_messages_254_);
lean_inc(v_cache_253_);
lean_inc(v_traceState_252_);
lean_inc(v_auxDeclNGen_251_);
lean_inc(v_ngen_250_);
lean_inc(v_nextMacroScope_249_);
lean_inc(v_env_248_);
lean_dec(v___x_244_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_270_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
lean_inc(v_openDecls_247_);
lean_inc(v_currNamespace_246_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v_currNamespace_246_);
lean_ctor_set(v___x_260_, 1, v_openDecls_247_);
v___x_261_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___y_237_);
lean_inc_ref(v___y_241_);
lean_inc_ref(v___y_238_);
v___x_262_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_262_, 0, v___y_238_);
lean_ctor_set(v___x_262_, 1, v___y_239_);
lean_ctor_set(v___x_262_, 2, v___y_240_);
lean_ctor_set(v___x_262_, 3, v___y_241_);
lean_ctor_set(v___x_262_, 4, v___x_261_);
lean_ctor_set_uint8(v___x_262_, sizeof(void*)*5, v___y_236_);
lean_ctor_set_uint8(v___x_262_, sizeof(void*)*5 + 1, v___y_235_);
lean_ctor_set_uint8(v___x_262_, sizeof(void*)*5 + 2, v_isSilent_230_);
v___x_263_ = l_Lean_MessageLog_add(v___x_262_, v_messages_254_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 6, v___x_263_);
v___x_265_ = v___x_258_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_env_248_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_nextMacroScope_249_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v_ngen_250_);
lean_ctor_set(v_reuseFailAlloc_269_, 3, v_auxDeclNGen_251_);
lean_ctor_set(v_reuseFailAlloc_269_, 4, v_traceState_252_);
lean_ctor_set(v_reuseFailAlloc_269_, 5, v_cache_253_);
lean_ctor_set(v_reuseFailAlloc_269_, 6, v___x_263_);
lean_ctor_set(v_reuseFailAlloc_269_, 7, v_infoState_255_);
lean_ctor_set(v_reuseFailAlloc_269_, 8, v_snapshotTasks_256_);
v___x_265_ = v_reuseFailAlloc_269_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_st_ref_put(v___y_243_, v___x_265_);
v___x_267_ = lean_box(0);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
}
}
v___jp_271_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_295_; 
v___x_280_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_228_);
v___x_281_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(v___x_280_, v___y_231_, v___y_232_);
v_a_282_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_295_ == 0)
{
v___x_284_ = v___x_281_;
v_isShared_285_ = v_isSharedCheck_295_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_295_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
lean_inc_ref_n(v___y_278_, 2);
v___x_286_ = l_Lean_FileMap_toPosition(v___y_278_, v___y_276_);
lean_dec(v___y_276_);
v___x_287_ = l_Lean_FileMap_toPosition(v___y_278_, v___y_279_);
lean_dec(v___y_279_);
v___x_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
v___x_289_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___closed__0));
if (v___y_273_ == 0)
{
lean_del_object(v___x_284_);
lean_dec_ref(v___y_272_);
v___y_235_ = v___y_274_;
v___y_236_ = v___y_275_;
v___y_237_ = v_a_282_;
v___y_238_ = v___y_277_;
v___y_239_ = v___x_286_;
v___y_240_ = v___x_288_;
v___y_241_ = v___x_289_;
v___y_242_ = v___y_231_;
v___y_243_ = v___y_232_;
goto v___jp_234_;
}
else
{
uint8_t v___x_290_; 
lean_inc(v_a_282_);
v___x_290_ = l_Lean_MessageData_hasTag(v___y_272_, v_a_282_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_293_; 
lean_dec_ref_known(v___x_288_, 1);
lean_dec_ref(v___x_286_);
lean_dec(v_a_282_);
v___x_291_ = lean_box(0);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_291_);
v___x_293_ = v___x_284_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
else
{
lean_del_object(v___x_284_);
v___y_235_ = v___y_274_;
v___y_236_ = v___y_275_;
v___y_237_ = v_a_282_;
v___y_238_ = v___y_277_;
v___y_239_ = v___x_286_;
v___y_240_ = v___x_288_;
v___y_241_ = v___x_289_;
v___y_242_ = v___y_231_;
v___y_243_ = v___y_232_;
goto v___jp_234_;
}
}
}
}
v___jp_296_:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Syntax_getTailPos_x3f(v___y_301_, v___y_300_);
lean_dec(v___y_301_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_inc(v___y_304_);
v___y_272_ = v___y_297_;
v___y_273_ = v___y_299_;
v___y_274_ = v___y_298_;
v___y_275_ = v___y_300_;
v___y_276_ = v___y_304_;
v___y_277_ = v___y_302_;
v___y_278_ = v___y_303_;
v___y_279_ = v___y_304_;
goto v___jp_271_;
}
else
{
lean_object* v_val_306_; 
v_val_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_val_306_);
lean_dec_ref_known(v___x_305_, 1);
v___y_272_ = v___y_297_;
v___y_273_ = v___y_299_;
v___y_274_ = v___y_298_;
v___y_275_ = v___y_300_;
v___y_276_ = v___y_304_;
v___y_277_ = v___y_302_;
v___y_278_ = v___y_303_;
v___y_279_ = v_val_306_;
goto v___jp_271_;
}
}
v___jp_307_:
{
lean_object* v_ref_315_; lean_object* v___x_316_; 
v_ref_315_ = l_Lean_replaceRef(v_ref_227_, v___y_309_);
v___x_316_ = l_Lean_Syntax_getPos_x3f(v_ref_315_, v___y_311_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v___x_317_; 
v___x_317_ = lean_unsigned_to_nat(0u);
v___y_297_ = v___y_308_;
v___y_298_ = v___y_314_;
v___y_299_ = v___y_310_;
v___y_300_ = v___y_311_;
v___y_301_ = v_ref_315_;
v___y_302_ = v___y_312_;
v___y_303_ = v___y_313_;
v___y_304_ = v___x_317_;
goto v___jp_296_;
}
else
{
lean_object* v_val_318_; 
v_val_318_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_val_318_);
lean_dec_ref_known(v___x_316_, 1);
v___y_297_ = v___y_308_;
v___y_298_ = v___y_314_;
v___y_299_ = v___y_310_;
v___y_300_ = v___y_311_;
v___y_301_ = v_ref_315_;
v___y_302_ = v___y_312_;
v___y_303_ = v___y_313_;
v___y_304_ = v_val_318_;
goto v___jp_296_;
}
}
v___jp_320_:
{
if (v___y_327_ == 0)
{
v___y_308_ = v___y_321_;
v___y_309_ = v___y_324_;
v___y_310_ = v___y_325_;
v___y_311_ = v___y_326_;
v___y_312_ = v___y_322_;
v___y_313_ = v___y_323_;
v___y_314_ = v_severity_229_;
goto v___jp_307_;
}
else
{
v___y_308_ = v___y_321_;
v___y_309_ = v___y_324_;
v___y_310_ = v___y_325_;
v___y_311_ = v___y_326_;
v___y_312_ = v___y_322_;
v___y_313_ = v___y_323_;
v___y_314_ = v___x_319_;
goto v___jp_307_;
}
}
v___jp_328_:
{
if (v___y_329_ == 0)
{
lean_object* v_toCold_330_; lean_object* v_ref_331_; uint8_t v_suppressElabErrors_332_; lean_object* v_fileName_333_; lean_object* v_fileMap_334_; lean_object* v_options_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___f_338_; uint8_t v___x_339_; uint8_t v___x_340_; 
v_toCold_330_ = lean_ctor_get(v___y_231_, 0);
v_ref_331_ = lean_ctor_get(v___y_231_, 2);
v_suppressElabErrors_332_ = lean_ctor_get_uint8(v___y_231_, sizeof(void*)*3 + 1);
v_fileName_333_ = lean_ctor_get(v_toCold_330_, 0);
v_fileMap_334_ = lean_ctor_get(v_toCold_330_, 1);
v_options_335_ = lean_ctor_get(v_toCold_330_, 2);
v___x_336_ = lean_box(v_suppressElabErrors_332_);
v___x_337_ = lean_box(v___y_329_);
v___f_338_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_338_, 0, v___x_336_);
lean_closure_set(v___f_338_, 1, v___x_337_);
v___x_339_ = 1;
v___x_340_ = l_Lean_instBEqMessageSeverity_beq(v_severity_229_, v___x_339_);
if (v___x_340_ == 0)
{
v___y_321_ = v___f_338_;
v___y_322_ = v_fileName_333_;
v___y_323_ = v_fileMap_334_;
v___y_324_ = v_ref_331_;
v___y_325_ = v_suppressElabErrors_332_;
v___y_326_ = v___y_329_;
v___y_327_ = v___x_340_;
goto v___jp_320_;
}
else
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = l_Lean_warningAsError;
v___x_342_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(v_options_335_, v___x_341_);
v___y_321_ = v___f_338_;
v___y_322_ = v_fileName_333_;
v___y_323_ = v_fileMap_334_;
v___y_324_ = v_ref_331_;
v___y_325_ = v_suppressElabErrors_332_;
v___y_326_ = v___y_329_;
v___y_327_ = v___x_342_;
goto v___jp_320_;
}
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec_ref(v_msgData_228_);
v___x_343_ = lean_box(0);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___boxed(lean_object* v_ref_347_, lean_object* v_msgData_348_, lean_object* v_severity_349_, lean_object* v_isSilent_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
uint8_t v_severity_boxed_354_; uint8_t v_isSilent_boxed_355_; lean_object* v_res_356_; 
v_severity_boxed_354_ = lean_unbox(v_severity_349_);
v_isSilent_boxed_355_ = lean_unbox(v_isSilent_350_);
v_res_356_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(v_ref_347_, v_msgData_348_, v_severity_boxed_354_, v_isSilent_boxed_355_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v_ref_347_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(lean_object* v_ref_357_, lean_object* v_msgData_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
uint8_t v___x_362_; uint8_t v___x_363_; lean_object* v___x_364_; 
v___x_362_ = 0;
v___x_363_ = 0;
v___x_364_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(v_ref_357_, v_msgData_358_, v___x_362_, v___x_363_, v___y_359_, v___y_360_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0___boxed(lean_object* v_ref_365_, lean_object* v_msgData_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(v_ref_365_, v_msgData_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v_ref_365_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportOutOfHeartbeats(lean_object* v_tac_373_, lean_object* v_stx_374_, lean_object* v_threshold_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_379_; lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_397_; 
v___x_379_ = l_Lean_heartbeatsPercent___redArg(v_a_376_);
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_397_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_397_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_397_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
uint8_t v___x_384_; 
v___x_384_ = lean_nat_dec_le(v_threshold_375_, v_a_380_);
lean_dec(v_a_380_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_387_; 
lean_dec(v_tac_373_);
v___x_385_ = lean_box(0);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_385_);
v___x_387_ = v___x_382_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
lean_del_object(v___x_382_);
v___x_389_ = ((lean_object*)(l_Lean_reportOutOfHeartbeats___closed__0));
v___x_390_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_tac_373_, v___x_384_);
v___x_391_ = lean_string_append(v___x_389_, v___x_390_);
lean_dec_ref(v___x_390_);
v___x_392_ = ((lean_object*)(l_Lean_reportOutOfHeartbeats___closed__1));
v___x_393_ = lean_string_append(v___x_391_, v___x_392_);
v___x_394_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
v___x_395_ = l_Lean_MessageData_ofFormat(v___x_394_);
v___x_396_ = l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(v_stx_374_, v___x_395_, v_a_376_, v_a_377_);
return v___x_396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportOutOfHeartbeats___boxed(lean_object* v_tac_398_, lean_object* v_stx_399_, lean_object* v_threshold_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_reportOutOfHeartbeats(v_tac_398_, v_stx_399_, v_threshold_400_, v_a_401_, v_a_402_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_threshold_400_);
lean_dec(v_stx_399_);
return v_res_404_;
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
