// Lean compiler output
// Module: Lake.Util.Proc
// Imports: public import Lake.Util.Log import Init.Data.String.TakeDrop
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
lean_object* l_IO_Process_output(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "PATH"};
static const lean_object* l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__0_value;
static const lean_string_object l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__1_value;
static const lean_string_object l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__2 = (const lean_object*)&l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__2_value;
static const lean_string_object l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__3 = (const lean_object*)&l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__3_value;
static const lean_string_object l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATH "};
static const lean_object* l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__4 = (const lean_object*)&l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_mkCmdLog_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_mkCmdLog_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_mkCmdLog___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "> "};
static const lean_object* l_Lake_mkCmdLog___closed__0 = (const lean_object*)&l_Lake_mkCmdLog___closed__0_value;
static const lean_string_object l_Lake_mkCmdLog___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_mkCmdLog___closed__1 = (const lean_object*)&l_Lake_mkCmdLog___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_mkCmdLog(lean_object*);
static const lean_string_object l_Lake_logOutput___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stderr:\n"};
static const lean_object* l_Lake_logOutput___redArg___lam__0___closed__0 = (const lean_object*)&l_Lake_logOutput___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg___lam__1(lean_object*, lean_object*);
static const lean_string_object l_Lake_logOutput___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stdout:\n"};
static const lean_object* l_Lake_logOutput___redArg___closed__0 = (const lean_object*)&l_Lake_logOutput___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logOutput(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_rawProc___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "failed to execute '"};
static const lean_object* l_Lake_rawProc___lam__0___closed__0 = (const lean_object*)&l_Lake_rawProc___lam__0___closed__0_value;
static const lean_string_object l_Lake_rawProc___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "': "};
static const lean_object* l_Lake_rawProc___lam__0___closed__1 = (const lean_object*)&l_Lake_rawProc___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__0(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_proc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "external command '"};
static const lean_object* l_Lake_proc___closed__0 = (const lean_object*)&l_Lake_proc___closed__0_value;
static const lean_string_object l_Lake_proc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "' exited with code "};
static const lean_object* l_Lake_proc___closed__1 = (const lean_object*)&l_Lake_proc___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc_x27___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_testProc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 2, 2, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_testProc___closed__0 = (const lean_object*)&l_Lake_testProc___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_testProc(lean_object*);
LEAN_EXPORT lean_object* l_Lake_testProc___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0(lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
if (lean_obj_tag(v_a_6_) == 0)
{
lean_object* v___x_8_; 
v___x_8_ = l_List_reverse___redArg(v_a_7_);
return v___x_8_;
}
else
{
lean_object* v_head_9_; lean_object* v_tail_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_34_; 
v_head_9_ = lean_ctor_get(v_a_6_, 0);
v_tail_10_ = lean_ctor_get(v_a_6_, 1);
v_isSharedCheck_34_ = !lean_is_exclusive(v_a_6_);
if (v_isSharedCheck_34_ == 0)
{
v___x_12_ = v_a_6_;
v_isShared_13_ = v_isSharedCheck_34_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_tail_10_);
lean_inc(v_head_9_);
lean_dec(v_a_6_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_34_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___y_15_; lean_object* v_fst_20_; lean_object* v_snd_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v_fst_20_ = lean_ctor_get(v_head_9_, 0);
lean_inc(v_fst_20_);
v_snd_21_ = lean_ctor_get(v_head_9_, 1);
lean_inc(v_snd_21_);
lean_dec(v_head_9_);
v___x_22_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__0));
v___x_23_ = lean_string_dec_eq(v_fst_20_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___y_27_; 
v___x_24_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__1));
v___x_25_ = lean_string_append(v_fst_20_, v___x_24_);
if (lean_obj_tag(v_snd_21_) == 0)
{
lean_object* v___x_31_; 
v___x_31_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__3));
v___y_27_ = v___x_31_;
goto v___jp_26_;
}
else
{
lean_object* v_val_32_; 
v_val_32_ = lean_ctor_get(v_snd_21_, 0);
lean_inc(v_val_32_);
lean_dec_ref(v_snd_21_);
v___y_27_ = v_val_32_;
goto v___jp_26_;
}
v___jp_26_:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_string_append(v___x_25_, v___y_27_);
lean_dec_ref(v___y_27_);
v___x_29_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__2));
v___x_30_ = lean_string_append(v___x_28_, v___x_29_);
v___y_15_ = v___x_30_;
goto v___jp_14_;
}
}
else
{
lean_object* v___x_33_; 
lean_dec(v_snd_21_);
lean_dec(v_fst_20_);
v___x_33_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__4));
v___y_15_ = v___x_33_;
goto v___jp_14_;
}
v___jp_14_:
{
lean_object* v___x_17_; 
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 1, v_a_7_);
lean_ctor_set(v___x_12_, 0, v___y_15_);
v___x_17_ = v___x_12_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v___y_15_);
lean_ctor_set(v_reuseFailAlloc_19_, 1, v_a_7_);
v___x_17_ = v_reuseFailAlloc_19_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
v_a_6_ = v_tail_10_;
v_a_7_ = v___x_17_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_mkCmdLog_spec__1(lean_object* v_x_35_, lean_object* v_x_36_){
_start:
{
if (lean_obj_tag(v_x_36_) == 0)
{
return v_x_35_;
}
else
{
lean_object* v_head_37_; lean_object* v_tail_38_; lean_object* v___x_39_; 
v_head_37_ = lean_ctor_get(v_x_36_, 0);
v_tail_38_ = lean_ctor_get(v_x_36_, 1);
v___x_39_ = lean_string_append(v_x_35_, v_head_37_);
v_x_35_ = v___x_39_;
v_x_36_ = v_tail_38_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_mkCmdLog_spec__1___boxed(lean_object* v_x_41_, lean_object* v_x_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_List_foldl___at___00Lake_mkCmdLog_spec__1(v_x_41_, v_x_42_);
lean_dec(v_x_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkCmdLog(lean_object* v_args_46_){
_start:
{
lean_object* v_cmd_47_; lean_object* v_args_48_; lean_object* v_cwd_49_; lean_object* v_env_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v_envStr_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v_cmdStr_59_; lean_object* v___y_61_; 
v_cmd_47_ = lean_ctor_get(v_args_46_, 1);
lean_inc_ref(v_cmd_47_);
v_args_48_ = lean_ctor_get(v_args_46_, 2);
lean_inc_ref(v_args_48_);
v_cwd_49_ = lean_ctor_get(v_args_46_, 3);
lean_inc(v_cwd_49_);
v_env_50_ = lean_ctor_get(v_args_46_, 4);
lean_inc_ref(v_env_50_);
lean_dec_ref(v_args_46_);
v___x_51_ = lean_array_to_list(v_env_50_);
v___x_52_ = lean_box(0);
v___x_53_ = l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0(v___x_51_, v___x_52_);
v___x_54_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__3));
v_envStr_55_ = l_List_foldl___at___00Lake_mkCmdLog_spec__1(v___x_54_, v___x_53_);
lean_dec(v___x_53_);
v___x_56_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_mkCmdLog_spec__0___closed__2));
v___x_57_ = lean_array_to_list(v_args_48_);
v___x_58_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_58_, 0, v_cmd_47_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v_cmdStr_59_ = l_String_intercalate(v___x_56_, v___x_58_);
if (lean_obj_tag(v_cwd_49_) == 0)
{
lean_object* v___x_66_; 
v___x_66_ = ((lean_object*)(l_Lake_mkCmdLog___closed__1));
v___y_61_ = v___x_66_;
goto v___jp_60_;
}
else
{
lean_object* v_val_67_; 
v_val_67_ = lean_ctor_get(v_cwd_49_, 0);
lean_inc(v_val_67_);
lean_dec_ref(v_cwd_49_);
v___y_61_ = v_val_67_;
goto v___jp_60_;
}
v___jp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_62_ = ((lean_object*)(l_Lake_mkCmdLog___closed__0));
v___x_63_ = lean_string_append(v___y_61_, v___x_62_);
v___x_64_ = lean_string_append(v___x_63_, v_envStr_55_);
lean_dec_ref(v_envStr_55_);
v___x_65_ = lean_string_append(v___x_64_, v_cmdStr_59_);
lean_dec_ref(v_cmdStr_59_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg___lam__0(lean_object* v_stderr_69_, lean_object* v_log_70_, lean_object* v_inst_71_, lean_object* v_____r_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_73_ = lean_string_utf8_byte_size(v_stderr_69_);
v___x_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = lean_nat_dec_eq(v___x_73_, v___x_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec_ref(v_inst_71_);
v___x_76_ = ((lean_object*)(l_Lake_logOutput___redArg___lam__0___closed__0));
v___x_77_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_77_, 0, v_stderr_69_);
lean_ctor_set(v___x_77_, 1, v___x_74_);
lean_ctor_set(v___x_77_, 2, v___x_73_);
v___x_78_ = l_String_Slice_trimAscii(v___x_77_);
v___x_79_ = l_String_Slice_toString(v___x_78_);
lean_dec_ref(v___x_78_);
v___x_80_ = lean_string_append(v___x_76_, v___x_79_);
lean_dec_ref(v___x_79_);
v___x_81_ = lean_apply_1(v_log_70_, v___x_80_);
return v___x_81_;
}
else
{
lean_object* v_toApplicative_82_; lean_object* v_toPure_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v_log_70_);
lean_dec_ref(v_stderr_69_);
v_toApplicative_82_ = lean_ctor_get(v_inst_71_, 0);
lean_inc_ref(v_toApplicative_82_);
lean_dec_ref(v_inst_71_);
v_toPure_83_ = lean_ctor_get(v_toApplicative_82_, 1);
lean_inc(v_toPure_83_);
lean_dec_ref(v_toApplicative_82_);
v___x_84_ = lean_box(0);
v___x_85_ = lean_apply_2(v_toPure_83_, lean_box(0), v___x_84_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg___lam__1(lean_object* v___f_86_, lean_object* v_____r_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_apply_1(v___f_86_, v_____r_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg(lean_object* v_inst_90_, lean_object* v_out_91_, lean_object* v_log_92_){
_start:
{
lean_object* v_stdout_93_; lean_object* v_stderr_94_; lean_object* v___f_95_; lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v_stdout_93_ = lean_ctor_get(v_out_91_, 0);
lean_inc_ref(v_stdout_93_);
v_stderr_94_ = lean_ctor_get(v_out_91_, 1);
lean_inc_ref(v_stderr_94_);
lean_dec_ref(v_out_91_);
lean_inc_ref(v_inst_90_);
lean_inc(v_log_92_);
lean_inc_ref(v_stderr_94_);
v___f_95_ = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__0), 4, 3);
lean_closure_set(v___f_95_, 0, v_stderr_94_);
lean_closure_set(v___f_95_, 1, v_log_92_);
lean_closure_set(v___f_95_, 2, v_inst_90_);
v___x_96_ = lean_string_utf8_byte_size(v_stdout_93_);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = lean_nat_dec_eq(v___x_96_, v___x_97_);
if (v___x_98_ == 0)
{
lean_object* v_toBind_99_; lean_object* v___f_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
lean_dec_ref(v_stderr_94_);
v_toBind_99_ = lean_ctor_get(v_inst_90_, 1);
lean_inc(v_toBind_99_);
lean_dec_ref(v_inst_90_);
v___f_100_ = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__1), 2, 1);
lean_closure_set(v___f_100_, 0, v___f_95_);
v___x_101_ = ((lean_object*)(l_Lake_logOutput___redArg___closed__0));
v___x_102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_102_, 0, v_stdout_93_);
lean_ctor_set(v___x_102_, 1, v___x_97_);
lean_ctor_set(v___x_102_, 2, v___x_96_);
v___x_103_ = l_String_Slice_trimAscii(v___x_102_);
v___x_104_ = l_String_Slice_toString(v___x_103_);
lean_dec_ref(v___x_103_);
v___x_105_ = lean_string_append(v___x_101_, v___x_104_);
lean_dec_ref(v___x_104_);
v___x_106_ = lean_apply_1(v_log_92_, v___x_105_);
v___x_107_ = lean_apply_4(v_toBind_99_, lean_box(0), lean_box(0), v___x_106_, v___f_100_);
return v___x_107_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec_ref(v___f_95_);
lean_dec_ref(v_stdout_93_);
v___x_108_ = lean_box(0);
v___x_109_ = l_Lake_logOutput___redArg___lam__0(v_stderr_94_, v_log_92_, v_inst_90_, v___x_108_);
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput(lean_object* v_m_110_, lean_object* v_inst_111_, lean_object* v_out_112_, lean_object* v_log_113_){
_start:
{
lean_object* v_stdout_114_; lean_object* v_stderr_115_; lean_object* v___f_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v_stdout_114_ = lean_ctor_get(v_out_112_, 0);
lean_inc_ref(v_stdout_114_);
v_stderr_115_ = lean_ctor_get(v_out_112_, 1);
lean_inc_ref(v_stderr_115_);
lean_dec_ref(v_out_112_);
lean_inc_ref(v_inst_111_);
lean_inc(v_log_113_);
lean_inc_ref(v_stderr_115_);
v___f_116_ = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__0), 4, 3);
lean_closure_set(v___f_116_, 0, v_stderr_115_);
lean_closure_set(v___f_116_, 1, v_log_113_);
lean_closure_set(v___f_116_, 2, v_inst_111_);
v___x_117_ = lean_string_utf8_byte_size(v_stdout_114_);
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_nat_dec_eq(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v_toBind_120_; lean_object* v___f_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec_ref(v_stderr_115_);
v_toBind_120_ = lean_ctor_get(v_inst_111_, 1);
lean_inc(v_toBind_120_);
lean_dec_ref(v_inst_111_);
v___f_121_ = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__1), 2, 1);
lean_closure_set(v___f_121_, 0, v___f_116_);
v___x_122_ = ((lean_object*)(l_Lake_logOutput___redArg___closed__0));
v___x_123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_123_, 0, v_stdout_114_);
lean_ctor_set(v___x_123_, 1, v___x_118_);
lean_ctor_set(v___x_123_, 2, v___x_117_);
v___x_124_ = l_String_Slice_trimAscii(v___x_123_);
v___x_125_ = l_String_Slice_toString(v___x_124_);
lean_dec_ref(v___x_124_);
v___x_126_ = lean_string_append(v___x_122_, v___x_125_);
lean_dec_ref(v___x_125_);
v___x_127_ = lean_apply_1(v_log_113_, v___x_126_);
v___x_128_ = lean_apply_4(v_toBind_120_, lean_box(0), lean_box(0), v___x_127_, v___f_121_);
return v___x_128_;
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec_ref(v___f_116_);
lean_dec_ref(v_stdout_114_);
v___x_129_ = lean_box(0);
v___x_130_ = l_Lake_logOutput___redArg___lam__0(v_stderr_115_, v_log_113_, v_inst_111_, v___x_129_);
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0(lean_object* v_args_133_, lean_object* v_____r_134_, lean_object* v___y_135_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_box(0);
lean_inc_ref(v_args_133_);
v___x_138_ = l_IO_Process_output(v_args_133_, v___x_137_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_140_; 
lean_dec_ref(v_args_133_);
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
lean_dec_ref(v___x_138_);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v_a_139_);
lean_ctor_set(v___x_140_, 1, v___y_135_);
return v___x_140_;
}
else
{
lean_object* v_a_141_; lean_object* v_cmd_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_a_141_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_141_);
lean_dec_ref(v___x_138_);
v_cmd_142_ = lean_ctor_get(v_args_133_, 1);
lean_inc_ref(v_cmd_142_);
lean_dec_ref(v_args_133_);
v___x_143_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__0));
v___x_144_ = lean_string_append(v___x_143_, v_cmd_142_);
lean_dec_ref(v_cmd_142_);
v___x_145_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__1));
v___x_146_ = lean_string_append(v___x_144_, v___x_145_);
v___x_147_ = lean_io_error_to_string(v_a_141_);
v___x_148_ = lean_string_append(v___x_146_, v___x_147_);
lean_dec_ref(v___x_147_);
v___x_149_ = 3;
v___x_150_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_150_, 0, v___x_148_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*1, v___x_149_);
v___x_151_ = lean_array_get_size(v___y_135_);
v___x_152_ = lean_array_push(v___y_135_, v___x_150_);
v___x_153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_151_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0___boxed(lean_object* v_args_154_, lean_object* v_____r_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lake_rawProc___lam__0(v_args_154_, v_____r_155_, v___y_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc(lean_object* v_args_159_, uint8_t v_quiet_160_, lean_object* v_a_161_){
_start:
{
lean_object* v___x_163_; lean_object* v___y_165_; 
v___x_163_ = lean_array_get_size(v_a_161_);
if (v_quiet_160_ == 0)
{
lean_object* v___x_175_; uint8_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
lean_inc_ref(v_args_159_);
v___x_175_ = l_Lake_mkCmdLog(v_args_159_);
v___x_176_ = 0;
v___x_177_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_177_, 0, v___x_175_);
lean_ctor_set_uint8(v___x_177_, sizeof(void*)*1, v___x_176_);
v___x_178_ = lean_box(0);
v___x_179_ = lean_array_push(v_a_161_, v___x_177_);
v___x_180_ = l_Lake_rawProc___lam__0(v_args_159_, v___x_178_, v___x_179_);
v___y_165_ = v___x_180_;
goto v___jp_164_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_box(0);
v___x_182_ = l_Lake_rawProc___lam__0(v_args_159_, v___x_181_, v_a_161_);
v___y_165_ = v___x_182_;
goto v___jp_164_;
}
v___jp_164_:
{
if (lean_obj_tag(v___y_165_) == 0)
{
return v___y_165_;
}
else
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
v_a_166_ = lean_ctor_get(v___y_165_, 1);
v_isSharedCheck_173_ = !lean_is_exclusive(v___y_165_);
if (v_isSharedCheck_173_ == 0)
{
lean_object* v_unused_174_; 
v_unused_174_ = lean_ctor_get(v___y_165_, 0);
lean_dec(v_unused_174_);
v___x_168_ = v___y_165_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___y_165_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_163_);
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_a_166_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___boxed(lean_object* v_args_183_, lean_object* v_quiet_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
uint8_t v_quiet_boxed_187_; lean_object* v_res_188_; 
v_quiet_boxed_187_ = lean_unbox(v_quiet_184_);
v_res_188_ = l_Lake_rawProc(v_args_183_, v_quiet_boxed_187_, v_a_185_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__0(uint8_t v_quiet_189_, uint8_t v___x_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
if (v_quiet_189_ == 0)
{
uint8_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_194_ = 1;
v___x_195_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_195_, 0, v___y_191_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*1, v___x_194_);
v___x_196_ = lean_box(0);
v___x_197_ = lean_array_push(v___y_192_, v___x_195_);
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
return v___x_198_;
}
else
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_199_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_199_, 0, v___y_191_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*1, v___x_190_);
v___x_200_ = lean_box(0);
v___x_201_ = lean_array_push(v___y_192_, v___x_199_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_200_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__0___boxed(lean_object* v_quiet_203_, lean_object* v___x_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
uint8_t v_quiet_boxed_208_; uint8_t v___x_5483__boxed_209_; lean_object* v_res_210_; 
v_quiet_boxed_208_ = lean_unbox(v_quiet_203_);
v___x_5483__boxed_209_ = lean_unbox(v___x_204_);
v_res_210_ = l_Lake_proc___lam__0(v_quiet_boxed_208_, v___x_5483__boxed_209_, v___y_205_, v___y_206_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__1(lean_object* v_stderr_211_, lean_object* v___y_212_, lean_object* v_____r_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_216_ = lean_string_utf8_byte_size(v_stderr_211_);
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_nat_dec_eq(v___x_216_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_219_ = ((lean_object*)(l_Lake_logOutput___redArg___lam__0___closed__0));
v___x_220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_220_, 0, v_stderr_211_);
lean_ctor_set(v___x_220_, 1, v___x_217_);
lean_ctor_set(v___x_220_, 2, v___x_216_);
v___x_221_ = l_String_Slice_trimAscii(v___x_220_);
v___x_222_ = l_String_Slice_toString(v___x_221_);
lean_dec_ref(v___x_221_);
v___x_223_ = lean_string_append(v___x_219_, v___x_222_);
lean_dec_ref(v___x_222_);
v___x_224_ = lean_apply_3(v___y_212_, v___x_223_, v___y_214_, lean_box(0));
return v___x_224_;
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec_ref(v___y_212_);
lean_dec_ref(v_stderr_211_);
v___x_225_ = lean_box(0);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___y_214_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__1___boxed(lean_object* v_stderr_227_, lean_object* v___y_228_, lean_object* v_____r_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lake_proc___lam__1(v_stderr_227_, v___y_228_, v_____r_229_, v___y_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lake_proc(lean_object* v_args_235_, uint8_t v_quiet_236_, lean_object* v_a_237_){
_start:
{
lean_object* v___x_239_; lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_239_ = lean_array_get_size(v_a_237_);
lean_inc_ref(v_args_235_);
v___x_243_ = l_Lake_mkCmdLog(v_args_235_);
v___x_244_ = 0;
v___x_245_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*1, v___x_244_);
v___x_246_ = lean_array_push(v_a_237_, v___x_245_);
v___x_247_ = lean_box(0);
lean_inc_ref(v_args_235_);
v___x_248_ = l_IO_Process_output(v_args_235_, v___x_247_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; uint32_t v_exitCode_250_; lean_object* v_stdout_251_; lean_object* v_stderr_252_; lean_object* v___y_254_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___y_281_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref(v___x_248_);
v_exitCode_250_ = lean_ctor_get_uint32(v_a_249_, sizeof(void*)*2);
v_stdout_251_ = lean_ctor_get(v_a_249_, 0);
lean_inc_ref(v_stdout_251_);
v_stderr_252_ = lean_ctor_get(v_a_249_, 1);
lean_inc_ref(v_stderr_252_);
lean_dec(v_a_249_);
v___x_279_ = lean_box(v_quiet_236_);
v___x_280_ = lean_box(v___x_244_);
v___y_281_ = lean_alloc_closure((void*)(l_Lake_proc___lam__0___boxed), 5, 2);
lean_closure_set(v___y_281_, 0, v___x_279_);
lean_closure_set(v___y_281_, 1, v___x_280_);
v___x_282_ = lean_string_utf8_byte_size(v_stdout_251_);
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = lean_nat_dec_eq(v___x_282_, v___x_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_a_291_; lean_object* v_a_292_; lean_object* v___x_293_; 
v___x_285_ = ((lean_object*)(l_Lake_logOutput___redArg___closed__0));
v___x_286_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_286_, 0, v_stdout_251_);
lean_ctor_set(v___x_286_, 1, v___x_283_);
lean_ctor_set(v___x_286_, 2, v___x_282_);
v___x_287_ = l_String_Slice_trimAscii(v___x_286_);
v___x_288_ = l_String_Slice_toString(v___x_287_);
lean_dec_ref(v___x_287_);
v___x_289_ = lean_string_append(v___x_285_, v___x_288_);
lean_dec_ref(v___x_288_);
v___x_290_ = l_Lake_proc___lam__0(v_quiet_236_, v___x_244_, v___x_289_, v___x_246_);
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
v_a_292_ = lean_ctor_get(v___x_290_, 1);
lean_inc(v_a_292_);
lean_dec_ref(v___x_290_);
v___x_293_ = l_Lake_proc___lam__1(v_stderr_252_, v___y_281_, v_a_291_, v_a_292_);
v___y_254_ = v___x_293_;
goto v___jp_253_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec_ref(v_stdout_251_);
v___x_294_ = lean_box(0);
v___x_295_ = l_Lake_proc___lam__1(v_stderr_252_, v___y_281_, v___x_294_, v___x_246_);
v___y_254_ = v___x_295_;
goto v___jp_253_;
}
v___jp_253_:
{
if (lean_obj_tag(v___y_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_276_; 
v_a_255_ = lean_ctor_get(v___y_254_, 1);
v_isSharedCheck_276_ = !lean_is_exclusive(v___y_254_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; 
v_unused_277_ = lean_ctor_get(v___y_254_, 0);
lean_dec(v_unused_277_);
v___x_257_ = v___y_254_;
v_isShared_258_ = v_isSharedCheck_276_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___y_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_276_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
uint32_t v___x_259_; uint8_t v___x_260_; 
v___x_259_ = 0;
v___x_260_ = lean_uint32_dec_eq(v_exitCode_250_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v_cmd_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
lean_del_object(v___x_257_);
v_cmd_261_ = lean_ctor_get(v_args_235_, 1);
lean_inc_ref(v_cmd_261_);
lean_dec_ref(v_args_235_);
v___x_262_ = ((lean_object*)(l_Lake_proc___closed__0));
v___x_263_ = lean_string_append(v___x_262_, v_cmd_261_);
lean_dec_ref(v_cmd_261_);
v___x_264_ = ((lean_object*)(l_Lake_proc___closed__1));
v___x_265_ = lean_string_append(v___x_263_, v___x_264_);
v___x_266_ = lean_uint32_to_nat(v_exitCode_250_);
v___x_267_ = l_Nat_reprFast(v___x_266_);
v___x_268_ = lean_string_append(v___x_265_, v___x_267_);
lean_dec_ref(v___x_267_);
v___x_269_ = 3;
v___x_270_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*1, v___x_269_);
v___x_271_ = lean_array_push(v_a_255_, v___x_270_);
v_a_241_ = v___x_271_;
goto v___jp_240_;
}
else
{
lean_object* v___x_272_; lean_object* v___x_274_; 
lean_dec_ref(v_args_235_);
v___x_272_ = lean_box(0);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v___x_272_);
v___x_274_ = v___x_257_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_a_255_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v_a_278_; 
lean_dec_ref(v_args_235_);
v_a_278_ = lean_ctor_get(v___y_254_, 1);
lean_inc(v_a_278_);
lean_dec_ref(v___y_254_);
v_a_241_ = v_a_278_;
goto v___jp_240_;
}
}
}
else
{
lean_object* v_a_296_; lean_object* v_cmd_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v_a_296_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_296_);
lean_dec_ref(v___x_248_);
v_cmd_297_ = lean_ctor_get(v_args_235_, 1);
lean_inc_ref(v_cmd_297_);
lean_dec_ref(v_args_235_);
v___x_298_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__0));
v___x_299_ = lean_string_append(v___x_298_, v_cmd_297_);
lean_dec_ref(v_cmd_297_);
v___x_300_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__1));
v___x_301_ = lean_string_append(v___x_299_, v___x_300_);
v___x_302_ = lean_io_error_to_string(v_a_296_);
v___x_303_ = lean_string_append(v___x_301_, v___x_302_);
lean_dec_ref(v___x_302_);
v___x_304_ = 3;
v___x_305_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set_uint8(v___x_305_, sizeof(void*)*1, v___x_304_);
v___x_306_ = lean_array_push(v___x_246_, v___x_305_);
v_a_241_ = v___x_306_;
goto v___jp_240_;
}
v___jp_240_:
{
lean_object* v___x_242_; 
v___x_242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_239_);
lean_ctor_set(v___x_242_, 1, v_a_241_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc___boxed(lean_object* v_args_307_, lean_object* v_quiet_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
uint8_t v_quiet_boxed_311_; lean_object* v_res_312_; 
v_quiet_boxed_311_ = lean_unbox(v_quiet_308_);
v_res_312_ = l_Lake_proc(v_args_307_, v_quiet_boxed_311_, v_a_309_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x27___lam__0(lean_object* v_stderr_313_, lean_object* v_____r_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_317_ = lean_string_utf8_byte_size(v_stderr_313_);
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_nat_dec_eq(v___x_317_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_320_ = ((lean_object*)(l_Lake_logOutput___redArg___lam__0___closed__0));
v___x_321_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_321_, 0, v_stderr_313_);
lean_ctor_set(v___x_321_, 1, v___x_318_);
lean_ctor_set(v___x_321_, 2, v___x_317_);
v___x_322_ = l_String_Slice_trimAscii(v___x_321_);
v___x_323_ = l_String_Slice_toString(v___x_322_);
lean_dec_ref(v___x_322_);
v___x_324_ = lean_string_append(v___x_320_, v___x_323_);
lean_dec_ref(v___x_323_);
v___x_325_ = 1;
v___x_326_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_326_, 0, v___x_324_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*1, v___x_325_);
v___x_327_ = lean_box(0);
v___x_328_ = lean_array_push(v___y_315_, v___x_326_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
return v___x_329_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec_ref(v_stderr_313_);
v___x_330_ = lean_box(0);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___y_315_);
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x27___lam__0___boxed(lean_object* v_stderr_332_, lean_object* v_____r_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lake_captureProc_x27___lam__0(v_stderr_332_, v_____r_333_, v___y_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x27(lean_object* v_args_337_, lean_object* v_a_338_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_box(0);
lean_inc_ref(v_args_337_);
v___x_341_ = l_IO_Process_output(v_args_337_, v___x_340_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; uint32_t v_exitCode_343_; lean_object* v_stdout_344_; lean_object* v_stderr_345_; uint32_t v___x_346_; uint8_t v___x_347_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref(v___x_341_);
v_exitCode_343_ = lean_ctor_get_uint32(v_a_342_, sizeof(void*)*2);
v_stdout_344_ = lean_ctor_get(v_a_342_, 0);
v_stderr_345_ = lean_ctor_get(v_a_342_, 1);
v___x_346_ = 0;
v___x_347_ = lean_uint32_dec_eq(v_exitCode_343_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; uint8_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v_a_353_; lean_object* v___y_356_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
lean_inc_ref(v_stderr_345_);
lean_inc_ref(v_stdout_344_);
lean_dec(v_a_342_);
lean_inc_ref(v_args_337_);
v___x_348_ = l_Lake_mkCmdLog(v_args_337_);
v___x_349_ = 0;
v___x_350_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set_uint8(v___x_350_, sizeof(void*)*1, v___x_349_);
v___x_351_ = lean_array_get_size(v_a_338_);
v___x_370_ = lean_array_push(v_a_338_, v___x_350_);
v___x_371_ = lean_string_utf8_byte_size(v_stdout_344_);
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = lean_nat_dec_eq(v___x_371_, v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_374_ = ((lean_object*)(l_Lake_logOutput___redArg___closed__0));
v___x_375_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_375_, 0, v_stdout_344_);
lean_ctor_set(v___x_375_, 1, v___x_372_);
lean_ctor_set(v___x_375_, 2, v___x_371_);
v___x_376_ = l_String_Slice_trimAscii(v___x_375_);
v___x_377_ = l_String_Slice_toString(v___x_376_);
lean_dec_ref(v___x_376_);
v___x_378_ = lean_string_append(v___x_374_, v___x_377_);
lean_dec_ref(v___x_377_);
v___x_379_ = 1;
v___x_380_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set_uint8(v___x_380_, sizeof(void*)*1, v___x_379_);
v___x_381_ = lean_box(0);
v___x_382_ = lean_array_push(v___x_370_, v___x_380_);
v___x_383_ = l_Lake_captureProc_x27___lam__0(v_stderr_345_, v___x_381_, v___x_382_);
v___y_356_ = v___x_383_;
goto v___jp_355_;
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec_ref(v_stdout_344_);
v___x_384_ = lean_box(0);
v___x_385_ = l_Lake_captureProc_x27___lam__0(v_stderr_345_, v___x_384_, v___x_370_);
v___y_356_ = v___x_385_;
goto v___jp_355_;
}
v___jp_352_:
{
lean_object* v___x_354_; 
v___x_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_351_);
lean_ctor_set(v___x_354_, 1, v_a_353_);
return v___x_354_;
}
v___jp_355_:
{
if (lean_obj_tag(v___y_356_) == 0)
{
lean_object* v_a_357_; lean_object* v_cmd_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_a_357_ = lean_ctor_get(v___y_356_, 1);
lean_inc(v_a_357_);
lean_dec_ref(v___y_356_);
v_cmd_358_ = lean_ctor_get(v_args_337_, 1);
lean_inc_ref(v_cmd_358_);
lean_dec_ref(v_args_337_);
v___x_359_ = ((lean_object*)(l_Lake_proc___closed__0));
v___x_360_ = lean_string_append(v___x_359_, v_cmd_358_);
lean_dec_ref(v_cmd_358_);
v___x_361_ = ((lean_object*)(l_Lake_proc___closed__1));
v___x_362_ = lean_string_append(v___x_360_, v___x_361_);
v___x_363_ = lean_uint32_to_nat(v_exitCode_343_);
v___x_364_ = l_Nat_reprFast(v___x_363_);
v___x_365_ = lean_string_append(v___x_362_, v___x_364_);
lean_dec_ref(v___x_364_);
v___x_366_ = 3;
v___x_367_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_367_, 0, v___x_365_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*1, v___x_366_);
v___x_368_ = lean_array_push(v_a_357_, v___x_367_);
v_a_353_ = v___x_368_;
goto v___jp_352_;
}
else
{
lean_object* v_a_369_; 
lean_dec_ref(v_args_337_);
v_a_369_ = lean_ctor_get(v___y_356_, 1);
lean_inc(v_a_369_);
lean_dec_ref(v___y_356_);
v_a_353_ = v_a_369_;
goto v___jp_352_;
}
}
}
else
{
lean_object* v___x_386_; 
lean_dec_ref(v_args_337_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_a_342_);
lean_ctor_set(v___x_386_, 1, v_a_338_);
return v___x_386_;
}
}
else
{
lean_object* v_a_387_; lean_object* v_cmd_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_a_387_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_387_);
lean_dec_ref(v___x_341_);
v_cmd_388_ = lean_ctor_get(v_args_337_, 1);
lean_inc_ref(v_cmd_388_);
lean_dec_ref(v_args_337_);
v___x_389_ = lean_array_get_size(v_a_338_);
v___x_390_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__0));
v___x_391_ = lean_string_append(v___x_390_, v_cmd_388_);
lean_dec_ref(v_cmd_388_);
v___x_392_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__1));
v___x_393_ = lean_string_append(v___x_391_, v___x_392_);
v___x_394_ = lean_io_error_to_string(v_a_387_);
v___x_395_ = lean_string_append(v___x_393_, v___x_394_);
lean_dec_ref(v___x_394_);
v___x_396_ = 3;
v___x_397_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*1, v___x_396_);
v___x_398_ = lean_array_push(v_a_338_, v___x_397_);
v___x_399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_389_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
return v___x_399_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x27___boxed(lean_object* v_args_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lake_captureProc_x27(v_args_400_, v_a_401_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc(lean_object* v_args_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lake_captureProc_x27(v_args_404_, v_a_405_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_425_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_a_409_ = lean_ctor_get(v___x_407_, 1);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_425_ == 0)
{
v___x_411_ = v___x_407_;
v_isShared_412_ = v_isSharedCheck_425_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_425_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v_stdout_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v_str_418_; lean_object* v_startInclusive_419_; lean_object* v_endExclusive_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v_stdout_413_ = lean_ctor_get(v_a_408_, 0);
lean_inc_ref(v_stdout_413_);
lean_dec(v_a_408_);
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = lean_string_utf8_byte_size(v_stdout_413_);
v___x_416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_416_, 0, v_stdout_413_);
lean_ctor_set(v___x_416_, 1, v___x_414_);
lean_ctor_set(v___x_416_, 2, v___x_415_);
v___x_417_ = l_String_Slice_trimAscii(v___x_416_);
v_str_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc_ref(v_str_418_);
v_startInclusive_419_ = lean_ctor_get(v___x_417_, 1);
lean_inc(v_startInclusive_419_);
v_endExclusive_420_ = lean_ctor_get(v___x_417_, 2);
lean_inc(v_endExclusive_420_);
lean_dec_ref(v___x_417_);
v___x_421_ = lean_string_utf8_extract(v_str_418_, v_startInclusive_419_, v_endExclusive_420_);
lean_dec(v_endExclusive_420_);
lean_dec(v_startInclusive_419_);
lean_dec_ref(v_str_418_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_421_);
v___x_423_ = v___x_411_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_a_409_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
else
{
lean_object* v_a_426_; lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
v_a_426_ = lean_ctor_get(v___x_407_, 0);
v_a_427_ = lean_ctor_get(v___x_407_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_407_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_inc(v_a_426_);
lean_dec(v___x_407_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_426_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc___boxed(lean_object* v_args_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lake_captureProc(v_args_435_, v_a_436_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f(lean_object* v_args_439_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_box(0);
v___x_442_ = l_IO_Process_output(v_args_439_, v___x_441_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_462_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_462_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_462_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_462_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
uint32_t v_exitCode_447_; lean_object* v_stdout_448_; uint32_t v___x_449_; uint8_t v___x_450_; 
v_exitCode_447_ = lean_ctor_get_uint32(v_a_443_, sizeof(void*)*2);
v_stdout_448_ = lean_ctor_get(v_a_443_, 0);
lean_inc_ref(v_stdout_448_);
lean_dec(v_a_443_);
v___x_449_ = 0;
v___x_450_ = lean_uint32_dec_eq(v_exitCode_447_, v___x_449_);
if (v___x_450_ == 0)
{
lean_dec_ref(v_stdout_448_);
lean_del_object(v___x_445_);
return v___x_441_;
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v_str_455_; lean_object* v_startInclusive_456_; lean_object* v_endExclusive_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_string_utf8_byte_size(v_stdout_448_);
v___x_453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_453_, 0, v_stdout_448_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
lean_ctor_set(v___x_453_, 2, v___x_452_);
v___x_454_ = l_String_Slice_trimAscii(v___x_453_);
v_str_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc_ref(v_str_455_);
v_startInclusive_456_ = lean_ctor_get(v___x_454_, 1);
lean_inc(v_startInclusive_456_);
v_endExclusive_457_ = lean_ctor_get(v___x_454_, 2);
lean_inc(v_endExclusive_457_);
lean_dec_ref(v___x_454_);
v___x_458_ = lean_string_utf8_extract(v_str_455_, v_startInclusive_456_, v_endExclusive_457_);
lean_dec(v_endExclusive_457_);
lean_dec(v_startInclusive_456_);
lean_dec_ref(v_str_455_);
if (v_isShared_446_ == 0)
{
lean_ctor_set_tag(v___x_445_, 1);
lean_ctor_set(v___x_445_, 0, v___x_458_);
v___x_460_ = v___x_445_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_dec_ref(v___x_442_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f___boxed(lean_object* v_args_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lake_captureProc_x3f(v_args_463_);
return v_res_465_;
}
}
LEAN_EXPORT uint8_t l_Lake_testProc(lean_object* v_args_468_){
_start:
{
lean_object* v___x_472_; lean_object* v_cmd_473_; lean_object* v_args_474_; lean_object* v_cwd_475_; lean_object* v_env_476_; uint8_t v_inheritEnv_477_; uint8_t v_setsid_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_492_; 
v___x_472_ = ((lean_object*)(l_Lake_testProc___closed__0));
v_cmd_473_ = lean_ctor_get(v_args_468_, 1);
v_args_474_ = lean_ctor_get(v_args_468_, 2);
v_cwd_475_ = lean_ctor_get(v_args_468_, 3);
v_env_476_ = lean_ctor_get(v_args_468_, 4);
v_inheritEnv_477_ = lean_ctor_get_uint8(v_args_468_, sizeof(void*)*5);
v_setsid_478_ = lean_ctor_get_uint8(v_args_468_, sizeof(void*)*5 + 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v_args_468_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; 
v_unused_493_ = lean_ctor_get(v_args_468_, 0);
lean_dec(v_unused_493_);
v___x_480_ = v_args_468_;
v_isShared_481_ = v_isSharedCheck_492_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_env_476_);
lean_inc(v_cwd_475_);
lean_inc(v_args_474_);
lean_inc(v_cmd_473_);
lean_dec(v_args_468_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_492_;
goto v_resetjp_479_;
}
v___jp_470_:
{
uint8_t v___x_471_; 
v___x_471_ = 0;
return v___x_471_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_472_);
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_cmd_473_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_args_474_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_cwd_475_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v_env_476_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*5, v_inheritEnv_477_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*5 + 1, v_setsid_478_);
v___x_483_ = v_reuseFailAlloc_491_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; 
v___x_484_ = lean_io_process_spawn(v___x_483_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_486_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref(v___x_484_);
v___x_486_ = lean_io_process_child_wait(v___x_472_, v_a_485_);
lean_dec(v_a_485_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; uint32_t v___x_488_; uint32_t v___x_489_; uint8_t v___x_490_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref(v___x_486_);
v___x_488_ = 0;
v___x_489_ = lean_unbox_uint32(v_a_487_);
lean_dec(v_a_487_);
v___x_490_ = lean_uint32_dec_eq(v___x_489_, v___x_488_);
return v___x_490_;
}
else
{
lean_dec_ref(v___x_486_);
goto v___jp_470_;
}
}
else
{
lean_dec_ref(v___x_484_);
goto v___jp_470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_testProc___boxed(lean_object* v_args_494_, lean_object* v_a_495_){
_start:
{
uint8_t v_res_496_; lean_object* v_r_497_; 
v_res_496_ = l_Lake_testProc(v_args_494_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
lean_object* runtime_initialize_Lake_Util_Log(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Proc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Util_Log(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Proc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Proc(builtin);
}
#ifdef __cplusplus
}
#endif
