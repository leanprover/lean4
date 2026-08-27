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
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_proc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "external command '"};
static const lean_object* l_Lake_proc___closed__0 = (const lean_object*)&l_Lake_proc___closed__0_value;
static const lean_string_object l_Lake_proc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "' exited with code "};
static const lean_object* l_Lake_proc___closed__1 = (const lean_object*)&l_Lake_proc___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_snd_21_, 1);
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
lean_dec_ref_known(v_cwd_49_, 1);
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
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg___lam__0(lean_object* v_stderr_69_, lean_object* v_log_70_, lean_object* v_toPure_71_, lean_object* v_____r_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_73_ = lean_string_utf8_byte_size(v_stderr_69_);
v___x_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = lean_nat_dec_eq(v___x_73_, v___x_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec(v_toPure_71_);
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
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v_log_70_);
lean_dec_ref(v_stderr_69_);
v___x_82_ = lean_box(0);
v___x_83_ = lean_apply_2(v_toPure_71_, lean_box(0), v___x_82_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg___lam__1(lean_object* v___f_84_, lean_object* v_____r_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_apply_1(v___f_84_, v_____r_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg(lean_object* v_inst_88_, lean_object* v_out_89_, lean_object* v_log_90_){
_start:
{
lean_object* v_toApplicative_91_; lean_object* v_toBind_92_; lean_object* v_toPure_93_; lean_object* v_stdout_94_; lean_object* v_stderr_95_; lean_object* v___f_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v_toApplicative_91_ = lean_ctor_get(v_inst_88_, 0);
lean_inc_ref(v_toApplicative_91_);
v_toBind_92_ = lean_ctor_get(v_inst_88_, 1);
lean_inc(v_toBind_92_);
lean_dec_ref(v_inst_88_);
v_toPure_93_ = lean_ctor_get(v_toApplicative_91_, 1);
lean_inc_n(v_toPure_93_, 2);
lean_dec_ref(v_toApplicative_91_);
v_stdout_94_ = lean_ctor_get(v_out_89_, 0);
lean_inc_ref(v_stdout_94_);
v_stderr_95_ = lean_ctor_get(v_out_89_, 1);
lean_inc_ref_n(v_stderr_95_, 2);
lean_dec_ref(v_out_89_);
lean_inc(v_log_90_);
v___f_96_ = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__0), 4, 3);
lean_closure_set(v___f_96_, 0, v_stderr_95_);
lean_closure_set(v___f_96_, 1, v_log_90_);
lean_closure_set(v___f_96_, 2, v_toPure_93_);
v___x_97_ = lean_string_utf8_byte_size(v_stdout_94_);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_nat_dec_eq(v___x_97_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___f_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
lean_dec_ref(v_stderr_95_);
lean_dec(v_toPure_93_);
v___f_100_ = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__1), 2, 1);
lean_closure_set(v___f_100_, 0, v___f_96_);
v___x_101_ = ((lean_object*)(l_Lake_logOutput___redArg___closed__0));
v___x_102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_102_, 0, v_stdout_94_);
lean_ctor_set(v___x_102_, 1, v___x_98_);
lean_ctor_set(v___x_102_, 2, v___x_97_);
v___x_103_ = l_String_Slice_trimAscii(v___x_102_);
v___x_104_ = l_String_Slice_toString(v___x_103_);
lean_dec_ref(v___x_103_);
v___x_105_ = lean_string_append(v___x_101_, v___x_104_);
lean_dec_ref(v___x_104_);
v___x_106_ = lean_apply_1(v_log_90_, v___x_105_);
v___x_107_ = lean_apply_4(v_toBind_92_, lean_box(0), lean_box(0), v___x_106_, v___f_100_);
return v___x_107_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec_ref(v___f_96_);
lean_dec_ref(v_stdout_94_);
lean_dec(v_toBind_92_);
v___x_108_ = lean_box(0);
v___x_109_ = l_Lake_logOutput___redArg___lam__0(v_stderr_95_, v_log_90_, v_toPure_93_, v___x_108_);
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput(lean_object* v_m_110_, lean_object* v_inst_111_, lean_object* v_out_112_, lean_object* v_log_113_){
_start:
{
lean_object* v_toApplicative_114_; lean_object* v_toBind_115_; lean_object* v_toPure_116_; lean_object* v_stdout_117_; lean_object* v_stderr_118_; lean_object* v___f_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v_toApplicative_114_ = lean_ctor_get(v_inst_111_, 0);
lean_inc_ref(v_toApplicative_114_);
v_toBind_115_ = lean_ctor_get(v_inst_111_, 1);
lean_inc(v_toBind_115_);
lean_dec_ref(v_inst_111_);
v_toPure_116_ = lean_ctor_get(v_toApplicative_114_, 1);
lean_inc_n(v_toPure_116_, 2);
lean_dec_ref(v_toApplicative_114_);
v_stdout_117_ = lean_ctor_get(v_out_112_, 0);
lean_inc_ref(v_stdout_117_);
v_stderr_118_ = lean_ctor_get(v_out_112_, 1);
lean_inc_ref_n(v_stderr_118_, 2);
lean_dec_ref(v_out_112_);
lean_inc(v_log_113_);
v___f_119_ = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__0), 4, 3);
lean_closure_set(v___f_119_, 0, v_stderr_118_);
lean_closure_set(v___f_119_, 1, v_log_113_);
lean_closure_set(v___f_119_, 2, v_toPure_116_);
v___x_120_ = lean_string_utf8_byte_size(v_stdout_117_);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_nat_dec_eq(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___f_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec_ref(v_stderr_118_);
lean_dec(v_toPure_116_);
v___f_123_ = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__1), 2, 1);
lean_closure_set(v___f_123_, 0, v___f_119_);
v___x_124_ = ((lean_object*)(l_Lake_logOutput___redArg___closed__0));
v___x_125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_125_, 0, v_stdout_117_);
lean_ctor_set(v___x_125_, 1, v___x_121_);
lean_ctor_set(v___x_125_, 2, v___x_120_);
v___x_126_ = l_String_Slice_trimAscii(v___x_125_);
v___x_127_ = l_String_Slice_toString(v___x_126_);
lean_dec_ref(v___x_126_);
v___x_128_ = lean_string_append(v___x_124_, v___x_127_);
lean_dec_ref(v___x_127_);
v___x_129_ = lean_apply_1(v_log_113_, v___x_128_);
v___x_130_ = lean_apply_4(v_toBind_115_, lean_box(0), lean_box(0), v___x_129_, v___f_123_);
return v___x_130_;
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; 
lean_dec_ref(v___f_119_);
lean_dec_ref(v_stdout_117_);
lean_dec(v_toBind_115_);
v___x_131_ = lean_box(0);
v___x_132_ = l_Lake_logOutput___redArg___lam__0(v_stderr_118_, v_log_113_, v_toPure_116_, v___x_131_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0(lean_object* v_args_135_, lean_object* v_input_x3f_136_, lean_object* v_____r_137_, lean_object* v___y_138_){
_start:
{
lean_object* v___x_140_; 
lean_inc_ref(v_args_135_);
v___x_140_ = l_IO_Process_output(v_args_135_, v_input_x3f_136_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_142_; 
lean_dec_ref(v_args_135_);
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_a_141_);
lean_dec_ref_known(v___x_140_, 1);
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v_a_141_);
lean_ctor_set(v___x_142_, 1, v___y_138_);
return v___x_142_;
}
else
{
lean_object* v_a_143_; lean_object* v_cmd_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_a_143_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_a_143_);
lean_dec_ref_known(v___x_140_, 1);
v_cmd_144_ = lean_ctor_get(v_args_135_, 1);
lean_inc_ref(v_cmd_144_);
lean_dec_ref(v_args_135_);
v___x_145_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__0));
v___x_146_ = lean_string_append(v___x_145_, v_cmd_144_);
lean_dec_ref(v_cmd_144_);
v___x_147_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__1));
v___x_148_ = lean_string_append(v___x_146_, v___x_147_);
v___x_149_ = lean_io_error_to_string(v_a_143_);
v___x_150_ = lean_string_append(v___x_148_, v___x_149_);
lean_dec_ref(v___x_149_);
v___x_151_ = 3;
v___x_152_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*1, v___x_151_);
v___x_153_ = lean_array_get_size(v___y_138_);
v___x_154_ = lean_array_push(v___y_138_, v___x_152_);
v___x_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_153_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0___boxed(lean_object* v_args_156_, lean_object* v_input_x3f_157_, lean_object* v_____r_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lake_rawProc___lam__0(v_args_156_, v_input_x3f_157_, v_____r_158_, v___y_159_);
lean_dec(v_input_x3f_157_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc(lean_object* v_args_162_, uint8_t v_quiet_163_, lean_object* v_input_x3f_164_, lean_object* v_a_165_){
_start:
{
lean_object* v___x_167_; lean_object* v___y_169_; 
v___x_167_ = lean_array_get_size(v_a_165_);
if (v_quiet_163_ == 0)
{
lean_object* v___x_179_; uint8_t v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
lean_inc_ref(v_args_162_);
v___x_179_ = l_Lake_mkCmdLog(v_args_162_);
v___x_180_ = 0;
v___x_181_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*1, v___x_180_);
v___x_182_ = lean_box(0);
v___x_183_ = lean_array_push(v_a_165_, v___x_181_);
v___x_184_ = l_Lake_rawProc___lam__0(v_args_162_, v_input_x3f_164_, v___x_182_, v___x_183_);
v___y_169_ = v___x_184_;
goto v___jp_168_;
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_box(0);
v___x_186_ = l_Lake_rawProc___lam__0(v_args_162_, v_input_x3f_164_, v___x_185_, v_a_165_);
v___y_169_ = v___x_186_;
goto v___jp_168_;
}
v___jp_168_:
{
if (lean_obj_tag(v___y_169_) == 0)
{
return v___y_169_;
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
v_a_170_ = lean_ctor_get(v___y_169_, 1);
v_isSharedCheck_177_ = !lean_is_exclusive(v___y_169_);
if (v_isSharedCheck_177_ == 0)
{
lean_object* v_unused_178_; 
v_unused_178_ = lean_ctor_get(v___y_169_, 0);
lean_dec(v_unused_178_);
v___x_172_ = v___y_169_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___y_169_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_167_);
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___boxed(lean_object* v_args_187_, lean_object* v_quiet_188_, lean_object* v_input_x3f_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
uint8_t v_quiet_boxed_192_; lean_object* v_res_193_; 
v_quiet_boxed_192_ = lean_unbox(v_quiet_188_);
v_res_193_ = l_Lake_rawProc(v_args_187_, v_quiet_boxed_192_, v_input_x3f_189_, v_a_190_);
lean_dec(v_input_x3f_189_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__0(lean_object* v_stderr_194_, lean_object* v_____r_195_, lean_object* v___y_196_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_198_ = lean_string_utf8_byte_size(v_stderr_194_);
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = lean_nat_dec_eq(v___x_198_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_201_ = ((lean_object*)(l_Lake_logOutput___redArg___lam__0___closed__0));
v___x_202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_202_, 0, v_stderr_194_);
lean_ctor_set(v___x_202_, 1, v___x_199_);
lean_ctor_set(v___x_202_, 2, v___x_198_);
v___x_203_ = l_String_Slice_trimAscii(v___x_202_);
v___x_204_ = l_String_Slice_toString(v___x_203_);
lean_dec_ref(v___x_203_);
v___x_205_ = lean_string_append(v___x_201_, v___x_204_);
lean_dec_ref(v___x_204_);
v___x_206_ = 1;
v___x_207_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set_uint8(v___x_207_, sizeof(void*)*1, v___x_206_);
v___x_208_ = lean_box(0);
v___x_209_ = lean_array_push(v___y_196_, v___x_207_);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
return v___x_210_;
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec_ref(v_stderr_194_);
v___x_211_ = lean_box(0);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___y_196_);
return v___x_212_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__0___boxed(lean_object* v_stderr_213_, lean_object* v_____r_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lake_proc___lam__0(v_stderr_213_, v_____r_214_, v___y_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__1(uint8_t v_quiet_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
if (v_quiet_218_ == 0)
{
uint8_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_222_ = 1;
v___x_223_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_223_, 0, v___y_219_);
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*1, v___x_222_);
v___x_224_ = lean_box(0);
v___x_225_ = lean_array_push(v___y_220_, v___x_223_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
return v___x_226_;
}
else
{
uint8_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_227_ = 0;
v___x_228_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_228_, 0, v___y_219_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*1, v___x_227_);
v___x_229_ = lean_box(0);
v___x_230_ = lean_array_push(v___y_220_, v___x_228_);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
return v___x_231_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__1___boxed(lean_object* v_quiet_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
uint8_t v_quiet_boxed_236_; lean_object* v_res_237_; 
v_quiet_boxed_236_ = lean_unbox(v_quiet_232_);
v_res_237_ = l_Lake_proc___lam__1(v_quiet_boxed_236_, v___y_233_, v___y_234_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__2(lean_object* v_stderr_238_, lean_object* v___y_239_, lean_object* v_____r_240_, lean_object* v___y_241_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_243_ = lean_string_utf8_byte_size(v_stderr_238_);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_nat_dec_eq(v___x_243_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_246_ = ((lean_object*)(l_Lake_logOutput___redArg___lam__0___closed__0));
v___x_247_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_247_, 0, v_stderr_238_);
lean_ctor_set(v___x_247_, 1, v___x_244_);
lean_ctor_set(v___x_247_, 2, v___x_243_);
v___x_248_ = l_String_Slice_trimAscii(v___x_247_);
v___x_249_ = l_String_Slice_toString(v___x_248_);
lean_dec_ref(v___x_248_);
v___x_250_ = lean_string_append(v___x_246_, v___x_249_);
lean_dec_ref(v___x_249_);
v___x_251_ = lean_apply_3(v___y_239_, v___x_250_, v___y_241_, lean_box(0));
return v___x_251_;
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec_ref(v___y_239_);
lean_dec_ref(v_stderr_238_);
v___x_252_ = lean_box(0);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___y_241_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__2___boxed(lean_object* v_stderr_254_, lean_object* v___y_255_, lean_object* v_____r_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lake_proc___lam__2(v_stderr_254_, v___y_255_, v_____r_256_, v___y_257_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lake_proc(lean_object* v_args_262_, uint8_t v_quiet_263_, lean_object* v_input_x3f_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___x_267_; lean_object* v_a_269_; lean_object* v___y_272_; lean_object* v___x_274_; uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_267_ = lean_array_get_size(v_a_265_);
lean_inc_ref_n(v_args_262_, 2);
v___x_274_ = l_Lake_mkCmdLog(v_args_262_);
v___x_275_ = 0;
v___x_276_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_276_, 0, v___x_274_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*1, v___x_275_);
v___x_277_ = lean_array_push(v_a_265_, v___x_276_);
v___x_278_ = l_IO_Process_output(v_args_262_, v_input_x3f_264_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; uint32_t v_exitCode_280_; lean_object* v_stdout_281_; lean_object* v_stderr_282_; lean_object* v___y_284_; uint32_t v___x_298_; uint8_t v___x_299_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_279_);
lean_dec_ref_known(v___x_278_, 1);
v_exitCode_280_ = lean_ctor_get_uint32(v_a_279_, sizeof(void*)*2);
v_stdout_281_ = lean_ctor_get(v_a_279_, 0);
lean_inc_ref(v_stdout_281_);
v_stderr_282_ = lean_ctor_get(v_a_279_, 1);
lean_inc_ref(v_stderr_282_);
lean_dec(v_a_279_);
v___x_298_ = 0;
v___x_299_ = lean_uint32_dec_eq(v_exitCode_280_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_300_ = lean_string_utf8_byte_size(v_stdout_281_);
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = lean_nat_dec_eq(v___x_300_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_303_ = ((lean_object*)(l_Lake_logOutput___redArg___closed__0));
v___x_304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_304_, 0, v_stdout_281_);
lean_ctor_set(v___x_304_, 1, v___x_301_);
lean_ctor_set(v___x_304_, 2, v___x_300_);
v___x_305_ = l_String_Slice_trimAscii(v___x_304_);
v___x_306_ = l_String_Slice_toString(v___x_305_);
lean_dec_ref(v___x_305_);
v___x_307_ = lean_string_append(v___x_303_, v___x_306_);
lean_dec_ref(v___x_306_);
v___x_308_ = 1;
v___x_309_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set_uint8(v___x_309_, sizeof(void*)*1, v___x_308_);
v___x_310_ = lean_box(0);
v___x_311_ = lean_array_push(v___x_277_, v___x_309_);
v___x_312_ = l_Lake_proc___lam__0(v_stderr_282_, v___x_310_, v___x_311_);
v___y_284_ = v___x_312_;
goto v___jp_283_;
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec_ref(v_stdout_281_);
v___x_313_ = lean_box(0);
v___x_314_ = l_Lake_proc___lam__0(v_stderr_282_, v___x_313_, v___x_277_);
v___y_284_ = v___x_314_;
goto v___jp_283_;
}
}
else
{
lean_object* v___x_315_; lean_object* v___y_316_; lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
lean_dec_ref(v_args_262_);
v___x_315_ = lean_box(v_quiet_263_);
v___y_316_ = lean_alloc_closure((void*)(l_Lake_proc___lam__1___boxed), 4, 1);
lean_closure_set(v___y_316_, 0, v___x_315_);
v___x_317_ = lean_string_utf8_byte_size(v_stdout_281_);
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_nat_dec_eq(v___x_317_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_a_326_; lean_object* v_a_327_; lean_object* v___x_328_; 
v___x_320_ = ((lean_object*)(l_Lake_logOutput___redArg___closed__0));
v___x_321_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_321_, 0, v_stdout_281_);
lean_ctor_set(v___x_321_, 1, v___x_318_);
lean_ctor_set(v___x_321_, 2, v___x_317_);
v___x_322_ = l_String_Slice_trimAscii(v___x_321_);
v___x_323_ = l_String_Slice_toString(v___x_322_);
lean_dec_ref(v___x_322_);
v___x_324_ = lean_string_append(v___x_320_, v___x_323_);
lean_dec_ref(v___x_323_);
v___x_325_ = l_Lake_proc___lam__1(v_quiet_263_, v___x_324_, v___x_277_);
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
v_a_327_ = lean_ctor_get(v___x_325_, 1);
lean_inc(v_a_327_);
lean_dec_ref(v___x_325_);
v___x_328_ = l_Lake_proc___lam__2(v_stderr_282_, v___y_316_, v_a_326_, v_a_327_);
v___y_272_ = v___x_328_;
goto v___jp_271_;
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec_ref(v_stdout_281_);
v___x_329_ = lean_box(0);
v___x_330_ = l_Lake_proc___lam__2(v_stderr_282_, v___y_316_, v___x_329_, v___x_277_);
v___y_272_ = v___x_330_;
goto v___jp_271_;
}
}
v___jp_283_:
{
if (lean_obj_tag(v___y_284_) == 0)
{
lean_object* v_a_285_; lean_object* v_cmd_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_a_285_ = lean_ctor_get(v___y_284_, 1);
lean_inc(v_a_285_);
lean_dec_ref_known(v___y_284_, 2);
v_cmd_286_ = lean_ctor_get(v_args_262_, 1);
lean_inc_ref(v_cmd_286_);
lean_dec_ref(v_args_262_);
v___x_287_ = ((lean_object*)(l_Lake_proc___closed__0));
v___x_288_ = lean_string_append(v___x_287_, v_cmd_286_);
lean_dec_ref(v_cmd_286_);
v___x_289_ = ((lean_object*)(l_Lake_proc___closed__1));
v___x_290_ = lean_string_append(v___x_288_, v___x_289_);
v___x_291_ = lean_uint32_to_nat(v_exitCode_280_);
v___x_292_ = l_Nat_reprFast(v___x_291_);
v___x_293_ = lean_string_append(v___x_290_, v___x_292_);
lean_dec_ref(v___x_292_);
v___x_294_ = 3;
v___x_295_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set_uint8(v___x_295_, sizeof(void*)*1, v___x_294_);
v___x_296_ = lean_array_push(v_a_285_, v___x_295_);
v_a_269_ = v___x_296_;
goto v___jp_268_;
}
else
{
lean_object* v_a_297_; 
lean_dec_ref(v_args_262_);
v_a_297_ = lean_ctor_get(v___y_284_, 1);
lean_inc(v_a_297_);
lean_dec_ref_known(v___y_284_, 2);
v_a_269_ = v_a_297_;
goto v___jp_268_;
}
}
}
else
{
lean_object* v_a_331_; lean_object* v_cmd_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_a_331_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_278_, 1);
v_cmd_332_ = lean_ctor_get(v_args_262_, 1);
lean_inc_ref(v_cmd_332_);
lean_dec_ref(v_args_262_);
v___x_333_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__0));
v___x_334_ = lean_string_append(v___x_333_, v_cmd_332_);
lean_dec_ref(v_cmd_332_);
v___x_335_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__1));
v___x_336_ = lean_string_append(v___x_334_, v___x_335_);
v___x_337_ = lean_io_error_to_string(v_a_331_);
v___x_338_ = lean_string_append(v___x_336_, v___x_337_);
lean_dec_ref(v___x_337_);
v___x_339_ = 3;
v___x_340_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_340_, 0, v___x_338_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*1, v___x_339_);
v___x_341_ = lean_array_push(v___x_277_, v___x_340_);
v_a_269_ = v___x_341_;
goto v___jp_268_;
}
v___jp_268_:
{
lean_object* v___x_270_; 
v___x_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_267_);
lean_ctor_set(v___x_270_, 1, v_a_269_);
return v___x_270_;
}
v___jp_271_:
{
if (lean_obj_tag(v___y_272_) == 0)
{
return v___y_272_;
}
else
{
lean_object* v_a_273_; 
v_a_273_ = lean_ctor_get(v___y_272_, 1);
lean_inc(v_a_273_);
lean_dec_ref_known(v___y_272_, 2);
v_a_269_ = v_a_273_;
goto v___jp_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc___boxed(lean_object* v_args_342_, lean_object* v_quiet_343_, lean_object* v_input_x3f_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
uint8_t v_quiet_boxed_347_; lean_object* v_res_348_; 
v_quiet_boxed_347_ = lean_unbox(v_quiet_343_);
v_res_348_ = l_Lake_proc(v_args_342_, v_quiet_boxed_347_, v_input_x3f_344_, v_a_345_);
lean_dec(v_input_x3f_344_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x27(lean_object* v_args_349_, lean_object* v_a_350_){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_box(0);
lean_inc_ref(v_args_349_);
v___x_353_ = l_IO_Process_output(v_args_349_, v___x_352_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; uint32_t v_exitCode_355_; lean_object* v_stdout_356_; lean_object* v_stderr_357_; uint32_t v___x_358_; uint8_t v___x_359_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_354_);
lean_dec_ref_known(v___x_353_, 1);
v_exitCode_355_ = lean_ctor_get_uint32(v_a_354_, sizeof(void*)*2);
v_stdout_356_ = lean_ctor_get(v_a_354_, 0);
v_stderr_357_ = lean_ctor_get(v_a_354_, 1);
v___x_358_ = 0;
v___x_359_ = lean_uint32_dec_eq(v_exitCode_355_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v_a_365_; lean_object* v___y_368_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
lean_inc_ref(v_stderr_357_);
lean_inc_ref(v_stdout_356_);
lean_dec(v_a_354_);
lean_inc_ref(v_args_349_);
v___x_360_ = l_Lake_mkCmdLog(v_args_349_);
v___x_361_ = 0;
v___x_362_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set_uint8(v___x_362_, sizeof(void*)*1, v___x_361_);
v___x_363_ = lean_array_get_size(v_a_350_);
v___x_382_ = lean_array_push(v_a_350_, v___x_362_);
v___x_383_ = lean_string_utf8_byte_size(v_stdout_356_);
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = lean_nat_dec_eq(v___x_383_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_386_ = ((lean_object*)(l_Lake_logOutput___redArg___closed__0));
v___x_387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_387_, 0, v_stdout_356_);
lean_ctor_set(v___x_387_, 1, v___x_384_);
lean_ctor_set(v___x_387_, 2, v___x_383_);
v___x_388_ = l_String_Slice_trimAscii(v___x_387_);
v___x_389_ = l_String_Slice_toString(v___x_388_);
lean_dec_ref(v___x_388_);
v___x_390_ = lean_string_append(v___x_386_, v___x_389_);
lean_dec_ref(v___x_389_);
v___x_391_ = 1;
v___x_392_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_392_, 0, v___x_390_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*1, v___x_391_);
v___x_393_ = lean_box(0);
v___x_394_ = lean_array_push(v___x_382_, v___x_392_);
v___x_395_ = l_Lake_proc___lam__0(v_stderr_357_, v___x_393_, v___x_394_);
v___y_368_ = v___x_395_;
goto v___jp_367_;
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec_ref(v_stdout_356_);
v___x_396_ = lean_box(0);
v___x_397_ = l_Lake_proc___lam__0(v_stderr_357_, v___x_396_, v___x_382_);
v___y_368_ = v___x_397_;
goto v___jp_367_;
}
v___jp_364_:
{
lean_object* v___x_366_; 
v___x_366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_363_);
lean_ctor_set(v___x_366_, 1, v_a_365_);
return v___x_366_;
}
v___jp_367_:
{
if (lean_obj_tag(v___y_368_) == 0)
{
lean_object* v_a_369_; lean_object* v_cmd_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_a_369_ = lean_ctor_get(v___y_368_, 1);
lean_inc(v_a_369_);
lean_dec_ref_known(v___y_368_, 2);
v_cmd_370_ = lean_ctor_get(v_args_349_, 1);
lean_inc_ref(v_cmd_370_);
lean_dec_ref(v_args_349_);
v___x_371_ = ((lean_object*)(l_Lake_proc___closed__0));
v___x_372_ = lean_string_append(v___x_371_, v_cmd_370_);
lean_dec_ref(v_cmd_370_);
v___x_373_ = ((lean_object*)(l_Lake_proc___closed__1));
v___x_374_ = lean_string_append(v___x_372_, v___x_373_);
v___x_375_ = lean_uint32_to_nat(v_exitCode_355_);
v___x_376_ = l_Nat_reprFast(v___x_375_);
v___x_377_ = lean_string_append(v___x_374_, v___x_376_);
lean_dec_ref(v___x_376_);
v___x_378_ = 3;
v___x_379_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*1, v___x_378_);
v___x_380_ = lean_array_push(v_a_369_, v___x_379_);
v_a_365_ = v___x_380_;
goto v___jp_364_;
}
else
{
lean_object* v_a_381_; 
lean_dec_ref(v_args_349_);
v_a_381_ = lean_ctor_get(v___y_368_, 1);
lean_inc(v_a_381_);
lean_dec_ref_known(v___y_368_, 2);
v_a_365_ = v_a_381_;
goto v___jp_364_;
}
}
}
else
{
lean_object* v___x_398_; 
lean_dec_ref(v_args_349_);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v_a_354_);
lean_ctor_set(v___x_398_, 1, v_a_350_);
return v___x_398_;
}
}
else
{
lean_object* v_a_399_; lean_object* v_cmd_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_a_399_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v___x_353_, 1);
v_cmd_400_ = lean_ctor_get(v_args_349_, 1);
lean_inc_ref(v_cmd_400_);
lean_dec_ref(v_args_349_);
v___x_401_ = lean_array_get_size(v_a_350_);
v___x_402_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__0));
v___x_403_ = lean_string_append(v___x_402_, v_cmd_400_);
lean_dec_ref(v_cmd_400_);
v___x_404_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__1));
v___x_405_ = lean_string_append(v___x_403_, v___x_404_);
v___x_406_ = lean_io_error_to_string(v_a_399_);
v___x_407_ = lean_string_append(v___x_405_, v___x_406_);
lean_dec_ref(v___x_406_);
v___x_408_ = 3;
v___x_409_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*1, v___x_408_);
v___x_410_ = lean_array_push(v_a_350_, v___x_409_);
v___x_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_401_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
return v___x_411_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x27___boxed(lean_object* v_args_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lake_captureProc_x27(v_args_412_, v_a_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc(lean_object* v_args_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lake_captureProc_x27(v_args_416_, v_a_417_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_437_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_a_421_ = lean_ctor_get(v___x_419_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_437_ == 0)
{
v___x_423_ = v___x_419_;
v_isShared_424_ = v_isSharedCheck_437_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_437_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_stdout_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v_str_430_; lean_object* v_startInclusive_431_; lean_object* v_endExclusive_432_; lean_object* v___x_433_; lean_object* v___x_435_; 
v_stdout_425_ = lean_ctor_get(v_a_420_, 0);
lean_inc_ref(v_stdout_425_);
lean_dec(v_a_420_);
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_string_utf8_byte_size(v_stdout_425_);
v___x_428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_428_, 0, v_stdout_425_);
lean_ctor_set(v___x_428_, 1, v___x_426_);
lean_ctor_set(v___x_428_, 2, v___x_427_);
v___x_429_ = l_String_Slice_trimAscii(v___x_428_);
v_str_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc_ref(v_str_430_);
v_startInclusive_431_ = lean_ctor_get(v___x_429_, 1);
lean_inc(v_startInclusive_431_);
v_endExclusive_432_ = lean_ctor_get(v___x_429_, 2);
lean_inc(v_endExclusive_432_);
lean_dec_ref(v___x_429_);
v___x_433_ = lean_string_utf8_extract_fast(v_str_430_, v_startInclusive_431_, v_endExclusive_432_);
lean_dec(v_endExclusive_432_);
lean_dec(v_startInclusive_431_);
lean_dec_ref(v_str_430_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_433_);
v___x_435_ = v___x_423_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_a_421_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
else
{
lean_object* v_a_438_; lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
v_a_438_ = lean_ctor_get(v___x_419_, 0);
v_a_439_ = lean_ctor_get(v___x_419_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_419_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_inc(v_a_438_);
lean_dec(v___x_419_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_438_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc___boxed(lean_object* v_args_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lake_captureProc(v_args_447_, v_a_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f(lean_object* v_args_451_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_box(0);
v___x_454_ = l_IO_Process_output(v_args_451_, v___x_453_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_474_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_474_ == 0)
{
v___x_457_ = v___x_454_;
v_isShared_458_ = v_isSharedCheck_474_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_454_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_474_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
uint32_t v_exitCode_459_; lean_object* v_stdout_460_; uint32_t v___x_461_; uint8_t v___x_462_; 
v_exitCode_459_ = lean_ctor_get_uint32(v_a_455_, sizeof(void*)*2);
v_stdout_460_ = lean_ctor_get(v_a_455_, 0);
lean_inc_ref(v_stdout_460_);
lean_dec(v_a_455_);
v___x_461_ = 0;
v___x_462_ = lean_uint32_dec_eq(v_exitCode_459_, v___x_461_);
if (v___x_462_ == 0)
{
lean_dec_ref(v_stdout_460_);
lean_del_object(v___x_457_);
return v___x_453_;
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v_str_467_; lean_object* v_startInclusive_468_; lean_object* v_endExclusive_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_464_ = lean_string_utf8_byte_size(v_stdout_460_);
v___x_465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_465_, 0, v_stdout_460_);
lean_ctor_set(v___x_465_, 1, v___x_463_);
lean_ctor_set(v___x_465_, 2, v___x_464_);
v___x_466_ = l_String_Slice_trimAscii(v___x_465_);
v_str_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc_ref(v_str_467_);
v_startInclusive_468_ = lean_ctor_get(v___x_466_, 1);
lean_inc(v_startInclusive_468_);
v_endExclusive_469_ = lean_ctor_get(v___x_466_, 2);
lean_inc(v_endExclusive_469_);
lean_dec_ref(v___x_466_);
v___x_470_ = lean_string_utf8_extract_fast(v_str_467_, v_startInclusive_468_, v_endExclusive_469_);
lean_dec(v_endExclusive_469_);
lean_dec(v_startInclusive_468_);
lean_dec_ref(v_str_467_);
if (v_isShared_458_ == 0)
{
lean_ctor_set_tag(v___x_457_, 1);
lean_ctor_set(v___x_457_, 0, v___x_470_);
v___x_472_ = v___x_457_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_454_, 1);
return v___x_453_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f___boxed(lean_object* v_args_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lake_captureProc_x3f(v_args_475_);
return v_res_477_;
}
}
LEAN_EXPORT uint8_t l_Lake_testProc(lean_object* v_args_480_){
_start:
{
lean_object* v___x_484_; lean_object* v_cmd_485_; lean_object* v_args_486_; lean_object* v_cwd_487_; lean_object* v_env_488_; uint8_t v_inheritEnv_489_; uint8_t v_setsid_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_504_; 
v___x_484_ = ((lean_object*)(l_Lake_testProc___closed__0));
v_cmd_485_ = lean_ctor_get(v_args_480_, 1);
v_args_486_ = lean_ctor_get(v_args_480_, 2);
v_cwd_487_ = lean_ctor_get(v_args_480_, 3);
v_env_488_ = lean_ctor_get(v_args_480_, 4);
v_inheritEnv_489_ = lean_ctor_get_uint8(v_args_480_, sizeof(void*)*5);
v_setsid_490_ = lean_ctor_get_uint8(v_args_480_, sizeof(void*)*5 + 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v_args_480_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; 
v_unused_505_ = lean_ctor_get(v_args_480_, 0);
lean_dec(v_unused_505_);
v___x_492_ = v_args_480_;
v_isShared_493_ = v_isSharedCheck_504_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_env_488_);
lean_inc(v_cwd_487_);
lean_inc(v_args_486_);
lean_inc(v_cmd_485_);
lean_dec(v_args_480_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_504_;
goto v_resetjp_491_;
}
v___jp_482_:
{
uint8_t v___x_483_; 
v___x_483_ = 0;
return v___x_483_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_484_);
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_cmd_485_);
lean_ctor_set(v_reuseFailAlloc_503_, 2, v_args_486_);
lean_ctor_set(v_reuseFailAlloc_503_, 3, v_cwd_487_);
lean_ctor_set(v_reuseFailAlloc_503_, 4, v_env_488_);
lean_ctor_set_uint8(v_reuseFailAlloc_503_, sizeof(void*)*5, v_inheritEnv_489_);
lean_ctor_set_uint8(v_reuseFailAlloc_503_, sizeof(void*)*5 + 1, v_setsid_490_);
v___x_495_ = v_reuseFailAlloc_503_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_496_; 
v___x_496_ = lean_io_process_spawn(v___x_495_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_498_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_496_, 1);
v___x_498_ = lean_io_process_child_wait(v___x_484_, v_a_497_);
lean_dec(v_a_497_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; uint32_t v___x_500_; uint32_t v___x_501_; uint8_t v___x_502_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref_known(v___x_498_, 1);
v___x_500_ = 0;
v___x_501_ = lean_unbox_uint32(v_a_499_);
lean_dec(v_a_499_);
v___x_502_ = lean_uint32_dec_eq(v___x_501_, v___x_500_);
return v___x_502_;
}
else
{
lean_dec_ref_known(v___x_498_, 1);
goto v___jp_482_;
}
}
else
{
lean_dec_ref_known(v___x_496_, 1);
goto v___jp_482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_testProc___boxed(lean_object* v_args_506_, lean_object* v_a_507_){
_start:
{
uint8_t v_res_508_; lean_object* v_r_509_; 
v_res_508_ = l_Lake_testProc(v_args_506_);
v_r_509_ = lean_box(v_res_508_);
return v_r_509_;
}
}
lean_object* runtime_initialize_Lake_Util_Log(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
