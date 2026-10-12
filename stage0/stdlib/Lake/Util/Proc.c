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
lean_object* lean_array_get_size(lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_proc___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__1(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lake_rawProc___lam__0(lean_object* v_args_135_, lean_object* v_input_x3f_136_, lean_object* v_____r_137_, lean_object* v___y_138_){
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
LEAN_EXPORT void l_Lake_rawProc___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_135_ = stack[0].m_obj;
lean_object* v_input_x3f_136_ = stack[1].m_obj;
lean_object* v_____r_137_ = stack[2].m_obj;
lean_object* v___y_138_ = stack[3].m_obj;
lean_object* v_res_156_;
v_res_156_ = l_Lake_rawProc___lam__0(v_args_135_, v_input_x3f_136_, v_____r_137_, v___y_138_);
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0___boxed(lean_object* v_args_157_, lean_object* v_input_x3f_158_, lean_object* v_____r_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lake_rawProc___lam__0(v_args_157_, v_input_x3f_158_, v_____r_159_, v___y_160_);
lean_dec(v_input_x3f_158_);
return v_res_162_;
}
}
lean_object* l_Lake_rawProc(lean_object* v_args_163_, uint8_t v_quiet_164_, lean_object* v_input_x3f_165_, lean_object* v_a_166_){
_start:
{
lean_object* v___x_168_; lean_object* v___y_170_; 
v___x_168_ = lean_array_get_size(v_a_166_);
if (v_quiet_164_ == 0)
{
lean_object* v___x_180_; uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
lean_inc_ref(v_args_163_);
v___x_180_ = l_Lake_mkCmdLog(v_args_163_);
v___x_181_ = 0;
v___x_182_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*1, v___x_181_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_array_push(v_a_166_, v___x_182_);
v___x_185_ = l_Lake_rawProc___lam__0(v_args_163_, v_input_x3f_165_, v___x_183_, v___x_184_);
v___y_170_ = v___x_185_;
goto v___jp_169_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_box(0);
v___x_187_ = l_Lake_rawProc___lam__0(v_args_163_, v_input_x3f_165_, v___x_186_, v_a_166_);
v___y_170_ = v___x_187_;
goto v___jp_169_;
}
v___jp_169_:
{
if (lean_obj_tag(v___y_170_) == 0)
{
return v___y_170_;
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
v_a_171_ = lean_ctor_get(v___y_170_, 1);
v_isSharedCheck_178_ = !lean_is_exclusive(v___y_170_);
if (v_isSharedCheck_178_ == 0)
{
lean_object* v_unused_179_; 
v_unused_179_ = lean_ctor_get(v___y_170_, 0);
lean_dec(v_unused_179_);
v___x_173_ = v___y_170_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___y_170_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 0, v___x_168_);
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_rawProc_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_163_ = stack[0].m_obj;
uint8_t v_quiet_164_ = stack[1].m_num;
lean_object* v_input_x3f_165_ = stack[2].m_obj;
lean_object* v_a_166_ = stack[3].m_obj;
lean_object* v_res_188_;
v_res_188_ = l_Lake_rawProc(v_args_163_, v_quiet_164_, v_input_x3f_165_, v_a_166_);
stack->m_obj
 = v_res_188_;
}
LEAN_EXPORT lean_object* l_Lake_rawProc___boxed(lean_object* v_args_189_, lean_object* v_quiet_190_, lean_object* v_input_x3f_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
uint8_t v_quiet_boxed_194_; lean_object* v_res_195_; 
v_quiet_boxed_194_ = lean_unbox(v_quiet_190_);
v_res_195_ = l_Lake_rawProc(v_args_189_, v_quiet_boxed_194_, v_input_x3f_191_, v_a_192_);
lean_dec(v_input_x3f_191_);
return v_res_195_;
}
}
lean_object* l_Lake_proc___lam__0(uint8_t v_quiet_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
if (v_quiet_196_ == 0)
{
uint8_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_200_ = 1;
v___x_201_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_201_, 0, v___y_197_);
lean_ctor_set_uint8(v___x_201_, sizeof(void*)*1, v___x_200_);
v___x_202_ = lean_box(0);
v___x_203_ = lean_array_push(v___y_198_, v___x_201_);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_202_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
return v___x_204_;
}
else
{
uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_205_ = 0;
v___x_206_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_206_, 0, v___y_197_);
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*1, v___x_205_);
v___x_207_ = lean_box(0);
v___x_208_ = lean_array_push(v___y_198_, v___x_206_);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_207_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
return v___x_209_;
}
}
}
LEAN_EXPORT void l_Lake_proc___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_quiet_196_ = stack[0].m_num;
lean_object* v___y_197_ = stack[1].m_obj;
lean_object* v___y_198_ = stack[2].m_obj;
lean_object* v_res_210_;
v_res_210_ = l_Lake_proc___lam__0(v_quiet_196_, v___y_197_, v___y_198_);
stack->m_obj
 = v_res_210_;
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__0___boxed(lean_object* v_quiet_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
uint8_t v_quiet_boxed_215_; lean_object* v_res_216_; 
v_quiet_boxed_215_ = lean_unbox(v_quiet_211_);
v_res_216_ = l_Lake_proc___lam__0(v_quiet_boxed_215_, v___y_212_, v___y_213_);
return v_res_216_;
}
}
lean_object* l_Lake_proc___lam__1(lean_object* v_stderr_217_, lean_object* v_____r_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_221_ = lean_string_utf8_byte_size(v_stderr_217_);
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_nat_dec_eq(v___x_221_, v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_224_ = ((lean_object*)(l_Lake_logOutput___redArg___lam__0___closed__0));
v___x_225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_225_, 0, v_stderr_217_);
lean_ctor_set(v___x_225_, 1, v___x_222_);
lean_ctor_set(v___x_225_, 2, v___x_221_);
v___x_226_ = l_String_Slice_trimAscii(v___x_225_);
v___x_227_ = l_String_Slice_toString(v___x_226_);
lean_dec_ref(v___x_226_);
v___x_228_ = lean_string_append(v___x_224_, v___x_227_);
lean_dec_ref(v___x_227_);
v___x_229_ = 1;
v___x_230_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set_uint8(v___x_230_, sizeof(void*)*1, v___x_229_);
v___x_231_ = lean_box(0);
v___x_232_ = lean_array_push(v___y_219_, v___x_230_);
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
return v___x_233_;
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec_ref(v_stderr_217_);
v___x_234_ = lean_box(0);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___y_219_);
return v___x_235_;
}
}
}
LEAN_EXPORT void l_Lake_proc___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_stderr_217_ = stack[0].m_obj;
lean_object* v_____r_218_ = stack[1].m_obj;
lean_object* v___y_219_ = stack[2].m_obj;
lean_object* v_res_236_;
v_res_236_ = l_Lake_proc___lam__1(v_stderr_217_, v_____r_218_, v___y_219_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__1___boxed(lean_object* v_stderr_237_, lean_object* v_____r_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lake_proc___lam__1(v_stderr_237_, v_____r_238_, v___y_239_);
return v_res_241_;
}
}
lean_object* l_Lake_proc___lam__2(lean_object* v_stderr_242_, lean_object* v___y_243_, lean_object* v_____r_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_247_ = lean_string_utf8_byte_size(v_stderr_242_);
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = lean_nat_dec_eq(v___x_247_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_250_ = ((lean_object*)(l_Lake_logOutput___redArg___lam__0___closed__0));
v___x_251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_251_, 0, v_stderr_242_);
lean_ctor_set(v___x_251_, 1, v___x_248_);
lean_ctor_set(v___x_251_, 2, v___x_247_);
v___x_252_ = l_String_Slice_trimAscii(v___x_251_);
v___x_253_ = l_String_Slice_toString(v___x_252_);
lean_dec_ref(v___x_252_);
v___x_254_ = lean_string_append(v___x_250_, v___x_253_);
lean_dec_ref(v___x_253_);
v___x_255_ = lean_apply_3(v___y_243_, v___x_254_, v___y_245_, lean_box(0));
return v___x_255_;
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec_ref(v___y_243_);
lean_dec_ref(v_stderr_242_);
v___x_256_ = lean_box(0);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___y_245_);
return v___x_257_;
}
}
}
LEAN_EXPORT void l_Lake_proc___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_stderr_242_ = stack[0].m_obj;
lean_object* v___y_243_ = stack[1].m_obj;
lean_object* v_____r_244_ = stack[2].m_obj;
lean_object* v___y_245_ = stack[3].m_obj;
lean_object* v_res_258_;
v_res_258_ = l_Lake_proc___lam__2(v_stderr_242_, v___y_243_, v_____r_244_, v___y_245_);
stack->m_obj
 = v_res_258_;
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__2___boxed(lean_object* v_stderr_259_, lean_object* v___y_260_, lean_object* v_____r_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lake_proc___lam__2(v_stderr_259_, v___y_260_, v_____r_261_, v___y_262_);
return v_res_264_;
}
}
lean_object* l_Lake_proc(lean_object* v_args_267_, uint8_t v_quiet_268_, lean_object* v_input_x3f_269_, lean_object* v_a_270_){
_start:
{
lean_object* v___x_272_; lean_object* v___y_273_; lean_object* v___x_274_; lean_object* v_a_276_; lean_object* v___y_279_; lean_object* v___x_281_; uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_272_ = lean_box(v_quiet_268_);
v___y_273_ = lean_alloc_closure((void*)(l_Lake_proc___lam__0___boxed), 4, 1);
lean_closure_set(v___y_273_, 0, v___x_272_);
v___x_274_ = lean_array_get_size(v_a_270_);
lean_inc_ref_n(v_args_267_, 2);
v___x_281_ = l_Lake_mkCmdLog(v_args_267_);
v___x_282_ = 0;
v___x_283_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_283_, 0, v___x_281_);
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*1, v___x_282_);
v___x_284_ = lean_array_push(v_a_270_, v___x_283_);
v___x_285_ = l_IO_Process_output(v_args_267_, v_input_x3f_269_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; uint32_t v_exitCode_287_; lean_object* v_stdout_288_; lean_object* v_stderr_289_; lean_object* v___y_291_; uint32_t v___x_305_; uint8_t v___x_306_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_a_286_);
lean_dec_ref_known(v___x_285_, 1);
v_exitCode_287_ = lean_ctor_get_uint32(v_a_286_, sizeof(void*)*2);
v_stdout_288_ = lean_ctor_get(v_a_286_, 0);
lean_inc_ref(v_stdout_288_);
v_stderr_289_ = lean_ctor_get(v_a_286_, 1);
lean_inc_ref(v_stderr_289_);
lean_dec(v_a_286_);
v___x_305_ = 0;
v___x_306_ = lean_uint32_dec_eq(v_exitCode_287_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
lean_dec_ref(v___y_273_);
v___x_307_ = lean_string_utf8_byte_size(v_stdout_288_);
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_nat_dec_eq(v___x_307_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_310_ = ((lean_object*)(l_Lake_logOutput___redArg___closed__0));
v___x_311_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_311_, 0, v_stdout_288_);
lean_ctor_set(v___x_311_, 1, v___x_308_);
lean_ctor_set(v___x_311_, 2, v___x_307_);
v___x_312_ = l_String_Slice_trimAscii(v___x_311_);
v___x_313_ = l_String_Slice_toString(v___x_312_);
lean_dec_ref(v___x_312_);
v___x_314_ = lean_string_append(v___x_310_, v___x_313_);
lean_dec_ref(v___x_313_);
v___x_315_ = 1;
v___x_316_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set_uint8(v___x_316_, sizeof(void*)*1, v___x_315_);
v___x_317_ = lean_box(0);
v___x_318_ = lean_array_push(v___x_284_, v___x_316_);
v___x_319_ = l_Lake_proc___lam__1(v_stderr_289_, v___x_317_, v___x_318_);
v___y_291_ = v___x_319_;
goto v___jp_290_;
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; 
lean_dec_ref(v_stdout_288_);
v___x_320_ = lean_box(0);
v___x_321_ = l_Lake_proc___lam__1(v_stderr_289_, v___x_320_, v___x_284_);
v___y_291_ = v___x_321_;
goto v___jp_290_;
}
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
lean_dec_ref(v_args_267_);
v___x_322_ = lean_string_utf8_byte_size(v_stdout_288_);
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = lean_nat_dec_eq(v___x_322_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v_a_331_; lean_object* v_a_332_; lean_object* v___x_333_; 
v___x_325_ = ((lean_object*)(l_Lake_logOutput___redArg___closed__0));
v___x_326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_326_, 0, v_stdout_288_);
lean_ctor_set(v___x_326_, 1, v___x_323_);
lean_ctor_set(v___x_326_, 2, v___x_322_);
v___x_327_ = l_String_Slice_trimAscii(v___x_326_);
v___x_328_ = l_String_Slice_toString(v___x_327_);
lean_dec_ref(v___x_327_);
v___x_329_ = lean_string_append(v___x_325_, v___x_328_);
lean_dec_ref(v___x_328_);
v___x_330_ = l_Lake_proc___lam__0(v_quiet_268_, v___x_329_, v___x_284_);
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
v_a_332_ = lean_ctor_get(v___x_330_, 1);
lean_inc(v_a_332_);
lean_dec_ref(v___x_330_);
v___x_333_ = l_Lake_proc___lam__2(v_stderr_289_, v___y_273_, v_a_331_, v_a_332_);
v___y_279_ = v___x_333_;
goto v___jp_278_;
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; 
lean_dec_ref(v_stdout_288_);
v___x_334_ = lean_box(0);
v___x_335_ = l_Lake_proc___lam__2(v_stderr_289_, v___y_273_, v___x_334_, v___x_284_);
v___y_279_ = v___x_335_;
goto v___jp_278_;
}
}
v___jp_290_:
{
if (lean_obj_tag(v___y_291_) == 0)
{
lean_object* v_a_292_; lean_object* v_cmd_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_a_292_ = lean_ctor_get(v___y_291_, 1);
lean_inc(v_a_292_);
lean_dec_ref_known(v___y_291_, 2);
v_cmd_293_ = lean_ctor_get(v_args_267_, 1);
lean_inc_ref(v_cmd_293_);
lean_dec_ref(v_args_267_);
v___x_294_ = ((lean_object*)(l_Lake_proc___closed__0));
v___x_295_ = lean_string_append(v___x_294_, v_cmd_293_);
lean_dec_ref(v_cmd_293_);
v___x_296_ = ((lean_object*)(l_Lake_proc___closed__1));
v___x_297_ = lean_string_append(v___x_295_, v___x_296_);
v___x_298_ = lean_uint32_to_nat(v_exitCode_287_);
v___x_299_ = l_Nat_reprFast(v___x_298_);
v___x_300_ = lean_string_append(v___x_297_, v___x_299_);
lean_dec_ref(v___x_299_);
v___x_301_ = 3;
v___x_302_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set_uint8(v___x_302_, sizeof(void*)*1, v___x_301_);
v___x_303_ = lean_array_push(v_a_292_, v___x_302_);
v_a_276_ = v___x_303_;
goto v___jp_275_;
}
else
{
lean_object* v_a_304_; 
lean_dec_ref(v_args_267_);
v_a_304_ = lean_ctor_get(v___y_291_, 1);
lean_inc(v_a_304_);
lean_dec_ref_known(v___y_291_, 2);
v_a_276_ = v_a_304_;
goto v___jp_275_;
}
}
}
else
{
lean_object* v_a_336_; lean_object* v_cmd_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec_ref(v___y_273_);
v_a_336_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_a_336_);
lean_dec_ref_known(v___x_285_, 1);
v_cmd_337_ = lean_ctor_get(v_args_267_, 1);
lean_inc_ref(v_cmd_337_);
lean_dec_ref(v_args_267_);
v___x_338_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__0));
v___x_339_ = lean_string_append(v___x_338_, v_cmd_337_);
lean_dec_ref(v_cmd_337_);
v___x_340_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__1));
v___x_341_ = lean_string_append(v___x_339_, v___x_340_);
v___x_342_ = lean_io_error_to_string(v_a_336_);
v___x_343_ = lean_string_append(v___x_341_, v___x_342_);
lean_dec_ref(v___x_342_);
v___x_344_ = 3;
v___x_345_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*1, v___x_344_);
v___x_346_ = lean_array_push(v___x_284_, v___x_345_);
v_a_276_ = v___x_346_;
goto v___jp_275_;
}
v___jp_275_:
{
lean_object* v___x_277_; 
v___x_277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_274_);
lean_ctor_set(v___x_277_, 1, v_a_276_);
return v___x_277_;
}
v___jp_278_:
{
if (lean_obj_tag(v___y_279_) == 0)
{
return v___y_279_;
}
else
{
lean_object* v_a_280_; 
v_a_280_ = lean_ctor_get(v___y_279_, 1);
lean_inc(v_a_280_);
lean_dec_ref_known(v___y_279_, 2);
v_a_276_ = v_a_280_;
goto v___jp_275_;
}
}
}
}
LEAN_EXPORT void l_Lake_proc_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_267_ = stack[0].m_obj;
uint8_t v_quiet_268_ = stack[1].m_num;
lean_object* v_input_x3f_269_ = stack[2].m_obj;
lean_object* v_a_270_ = stack[3].m_obj;
lean_object* v_res_347_;
v_res_347_ = l_Lake_proc(v_args_267_, v_quiet_268_, v_input_x3f_269_, v_a_270_);
stack->m_obj
 = v_res_347_;
}
LEAN_EXPORT lean_object* l_Lake_proc___boxed(lean_object* v_args_348_, lean_object* v_quiet_349_, lean_object* v_input_x3f_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
uint8_t v_quiet_boxed_353_; lean_object* v_res_354_; 
v_quiet_boxed_353_ = lean_unbox(v_quiet_349_);
v_res_354_ = l_Lake_proc(v_args_348_, v_quiet_boxed_353_, v_input_x3f_350_, v_a_351_);
lean_dec(v_input_x3f_350_);
return v_res_354_;
}
}
lean_object* l_Lake_captureProc_x27(lean_object* v_args_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v_a_361_; lean_object* v___x_363_; 
v___x_358_ = lean_box(0);
v___x_359_ = lean_array_get_size(v_a_356_);
lean_inc_ref(v_args_355_);
v___x_363_ = l_IO_Process_output(v_args_355_, v___x_358_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; uint32_t v_exitCode_365_; lean_object* v_stdout_366_; lean_object* v_stderr_367_; lean_object* v___y_369_; uint32_t v___x_383_; uint8_t v___x_384_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v___x_363_, 1);
v_exitCode_365_ = lean_ctor_get_uint32(v_a_364_, sizeof(void*)*2);
v_stdout_366_ = lean_ctor_get(v_a_364_, 0);
v_stderr_367_ = lean_ctor_get(v_a_364_, 1);
v___x_383_ = 0;
v___x_384_ = lean_uint32_dec_eq(v_exitCode_365_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; uint8_t v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
lean_inc_ref(v_stderr_367_);
lean_inc_ref(v_stdout_366_);
lean_dec(v_a_364_);
lean_inc_ref(v_args_355_);
v___x_385_ = l_Lake_mkCmdLog(v_args_355_);
v___x_386_ = 0;
v___x_387_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_387_, 0, v___x_385_);
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*1, v___x_386_);
v___x_388_ = lean_array_push(v_a_356_, v___x_387_);
v___x_389_ = lean_string_utf8_byte_size(v_stdout_366_);
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_nat_dec_eq(v___x_389_, v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_392_ = ((lean_object*)(l_Lake_logOutput___redArg___closed__0));
v___x_393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_393_, 0, v_stdout_366_);
lean_ctor_set(v___x_393_, 1, v___x_390_);
lean_ctor_set(v___x_393_, 2, v___x_389_);
v___x_394_ = l_String_Slice_trimAscii(v___x_393_);
v___x_395_ = l_String_Slice_toString(v___x_394_);
lean_dec_ref(v___x_394_);
v___x_396_ = lean_string_append(v___x_392_, v___x_395_);
lean_dec_ref(v___x_395_);
v___x_397_ = 1;
v___x_398_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*1, v___x_397_);
v___x_399_ = lean_box(0);
v___x_400_ = lean_array_push(v___x_388_, v___x_398_);
v___x_401_ = l_Lake_proc___lam__1(v_stderr_367_, v___x_399_, v___x_400_);
v___y_369_ = v___x_401_;
goto v___jp_368_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec_ref(v_stdout_366_);
v___x_402_ = lean_box(0);
v___x_403_ = l_Lake_proc___lam__1(v_stderr_367_, v___x_402_, v___x_388_);
v___y_369_ = v___x_403_;
goto v___jp_368_;
}
}
else
{
lean_object* v___x_404_; 
lean_dec_ref(v_args_355_);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v_a_364_);
lean_ctor_set(v___x_404_, 1, v_a_356_);
return v___x_404_;
}
v___jp_368_:
{
if (lean_obj_tag(v___y_369_) == 0)
{
lean_object* v_a_370_; lean_object* v_cmd_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_a_370_ = lean_ctor_get(v___y_369_, 1);
lean_inc(v_a_370_);
lean_dec_ref_known(v___y_369_, 2);
v_cmd_371_ = lean_ctor_get(v_args_355_, 1);
lean_inc_ref(v_cmd_371_);
lean_dec_ref(v_args_355_);
v___x_372_ = ((lean_object*)(l_Lake_proc___closed__0));
v___x_373_ = lean_string_append(v___x_372_, v_cmd_371_);
lean_dec_ref(v_cmd_371_);
v___x_374_ = ((lean_object*)(l_Lake_proc___closed__1));
v___x_375_ = lean_string_append(v___x_373_, v___x_374_);
v___x_376_ = lean_uint32_to_nat(v_exitCode_365_);
v___x_377_ = l_Nat_reprFast(v___x_376_);
v___x_378_ = lean_string_append(v___x_375_, v___x_377_);
lean_dec_ref(v___x_377_);
v___x_379_ = 3;
v___x_380_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set_uint8(v___x_380_, sizeof(void*)*1, v___x_379_);
v___x_381_ = lean_array_push(v_a_370_, v___x_380_);
v_a_361_ = v___x_381_;
goto v___jp_360_;
}
else
{
lean_object* v_a_382_; 
lean_dec_ref(v_args_355_);
v_a_382_ = lean_ctor_get(v___y_369_, 1);
lean_inc(v_a_382_);
lean_dec_ref_known(v___y_369_, 2);
v_a_361_ = v_a_382_;
goto v___jp_360_;
}
}
}
else
{
lean_object* v_a_405_; lean_object* v_cmd_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_a_405_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_405_);
lean_dec_ref_known(v___x_363_, 1);
v_cmd_406_ = lean_ctor_get(v_args_355_, 1);
lean_inc_ref(v_cmd_406_);
lean_dec_ref(v_args_355_);
v___x_407_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__0));
v___x_408_ = lean_string_append(v___x_407_, v_cmd_406_);
lean_dec_ref(v_cmd_406_);
v___x_409_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__1));
v___x_410_ = lean_string_append(v___x_408_, v___x_409_);
v___x_411_ = lean_io_error_to_string(v_a_405_);
v___x_412_ = lean_string_append(v___x_410_, v___x_411_);
lean_dec_ref(v___x_411_);
v___x_413_ = 3;
v___x_414_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_414_, 0, v___x_412_);
lean_ctor_set_uint8(v___x_414_, sizeof(void*)*1, v___x_413_);
v___x_415_ = lean_array_push(v_a_356_, v___x_414_);
v___x_416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_359_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
return v___x_416_;
}
v___jp_360_:
{
lean_object* v___x_362_; 
v___x_362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_359_);
lean_ctor_set(v___x_362_, 1, v_a_361_);
return v___x_362_;
}
}
}
LEAN_EXPORT void l_Lake_captureProc_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_355_ = stack[0].m_obj;
lean_object* v_a_356_ = stack[1].m_obj;
lean_object* v_res_417_;
v_res_417_ = l_Lake_captureProc_x27(v_args_355_, v_a_356_);
stack->m_obj
 = v_res_417_;
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x27___boxed(lean_object* v_args_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lake_captureProc_x27(v_args_418_, v_a_419_);
return v_res_421_;
}
}
lean_object* l_Lake_captureProc(lean_object* v_args_422_, lean_object* v_a_423_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lake_captureProc_x27(v_args_422_, v_a_423_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_443_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
v_a_427_ = lean_ctor_get(v___x_425_, 1);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_443_ == 0)
{
v___x_429_ = v___x_425_;
v_isShared_430_ = v_isSharedCheck_443_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_inc(v_a_426_);
lean_dec(v___x_425_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_443_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v_stdout_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v_str_436_; lean_object* v_startInclusive_437_; lean_object* v_endExclusive_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v_stdout_431_ = lean_ctor_get(v_a_426_, 0);
lean_inc_ref(v_stdout_431_);
lean_dec(v_a_426_);
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = lean_string_utf8_byte_size(v_stdout_431_);
v___x_434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_434_, 0, v_stdout_431_);
lean_ctor_set(v___x_434_, 1, v___x_432_);
lean_ctor_set(v___x_434_, 2, v___x_433_);
v___x_435_ = l_String_Slice_trimAscii(v___x_434_);
v_str_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc_ref(v_str_436_);
v_startInclusive_437_ = lean_ctor_get(v___x_435_, 1);
lean_inc(v_startInclusive_437_);
v_endExclusive_438_ = lean_ctor_get(v___x_435_, 2);
lean_inc(v_endExclusive_438_);
lean_dec_ref(v___x_435_);
v___x_439_ = lean_string_utf8_extract_fast(v_str_436_, v_startInclusive_437_, v_endExclusive_438_);
lean_dec(v_endExclusive_438_);
lean_dec(v_startInclusive_437_);
lean_dec_ref(v_str_436_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_439_);
v___x_441_ = v___x_429_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_a_427_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
else
{
lean_object* v_a_444_; lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
v_a_444_ = lean_ctor_get(v___x_425_, 0);
v_a_445_ = lean_ctor_get(v___x_425_, 1);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_425_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_inc(v_a_444_);
lean_dec(v___x_425_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_444_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_captureProc_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_422_ = stack[0].m_obj;
lean_object* v_a_423_ = stack[1].m_obj;
lean_object* v_res_453_;
v_res_453_ = l_Lake_captureProc(v_args_422_, v_a_423_);
stack->m_obj
 = v_res_453_;
}
LEAN_EXPORT lean_object* l_Lake_captureProc___boxed(lean_object* v_args_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lake_captureProc(v_args_454_, v_a_455_);
return v_res_457_;
}
}
lean_object* l_Lake_captureProc_x3f(lean_object* v_args_458_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_box(0);
v___x_461_ = l_IO_Process_output(v_args_458_, v___x_460_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_481_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_481_ == 0)
{
v___x_464_ = v___x_461_;
v_isShared_465_ = v_isSharedCheck_481_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_461_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_481_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint32_t v_exitCode_466_; lean_object* v_stdout_467_; uint32_t v___x_468_; uint8_t v___x_469_; 
v_exitCode_466_ = lean_ctor_get_uint32(v_a_462_, sizeof(void*)*2);
v_stdout_467_ = lean_ctor_get(v_a_462_, 0);
lean_inc_ref(v_stdout_467_);
lean_dec(v_a_462_);
v___x_468_ = 0;
v___x_469_ = lean_uint32_dec_eq(v_exitCode_466_, v___x_468_);
if (v___x_469_ == 0)
{
lean_dec_ref(v_stdout_467_);
lean_del_object(v___x_464_);
return v___x_460_;
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v_str_474_; lean_object* v_startInclusive_475_; lean_object* v_endExclusive_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_string_utf8_byte_size(v_stdout_467_);
v___x_472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_472_, 0, v_stdout_467_);
lean_ctor_set(v___x_472_, 1, v___x_470_);
lean_ctor_set(v___x_472_, 2, v___x_471_);
v___x_473_ = l_String_Slice_trimAscii(v___x_472_);
v_str_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc_ref(v_str_474_);
v_startInclusive_475_ = lean_ctor_get(v___x_473_, 1);
lean_inc(v_startInclusive_475_);
v_endExclusive_476_ = lean_ctor_get(v___x_473_, 2);
lean_inc(v_endExclusive_476_);
lean_dec_ref(v___x_473_);
v___x_477_ = lean_string_utf8_extract_fast(v_str_474_, v_startInclusive_475_, v_endExclusive_476_);
lean_dec(v_endExclusive_476_);
lean_dec(v_startInclusive_475_);
lean_dec_ref(v_str_474_);
if (v_isShared_465_ == 0)
{
lean_ctor_set_tag(v___x_464_, 1);
lean_ctor_set(v___x_464_, 0, v___x_477_);
v___x_479_ = v___x_464_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_461_, 1);
return v___x_460_;
}
}
}
LEAN_EXPORT void l_Lake_captureProc_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_458_ = stack[0].m_obj;
lean_object* v_res_482_;
v_res_482_ = l_Lake_captureProc_x3f(v_args_458_);
stack->m_obj
 = v_res_482_;
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f___boxed(lean_object* v_args_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lake_captureProc_x3f(v_args_483_);
return v_res_485_;
}
}
uint8_t l_Lake_testProc(lean_object* v_args_488_){
_start:
{
lean_object* v___x_492_; lean_object* v_cmd_493_; lean_object* v_args_494_; lean_object* v_cwd_495_; lean_object* v_env_496_; uint8_t v_inheritEnv_497_; uint8_t v_setsid_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_512_; 
v___x_492_ = ((lean_object*)(l_Lake_testProc___closed__0));
v_cmd_493_ = lean_ctor_get(v_args_488_, 1);
v_args_494_ = lean_ctor_get(v_args_488_, 2);
v_cwd_495_ = lean_ctor_get(v_args_488_, 3);
v_env_496_ = lean_ctor_get(v_args_488_, 4);
v_inheritEnv_497_ = lean_ctor_get_uint8(v_args_488_, sizeof(void*)*5);
v_setsid_498_ = lean_ctor_get_uint8(v_args_488_, sizeof(void*)*5 + 1);
v_isSharedCheck_512_ = !lean_is_exclusive(v_args_488_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; 
v_unused_513_ = lean_ctor_get(v_args_488_, 0);
lean_dec(v_unused_513_);
v___x_500_ = v_args_488_;
v_isShared_501_ = v_isSharedCheck_512_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_env_496_);
lean_inc(v_cwd_495_);
lean_inc(v_args_494_);
lean_inc(v_cmd_493_);
lean_dec(v_args_488_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_512_;
goto v_resetjp_499_;
}
v___jp_490_:
{
uint8_t v___x_491_; 
v___x_491_ = 0;
return v___x_491_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_492_);
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_cmd_493_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_args_494_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_cwd_495_);
lean_ctor_set(v_reuseFailAlloc_511_, 4, v_env_496_);
lean_ctor_set_uint8(v_reuseFailAlloc_511_, sizeof(void*)*5, v_inheritEnv_497_);
lean_ctor_set_uint8(v_reuseFailAlloc_511_, sizeof(void*)*5 + 1, v_setsid_498_);
v___x_503_ = v_reuseFailAlloc_511_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; 
v___x_504_ = lean_io_process_spawn(v___x_503_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_506_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref_known(v___x_504_, 1);
v___x_506_ = lean_io_process_child_wait(v___x_492_, v_a_505_);
lean_dec(v_a_505_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; uint32_t v___x_508_; uint32_t v___x_509_; uint8_t v___x_510_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
v___x_508_ = 0;
v___x_509_ = lean_unbox_uint32(v_a_507_);
lean_dec(v_a_507_);
v___x_510_ = lean_uint32_dec_eq(v___x_509_, v___x_508_);
return v___x_510_;
}
else
{
lean_dec_ref_known(v___x_506_, 1);
goto v___jp_490_;
}
}
else
{
lean_dec_ref_known(v___x_504_, 1);
goto v___jp_490_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_testProc_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_488_ = stack[0].m_obj;
uint8_t v_res_514_;
v_res_514_ = l_Lake_testProc(v_args_488_);
stack->m_num = v_res_514_;
}
LEAN_EXPORT lean_object* l_Lake_testProc___boxed(lean_object* v_args_515_, lean_object* v_a_516_){
_start:
{
uint8_t v_res_517_; lean_object* v_r_518_; 
v_res_517_ = l_Lake_testProc(v_args_515_);
v_r_518_ = lean_box(v_res_517_);
return v_r_518_;
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
