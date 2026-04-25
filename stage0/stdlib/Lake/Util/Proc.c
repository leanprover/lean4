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
LEAN_EXPORT lean_object* l_Lake_proc___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__1(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_proc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "external command '"};
static const lean_object* l_Lake_proc___closed__0 = (const lean_object*)&l_Lake_proc___closed__0_value;
static const lean_string_object l_Lake_proc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "' exited with code "};
static const lean_object* l_Lake_proc___closed__1 = (const lean_object*)&l_Lake_proc___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref_n(v_stderr_94_, 2);
lean_dec_ref(v_out_91_);
lean_inc_ref(v_inst_90_);
lean_inc(v_log_92_);
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
lean_inc_ref_n(v_stderr_115_, 2);
lean_dec_ref(v_out_112_);
lean_inc_ref(v_inst_111_);
lean_inc(v_log_113_);
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
LEAN_EXPORT lean_object* l_Lake_proc___lam__0(lean_object* v_stderr_189_, lean_object* v_____r_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_193_ = lean_string_utf8_byte_size(v_stderr_189_);
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_nat_dec_eq(v___x_193_, v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_196_ = ((lean_object*)(l_Lake_logOutput___redArg___lam__0___closed__0));
v___x_197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_197_, 0, v_stderr_189_);
lean_ctor_set(v___x_197_, 1, v___x_194_);
lean_ctor_set(v___x_197_, 2, v___x_193_);
v___x_198_ = l_String_Slice_trimAscii(v___x_197_);
v___x_199_ = l_String_Slice_toString(v___x_198_);
lean_dec_ref(v___x_198_);
v___x_200_ = lean_string_append(v___x_196_, v___x_199_);
lean_dec_ref(v___x_199_);
v___x_201_ = 1;
v___x_202_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_202_, 0, v___x_200_);
lean_ctor_set_uint8(v___x_202_, sizeof(void*)*1, v___x_201_);
v___x_203_ = lean_box(0);
v___x_204_ = lean_array_push(v___y_191_, v___x_202_);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_203_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
return v___x_205_;
}
else
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec_ref(v_stderr_189_);
v___x_206_ = lean_box(0);
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___y_191_);
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__0___boxed(lean_object* v_stderr_208_, lean_object* v_____r_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lake_proc___lam__0(v_stderr_208_, v_____r_209_, v___y_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__1(uint8_t v_quiet_213_, uint8_t v___x_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
if (v_quiet_213_ == 0)
{
uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_218_ = 1;
v___x_219_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_219_, 0, v___y_215_);
lean_ctor_set_uint8(v___x_219_, sizeof(void*)*1, v___x_218_);
v___x_220_ = lean_box(0);
v___x_221_ = lean_array_push(v___y_216_, v___x_219_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_220_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
return v___x_222_;
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_223_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_223_, 0, v___y_215_);
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*1, v___x_214_);
v___x_224_ = lean_box(0);
v___x_225_ = lean_array_push(v___y_216_, v___x_223_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__1___boxed(lean_object* v_quiet_227_, lean_object* v___x_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
uint8_t v_quiet_boxed_232_; uint8_t v___x_5499__boxed_233_; lean_object* v_res_234_; 
v_quiet_boxed_232_ = lean_unbox(v_quiet_227_);
v___x_5499__boxed_233_ = lean_unbox(v___x_228_);
v_res_234_ = l_Lake_proc___lam__1(v_quiet_boxed_232_, v___x_5499__boxed_233_, v___y_229_, v___y_230_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__2(lean_object* v_stderr_235_, lean_object* v___y_236_, lean_object* v_____r_237_, lean_object* v___y_238_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_240_ = lean_string_utf8_byte_size(v_stderr_235_);
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_nat_dec_eq(v___x_240_, v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_243_ = ((lean_object*)(l_Lake_logOutput___redArg___lam__0___closed__0));
v___x_244_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_244_, 0, v_stderr_235_);
lean_ctor_set(v___x_244_, 1, v___x_241_);
lean_ctor_set(v___x_244_, 2, v___x_240_);
v___x_245_ = l_String_Slice_trimAscii(v___x_244_);
v___x_246_ = l_String_Slice_toString(v___x_245_);
lean_dec_ref(v___x_245_);
v___x_247_ = lean_string_append(v___x_243_, v___x_246_);
lean_dec_ref(v___x_246_);
v___x_248_ = lean_apply_3(v___y_236_, v___x_247_, v___y_238_, lean_box(0));
return v___x_248_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec_ref(v___y_236_);
lean_dec_ref(v_stderr_235_);
v___x_249_ = lean_box(0);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___y_238_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__2___boxed(lean_object* v_stderr_251_, lean_object* v___y_252_, lean_object* v_____r_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lake_proc___lam__2(v_stderr_251_, v___y_252_, v_____r_253_, v___y_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_proc(lean_object* v_args_259_, uint8_t v_quiet_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_263_; lean_object* v_a_265_; lean_object* v___y_268_; lean_object* v___x_270_; uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_263_ = lean_array_get_size(v_a_261_);
lean_inc_ref_n(v_args_259_, 2);
v___x_270_ = l_Lake_mkCmdLog(v_args_259_);
v___x_271_ = 0;
v___x_272_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*1, v___x_271_);
v___x_273_ = lean_array_push(v_a_261_, v___x_272_);
v___x_274_ = lean_box(0);
v___x_275_ = l_IO_Process_output(v_args_259_, v___x_274_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; uint32_t v_exitCode_277_; lean_object* v_stdout_278_; lean_object* v_stderr_279_; lean_object* v___y_281_; uint32_t v___x_295_; uint8_t v___x_296_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref(v___x_275_);
v_exitCode_277_ = lean_ctor_get_uint32(v_a_276_, sizeof(void*)*2);
v_stdout_278_ = lean_ctor_get(v_a_276_, 0);
lean_inc_ref(v_stdout_278_);
v_stderr_279_ = lean_ctor_get(v_a_276_, 1);
lean_inc_ref(v_stderr_279_);
lean_dec(v_a_276_);
v___x_295_ = 0;
v___x_296_ = lean_uint32_dec_eq(v_exitCode_277_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_297_ = lean_string_utf8_byte_size(v_stdout_278_);
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_nat_dec_eq(v___x_297_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_300_ = ((lean_object*)(l_Lake_logOutput___redArg___closed__0));
v___x_301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_301_, 0, v_stdout_278_);
lean_ctor_set(v___x_301_, 1, v___x_298_);
lean_ctor_set(v___x_301_, 2, v___x_297_);
v___x_302_ = l_String_Slice_trimAscii(v___x_301_);
v___x_303_ = l_String_Slice_toString(v___x_302_);
lean_dec_ref(v___x_302_);
v___x_304_ = lean_string_append(v___x_300_, v___x_303_);
lean_dec_ref(v___x_303_);
v___x_305_ = 1;
v___x_306_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_306_, 0, v___x_304_);
lean_ctor_set_uint8(v___x_306_, sizeof(void*)*1, v___x_305_);
v___x_307_ = lean_box(0);
v___x_308_ = lean_array_push(v___x_273_, v___x_306_);
v___x_309_ = l_Lake_proc___lam__0(v_stderr_279_, v___x_307_, v___x_308_);
v___y_281_ = v___x_309_;
goto v___jp_280_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec_ref(v_stdout_278_);
v___x_310_ = lean_box(0);
v___x_311_ = l_Lake_proc___lam__0(v_stderr_279_, v___x_310_, v___x_273_);
v___y_281_ = v___x_311_;
goto v___jp_280_;
}
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___y_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
lean_dec_ref(v_args_259_);
v___x_312_ = lean_box(v_quiet_260_);
v___x_313_ = lean_box(v___x_271_);
v___y_314_ = lean_alloc_closure((void*)(l_Lake_proc___lam__1___boxed), 5, 2);
lean_closure_set(v___y_314_, 0, v___x_312_);
lean_closure_set(v___y_314_, 1, v___x_313_);
v___x_315_ = lean_string_utf8_byte_size(v_stdout_278_);
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = lean_nat_dec_eq(v___x_315_, v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v_a_324_; lean_object* v_a_325_; lean_object* v___x_326_; 
v___x_318_ = ((lean_object*)(l_Lake_logOutput___redArg___closed__0));
v___x_319_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_319_, 0, v_stdout_278_);
lean_ctor_set(v___x_319_, 1, v___x_316_);
lean_ctor_set(v___x_319_, 2, v___x_315_);
v___x_320_ = l_String_Slice_trimAscii(v___x_319_);
v___x_321_ = l_String_Slice_toString(v___x_320_);
lean_dec_ref(v___x_320_);
v___x_322_ = lean_string_append(v___x_318_, v___x_321_);
lean_dec_ref(v___x_321_);
v___x_323_ = l_Lake_proc___lam__1(v_quiet_260_, v___x_271_, v___x_322_, v___x_273_);
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_324_);
v_a_325_ = lean_ctor_get(v___x_323_, 1);
lean_inc(v_a_325_);
lean_dec_ref(v___x_323_);
v___x_326_ = l_Lake_proc___lam__2(v_stderr_279_, v___y_314_, v_a_324_, v_a_325_);
v___y_268_ = v___x_326_;
goto v___jp_267_;
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec_ref(v_stdout_278_);
v___x_327_ = lean_box(0);
v___x_328_ = l_Lake_proc___lam__2(v_stderr_279_, v___y_314_, v___x_327_, v___x_273_);
v___y_268_ = v___x_328_;
goto v___jp_267_;
}
}
v___jp_280_:
{
if (lean_obj_tag(v___y_281_) == 0)
{
lean_object* v_a_282_; lean_object* v_cmd_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_a_282_ = lean_ctor_get(v___y_281_, 1);
lean_inc(v_a_282_);
lean_dec_ref(v___y_281_);
v_cmd_283_ = lean_ctor_get(v_args_259_, 1);
lean_inc_ref(v_cmd_283_);
lean_dec_ref(v_args_259_);
v___x_284_ = ((lean_object*)(l_Lake_proc___closed__0));
v___x_285_ = lean_string_append(v___x_284_, v_cmd_283_);
lean_dec_ref(v_cmd_283_);
v___x_286_ = ((lean_object*)(l_Lake_proc___closed__1));
v___x_287_ = lean_string_append(v___x_285_, v___x_286_);
v___x_288_ = lean_uint32_to_nat(v_exitCode_277_);
v___x_289_ = l_Nat_reprFast(v___x_288_);
v___x_290_ = lean_string_append(v___x_287_, v___x_289_);
lean_dec_ref(v___x_289_);
v___x_291_ = 3;
v___x_292_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*1, v___x_291_);
v___x_293_ = lean_array_push(v_a_282_, v___x_292_);
v_a_265_ = v___x_293_;
goto v___jp_264_;
}
else
{
lean_object* v_a_294_; 
lean_dec_ref(v_args_259_);
v_a_294_ = lean_ctor_get(v___y_281_, 1);
lean_inc(v_a_294_);
lean_dec_ref(v___y_281_);
v_a_265_ = v_a_294_;
goto v___jp_264_;
}
}
}
else
{
lean_object* v_a_329_; lean_object* v_cmd_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_a_329_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_329_);
lean_dec_ref(v___x_275_);
v_cmd_330_ = lean_ctor_get(v_args_259_, 1);
lean_inc_ref(v_cmd_330_);
lean_dec_ref(v_args_259_);
v___x_331_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__0));
v___x_332_ = lean_string_append(v___x_331_, v_cmd_330_);
lean_dec_ref(v_cmd_330_);
v___x_333_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__1));
v___x_334_ = lean_string_append(v___x_332_, v___x_333_);
v___x_335_ = lean_io_error_to_string(v_a_329_);
v___x_336_ = lean_string_append(v___x_334_, v___x_335_);
lean_dec_ref(v___x_335_);
v___x_337_ = 3;
v___x_338_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set_uint8(v___x_338_, sizeof(void*)*1, v___x_337_);
v___x_339_ = lean_array_push(v___x_273_, v___x_338_);
v_a_265_ = v___x_339_;
goto v___jp_264_;
}
v___jp_264_:
{
lean_object* v___x_266_; 
v___x_266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_263_);
lean_ctor_set(v___x_266_, 1, v_a_265_);
return v___x_266_;
}
v___jp_267_:
{
if (lean_obj_tag(v___y_268_) == 0)
{
return v___y_268_;
}
else
{
lean_object* v_a_269_; 
v_a_269_ = lean_ctor_get(v___y_268_, 1);
lean_inc(v_a_269_);
lean_dec_ref(v___y_268_);
v_a_265_ = v_a_269_;
goto v___jp_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc___boxed(lean_object* v_args_340_, lean_object* v_quiet_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
uint8_t v_quiet_boxed_344_; lean_object* v_res_345_; 
v_quiet_boxed_344_ = lean_unbox(v_quiet_341_);
v_res_345_ = l_Lake_proc(v_args_340_, v_quiet_boxed_344_, v_a_342_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x27(lean_object* v_args_346_, lean_object* v_a_347_){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_box(0);
lean_inc_ref(v_args_346_);
v___x_350_ = l_IO_Process_output(v_args_346_, v___x_349_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; uint32_t v_exitCode_352_; lean_object* v_stdout_353_; lean_object* v_stderr_354_; uint32_t v___x_355_; uint8_t v___x_356_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_a_351_);
lean_dec_ref(v___x_350_);
v_exitCode_352_ = lean_ctor_get_uint32(v_a_351_, sizeof(void*)*2);
v_stdout_353_ = lean_ctor_get(v_a_351_, 0);
v_stderr_354_ = lean_ctor_get(v_a_351_, 1);
v___x_355_ = 0;
v___x_356_ = lean_uint32_dec_eq(v_exitCode_352_, v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v_a_362_; lean_object* v___y_365_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
lean_inc_ref(v_stderr_354_);
lean_inc_ref(v_stdout_353_);
lean_dec(v_a_351_);
lean_inc_ref(v_args_346_);
v___x_357_ = l_Lake_mkCmdLog(v_args_346_);
v___x_358_ = 0;
v___x_359_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*1, v___x_358_);
v___x_360_ = lean_array_get_size(v_a_347_);
v___x_379_ = lean_array_push(v_a_347_, v___x_359_);
v___x_380_ = lean_string_utf8_byte_size(v_stdout_353_);
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = lean_nat_dec_eq(v___x_380_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_383_ = ((lean_object*)(l_Lake_logOutput___redArg___closed__0));
v___x_384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_384_, 0, v_stdout_353_);
lean_ctor_set(v___x_384_, 1, v___x_381_);
lean_ctor_set(v___x_384_, 2, v___x_380_);
v___x_385_ = l_String_Slice_trimAscii(v___x_384_);
v___x_386_ = l_String_Slice_toString(v___x_385_);
lean_dec_ref(v___x_385_);
v___x_387_ = lean_string_append(v___x_383_, v___x_386_);
lean_dec_ref(v___x_386_);
v___x_388_ = 1;
v___x_389_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*1, v___x_388_);
v___x_390_ = lean_box(0);
v___x_391_ = lean_array_push(v___x_379_, v___x_389_);
v___x_392_ = l_Lake_proc___lam__0(v_stderr_354_, v___x_390_, v___x_391_);
v___y_365_ = v___x_392_;
goto v___jp_364_;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec_ref(v_stdout_353_);
v___x_393_ = lean_box(0);
v___x_394_ = l_Lake_proc___lam__0(v_stderr_354_, v___x_393_, v___x_379_);
v___y_365_ = v___x_394_;
goto v___jp_364_;
}
v___jp_361_:
{
lean_object* v___x_363_; 
v___x_363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_360_);
lean_ctor_set(v___x_363_, 1, v_a_362_);
return v___x_363_;
}
v___jp_364_:
{
if (lean_obj_tag(v___y_365_) == 0)
{
lean_object* v_a_366_; lean_object* v_cmd_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_a_366_ = lean_ctor_get(v___y_365_, 1);
lean_inc(v_a_366_);
lean_dec_ref(v___y_365_);
v_cmd_367_ = lean_ctor_get(v_args_346_, 1);
lean_inc_ref(v_cmd_367_);
lean_dec_ref(v_args_346_);
v___x_368_ = ((lean_object*)(l_Lake_proc___closed__0));
v___x_369_ = lean_string_append(v___x_368_, v_cmd_367_);
lean_dec_ref(v_cmd_367_);
v___x_370_ = ((lean_object*)(l_Lake_proc___closed__1));
v___x_371_ = lean_string_append(v___x_369_, v___x_370_);
v___x_372_ = lean_uint32_to_nat(v_exitCode_352_);
v___x_373_ = l_Nat_reprFast(v___x_372_);
v___x_374_ = lean_string_append(v___x_371_, v___x_373_);
lean_dec_ref(v___x_373_);
v___x_375_ = 3;
v___x_376_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set_uint8(v___x_376_, sizeof(void*)*1, v___x_375_);
v___x_377_ = lean_array_push(v_a_366_, v___x_376_);
v_a_362_ = v___x_377_;
goto v___jp_361_;
}
else
{
lean_object* v_a_378_; 
lean_dec_ref(v_args_346_);
v_a_378_ = lean_ctor_get(v___y_365_, 1);
lean_inc(v_a_378_);
lean_dec_ref(v___y_365_);
v_a_362_ = v_a_378_;
goto v___jp_361_;
}
}
}
else
{
lean_object* v___x_395_; 
lean_dec_ref(v_args_346_);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v_a_351_);
lean_ctor_set(v___x_395_, 1, v_a_347_);
return v___x_395_;
}
}
else
{
lean_object* v_a_396_; lean_object* v_cmd_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v_a_396_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_a_396_);
lean_dec_ref(v___x_350_);
v_cmd_397_ = lean_ctor_get(v_args_346_, 1);
lean_inc_ref(v_cmd_397_);
lean_dec_ref(v_args_346_);
v___x_398_ = lean_array_get_size(v_a_347_);
v___x_399_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__0));
v___x_400_ = lean_string_append(v___x_399_, v_cmd_397_);
lean_dec_ref(v_cmd_397_);
v___x_401_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__1));
v___x_402_ = lean_string_append(v___x_400_, v___x_401_);
v___x_403_ = lean_io_error_to_string(v_a_396_);
v___x_404_ = lean_string_append(v___x_402_, v___x_403_);
lean_dec_ref(v___x_403_);
v___x_405_ = 3;
v___x_406_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_406_, 0, v___x_404_);
lean_ctor_set_uint8(v___x_406_, sizeof(void*)*1, v___x_405_);
v___x_407_ = lean_array_push(v_a_347_, v___x_406_);
v___x_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_398_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x27___boxed(lean_object* v_args_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lake_captureProc_x27(v_args_409_, v_a_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc(lean_object* v_args_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lake_captureProc_x27(v_args_413_, v_a_414_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_434_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_a_418_ = lean_ctor_get(v___x_416_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_434_ == 0)
{
v___x_420_ = v___x_416_;
v_isShared_421_ = v_isSharedCheck_434_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_434_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v_stdout_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v_str_427_; lean_object* v_startInclusive_428_; lean_object* v_endExclusive_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v_stdout_422_ = lean_ctor_get(v_a_417_, 0);
lean_inc_ref(v_stdout_422_);
lean_dec(v_a_417_);
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = lean_string_utf8_byte_size(v_stdout_422_);
v___x_425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_425_, 0, v_stdout_422_);
lean_ctor_set(v___x_425_, 1, v___x_423_);
lean_ctor_set(v___x_425_, 2, v___x_424_);
v___x_426_ = l_String_Slice_trimAscii(v___x_425_);
v_str_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc_ref(v_str_427_);
v_startInclusive_428_ = lean_ctor_get(v___x_426_, 1);
lean_inc(v_startInclusive_428_);
v_endExclusive_429_ = lean_ctor_get(v___x_426_, 2);
lean_inc(v_endExclusive_429_);
lean_dec_ref(v___x_426_);
v___x_430_ = lean_string_utf8_extract(v_str_427_, v_startInclusive_428_, v_endExclusive_429_);
lean_dec(v_endExclusive_429_);
lean_dec(v_startInclusive_428_);
lean_dec_ref(v_str_427_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_430_);
v___x_432_ = v___x_420_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_a_418_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
else
{
lean_object* v_a_435_; lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
v_a_435_ = lean_ctor_get(v___x_416_, 0);
v_a_436_ = lean_ctor_get(v___x_416_, 1);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_416_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_inc(v_a_435_);
lean_dec(v___x_416_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_435_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc___boxed(lean_object* v_args_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lake_captureProc(v_args_444_, v_a_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f(lean_object* v_args_448_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_box(0);
v___x_451_ = l_IO_Process_output(v_args_448_, v___x_450_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_471_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_471_ == 0)
{
v___x_454_ = v___x_451_;
v_isShared_455_ = v_isSharedCheck_471_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_471_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
uint32_t v_exitCode_456_; lean_object* v_stdout_457_; uint32_t v___x_458_; uint8_t v___x_459_; 
v_exitCode_456_ = lean_ctor_get_uint32(v_a_452_, sizeof(void*)*2);
v_stdout_457_ = lean_ctor_get(v_a_452_, 0);
lean_inc_ref(v_stdout_457_);
lean_dec(v_a_452_);
v___x_458_ = 0;
v___x_459_ = lean_uint32_dec_eq(v_exitCode_456_, v___x_458_);
if (v___x_459_ == 0)
{
lean_dec_ref(v_stdout_457_);
lean_del_object(v___x_454_);
return v___x_450_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v_str_464_; lean_object* v_startInclusive_465_; lean_object* v_endExclusive_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = lean_string_utf8_byte_size(v_stdout_457_);
v___x_462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_462_, 0, v_stdout_457_);
lean_ctor_set(v___x_462_, 1, v___x_460_);
lean_ctor_set(v___x_462_, 2, v___x_461_);
v___x_463_ = l_String_Slice_trimAscii(v___x_462_);
v_str_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc_ref(v_str_464_);
v_startInclusive_465_ = lean_ctor_get(v___x_463_, 1);
lean_inc(v_startInclusive_465_);
v_endExclusive_466_ = lean_ctor_get(v___x_463_, 2);
lean_inc(v_endExclusive_466_);
lean_dec_ref(v___x_463_);
v___x_467_ = lean_string_utf8_extract(v_str_464_, v_startInclusive_465_, v_endExclusive_466_);
lean_dec(v_endExclusive_466_);
lean_dec(v_startInclusive_465_);
lean_dec_ref(v_str_464_);
if (v_isShared_455_ == 0)
{
lean_ctor_set_tag(v___x_454_, 1);
lean_ctor_set(v___x_454_, 0, v___x_467_);
v___x_469_ = v___x_454_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_dec_ref(v___x_451_);
return v___x_450_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f___boxed(lean_object* v_args_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lake_captureProc_x3f(v_args_472_);
return v_res_474_;
}
}
LEAN_EXPORT uint8_t l_Lake_testProc(lean_object* v_args_477_){
_start:
{
lean_object* v___x_481_; lean_object* v_cmd_482_; lean_object* v_args_483_; lean_object* v_cwd_484_; lean_object* v_env_485_; uint8_t v_inheritEnv_486_; uint8_t v_setsid_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_501_; 
v___x_481_ = ((lean_object*)(l_Lake_testProc___closed__0));
v_cmd_482_ = lean_ctor_get(v_args_477_, 1);
v_args_483_ = lean_ctor_get(v_args_477_, 2);
v_cwd_484_ = lean_ctor_get(v_args_477_, 3);
v_env_485_ = lean_ctor_get(v_args_477_, 4);
v_inheritEnv_486_ = lean_ctor_get_uint8(v_args_477_, sizeof(void*)*5);
v_setsid_487_ = lean_ctor_get_uint8(v_args_477_, sizeof(void*)*5 + 1);
v_isSharedCheck_501_ = !lean_is_exclusive(v_args_477_);
if (v_isSharedCheck_501_ == 0)
{
lean_object* v_unused_502_; 
v_unused_502_ = lean_ctor_get(v_args_477_, 0);
lean_dec(v_unused_502_);
v___x_489_ = v_args_477_;
v_isShared_490_ = v_isSharedCheck_501_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_env_485_);
lean_inc(v_cwd_484_);
lean_inc(v_args_483_);
lean_inc(v_cmd_482_);
lean_dec(v_args_477_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_501_;
goto v_resetjp_488_;
}
v___jp_479_:
{
uint8_t v___x_480_; 
v___x_480_ = 0;
return v___x_480_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_481_);
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_cmd_482_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v_args_483_);
lean_ctor_set(v_reuseFailAlloc_500_, 3, v_cwd_484_);
lean_ctor_set(v_reuseFailAlloc_500_, 4, v_env_485_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, sizeof(void*)*5, v_inheritEnv_486_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, sizeof(void*)*5 + 1, v_setsid_487_);
v___x_492_ = v_reuseFailAlloc_500_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; 
v___x_493_ = lean_io_process_spawn(v___x_492_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_495_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref(v___x_493_);
v___x_495_ = lean_io_process_child_wait(v___x_481_, v_a_494_);
lean_dec(v_a_494_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; uint32_t v___x_497_; uint32_t v___x_498_; uint8_t v___x_499_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref(v___x_495_);
v___x_497_ = 0;
v___x_498_ = lean_unbox_uint32(v_a_496_);
lean_dec(v_a_496_);
v___x_499_ = lean_uint32_dec_eq(v___x_498_, v___x_497_);
return v___x_499_;
}
else
{
lean_dec_ref(v___x_495_);
goto v___jp_479_;
}
}
else
{
lean_dec_ref(v___x_493_);
goto v___jp_479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_testProc___boxed(lean_object* v_args_503_, lean_object* v_a_504_){
_start:
{
uint8_t v_res_505_; lean_object* v_r_506_; 
v_res_505_ = l_Lake_testProc(v_args_503_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
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
