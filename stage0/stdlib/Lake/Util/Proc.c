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
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0(lean_object* v_args_133_, lean_object* v_input_x3f_134_, lean_object* v_____r_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; 
lean_inc_ref(v_args_133_);
v___x_138_ = l_IO_Process_output(v_args_133_, v_input_x3f_134_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_140_; 
lean_dec_ref(v_args_133_);
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
lean_dec_ref_known(v___x_138_, 1);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v_a_139_);
lean_ctor_set(v___x_140_, 1, v___y_136_);
return v___x_140_;
}
else
{
lean_object* v_a_141_; lean_object* v_cmd_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_a_141_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_141_);
lean_dec_ref_known(v___x_138_, 1);
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
v___x_151_ = lean_array_get_size(v___y_136_);
v___x_152_ = lean_array_push(v___y_136_, v___x_150_);
v___x_153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_151_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0___boxed(lean_object* v_args_154_, lean_object* v_input_x3f_155_, lean_object* v_____r_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lake_rawProc___lam__0(v_args_154_, v_input_x3f_155_, v_____r_156_, v___y_157_);
lean_dec(v_input_x3f_155_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc(lean_object* v_args_160_, uint8_t v_quiet_161_, lean_object* v_input_x3f_162_, lean_object* v_a_163_){
_start:
{
lean_object* v___x_165_; lean_object* v___y_167_; 
v___x_165_ = lean_array_get_size(v_a_163_);
if (v_quiet_161_ == 0)
{
lean_object* v___x_177_; uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
lean_inc_ref(v_args_160_);
v___x_177_ = l_Lake_mkCmdLog(v_args_160_);
v___x_178_ = 0;
v___x_179_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*1, v___x_178_);
v___x_180_ = lean_box(0);
v___x_181_ = lean_array_push(v_a_163_, v___x_179_);
v___x_182_ = l_Lake_rawProc___lam__0(v_args_160_, v_input_x3f_162_, v___x_180_, v___x_181_);
v___y_167_ = v___x_182_;
goto v___jp_166_;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_box(0);
v___x_184_ = l_Lake_rawProc___lam__0(v_args_160_, v_input_x3f_162_, v___x_183_, v_a_163_);
v___y_167_ = v___x_184_;
goto v___jp_166_;
}
v___jp_166_:
{
if (lean_obj_tag(v___y_167_) == 0)
{
return v___y_167_;
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
v_a_168_ = lean_ctor_get(v___y_167_, 1);
v_isSharedCheck_175_ = !lean_is_exclusive(v___y_167_);
if (v_isSharedCheck_175_ == 0)
{
lean_object* v_unused_176_; 
v_unused_176_ = lean_ctor_get(v___y_167_, 0);
lean_dec(v_unused_176_);
v___x_170_ = v___y_167_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___y_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_165_);
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___boxed(lean_object* v_args_185_, lean_object* v_quiet_186_, lean_object* v_input_x3f_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
uint8_t v_quiet_boxed_190_; lean_object* v_res_191_; 
v_quiet_boxed_190_ = lean_unbox(v_quiet_186_);
v_res_191_ = l_Lake_rawProc(v_args_185_, v_quiet_boxed_190_, v_input_x3f_187_, v_a_188_);
lean_dec(v_input_x3f_187_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__0(lean_object* v_stderr_192_, lean_object* v_____r_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_196_ = lean_string_utf8_byte_size(v_stderr_192_);
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_nat_dec_eq(v___x_196_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_199_ = ((lean_object*)(l_Lake_logOutput___redArg___lam__0___closed__0));
v___x_200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_200_, 0, v_stderr_192_);
lean_ctor_set(v___x_200_, 1, v___x_197_);
lean_ctor_set(v___x_200_, 2, v___x_196_);
v___x_201_ = l_String_Slice_trimAscii(v___x_200_);
v___x_202_ = l_String_Slice_toString(v___x_201_);
lean_dec_ref(v___x_201_);
v___x_203_ = lean_string_append(v___x_199_, v___x_202_);
lean_dec_ref(v___x_202_);
v___x_204_ = 1;
v___x_205_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_205_, 0, v___x_203_);
lean_ctor_set_uint8(v___x_205_, sizeof(void*)*1, v___x_204_);
v___x_206_ = lean_box(0);
v___x_207_ = lean_array_push(v___y_194_, v___x_205_);
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_206_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
return v___x_208_;
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec_ref(v_stderr_192_);
v___x_209_ = lean_box(0);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___y_194_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__0___boxed(lean_object* v_stderr_211_, lean_object* v_____r_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lake_proc___lam__0(v_stderr_211_, v_____r_212_, v___y_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__1(uint8_t v_quiet_216_, uint8_t v___x_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
if (v_quiet_216_ == 0)
{
uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_221_ = 1;
v___x_222_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_222_, 0, v___y_218_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*1, v___x_221_);
v___x_223_ = lean_box(0);
v___x_224_ = lean_array_push(v___y_219_, v___x_222_);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_226_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_226_, 0, v___y_218_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*1, v___x_217_);
v___x_227_ = lean_box(0);
v___x_228_ = lean_array_push(v___y_219_, v___x_226_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__1___boxed(lean_object* v_quiet_230_, lean_object* v___x_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
uint8_t v_quiet_boxed_235_; uint8_t v___x_5490__boxed_236_; lean_object* v_res_237_; 
v_quiet_boxed_235_ = lean_unbox(v_quiet_230_);
v___x_5490__boxed_236_ = lean_unbox(v___x_231_);
v_res_237_ = l_Lake_proc___lam__1(v_quiet_boxed_235_, v___x_5490__boxed_236_, v___y_232_, v___y_233_);
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
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___y_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
lean_dec_ref(v_args_262_);
v___x_315_ = lean_box(v_quiet_263_);
v___x_316_ = lean_box(v___x_275_);
v___y_317_ = lean_alloc_closure((void*)(l_Lake_proc___lam__1___boxed), 5, 2);
lean_closure_set(v___y_317_, 0, v___x_315_);
lean_closure_set(v___y_317_, 1, v___x_316_);
v___x_318_ = lean_string_utf8_byte_size(v_stdout_281_);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_nat_dec_eq(v___x_318_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v_a_327_; lean_object* v_a_328_; lean_object* v___x_329_; 
v___x_321_ = ((lean_object*)(l_Lake_logOutput___redArg___closed__0));
v___x_322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_322_, 0, v_stdout_281_);
lean_ctor_set(v___x_322_, 1, v___x_319_);
lean_ctor_set(v___x_322_, 2, v___x_318_);
v___x_323_ = l_String_Slice_trimAscii(v___x_322_);
v___x_324_ = l_String_Slice_toString(v___x_323_);
lean_dec_ref(v___x_323_);
v___x_325_ = lean_string_append(v___x_321_, v___x_324_);
lean_dec_ref(v___x_324_);
v___x_326_ = l_Lake_proc___lam__1(v_quiet_263_, v___x_275_, v___x_325_, v___x_277_);
v_a_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_327_);
v_a_328_ = lean_ctor_get(v___x_326_, 1);
lean_inc(v_a_328_);
lean_dec_ref(v___x_326_);
v___x_329_ = l_Lake_proc___lam__2(v_stderr_282_, v___y_317_, v_a_327_, v_a_328_);
v___y_272_ = v___x_329_;
goto v___jp_271_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec_ref(v_stdout_281_);
v___x_330_ = lean_box(0);
v___x_331_ = l_Lake_proc___lam__2(v_stderr_282_, v___y_317_, v___x_330_, v___x_277_);
v___y_272_ = v___x_331_;
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
lean_object* v_a_332_; lean_object* v_cmd_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_a_332_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_278_, 1);
v_cmd_333_ = lean_ctor_get(v_args_262_, 1);
lean_inc_ref(v_cmd_333_);
lean_dec_ref(v_args_262_);
v___x_334_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__0));
v___x_335_ = lean_string_append(v___x_334_, v_cmd_333_);
lean_dec_ref(v_cmd_333_);
v___x_336_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__1));
v___x_337_ = lean_string_append(v___x_335_, v___x_336_);
v___x_338_ = lean_io_error_to_string(v_a_332_);
v___x_339_ = lean_string_append(v___x_337_, v___x_338_);
lean_dec_ref(v___x_338_);
v___x_340_ = 3;
v___x_341_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set_uint8(v___x_341_, sizeof(void*)*1, v___x_340_);
v___x_342_ = lean_array_push(v___x_277_, v___x_341_);
v_a_269_ = v___x_342_;
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
LEAN_EXPORT lean_object* l_Lake_proc___boxed(lean_object* v_args_343_, lean_object* v_quiet_344_, lean_object* v_input_x3f_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
uint8_t v_quiet_boxed_348_; lean_object* v_res_349_; 
v_quiet_boxed_348_ = lean_unbox(v_quiet_344_);
v_res_349_ = l_Lake_proc(v_args_343_, v_quiet_boxed_348_, v_input_x3f_345_, v_a_346_);
lean_dec(v_input_x3f_345_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x27(lean_object* v_args_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_box(0);
lean_inc_ref(v_args_350_);
v___x_354_ = l_IO_Process_output(v_args_350_, v___x_353_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; uint32_t v_exitCode_356_; lean_object* v_stdout_357_; lean_object* v_stderr_358_; uint32_t v___x_359_; uint8_t v___x_360_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref_known(v___x_354_, 1);
v_exitCode_356_ = lean_ctor_get_uint32(v_a_355_, sizeof(void*)*2);
v_stdout_357_ = lean_ctor_get(v_a_355_, 0);
v_stderr_358_ = lean_ctor_get(v_a_355_, 1);
v___x_359_ = 0;
v___x_360_ = lean_uint32_dec_eq(v_exitCode_356_, v___x_359_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; uint8_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v_a_366_; lean_object* v___y_369_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
lean_inc_ref(v_stderr_358_);
lean_inc_ref(v_stdout_357_);
lean_dec(v_a_355_);
lean_inc_ref(v_args_350_);
v___x_361_ = l_Lake_mkCmdLog(v_args_350_);
v___x_362_ = 0;
v___x_363_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set_uint8(v___x_363_, sizeof(void*)*1, v___x_362_);
v___x_364_ = lean_array_get_size(v_a_351_);
v___x_383_ = lean_array_push(v_a_351_, v___x_363_);
v___x_384_ = lean_string_utf8_byte_size(v_stdout_357_);
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = lean_nat_dec_eq(v___x_384_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_387_ = ((lean_object*)(l_Lake_logOutput___redArg___closed__0));
v___x_388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_388_, 0, v_stdout_357_);
lean_ctor_set(v___x_388_, 1, v___x_385_);
lean_ctor_set(v___x_388_, 2, v___x_384_);
v___x_389_ = l_String_Slice_trimAscii(v___x_388_);
v___x_390_ = l_String_Slice_toString(v___x_389_);
lean_dec_ref(v___x_389_);
v___x_391_ = lean_string_append(v___x_387_, v___x_390_);
lean_dec_ref(v___x_390_);
v___x_392_ = 1;
v___x_393_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_393_, 0, v___x_391_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*1, v___x_392_);
v___x_394_ = lean_box(0);
v___x_395_ = lean_array_push(v___x_383_, v___x_393_);
v___x_396_ = l_Lake_proc___lam__0(v_stderr_358_, v___x_394_, v___x_395_);
v___y_369_ = v___x_396_;
goto v___jp_368_;
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec_ref(v_stdout_357_);
v___x_397_ = lean_box(0);
v___x_398_ = l_Lake_proc___lam__0(v_stderr_358_, v___x_397_, v___x_383_);
v___y_369_ = v___x_398_;
goto v___jp_368_;
}
v___jp_365_:
{
lean_object* v___x_367_; 
v___x_367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_364_);
lean_ctor_set(v___x_367_, 1, v_a_366_);
return v___x_367_;
}
v___jp_368_:
{
if (lean_obj_tag(v___y_369_) == 0)
{
lean_object* v_a_370_; lean_object* v_cmd_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_a_370_ = lean_ctor_get(v___y_369_, 1);
lean_inc(v_a_370_);
lean_dec_ref_known(v___y_369_, 2);
v_cmd_371_ = lean_ctor_get(v_args_350_, 1);
lean_inc_ref(v_cmd_371_);
lean_dec_ref(v_args_350_);
v___x_372_ = ((lean_object*)(l_Lake_proc___closed__0));
v___x_373_ = lean_string_append(v___x_372_, v_cmd_371_);
lean_dec_ref(v_cmd_371_);
v___x_374_ = ((lean_object*)(l_Lake_proc___closed__1));
v___x_375_ = lean_string_append(v___x_373_, v___x_374_);
v___x_376_ = lean_uint32_to_nat(v_exitCode_356_);
v___x_377_ = l_Nat_reprFast(v___x_376_);
v___x_378_ = lean_string_append(v___x_375_, v___x_377_);
lean_dec_ref(v___x_377_);
v___x_379_ = 3;
v___x_380_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set_uint8(v___x_380_, sizeof(void*)*1, v___x_379_);
v___x_381_ = lean_array_push(v_a_370_, v___x_380_);
v_a_366_ = v___x_381_;
goto v___jp_365_;
}
else
{
lean_object* v_a_382_; 
lean_dec_ref(v_args_350_);
v_a_382_ = lean_ctor_get(v___y_369_, 1);
lean_inc(v_a_382_);
lean_dec_ref_known(v___y_369_, 2);
v_a_366_ = v_a_382_;
goto v___jp_365_;
}
}
}
else
{
lean_object* v___x_399_; 
lean_dec_ref(v_args_350_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_a_355_);
lean_ctor_set(v___x_399_, 1, v_a_351_);
return v___x_399_;
}
}
else
{
lean_object* v_a_400_; lean_object* v_cmd_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_a_400_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_400_);
lean_dec_ref_known(v___x_354_, 1);
v_cmd_401_ = lean_ctor_get(v_args_350_, 1);
lean_inc_ref(v_cmd_401_);
lean_dec_ref(v_args_350_);
v___x_402_ = lean_array_get_size(v_a_351_);
v___x_403_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__0));
v___x_404_ = lean_string_append(v___x_403_, v_cmd_401_);
lean_dec_ref(v_cmd_401_);
v___x_405_ = ((lean_object*)(l_Lake_rawProc___lam__0___closed__1));
v___x_406_ = lean_string_append(v___x_404_, v___x_405_);
v___x_407_ = lean_io_error_to_string(v_a_400_);
v___x_408_ = lean_string_append(v___x_406_, v___x_407_);
lean_dec_ref(v___x_407_);
v___x_409_ = 3;
v___x_410_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_410_, 0, v___x_408_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*1, v___x_409_);
v___x_411_ = lean_array_push(v_a_351_, v___x_410_);
v___x_412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_402_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x27___boxed(lean_object* v_args_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lake_captureProc_x27(v_args_413_, v_a_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc(lean_object* v_args_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lake_captureProc_x27(v_args_417_, v_a_418_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_438_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_a_422_ = lean_ctor_get(v___x_420_, 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_438_ == 0)
{
v___x_424_ = v___x_420_;
v_isShared_425_ = v_isSharedCheck_438_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_438_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v_stdout_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v_str_431_; lean_object* v_startInclusive_432_; lean_object* v_endExclusive_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
v_stdout_426_ = lean_ctor_get(v_a_421_, 0);
lean_inc_ref(v_stdout_426_);
lean_dec(v_a_421_);
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = lean_string_utf8_byte_size(v_stdout_426_);
v___x_429_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_429_, 0, v_stdout_426_);
lean_ctor_set(v___x_429_, 1, v___x_427_);
lean_ctor_set(v___x_429_, 2, v___x_428_);
v___x_430_ = l_String_Slice_trimAscii(v___x_429_);
v_str_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc_ref(v_str_431_);
v_startInclusive_432_ = lean_ctor_get(v___x_430_, 1);
lean_inc(v_startInclusive_432_);
v_endExclusive_433_ = lean_ctor_get(v___x_430_, 2);
lean_inc(v_endExclusive_433_);
lean_dec_ref(v___x_430_);
v___x_434_ = lean_string_utf8_extract(v_str_431_, v_startInclusive_432_, v_endExclusive_433_);
lean_dec(v_endExclusive_433_);
lean_dec(v_startInclusive_432_);
lean_dec_ref(v_str_431_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_434_);
v___x_436_ = v___x_424_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_a_422_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
else
{
lean_object* v_a_439_; lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
v_a_439_ = lean_ctor_get(v___x_420_, 0);
v_a_440_ = lean_ctor_get(v___x_420_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_420_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_inc(v_a_439_);
lean_dec(v___x_420_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_439_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc___boxed(lean_object* v_args_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lake_captureProc(v_args_448_, v_a_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f(lean_object* v_args_452_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_box(0);
v___x_455_ = l_IO_Process_output(v_args_452_, v___x_454_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_475_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_475_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_475_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_475_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
uint32_t v_exitCode_460_; lean_object* v_stdout_461_; uint32_t v___x_462_; uint8_t v___x_463_; 
v_exitCode_460_ = lean_ctor_get_uint32(v_a_456_, sizeof(void*)*2);
v_stdout_461_ = lean_ctor_get(v_a_456_, 0);
lean_inc_ref(v_stdout_461_);
lean_dec(v_a_456_);
v___x_462_ = 0;
v___x_463_ = lean_uint32_dec_eq(v_exitCode_460_, v___x_462_);
if (v___x_463_ == 0)
{
lean_dec_ref(v_stdout_461_);
lean_del_object(v___x_458_);
return v___x_454_;
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_str_468_; lean_object* v_startInclusive_469_; lean_object* v_endExclusive_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = lean_string_utf8_byte_size(v_stdout_461_);
v___x_466_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_466_, 0, v_stdout_461_);
lean_ctor_set(v___x_466_, 1, v___x_464_);
lean_ctor_set(v___x_466_, 2, v___x_465_);
v___x_467_ = l_String_Slice_trimAscii(v___x_466_);
v_str_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc_ref(v_str_468_);
v_startInclusive_469_ = lean_ctor_get(v___x_467_, 1);
lean_inc(v_startInclusive_469_);
v_endExclusive_470_ = lean_ctor_get(v___x_467_, 2);
lean_inc(v_endExclusive_470_);
lean_dec_ref(v___x_467_);
v___x_471_ = lean_string_utf8_extract(v_str_468_, v_startInclusive_469_, v_endExclusive_470_);
lean_dec(v_endExclusive_470_);
lean_dec(v_startInclusive_469_);
lean_dec_ref(v_str_468_);
if (v_isShared_459_ == 0)
{
lean_ctor_set_tag(v___x_458_, 1);
lean_ctor_set(v___x_458_, 0, v___x_471_);
v___x_473_ = v___x_458_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_455_, 1);
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f___boxed(lean_object* v_args_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lake_captureProc_x3f(v_args_476_);
return v_res_478_;
}
}
LEAN_EXPORT uint8_t l_Lake_testProc(lean_object* v_args_481_){
_start:
{
lean_object* v___x_485_; lean_object* v_cmd_486_; lean_object* v_args_487_; lean_object* v_cwd_488_; lean_object* v_env_489_; uint8_t v_inheritEnv_490_; uint8_t v_setsid_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_505_; 
v___x_485_ = ((lean_object*)(l_Lake_testProc___closed__0));
v_cmd_486_ = lean_ctor_get(v_args_481_, 1);
v_args_487_ = lean_ctor_get(v_args_481_, 2);
v_cwd_488_ = lean_ctor_get(v_args_481_, 3);
v_env_489_ = lean_ctor_get(v_args_481_, 4);
v_inheritEnv_490_ = lean_ctor_get_uint8(v_args_481_, sizeof(void*)*5);
v_setsid_491_ = lean_ctor_get_uint8(v_args_481_, sizeof(void*)*5 + 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_args_481_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v_args_481_, 0);
lean_dec(v_unused_506_);
v___x_493_ = v_args_481_;
v_isShared_494_ = v_isSharedCheck_505_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_env_489_);
lean_inc(v_cwd_488_);
lean_inc(v_args_487_);
lean_inc(v_cmd_486_);
lean_dec(v_args_481_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_505_;
goto v_resetjp_492_;
}
v___jp_483_:
{
uint8_t v___x_484_; 
v___x_484_ = 0;
return v___x_484_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_485_);
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_cmd_486_);
lean_ctor_set(v_reuseFailAlloc_504_, 2, v_args_487_);
lean_ctor_set(v_reuseFailAlloc_504_, 3, v_cwd_488_);
lean_ctor_set(v_reuseFailAlloc_504_, 4, v_env_489_);
lean_ctor_set_uint8(v_reuseFailAlloc_504_, sizeof(void*)*5, v_inheritEnv_490_);
lean_ctor_set_uint8(v_reuseFailAlloc_504_, sizeof(void*)*5 + 1, v_setsid_491_);
v___x_496_ = v_reuseFailAlloc_504_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_497_; 
v___x_497_ = lean_io_process_spawn(v___x_496_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_499_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref_known(v___x_497_, 1);
v___x_499_ = lean_io_process_child_wait(v___x_485_, v_a_498_);
lean_dec(v_a_498_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; uint32_t v___x_501_; uint32_t v___x_502_; uint8_t v___x_503_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_499_, 1);
v___x_501_ = 0;
v___x_502_ = lean_unbox_uint32(v_a_500_);
lean_dec(v_a_500_);
v___x_503_ = lean_uint32_dec_eq(v___x_502_, v___x_501_);
return v___x_503_;
}
else
{
lean_dec_ref_known(v___x_499_, 1);
goto v___jp_483_;
}
}
else
{
lean_dec_ref_known(v___x_497_, 1);
goto v___jp_483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_testProc___boxed(lean_object* v_args_507_, lean_object* v_a_508_){
_start:
{
uint8_t v_res_509_; lean_object* v_r_510_; 
v_res_509_ = l_Lake_testProc(v_args_507_);
v_r_510_ = lean_box(v_res_509_);
return v_r_510_;
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
