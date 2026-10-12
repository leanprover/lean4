// Lean compiler output
// Module: Lake.Util.Lock
// Imports: public import Init.System.IO import Init.Data.ToString.Macro
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
lean_object* l_IO_sleep(uint32_t);
lean_object* lean_get_stderr();
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
uint32_t lean_io_process_get_pid();
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_IO_eprintln___redArg(lean_object*, lean_object*);
lean_object* l_IO_FS_removeFile___boxed(lean_object*, lean_object*);
lean_object* l_instMonadExceptOfEIO___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "warning: waiting for prior `lake build` invocation to finish... (remove '"};
static const lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__0 = (const lean_object*)&l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__0_value;
static const lean_string_object l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "' if stuck)"};
static const lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__1 = (const lean_object*)&l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__1___boxed(lean_object*);
static const lean_string_object l_Lake_withLockFile___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "warning: `"};
static const lean_object* l_Lake_withLockFile___redArg___lam__2___closed__0 = (const lean_object*)&l_Lake_withLockFile___redArg___lam__2___closed__0_value;
static const lean_string_object l_Lake_withLockFile___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "` was deleted before the lock was released"};
static const lean_object* l_Lake_withLockFile___redArg___lam__2___closed__1 = (const lean_object*)&l_Lake_withLockFile___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_withLockFile___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_withLockFile___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_withLockFile___redArg___closed__0 = (const lean_object*)&l_Lake_withLockFile___redArg___closed__0_value;
static const lean_closure_object l_Lake_withLockFile___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_withLockFile___redArg___closed__1 = (const lean_object*)&l_Lake_withLockFile___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0(lean_object* v_lockFile_1_, lean_object* v_____r_2_){
_start:
{
uint8_t v___x_4_; lean_object* v___x_5_; 
v___x_4_ = 2;
v___x_5_ = lean_io_prim_handle_mk(v_lockFile_1_, v___x_4_);
if (lean_obj_tag(v___x_5_) == 0)
{
lean_object* v_a_6_; uint32_t v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_a_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_a_6_);
lean_dec_ref_known(v___x_5_, 1);
v___x_7_ = lean_io_process_get_pid();
v___x_8_ = lean_uint32_to_nat(v___x_7_);
v___x_9_ = l_Nat_reprFast(v___x_8_);
v___x_10_ = l_IO_FS_Handle_putStrLn(v_a_6_, v___x_9_);
lean_dec(v_a_6_);
return v___x_10_;
}
else
{
lean_object* v_a_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_18_; 
v_a_11_ = lean_ctor_get(v___x_5_, 0);
v_isSharedCheck_18_ = !lean_is_exclusive(v___x_5_);
if (v_isSharedCheck_18_ == 0)
{
v___x_13_ = v___x_5_;
v_isShared_14_ = v_isSharedCheck_18_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_a_11_);
lean_dec(v___x_5_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_18_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_16_; 
if (v_isShared_14_ == 0)
{
v___x_16_ = v___x_13_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v_a_11_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lockFile_1_ = stack[0].m_obj;
lean_object* v_____r_2_ = stack[1].m_obj;
lean_object* v_res_19_;
v_res_19_ = l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0(v_lockFile_1_, v_____r_2_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0___boxed(lean_object* v_lockFile_20_, lean_object* v_____r_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0(v_lockFile_20_, v_____r_21_);
lean_dec_ref(v_lockFile_20_);
return v_res_23_;
}
}
lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop(lean_object* v_lockFile_26_, uint8_t v_firstTime_27_){
_start:
{
lean_object* v___y_35_; lean_object* v___x_45_; 
lean_inc_ref(v_lockFile_26_);
v___x_45_ = l_System_FilePath_parent(v_lockFile_26_);
if (lean_obj_tag(v___x_45_) == 1)
{
lean_object* v_val_46_; lean_object* v___x_47_; 
v_val_46_ = lean_ctor_get(v___x_45_, 0);
lean_inc(v_val_46_);
lean_dec_ref_known(v___x_45_, 1);
v___x_47_ = l_IO_FS_createDirAll(v_val_46_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; lean_object* v___x_49_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_a_48_);
lean_dec_ref_known(v___x_47_, 1);
v___x_49_ = l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0(v_lockFile_26_, v_a_48_);
v___y_35_ = v___x_49_;
goto v___jp_34_;
}
else
{
v___y_35_ = v___x_47_;
goto v___jp_34_;
}
}
else
{
lean_object* v___x_50_; lean_object* v___x_51_; 
lean_dec(v___x_45_);
v___x_50_ = lean_box(0);
v___x_51_ = l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0(v_lockFile_26_, v___x_50_);
v___y_35_ = v___x_51_;
goto v___jp_34_;
}
v___jp_29_:
{
uint32_t v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_30_ = 300;
v___x_31_ = l_IO_sleep(v___x_30_);
v___x_32_ = 0;
v_firstTime_27_ = v___x_32_;
goto _start;
}
v___jp_34_:
{
if (lean_obj_tag(v___y_35_) == 0)
{
lean_dec_ref(v_lockFile_26_);
return v___y_35_;
}
else
{
lean_object* v_a_36_; 
v_a_36_ = lean_ctor_get(v___y_35_, 0);
if (lean_obj_tag(v_a_36_) == 0)
{
lean_dec_ref_known(v___y_35_, 1);
if (v_firstTime_27_ == 0)
{
goto v___jp_29_;
}
else
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_37_ = lean_get_stderr();
v___x_38_ = ((lean_object*)(l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__0));
v___x_39_ = lean_string_append(v___x_38_, v_lockFile_26_);
v___x_40_ = ((lean_object*)(l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__1));
v___x_41_ = lean_string_append(v___x_39_, v___x_40_);
lean_inc_ref(v___x_37_);
v___x_42_ = l_IO_FS_Stream_putStrLn(v___x_37_, v___x_41_);
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v_flush_43_; lean_object* v___x_44_; 
lean_dec_ref_known(v___x_42_, 1);
v_flush_43_ = lean_ctor_get(v___x_37_, 0);
lean_inc_ref(v_flush_43_);
lean_dec_ref(v___x_37_);
v___x_44_ = lean_apply_1(v_flush_43_, lean_box(0));
if (lean_obj_tag(v___x_44_) == 0)
{
lean_dec_ref_known(v___x_44_, 1);
goto v___jp_29_;
}
else
{
lean_dec_ref(v_lockFile_26_);
return v___x_44_;
}
}
else
{
lean_dec_ref(v___x_37_);
lean_dec_ref(v_lockFile_26_);
return v___x_42_;
}
}
}
else
{
lean_dec_ref(v_lockFile_26_);
return v___y_35_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop_0interp(lean_interpreter_value* stack)
{
lean_object* v_lockFile_26_ = stack[0].m_obj;
uint8_t v_firstTime_27_ = stack[1].m_num;
lean_object* v_res_52_;
v_res_52_ = l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop(v_lockFile_26_, v_firstTime_27_);
stack->m_obj
 = v_res_52_;
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___boxed(lean_object* v_lockFile_53_, lean_object* v_firstTime_54_, lean_object* v_a_55_){
_start:
{
uint8_t v_firstTime_boxed_56_; lean_object* v_res_57_; 
v_firstTime_boxed_56_ = lean_unbox(v_firstTime_54_);
v_res_57_ = l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop(v_lockFile_53_, v_firstTime_boxed_56_);
return v_res_57_;
}
}
lean_object* l_Lake_busyAcquireLockFile(lean_object* v_lockFile_58_){
_start:
{
uint8_t v___x_60_; lean_object* v___x_61_; 
v___x_60_ = 1;
v___x_61_ = l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop(v_lockFile_58_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT void l_Lake_busyAcquireLockFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_lockFile_58_ = stack[0].m_obj;
lean_object* v_res_62_;
v_res_62_ = l_Lake_busyAcquireLockFile(v_lockFile_58_);
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile___boxed(lean_object* v_lockFile_63_, lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lake_busyAcquireLockFile(v_lockFile_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__0(lean_object* v_act_66_, lean_object* v_____r_67_){
_start:
{
lean_inc(v_act_66_);
return v_act_66_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__0___boxed(lean_object* v_act_68_, lean_object* v_____r_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lake_withLockFile___redArg___lam__0(v_act_68_, v_____r_69_);
lean_dec(v_act_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__1(lean_object* v_x_71_){
_start:
{
lean_object* v_fst_72_; 
v_fst_72_ = lean_ctor_get(v_x_71_, 0);
lean_inc(v_fst_72_);
return v_fst_72_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__1___boxed(lean_object* v_x_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lake_withLockFile___redArg___lam__1(v_x_73_);
lean_dec_ref(v_x_73_);
return v_res_74_;
}
}
lean_object* l_Lake_withLockFile___redArg___lam__2(lean_object* v_lockFile_77_, lean_object* v___f_78_, lean_object* v_x_79_){
_start:
{
if (lean_obj_tag(v_x_79_) == 11)
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec_ref_known(v_x_79_, 2);
v___x_81_ = ((lean_object*)(l_Lake_withLockFile___redArg___lam__2___closed__0));
v___x_82_ = lean_string_append(v___x_81_, v_lockFile_77_);
v___x_83_ = ((lean_object*)(l_Lake_withLockFile___redArg___lam__2___closed__1));
v___x_84_ = lean_string_append(v___x_82_, v___x_83_);
v___x_85_ = l_IO_eprintln___redArg(v___f_78_, v___x_84_);
return v___x_85_;
}
else
{
lean_object* v___x_86_; 
lean_dec_ref(v___f_78_);
v___x_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_86_, 0, v_x_79_);
return v___x_86_;
}
}
}
LEAN_EXPORT void l_Lake_withLockFile___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_lockFile_77_ = stack[0].m_obj;
lean_object* v___f_78_ = stack[1].m_obj;
lean_object* v_x_79_ = stack[2].m_obj;
lean_object* v_res_87_;
v_res_87_ = l_Lake_withLockFile___redArg___lam__2(v_lockFile_77_, v___f_78_, v_x_79_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__2___boxed(lean_object* v_lockFile_88_, lean_object* v___f_89_, lean_object* v_x_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lake_withLockFile___redArg___lam__2(v_lockFile_88_, v___f_89_, v_x_90_);
lean_dec_ref(v_lockFile_88_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__3(lean_object* v___x_93_, lean_object* v_x_94_){
_start:
{
lean_inc(v___x_93_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__3___boxed(lean_object* v___x_95_, lean_object* v_x_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lake_withLockFile___redArg___lam__3(v___x_95_, v_x_96_);
lean_dec(v_x_96_);
lean_dec(v___x_95_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg(lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_lockFile_103_, lean_object* v_act_104_){
_start:
{
lean_object* v_toApplicative_105_; lean_object* v_toFunctor_106_; lean_object* v_toBind_107_; lean_object* v_map_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___f_111_; lean_object* v___f_112_; lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v_this_117_; lean_object* v___x_118_; lean_object* v___f_119_; lean_object* v_y_120_; lean_object* v___x_121_; 
v_toApplicative_105_ = lean_ctor_get(v_inst_100_, 0);
v_toFunctor_106_ = lean_ctor_get(v_toApplicative_105_, 0);
lean_inc_ref(v_toFunctor_106_);
v_toBind_107_ = lean_ctor_get(v_inst_100_, 1);
lean_inc(v_toBind_107_);
lean_dec_ref(v_inst_100_);
v_map_108_ = lean_ctor_get(v_toFunctor_106_, 0);
lean_inc(v_map_108_);
lean_dec_ref(v_toFunctor_106_);
lean_inc_ref_n(v_lockFile_103_, 2);
v___x_109_ = lean_alloc_closure((void*)(l_Lake_busyAcquireLockFile___boxed), 2, 1);
lean_closure_set(v___x_109_, 0, v_lockFile_103_);
lean_inc(v_inst_102_);
v___x_110_ = lean_apply_2(v_inst_102_, lean_box(0), v___x_109_);
v___f_111_ = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_111_, 0, v_act_104_);
v___f_112_ = ((lean_object*)(l_Lake_withLockFile___redArg___closed__0));
v___f_113_ = ((lean_object*)(l_Lake_withLockFile___redArg___closed__1));
v___f_114_ = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_114_, 0, v_lockFile_103_);
lean_closure_set(v___f_114_, 1, v___f_113_);
v___x_115_ = lean_apply_4(v_toBind_107_, lean_box(0), lean_box(0), v___x_110_, v___f_111_);
v___x_116_ = lean_alloc_closure((void*)(l_IO_FS_removeFile___boxed), 2, 1);
lean_closure_set(v___x_116_, 0, v_lockFile_103_);
v_this_117_ = lean_alloc_closure((void*)(l_instMonadExceptOfEIO___aux__3___boxed), 5, 4);
lean_closure_set(v_this_117_, 0, lean_box(0));
lean_closure_set(v_this_117_, 1, lean_box(0));
lean_closure_set(v_this_117_, 2, v___x_116_);
lean_closure_set(v_this_117_, 3, v___f_114_);
v___x_118_ = lean_apply_2(v_inst_102_, lean_box(0), v_this_117_);
v___f_119_ = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__3___boxed), 2, 1);
lean_closure_set(v___f_119_, 0, v___x_118_);
v_y_120_ = lean_apply_4(v_inst_101_, lean_box(0), lean_box(0), v___x_115_, v___f_119_);
v___x_121_ = lean_apply_4(v_map_108_, lean_box(0), lean_box(0), v___f_112_, v_y_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile(lean_object* v_m_122_, lean_object* v_00_u03b1_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_lockFile_127_, lean_object* v_act_128_){
_start:
{
lean_object* v_toApplicative_129_; lean_object* v_toFunctor_130_; lean_object* v_toBind_131_; lean_object* v_map_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___f_135_; lean_object* v___f_136_; lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v_this_141_; lean_object* v___x_142_; lean_object* v___f_143_; lean_object* v_y_144_; lean_object* v___x_145_; 
v_toApplicative_129_ = lean_ctor_get(v_inst_124_, 0);
v_toFunctor_130_ = lean_ctor_get(v_toApplicative_129_, 0);
lean_inc_ref(v_toFunctor_130_);
v_toBind_131_ = lean_ctor_get(v_inst_124_, 1);
lean_inc(v_toBind_131_);
lean_dec_ref(v_inst_124_);
v_map_132_ = lean_ctor_get(v_toFunctor_130_, 0);
lean_inc(v_map_132_);
lean_dec_ref(v_toFunctor_130_);
lean_inc_ref_n(v_lockFile_127_, 2);
v___x_133_ = lean_alloc_closure((void*)(l_Lake_busyAcquireLockFile___boxed), 2, 1);
lean_closure_set(v___x_133_, 0, v_lockFile_127_);
lean_inc(v_inst_126_);
v___x_134_ = lean_apply_2(v_inst_126_, lean_box(0), v___x_133_);
v___f_135_ = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_135_, 0, v_act_128_);
v___f_136_ = ((lean_object*)(l_Lake_withLockFile___redArg___closed__0));
v___f_137_ = ((lean_object*)(l_Lake_withLockFile___redArg___closed__1));
v___f_138_ = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_138_, 0, v_lockFile_127_);
lean_closure_set(v___f_138_, 1, v___f_137_);
v___x_139_ = lean_apply_4(v_toBind_131_, lean_box(0), lean_box(0), v___x_134_, v___f_135_);
v___x_140_ = lean_alloc_closure((void*)(l_IO_FS_removeFile___boxed), 2, 1);
lean_closure_set(v___x_140_, 0, v_lockFile_127_);
v_this_141_ = lean_alloc_closure((void*)(l_instMonadExceptOfEIO___aux__3___boxed), 5, 4);
lean_closure_set(v_this_141_, 0, lean_box(0));
lean_closure_set(v_this_141_, 1, lean_box(0));
lean_closure_set(v_this_141_, 2, v___x_140_);
lean_closure_set(v_this_141_, 3, v___f_138_);
v___x_142_ = lean_apply_2(v_inst_126_, lean_box(0), v_this_141_);
v___f_143_ = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__3___boxed), 2, 1);
lean_closure_set(v___f_143_, 0, v___x_142_);
v_y_144_ = lean_apply_4(v_inst_125_, lean_box(0), lean_box(0), v___x_139_, v___f_143_);
v___x_145_ = lean_apply_4(v_map_132_, lean_box(0), lean_box(0), v___f_136_, v_y_144_);
return v___x_145_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Lock(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Lock(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Lock(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Lock(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Lock(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Lock(builtin);
}
#ifdef __cplusplus
}
#endif
