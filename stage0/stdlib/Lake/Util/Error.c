// Lean compiler output
// Module: Lake.Util.Error
// Imports: public import Init.System.IO
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
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_EIO_toBaseIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorIO___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadErrorIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadErrorIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadErrorIO___closed__0 = (const lean_object*)&l_Lake_instMonadErrorIO___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadErrorIO = (const lean_object*)&l_Lake_instMonadErrorIO___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instMonadErrorEIOString___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorEIOString___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadErrorEIOString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadErrorEIOString___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadErrorEIOString___closed__0 = (const lean_object*)&l_Lake_instMonadErrorEIOString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadErrorEIOString = (const lean_object*)&l_Lake_instMonadErrorEIOString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instMonadErrorExceptString___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadErrorExceptString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadErrorExceptString___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadErrorExceptString___closed__0 = (const lean_object*)&l_Lake_instMonadErrorExceptString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadErrorExceptString = (const lean_object*)&l_Lake_instMonadErrorExceptString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_MonadError_runEIO___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadError_runEIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadError_runEIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadError_runIO___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadError_runIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadError_runIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorOfMonadLift___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_00_u03b1_3_, lean_object* v_msg_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_apply_2(v_inst_1_, lean_box(0), v_msg_4_);
v___x_6_ = lean_apply_2(v_inst_2_, lean_box(0), v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorOfMonadLift___redArg(lean_object* v_inst_7_, lean_object* v_inst_8_){
_start:
{
lean_object* v___f_9_; 
v___f_9_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_9_, 0, v_inst_8_);
lean_closure_set(v___f_9_, 1, v_inst_7_);
return v___f_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorOfMonadLift(lean_object* v_m_10_, lean_object* v_n_11_, lean_object* v_inst_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v___f_14_; 
v___f_14_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_14_, 0, v_inst_13_);
lean_closure_set(v___f_14_, 1, v_inst_12_);
return v___f_14_;
}
}
lean_object* l_Lake_instMonadErrorIO___lam__0(lean_object* v_00_u03b1_15_, lean_object* v_msg_16_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_mk_io_user_error(v_msg_16_);
v___x_19_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT void l_Lake_instMonadErrorIO___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_16_ = stack[1].m_obj;
lean_object* v_res_20_;
v_res_20_ = l_Lake_instMonadErrorIO___lam__0(lean_box(0), v_msg_16_);
stack->m_obj
 = v_res_20_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorIO___lam__0___boxed(lean_object* v_00_u03b1_21_, lean_object* v_msg_22_, lean_object* v___y_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lake_instMonadErrorIO___lam__0(v_00_u03b1_21_, v_msg_22_);
return v_res_24_;
}
}
lean_object* l_Lake_instMonadErrorEIOString___lam__0(lean_object* v_00_u03b1_27_, lean_object* v_msg_28_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_30_, 0, v_msg_28_);
return v___x_30_;
}
}
LEAN_EXPORT void l_Lake_instMonadErrorEIOString___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_28_ = stack[1].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lake_instMonadErrorEIOString___lam__0(lean_box(0), v_msg_28_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorEIOString___lam__0___boxed(lean_object* v_00_u03b1_32_, lean_object* v_msg_33_, lean_object* v___y_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lake_instMonadErrorEIOString___lam__0(v_00_u03b1_32_, v_msg_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorExceptString___lam__0(lean_object* v_00_u03b1_38_, lean_object* v_msg_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_40_, 0, v_msg_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadError_runEIO___redArg___lam__0(lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_toPure_45_, lean_object* v_____do__lift_46_){
_start:
{
if (lean_obj_tag(v_____do__lift_46_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_toPure_45_);
v_a_47_ = lean_ctor_get(v_____do__lift_46_, 0);
lean_inc(v_a_47_);
lean_dec_ref_known(v_____do__lift_46_, 1);
v___x_48_ = lean_apply_1(v_inst_43_, v_a_47_);
v___x_49_ = lean_apply_2(v_inst_44_, lean_box(0), v___x_48_);
return v___x_49_;
}
else
{
lean_object* v_a_50_; lean_object* v___x_51_; 
lean_dec(v_inst_44_);
lean_dec_ref(v_inst_43_);
v_a_50_ = lean_ctor_get(v_____do__lift_46_, 0);
lean_inc(v_a_50_);
lean_dec_ref_known(v_____do__lift_46_, 1);
v___x_51_ = lean_apply_2(v_toPure_45_, lean_box(0), v_a_50_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MonadError_runEIO___redArg(lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_toApplicative_57_; lean_object* v_toBind_58_; lean_object* v_toPure_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___f_62_; lean_object* v___x_63_; 
v_toApplicative_57_ = lean_ctor_get(v_inst_52_, 0);
lean_inc_ref(v_toApplicative_57_);
v_toBind_58_ = lean_ctor_get(v_inst_52_, 1);
lean_inc(v_toBind_58_);
lean_dec_ref(v_inst_52_);
v_toPure_59_ = lean_ctor_get(v_toApplicative_57_, 1);
lean_inc(v_toPure_59_);
lean_dec_ref(v_toApplicative_57_);
v___x_60_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_60_, 0, lean_box(0));
lean_closure_set(v___x_60_, 1, lean_box(0));
lean_closure_set(v___x_60_, 2, v_x_56_);
v___x_61_ = lean_apply_2(v_inst_54_, lean_box(0), v___x_60_);
v___f_62_ = lean_alloc_closure((void*)(l_Lake_MonadError_runEIO___redArg___lam__0), 4, 3);
lean_closure_set(v___f_62_, 0, v_inst_55_);
lean_closure_set(v___f_62_, 1, v_inst_53_);
lean_closure_set(v___f_62_, 2, v_toPure_59_);
v___x_63_ = lean_apply_4(v_toBind_58_, lean_box(0), lean_box(0), v___x_61_, v___f_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadError_runEIO(lean_object* v_m_64_, lean_object* v_00_u03b5_65_, lean_object* v_00_u03b1_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_x_71_){
_start:
{
lean_object* v_toApplicative_72_; lean_object* v_toBind_73_; lean_object* v_toPure_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___f_77_; lean_object* v___x_78_; 
v_toApplicative_72_ = lean_ctor_get(v_inst_67_, 0);
lean_inc_ref(v_toApplicative_72_);
v_toBind_73_ = lean_ctor_get(v_inst_67_, 1);
lean_inc(v_toBind_73_);
lean_dec_ref(v_inst_67_);
v_toPure_74_ = lean_ctor_get(v_toApplicative_72_, 1);
lean_inc(v_toPure_74_);
lean_dec_ref(v_toApplicative_72_);
v___x_75_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_75_, 0, lean_box(0));
lean_closure_set(v___x_75_, 1, lean_box(0));
lean_closure_set(v___x_75_, 2, v_x_71_);
v___x_76_ = lean_apply_2(v_inst_69_, lean_box(0), v___x_75_);
v___f_77_ = lean_alloc_closure((void*)(l_Lake_MonadError_runEIO___redArg___lam__0), 4, 3);
lean_closure_set(v___f_77_, 0, v_inst_70_);
lean_closure_set(v___f_77_, 1, v_inst_68_);
lean_closure_set(v___f_77_, 2, v_toPure_74_);
v___x_78_ = lean_apply_4(v_toBind_73_, lean_box(0), lean_box(0), v___x_76_, v___f_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadError_runIO___redArg___lam__0(lean_object* v_inst_79_, lean_object* v_toPure_80_, lean_object* v_____do__lift_81_){
_start:
{
if (lean_obj_tag(v_____do__lift_81_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec(v_toPure_80_);
v_a_82_ = lean_ctor_get(v_____do__lift_81_, 0);
lean_inc(v_a_82_);
lean_dec_ref_known(v_____do__lift_81_, 1);
v___x_83_ = lean_io_error_to_string(v_a_82_);
v___x_84_ = lean_apply_2(v_inst_79_, lean_box(0), v___x_83_);
return v___x_84_;
}
else
{
lean_object* v_a_85_; lean_object* v___x_86_; 
lean_dec(v_inst_79_);
v_a_85_ = lean_ctor_get(v_____do__lift_81_, 0);
lean_inc(v_a_85_);
lean_dec_ref_known(v_____do__lift_81_, 1);
v___x_86_ = lean_apply_2(v_toPure_80_, lean_box(0), v_a_85_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MonadError_runIO___redArg(lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_x_90_){
_start:
{
lean_object* v_toApplicative_91_; lean_object* v_toBind_92_; lean_object* v_toPure_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___f_96_; lean_object* v___x_97_; 
v_toApplicative_91_ = lean_ctor_get(v_inst_87_, 0);
lean_inc_ref(v_toApplicative_91_);
v_toBind_92_ = lean_ctor_get(v_inst_87_, 1);
lean_inc(v_toBind_92_);
lean_dec_ref(v_inst_87_);
v_toPure_93_ = lean_ctor_get(v_toApplicative_91_, 1);
lean_inc(v_toPure_93_);
lean_dec_ref(v_toApplicative_91_);
v___x_94_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_94_, 0, lean_box(0));
lean_closure_set(v___x_94_, 1, lean_box(0));
lean_closure_set(v___x_94_, 2, v_x_90_);
v___x_95_ = lean_apply_2(v_inst_89_, lean_box(0), v___x_94_);
v___f_96_ = lean_alloc_closure((void*)(l_Lake_MonadError_runIO___redArg___lam__0), 3, 2);
lean_closure_set(v___f_96_, 0, v_inst_88_);
lean_closure_set(v___f_96_, 1, v_toPure_93_);
v___x_97_ = lean_apply_4(v_toBind_92_, lean_box(0), lean_box(0), v___x_95_, v___f_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadError_runIO(lean_object* v_m_98_, lean_object* v_00_u03b1_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_x_103_){
_start:
{
lean_object* v_toApplicative_104_; lean_object* v_toBind_105_; lean_object* v_toPure_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___f_109_; lean_object* v___x_110_; 
v_toApplicative_104_ = lean_ctor_get(v_inst_100_, 0);
lean_inc_ref(v_toApplicative_104_);
v_toBind_105_ = lean_ctor_get(v_inst_100_, 1);
lean_inc(v_toBind_105_);
lean_dec_ref(v_inst_100_);
v_toPure_106_ = lean_ctor_get(v_toApplicative_104_, 1);
lean_inc(v_toPure_106_);
lean_dec_ref(v_toApplicative_104_);
v___x_107_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_107_, 0, lean_box(0));
lean_closure_set(v___x_107_, 1, lean_box(0));
lean_closure_set(v___x_107_, 2, v_x_103_);
v___x_108_ = lean_apply_2(v_inst_102_, lean_box(0), v___x_107_);
v___f_109_ = lean_alloc_closure((void*)(l_Lake_MonadError_runIO___redArg___lam__0), 3, 2);
lean_closure_set(v___f_109_, 0, v_inst_101_);
lean_closure_set(v___f_109_, 1, v_toPure_106_);
v___x_110_ = lean_apply_4(v_toBind_105_, lean_box(0), lean_box(0), v___x_108_, v___f_109_);
return v___x_110_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Error(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Error(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Error(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Error(builtin);
}
#ifdef __cplusplus
}
#endif
