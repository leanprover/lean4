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
LEAN_EXPORT lean_object* l_Lake_instMonadErrorIO___lam__0(lean_object* v_00_u03b1_15_, lean_object* v_msg_16_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_mk_io_user_error(v_msg_16_);
v___x_19_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorIO___lam__0___boxed(lean_object* v_00_u03b1_20_, lean_object* v_msg_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lake_instMonadErrorIO___lam__0(v_00_u03b1_20_, v_msg_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorEIOString___lam__0(lean_object* v_00_u03b1_26_, lean_object* v_msg_27_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_29_, 0, v_msg_27_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorEIOString___lam__0___boxed(lean_object* v_00_u03b1_30_, lean_object* v_msg_31_, lean_object* v___y_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lake_instMonadErrorEIOString___lam__0(v_00_u03b1_30_, v_msg_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorExceptString___lam__0(lean_object* v_00_u03b1_36_, lean_object* v_msg_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_38_, 0, v_msg_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadError_runEIO___redArg___lam__0(lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_toPure_43_, lean_object* v_____do__lift_44_){
_start:
{
if (lean_obj_tag(v_____do__lift_44_) == 0)
{
lean_object* v_a_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
lean_dec(v_toPure_43_);
v_a_45_ = lean_ctor_get(v_____do__lift_44_, 0);
lean_inc(v_a_45_);
lean_dec_ref(v_____do__lift_44_);
v___x_46_ = lean_apply_1(v_inst_41_, v_a_45_);
v___x_47_ = lean_apply_2(v_inst_42_, lean_box(0), v___x_46_);
return v___x_47_;
}
else
{
lean_object* v_a_48_; lean_object* v___x_49_; 
lean_dec(v_inst_42_);
lean_dec_ref(v_inst_41_);
v_a_48_ = lean_ctor_get(v_____do__lift_44_, 0);
lean_inc(v_a_48_);
lean_dec_ref(v_____do__lift_44_);
v___x_49_ = lean_apply_2(v_toPure_43_, lean_box(0), v_a_48_);
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MonadError_runEIO___redArg(lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_x_54_){
_start:
{
lean_object* v_toApplicative_55_; lean_object* v_toBind_56_; lean_object* v_toPure_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___f_60_; lean_object* v___x_61_; 
v_toApplicative_55_ = lean_ctor_get(v_inst_50_, 0);
lean_inc_ref(v_toApplicative_55_);
v_toBind_56_ = lean_ctor_get(v_inst_50_, 1);
lean_inc(v_toBind_56_);
lean_dec_ref(v_inst_50_);
v_toPure_57_ = lean_ctor_get(v_toApplicative_55_, 1);
lean_inc(v_toPure_57_);
lean_dec_ref(v_toApplicative_55_);
v___x_58_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_58_, 0, lean_box(0));
lean_closure_set(v___x_58_, 1, lean_box(0));
lean_closure_set(v___x_58_, 2, v_x_54_);
v___x_59_ = lean_apply_2(v_inst_52_, lean_box(0), v___x_58_);
v___f_60_ = lean_alloc_closure((void*)(l_Lake_MonadError_runEIO___redArg___lam__0), 4, 3);
lean_closure_set(v___f_60_, 0, v_inst_53_);
lean_closure_set(v___f_60_, 1, v_inst_51_);
lean_closure_set(v___f_60_, 2, v_toPure_57_);
v___x_61_ = lean_apply_4(v_toBind_56_, lean_box(0), lean_box(0), v___x_59_, v___f_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadError_runEIO(lean_object* v_m_62_, lean_object* v_00_u03b5_63_, lean_object* v_00_u03b1_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_x_69_){
_start:
{
lean_object* v_toApplicative_70_; lean_object* v_toBind_71_; lean_object* v_toPure_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___f_75_; lean_object* v___x_76_; 
v_toApplicative_70_ = lean_ctor_get(v_inst_65_, 0);
lean_inc_ref(v_toApplicative_70_);
v_toBind_71_ = lean_ctor_get(v_inst_65_, 1);
lean_inc(v_toBind_71_);
lean_dec_ref(v_inst_65_);
v_toPure_72_ = lean_ctor_get(v_toApplicative_70_, 1);
lean_inc(v_toPure_72_);
lean_dec_ref(v_toApplicative_70_);
v___x_73_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_73_, 0, lean_box(0));
lean_closure_set(v___x_73_, 1, lean_box(0));
lean_closure_set(v___x_73_, 2, v_x_69_);
v___x_74_ = lean_apply_2(v_inst_67_, lean_box(0), v___x_73_);
v___f_75_ = lean_alloc_closure((void*)(l_Lake_MonadError_runEIO___redArg___lam__0), 4, 3);
lean_closure_set(v___f_75_, 0, v_inst_68_);
lean_closure_set(v___f_75_, 1, v_inst_66_);
lean_closure_set(v___f_75_, 2, v_toPure_72_);
v___x_76_ = lean_apply_4(v_toBind_71_, lean_box(0), lean_box(0), v___x_74_, v___f_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadError_runIO___redArg___lam__0(lean_object* v_inst_77_, lean_object* v_toPure_78_, lean_object* v_____do__lift_79_){
_start:
{
if (lean_obj_tag(v_____do__lift_79_) == 0)
{
lean_object* v_a_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_toPure_78_);
v_a_80_ = lean_ctor_get(v_____do__lift_79_, 0);
lean_inc(v_a_80_);
lean_dec_ref(v_____do__lift_79_);
v___x_81_ = lean_io_error_to_string(v_a_80_);
v___x_82_ = lean_apply_2(v_inst_77_, lean_box(0), v___x_81_);
return v___x_82_;
}
else
{
lean_object* v_a_83_; lean_object* v___x_84_; 
lean_dec(v_inst_77_);
v_a_83_ = lean_ctor_get(v_____do__lift_79_, 0);
lean_inc(v_a_83_);
lean_dec_ref(v_____do__lift_79_);
v___x_84_ = lean_apply_2(v_toPure_78_, lean_box(0), v_a_83_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MonadError_runIO___redArg(lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_x_88_){
_start:
{
lean_object* v_toApplicative_89_; lean_object* v_toBind_90_; lean_object* v_toPure_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___f_94_; lean_object* v___x_95_; 
v_toApplicative_89_ = lean_ctor_get(v_inst_85_, 0);
lean_inc_ref(v_toApplicative_89_);
v_toBind_90_ = lean_ctor_get(v_inst_85_, 1);
lean_inc(v_toBind_90_);
lean_dec_ref(v_inst_85_);
v_toPure_91_ = lean_ctor_get(v_toApplicative_89_, 1);
lean_inc(v_toPure_91_);
lean_dec_ref(v_toApplicative_89_);
v___x_92_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_92_, 0, lean_box(0));
lean_closure_set(v___x_92_, 1, lean_box(0));
lean_closure_set(v___x_92_, 2, v_x_88_);
v___x_93_ = lean_apply_2(v_inst_87_, lean_box(0), v___x_92_);
v___f_94_ = lean_alloc_closure((void*)(l_Lake_MonadError_runIO___redArg___lam__0), 3, 2);
lean_closure_set(v___f_94_, 0, v_inst_86_);
lean_closure_set(v___f_94_, 1, v_toPure_91_);
v___x_95_ = lean_apply_4(v_toBind_90_, lean_box(0), lean_box(0), v___x_93_, v___f_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadError_runIO(lean_object* v_m_96_, lean_object* v_00_u03b1_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_x_101_){
_start:
{
lean_object* v_toApplicative_102_; lean_object* v_toBind_103_; lean_object* v_toPure_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___f_107_; lean_object* v___x_108_; 
v_toApplicative_102_ = lean_ctor_get(v_inst_98_, 0);
lean_inc_ref(v_toApplicative_102_);
v_toBind_103_ = lean_ctor_get(v_inst_98_, 1);
lean_inc(v_toBind_103_);
lean_dec_ref(v_inst_98_);
v_toPure_104_ = lean_ctor_get(v_toApplicative_102_, 1);
lean_inc(v_toPure_104_);
lean_dec_ref(v_toApplicative_102_);
v___x_105_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_105_, 0, lean_box(0));
lean_closure_set(v___x_105_, 1, lean_box(0));
lean_closure_set(v___x_105_, 2, v_x_101_);
v___x_106_ = lean_apply_2(v_inst_100_, lean_box(0), v___x_105_);
v___f_107_ = lean_alloc_closure((void*)(l_Lake_MonadError_runIO___redArg___lam__0), 3, 2);
lean_closure_set(v___f_107_, 0, v_inst_99_);
lean_closure_set(v___f_107_, 1, v_toPure_104_);
v___x_108_ = lean_apply_4(v_toBind_103_, lean_box(0), lean_box(0), v___x_106_, v___f_107_);
return v___x_108_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Error(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
