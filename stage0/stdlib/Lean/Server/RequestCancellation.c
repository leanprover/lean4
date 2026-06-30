// Lean compiler output
// Module: Lean.Server.RequestCancellation
// Imports: public import Lean.Server.ServerTask public import Init.System.Promise public import Init.System.CancelToken
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
lean_object* l_IO_CancelToken_set(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_IO_CancelToken_isSet(lean_object*);
lean_object* l_ExceptT_bindCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_CancelToken_new();
lean_object* lean_io_promise_new();
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_new();
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_new___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByCancelRequest(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByCancelRequest___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByEdit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByEdit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Server_RequestCancellationToken_requestCancellationTask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask___closed__0 = (const lean_object*)&l_Lean_Server_RequestCancellationToken_requestCancellationTask___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_editCancellationTask(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_editCancellationTask___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancellationTasks(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancellationTasks___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelledByEdit___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_RequestCancellationToken_wasCancelled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelled___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_toCtorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_requestCancelled;
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_run___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0___boxed(lean_object*);
static const lean_ctor_object l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_CancellableT_checkCancelled___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___closed__0 = (const lean_object*)&l_Lean_Server_CancellableT_checkCancelled___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_checkCancelled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_checkCancelled___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableCancellableTOfMonadOfMonadLiftTBaseIO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableCancellableTOfMonadOfMonadLiftTBaseIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_new(){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_2_ = l_IO_CancelToken_new();
v___x_3_ = l_IO_CancelToken_new();
v___x_4_ = lean_io_promise_new();
v___x_5_ = lean_io_promise_new();
v___x_6_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6_, 0, v___x_2_);
lean_ctor_set(v___x_6_, 1, v___x_3_);
lean_ctor_set(v___x_6_, 2, v___x_4_);
lean_ctor_set(v___x_6_, 3, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_new___boxed(lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Server_RequestCancellationToken_new();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByCancelRequest(lean_object* v_tk_9_){
_start:
{
lean_object* v_cancelledByCancelRequest_11_; lean_object* v_requestCancellationPromise_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_cancelledByCancelRequest_11_ = lean_ctor_get(v_tk_9_, 0);
v_requestCancellationPromise_12_ = lean_ctor_get(v_tk_9_, 2);
v___x_13_ = l_IO_CancelToken_set(v_cancelledByCancelRequest_11_);
v___x_14_ = lean_box(0);
v___x_15_ = lean_io_promise_resolve(v___x_14_, v_requestCancellationPromise_12_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByCancelRequest___boxed(lean_object* v_tk_16_, lean_object* v_a_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Server_RequestCancellationToken_cancelByCancelRequest(v_tk_16_);
lean_dec_ref(v_tk_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByEdit(lean_object* v_tk_19_){
_start:
{
lean_object* v_cancelledByEdit_21_; lean_object* v_editCancellationPromise_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v_cancelledByEdit_21_ = lean_ctor_get(v_tk_19_, 1);
v_editCancellationPromise_22_ = lean_ctor_get(v_tk_19_, 3);
v___x_23_ = l_IO_CancelToken_set(v_cancelledByEdit_21_);
v___x_24_ = lean_box(0);
v___x_25_ = lean_io_promise_resolve(v___x_24_, v_editCancellationPromise_22_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByEdit___boxed(lean_object* v_tk_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Server_RequestCancellationToken_cancelByEdit(v_tk_26_);
lean_dec_ref(v_tk_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0(lean_object* v_x_29_){
_start:
{
if (lean_obj_tag(v_x_29_) == 0)
{
lean_object* v___x_30_; 
v___x_30_ = lean_box(0);
return v___x_30_;
}
else
{
lean_object* v_val_31_; 
v_val_31_ = lean_ctor_get(v_x_29_, 0);
lean_inc(v_val_31_);
return v_val_31_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0___boxed(lean_object* v_x_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0(v_x_32_);
lean_dec(v_x_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask(lean_object* v_tk_35_){
_start:
{
lean_object* v_requestCancellationPromise_36_; lean_object* v___f_37_; lean_object* v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; lean_object* v___x_41_; 
v_requestCancellationPromise_36_ = lean_ctor_get(v_tk_35_, 2);
v___f_37_ = ((lean_object*)(l_Lean_Server_RequestCancellationToken_requestCancellationTask___closed__0));
v___x_38_ = lean_io_promise_result_opt(v_requestCancellationPromise_36_);
v___x_39_ = lean_unsigned_to_nat(0u);
v___x_40_ = 1;
v___x_41_ = lean_task_map(v___f_37_, v___x_38_, v___x_39_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask___boxed(lean_object* v_tk_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask(v_tk_42_);
lean_dec_ref(v_tk_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_editCancellationTask(lean_object* v_tk_44_){
_start:
{
lean_object* v_editCancellationPromise_45_; lean_object* v___f_46_; lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; lean_object* v___x_50_; 
v_editCancellationPromise_45_ = lean_ctor_get(v_tk_44_, 3);
v___f_46_ = ((lean_object*)(l_Lean_Server_RequestCancellationToken_requestCancellationTask___closed__0));
v___x_47_ = lean_io_promise_result_opt(v_editCancellationPromise_45_);
v___x_48_ = lean_unsigned_to_nat(0u);
v___x_49_ = 1;
v___x_50_ = lean_task_map(v___f_46_, v___x_47_, v___x_48_, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_editCancellationTask___boxed(lean_object* v_tk_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Server_RequestCancellationToken_editCancellationTask(v_tk_51_);
lean_dec_ref(v_tk_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancellationTasks(lean_object* v_tk_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_54_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask(v_tk_53_);
v___x_55_ = l_Lean_Server_RequestCancellationToken_editCancellationTask(v_tk_53_);
v___x_56_ = lean_box(0);
v___x_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
v___x_58_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_54_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancellationTasks___boxed(lean_object* v_tk_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_tk_59_);
lean_dec_ref(v_tk_59_);
return v_res_60_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(lean_object* v_tk_61_){
_start:
{
lean_object* v_cancelledByCancelRequest_63_; uint8_t v___x_64_; 
v_cancelledByCancelRequest_63_ = lean_ctor_get(v_tk_61_, 0);
v___x_64_ = l_IO_CancelToken_isSet(v_cancelledByCancelRequest_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest___boxed(lean_object* v_tk_65_, lean_object* v_a_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_tk_65_);
lean_dec_ref(v_tk_65_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(lean_object* v_tk_69_){
_start:
{
lean_object* v_cancelledByEdit_71_; uint8_t v___x_72_; 
v_cancelledByEdit_71_ = lean_ctor_get(v_tk_69_, 1);
v___x_72_ = l_IO_CancelToken_isSet(v_cancelledByEdit_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelledByEdit___boxed(lean_object* v_tk_73_, lean_object* v_a_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(v_tk_73_);
lean_dec_ref(v_tk_73_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_RequestCancellationToken_wasCancelled(lean_object* v_tk_77_){
_start:
{
uint8_t v___x_79_; uint8_t v___x_80_; 
v___x_79_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_tk_77_);
v___x_80_ = l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(v_tk_77_);
if (v___x_79_ == 0)
{
return v___x_80_;
}
else
{
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelled___boxed(lean_object* v_tk_81_, lean_object* v_a_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l_Lean_Server_RequestCancellationToken_wasCancelled(v_tk_81_);
lean_dec_ref(v_tk_81_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_toCtorIdx(lean_object* v_x_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_unsigned_to_nat(0u);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_Server_RequestCancellation_requestCancelled(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_box(0);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_run___redArg(lean_object* v_tk_88_, lean_object* v_x_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_apply_1(v_x_89_, v_tk_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_run(lean_object* v_m_91_, lean_object* v_00_u03b1_92_, lean_object* v_tk_93_, lean_object* v_x_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_apply_1(v_x_94_, v_tk_93_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_run___redArg(lean_object* v_tk_96_, lean_object* v_x_97_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_apply_2(v_x_97_, v_tk_96_, lean_box(0));
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_run___redArg___boxed(lean_object* v_tk_100_, lean_object* v_x_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_Server_CancellableM_run___redArg(v_tk_100_, v_x_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_run(lean_object* v_00_u03b1_104_, lean_object* v_tk_105_, lean_object* v_x_106_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_apply_2(v_x_106_, v_tk_105_, lean_box(0));
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_run___boxed(lean_object* v_00_u03b1_109_, lean_object* v_tk_110_, lean_object* v_x_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Server_CancellableM_run(v_00_u03b1_109_, v_tk_110_, v_x_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0(uint8_t v_a_114_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_box(v_a_114_);
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0___boxed(lean_object* v_a_117_){
_start:
{
uint8_t v_a_668__boxed_118_; lean_object* v_res_119_; 
v_a_668__boxed_118_ = lean_unbox(v_a_117_);
v_res_119_ = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0(v_a_668__boxed_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1(lean_object* v_toPure_124_, uint8_t v_a_125_){
_start:
{
if (v_a_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0));
v___x_127_ = lean_apply_2(v_toPure_124_, lean_box(0), v___x_126_);
return v___x_127_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1));
v___x_129_ = lean_apply_2(v_toPure_124_, lean_box(0), v___x_128_);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___boxed(lean_object* v_toPure_130_, lean_object* v_a_131_){
_start:
{
uint8_t v_a_boxed_132_; lean_object* v_res_133_; 
v_a_boxed_132_ = lean_unbox(v_a_131_);
v_res_133_ = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1(v_toPure_130_, v_a_boxed_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__2(lean_object* v_toFunctor_134_, lean_object* v_inst_135_, lean_object* v___f_136_, lean_object* v_inst_137_, lean_object* v___f_138_, lean_object* v_toBind_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_map_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_map_141_ = lean_ctor_get(v_toFunctor_134_, 0);
lean_inc(v_map_141_);
lean_dec_ref(v_toFunctor_134_);
v___x_142_ = lean_alloc_closure((void*)(l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest___boxed), 2, 1);
lean_closure_set(v___x_142_, 0, v_a_140_);
v___x_143_ = lean_apply_2(v_inst_135_, lean_box(0), v___x_142_);
v___x_144_ = lean_apply_4(v_map_141_, lean_box(0), lean_box(0), v___f_136_, v___x_143_);
v___x_145_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_145_, 0, lean_box(0));
lean_closure_set(v___x_145_, 1, lean_box(0));
lean_closure_set(v___x_145_, 2, v_inst_137_);
lean_closure_set(v___x_145_, 3, lean_box(0));
lean_closure_set(v___x_145_, 4, lean_box(0));
lean_closure_set(v___x_145_, 5, v___f_138_);
v___x_146_ = lean_apply_4(v_toBind_139_, lean_box(0), lean_box(0), v___x_144_, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg(lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_toApplicative_151_; lean_object* v_toBind_152_; lean_object* v_toFunctor_153_; lean_object* v_toPure_154_; lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_toApplicative_151_ = lean_ctor_get(v_inst_148_, 0);
v_toBind_152_ = lean_ctor_get(v_inst_148_, 1);
lean_inc_n(v_toBind_152_, 2);
v_toFunctor_153_ = lean_ctor_get(v_toApplicative_151_, 0);
v_toPure_154_ = lean_ctor_get(v_toApplicative_151_, 1);
v___f_155_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___redArg___closed__0));
lean_inc_n(v_toPure_154_, 2);
v___f_156_ = lean_alloc_closure((void*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_156_, 0, v_toPure_154_);
lean_inc_ref(v_inst_148_);
lean_inc_ref(v_toFunctor_153_);
v___f_157_ = lean_alloc_closure((void*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__2), 7, 6);
lean_closure_set(v___f_157_, 0, v_toFunctor_153_);
lean_closure_set(v___f_157_, 1, v_inst_149_);
lean_closure_set(v___f_157_, 2, v___f_155_);
lean_closure_set(v___f_157_, 3, v_inst_148_);
lean_closure_set(v___f_157_, 4, v___f_156_);
lean_closure_set(v___f_157_, 5, v_toBind_152_);
lean_inc_ref(v_a_150_);
v___x_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_158_, 0, v_a_150_);
v___x_159_ = lean_apply_2(v_toPure_154_, lean_box(0), v___x_158_);
v___x_160_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_160_, 0, lean_box(0));
lean_closure_set(v___x_160_, 1, lean_box(0));
lean_closure_set(v___x_160_, 2, v_inst_148_);
lean_closure_set(v___x_160_, 3, lean_box(0));
lean_closure_set(v___x_160_, 4, lean_box(0));
lean_closure_set(v___x_160_, 5, v___f_157_);
v___x_161_ = lean_apply_4(v_toBind_152_, lean_box(0), lean_box(0), v___x_159_, v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___boxed(lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Server_CancellableT_checkCancelled___redArg(v_inst_162_, v_inst_163_, v_a_164_);
lean_dec_ref(v_a_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled(lean_object* v_m_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_a_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_Server_CancellableT_checkCancelled___redArg(v_inst_167_, v_inst_168_, v_a_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___boxed(lean_object* v_m_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Server_CancellableT_checkCancelled(v_m_171_, v_inst_172_, v_inst_173_, v_a_174_);
lean_dec_ref(v_a_174_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0(lean_object* v_a_176_){
_start:
{
uint8_t v___x_178_; 
v___x_178_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_a_176_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0));
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
return v___x_180_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1));
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0___boxed(lean_object* v_a_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0(v_a_183_);
lean_dec_ref(v_a_183_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_checkCancelled(lean_object* v_a_186_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0(v_a_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_checkCancelled___boxed(lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Server_CancellableM_checkCancelled(v_a_189_);
lean_dec_ref(v_a_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableOfMonadLift___redArg(lean_object* v_inst_192_, lean_object* v_inst_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_apply_2(v_inst_192_, lean_box(0), v_inst_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableOfMonadLift(lean_object* v_m_195_, lean_object* v_n_196_, lean_object* v_inst_197_, lean_object* v_inst_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_apply_2(v_inst_197_, lean_box(0), v_inst_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableCancellableTOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_200_, lean_object* v_inst_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lean_alloc_closure((void*)(l_Lean_Server_CancellableT_checkCancelled___boxed), 4, 3);
lean_closure_set(v___x_202_, 0, lean_box(0));
lean_closure_set(v___x_202_, 1, v_inst_200_);
lean_closure_set(v___x_202_, 2, v_inst_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableCancellableTOfMonadOfMonadLiftTBaseIO(lean_object* v_m_203_, lean_object* v_inst_204_, lean_object* v_inst_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_alloc_closure((void*)(l_Lean_Server_CancellableT_checkCancelled___boxed), 4, 3);
lean_closure_set(v___x_206_, 0, lean_box(0));
lean_closure_set(v___x_206_, 1, v_inst_204_);
lean_closure_set(v___x_206_, 2, v_inst_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check___redArg(lean_object* v_inst_207_){
_start:
{
lean_inc(v_inst_207_);
return v_inst_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check___redArg___boxed(lean_object* v_inst_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Server_RequestCancellation_check___redArg(v_inst_208_);
lean_dec(v_inst_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check(lean_object* v_m_210_, lean_object* v_inst_211_){
_start:
{
lean_inc(v_inst_211_);
return v_inst_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check___boxed(lean_object* v_m_212_, lean_object* v_inst_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Server_RequestCancellation_check(v_m_212_, v_inst_213_);
lean_dec(v_inst_213_);
return v_res_214_;
}
}
lean_object* runtime_initialize_Lean_Server_ServerTask(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Promise(uint8_t builtin);
lean_object* runtime_initialize_Init_System_CancelToken(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_RequestCancellation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Server_ServerTask(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_CancelToken(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_RequestCancellation_requestCancelled = _init_l_Lean_Server_RequestCancellation_requestCancelled();
lean_mark_persistent(l_Lean_Server_RequestCancellation_requestCancelled);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_RequestCancellation(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_ServerTask(uint8_t builtin);
lean_object* initialize_Init_System_Promise(uint8_t builtin);
lean_object* initialize_Init_System_CancelToken(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_RequestCancellation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_ServerTask(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_CancelToken(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_RequestCancellation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_RequestCancellation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_RequestCancellation(builtin);
}
#ifdef __cplusplus
}
#endif
