// Lean compiler output
// Module: Lean.Server.RequestCancellation
// Imports: public import Lean.Server.ServerTask public import Init.System.Promise
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_ExceptT_bindCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_2_ = 0;
v___x_3_ = lean_box(v___x_2_);
v___x_4_ = lean_st_mk_ref(v___x_3_);
v___x_5_ = lean_box(v___x_2_);
v___x_6_ = lean_st_mk_ref(v___x_5_);
v___x_7_ = lean_io_promise_new();
v___x_8_ = lean_io_promise_new();
v___x_9_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_9_, 0, v___x_4_);
lean_ctor_set(v___x_9_, 1, v___x_6_);
lean_ctor_set(v___x_9_, 2, v___x_7_);
lean_ctor_set(v___x_9_, 3, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_new___boxed(lean_object* v_a_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Server_RequestCancellationToken_new();
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByCancelRequest(lean_object* v_tk_12_){
_start:
{
lean_object* v_cancelledByCancelRequest_14_; lean_object* v_requestCancellationPromise_15_; uint8_t v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v_cancelledByCancelRequest_14_ = lean_ctor_get(v_tk_12_, 0);
v_requestCancellationPromise_15_ = lean_ctor_get(v_tk_12_, 2);
v___x_16_ = 1;
v___x_17_ = lean_box(v___x_16_);
v___x_18_ = lean_st_ref_set(v_cancelledByCancelRequest_14_, v___x_17_);
v___x_19_ = lean_box(0);
v___x_20_ = lean_io_promise_resolve(v___x_19_, v_requestCancellationPromise_15_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByCancelRequest___boxed(lean_object* v_tk_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Server_RequestCancellationToken_cancelByCancelRequest(v_tk_21_);
lean_dec_ref(v_tk_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByEdit(lean_object* v_tk_24_){
_start:
{
lean_object* v_cancelledByEdit_26_; lean_object* v_editCancellationPromise_27_; uint8_t v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_cancelledByEdit_26_ = lean_ctor_get(v_tk_24_, 1);
v_editCancellationPromise_27_ = lean_ctor_get(v_tk_24_, 3);
v___x_28_ = 1;
v___x_29_ = lean_box(v___x_28_);
v___x_30_ = lean_st_ref_set(v_cancelledByEdit_26_, v___x_29_);
v___x_31_ = lean_box(0);
v___x_32_ = lean_io_promise_resolve(v___x_31_, v_editCancellationPromise_27_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByEdit___boxed(lean_object* v_tk_33_, lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Server_RequestCancellationToken_cancelByEdit(v_tk_33_);
lean_dec_ref(v_tk_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0(lean_object* v_x_36_){
_start:
{
if (lean_obj_tag(v_x_36_) == 0)
{
lean_object* v___x_37_; 
v___x_37_ = lean_box(0);
return v___x_37_;
}
else
{
lean_object* v_val_38_; 
v_val_38_ = lean_ctor_get(v_x_36_, 0);
lean_inc(v_val_38_);
return v_val_38_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0___boxed(lean_object* v_x_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0(v_x_39_);
lean_dec(v_x_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask(lean_object* v_tk_42_){
_start:
{
lean_object* v_requestCancellationPromise_43_; lean_object* v___f_44_; lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; lean_object* v___x_48_; 
v_requestCancellationPromise_43_ = lean_ctor_get(v_tk_42_, 2);
v___f_44_ = ((lean_object*)(l_Lean_Server_RequestCancellationToken_requestCancellationTask___closed__0));
v___x_45_ = lean_io_promise_result_opt(v_requestCancellationPromise_43_);
v___x_46_ = lean_unsigned_to_nat(0u);
v___x_47_ = 1;
v___x_48_ = lean_task_map(v___f_44_, v___x_45_, v___x_46_, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask___boxed(lean_object* v_tk_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask(v_tk_49_);
lean_dec_ref(v_tk_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_editCancellationTask(lean_object* v_tk_51_){
_start:
{
lean_object* v_editCancellationPromise_52_; lean_object* v___f_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; lean_object* v___x_57_; 
v_editCancellationPromise_52_ = lean_ctor_get(v_tk_51_, 3);
v___f_53_ = ((lean_object*)(l_Lean_Server_RequestCancellationToken_requestCancellationTask___closed__0));
v___x_54_ = lean_io_promise_result_opt(v_editCancellationPromise_52_);
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = 1;
v___x_57_ = lean_task_map(v___f_53_, v___x_54_, v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_editCancellationTask___boxed(lean_object* v_tk_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_Server_RequestCancellationToken_editCancellationTask(v_tk_58_);
lean_dec_ref(v_tk_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancellationTasks(lean_object* v_tk_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_61_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask(v_tk_60_);
v___x_62_ = l_Lean_Server_RequestCancellationToken_editCancellationTask(v_tk_60_);
v___x_63_ = lean_box(0);
v___x_64_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_62_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
v___x_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_61_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancellationTasks___boxed(lean_object* v_tk_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_tk_66_);
lean_dec_ref(v_tk_66_);
return v_res_67_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(lean_object* v_tk_68_){
_start:
{
lean_object* v_cancelledByCancelRequest_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v_cancelledByCancelRequest_70_ = lean_ctor_get(v_tk_68_, 0);
v___x_71_ = lean_st_ref_get(v_cancelledByCancelRequest_70_);
v___x_72_ = lean_unbox(v___x_71_);
lean_dec(v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest___boxed(lean_object* v_tk_73_, lean_object* v_a_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_tk_73_);
lean_dec_ref(v_tk_73_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(lean_object* v_tk_77_){
_start:
{
lean_object* v_cancelledByEdit_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v_cancelledByEdit_79_ = lean_ctor_get(v_tk_77_, 1);
v___x_80_ = lean_st_ref_get(v_cancelledByEdit_79_);
v___x_81_ = lean_unbox(v___x_80_);
lean_dec(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelledByEdit___boxed(lean_object* v_tk_82_, lean_object* v_a_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(v_tk_82_);
lean_dec_ref(v_tk_82_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_RequestCancellationToken_wasCancelled(lean_object* v_tk_86_){
_start:
{
uint8_t v___x_88_; uint8_t v___x_89_; 
v___x_88_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_tk_86_);
v___x_89_ = l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(v_tk_86_);
if (v___x_88_ == 0)
{
return v___x_89_;
}
else
{
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelled___boxed(lean_object* v_tk_90_, lean_object* v_a_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Lean_Server_RequestCancellationToken_wasCancelled(v_tk_90_);
lean_dec_ref(v_tk_90_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_toCtorIdx(lean_object* v_x_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_unsigned_to_nat(0u);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Server_RequestCancellation_requestCancelled(void){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_box(0);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_run___redArg(lean_object* v_tk_97_, lean_object* v_x_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_apply_1(v_x_98_, v_tk_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_run(lean_object* v_m_100_, lean_object* v_00_u03b1_101_, lean_object* v_tk_102_, lean_object* v_x_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_apply_1(v_x_103_, v_tk_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_run___redArg(lean_object* v_tk_105_, lean_object* v_x_106_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_apply_2(v_x_106_, v_tk_105_, lean_box(0));
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_run___redArg___boxed(lean_object* v_tk_109_, lean_object* v_x_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_Server_CancellableM_run___redArg(v_tk_109_, v_x_110_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_run(lean_object* v_00_u03b1_113_, lean_object* v_tk_114_, lean_object* v_x_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = lean_apply_2(v_x_115_, v_tk_114_, lean_box(0));
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_run___boxed(lean_object* v_00_u03b1_118_, lean_object* v_tk_119_, lean_object* v_x_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Server_CancellableM_run(v_00_u03b1_118_, v_tk_119_, v_x_120_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0(uint8_t v_a_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_box(v_a_123_);
v___x_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0___boxed(lean_object* v_a_126_){
_start:
{
uint8_t v_a_669__boxed_127_; lean_object* v_res_128_; 
v_a_669__boxed_127_ = lean_unbox(v_a_126_);
v_res_128_ = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0(v_a_669__boxed_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1(lean_object* v_toPure_133_, uint8_t v_a_134_){
_start:
{
if (v_a_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0));
v___x_136_ = lean_apply_2(v_toPure_133_, lean_box(0), v___x_135_);
return v___x_136_;
}
else
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1));
v___x_138_ = lean_apply_2(v_toPure_133_, lean_box(0), v___x_137_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___boxed(lean_object* v_toPure_139_, lean_object* v_a_140_){
_start:
{
uint8_t v_a_boxed_141_; lean_object* v_res_142_; 
v_a_boxed_141_ = lean_unbox(v_a_140_);
v_res_142_ = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1(v_toPure_139_, v_a_boxed_141_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__2(lean_object* v_toFunctor_143_, lean_object* v_inst_144_, lean_object* v___f_145_, lean_object* v_inst_146_, lean_object* v___f_147_, lean_object* v_toBind_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_map_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_map_150_ = lean_ctor_get(v_toFunctor_143_, 0);
lean_inc(v_map_150_);
lean_dec_ref(v_toFunctor_143_);
v___x_151_ = lean_alloc_closure((void*)(l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest___boxed), 2, 1);
lean_closure_set(v___x_151_, 0, v_a_149_);
v___x_152_ = lean_apply_2(v_inst_144_, lean_box(0), v___x_151_);
v___x_153_ = lean_apply_4(v_map_150_, lean_box(0), lean_box(0), v___f_145_, v___x_152_);
v___x_154_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_154_, 0, lean_box(0));
lean_closure_set(v___x_154_, 1, lean_box(0));
lean_closure_set(v___x_154_, 2, v_inst_146_);
lean_closure_set(v___x_154_, 3, lean_box(0));
lean_closure_set(v___x_154_, 4, lean_box(0));
lean_closure_set(v___x_154_, 5, v___f_147_);
v___x_155_ = lean_apply_4(v_toBind_148_, lean_box(0), lean_box(0), v___x_153_, v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg(lean_object* v_inst_157_, lean_object* v_inst_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_toApplicative_160_; lean_object* v_toBind_161_; lean_object* v_toFunctor_162_; lean_object* v_toPure_163_; lean_object* v___f_164_; lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_toApplicative_160_ = lean_ctor_get(v_inst_157_, 0);
v_toBind_161_ = lean_ctor_get(v_inst_157_, 1);
lean_inc(v_toBind_161_);
v_toFunctor_162_ = lean_ctor_get(v_toApplicative_160_, 0);
v_toPure_163_ = lean_ctor_get(v_toApplicative_160_, 1);
v___f_164_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___redArg___closed__0));
lean_inc(v_toPure_163_);
v___f_165_ = lean_alloc_closure((void*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_165_, 0, v_toPure_163_);
lean_inc(v_toBind_161_);
lean_inc_ref(v_inst_157_);
lean_inc_ref(v_toFunctor_162_);
v___f_166_ = lean_alloc_closure((void*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__2), 7, 6);
lean_closure_set(v___f_166_, 0, v_toFunctor_162_);
lean_closure_set(v___f_166_, 1, v_inst_158_);
lean_closure_set(v___f_166_, 2, v___f_164_);
lean_closure_set(v___f_166_, 3, v_inst_157_);
lean_closure_set(v___f_166_, 4, v___f_165_);
lean_closure_set(v___f_166_, 5, v_toBind_161_);
v___x_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_167_, 0, v_a_159_);
lean_inc(v_toPure_163_);
v___x_168_ = lean_apply_2(v_toPure_163_, lean_box(0), v___x_167_);
v___x_169_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_169_, 0, lean_box(0));
lean_closure_set(v___x_169_, 1, lean_box(0));
lean_closure_set(v___x_169_, 2, v_inst_157_);
lean_closure_set(v___x_169_, 3, lean_box(0));
lean_closure_set(v___x_169_, 4, lean_box(0));
lean_closure_set(v___x_169_, 5, v___f_166_);
v___x_170_ = lean_apply_4(v_toBind_161_, lean_box(0), lean_box(0), v___x_168_, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled(lean_object* v_m_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_a_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Server_CancellableT_checkCancelled___redArg(v_inst_172_, v_inst_173_, v_a_174_);
return v___x_175_;
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
v___x_202_ = lean_alloc_closure((void*)(l_Lean_Server_CancellableT_checkCancelled), 4, 3);
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
v___x_206_ = lean_alloc_closure((void*)(l_Lean_Server_CancellableT_checkCancelled), 4, 3);
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
