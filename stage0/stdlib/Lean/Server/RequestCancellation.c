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
lean_object* l_Lean_Server_RequestCancellationToken_new(){
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
LEAN_EXPORT void l_Lean_Server_RequestCancellationToken_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Server_RequestCancellationToken_new();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_new___boxed(lean_object* v_a_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Server_RequestCancellationToken_new();
return v_res_9_;
}
}
lean_object* l_Lean_Server_RequestCancellationToken_cancelByCancelRequest(lean_object* v_tk_10_){
_start:
{
lean_object* v_cancelledByCancelRequest_12_; lean_object* v_requestCancellationPromise_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_cancelledByCancelRequest_12_ = lean_ctor_get(v_tk_10_, 0);
v_requestCancellationPromise_13_ = lean_ctor_get(v_tk_10_, 2);
v___x_14_ = l_IO_CancelToken_set(v_cancelledByCancelRequest_12_);
v___x_15_ = lean_box(0);
v___x_16_ = lean_io_promise_resolve(v___x_15_, v_requestCancellationPromise_13_);
return v___x_16_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestCancellationToken_cancelByCancelRequest_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_10_ = stack[0].m_obj;
lean_object* v_res_17_;
v_res_17_ = l_Lean_Server_RequestCancellationToken_cancelByCancelRequest(v_tk_10_);
stack->m_obj
 = v_res_17_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByCancelRequest___boxed(lean_object* v_tk_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Server_RequestCancellationToken_cancelByCancelRequest(v_tk_18_);
lean_dec_ref(v_tk_18_);
return v_res_20_;
}
}
lean_object* l_Lean_Server_RequestCancellationToken_cancelByEdit(lean_object* v_tk_21_){
_start:
{
lean_object* v_cancelledByEdit_23_; lean_object* v_editCancellationPromise_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v_cancelledByEdit_23_ = lean_ctor_get(v_tk_21_, 1);
v_editCancellationPromise_24_ = lean_ctor_get(v_tk_21_, 3);
v___x_25_ = l_IO_CancelToken_set(v_cancelledByEdit_23_);
v___x_26_ = lean_box(0);
v___x_27_ = lean_io_promise_resolve(v___x_26_, v_editCancellationPromise_24_);
return v___x_27_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestCancellationToken_cancelByEdit_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_21_ = stack[0].m_obj;
lean_object* v_res_28_;
v_res_28_ = l_Lean_Server_RequestCancellationToken_cancelByEdit(v_tk_21_);
stack->m_obj
 = v_res_28_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancelByEdit___boxed(lean_object* v_tk_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Server_RequestCancellationToken_cancelByEdit(v_tk_29_);
lean_dec_ref(v_tk_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0(lean_object* v_x_32_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
lean_object* v___x_33_; 
v___x_33_ = lean_box(0);
return v___x_33_;
}
else
{
lean_object* v_val_34_; 
v_val_34_ = lean_ctor_get(v_x_32_, 0);
lean_inc(v_val_34_);
return v_val_34_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0___boxed(lean_object* v_x_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0(v_x_35_);
lean_dec(v_x_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask(lean_object* v_tk_38_){
_start:
{
lean_object* v_requestCancellationPromise_39_; lean_object* v___f_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; lean_object* v___x_44_; 
v_requestCancellationPromise_39_ = lean_ctor_get(v_tk_38_, 2);
v___f_40_ = ((lean_object*)(l_Lean_Server_RequestCancellationToken_requestCancellationTask___closed__0));
v___x_41_ = lean_io_promise_result_opt(v_requestCancellationPromise_39_);
v___x_42_ = lean_unsigned_to_nat(0u);
v___x_43_ = 1;
v___x_44_ = lean_task_map(v___f_40_, v___x_41_, v___x_42_, v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask___boxed(lean_object* v_tk_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask(v_tk_45_);
lean_dec_ref(v_tk_45_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_editCancellationTask(lean_object* v_tk_47_){
_start:
{
lean_object* v_editCancellationPromise_48_; lean_object* v___f_49_; lean_object* v___x_50_; lean_object* v___x_51_; uint8_t v___x_52_; lean_object* v___x_53_; 
v_editCancellationPromise_48_ = lean_ctor_get(v_tk_47_, 3);
v___f_49_ = ((lean_object*)(l_Lean_Server_RequestCancellationToken_requestCancellationTask___closed__0));
v___x_50_ = lean_io_promise_result_opt(v_editCancellationPromise_48_);
v___x_51_ = lean_unsigned_to_nat(0u);
v___x_52_ = 1;
v___x_53_ = lean_task_map(v___f_49_, v___x_50_, v___x_51_, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_editCancellationTask___boxed(lean_object* v_tk_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_Server_RequestCancellationToken_editCancellationTask(v_tk_54_);
lean_dec_ref(v_tk_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancellationTasks(lean_object* v_tk_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_57_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask(v_tk_56_);
v___x_58_ = l_Lean_Server_RequestCancellationToken_editCancellationTask(v_tk_56_);
v___x_59_ = lean_box(0);
v___x_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
v___x_61_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_57_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_cancellationTasks___boxed(lean_object* v_tk_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_tk_62_);
lean_dec_ref(v_tk_62_);
return v_res_63_;
}
}
uint8_t l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(lean_object* v_tk_64_){
_start:
{
lean_object* v_cancelledByCancelRequest_66_; uint8_t v___x_67_; 
v_cancelledByCancelRequest_66_ = lean_ctor_get(v_tk_64_, 0);
v___x_67_ = l_IO_CancelToken_isSet(v_cancelledByCancelRequest_66_);
return v___x_67_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_64_ = stack[0].m_obj;
uint8_t v_res_68_;
v_res_68_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_tk_64_);
stack->m_num = v_res_68_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest___boxed(lean_object* v_tk_69_, lean_object* v_a_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_tk_69_);
lean_dec_ref(v_tk_69_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
uint8_t l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(lean_object* v_tk_73_){
_start:
{
lean_object* v_cancelledByEdit_75_; uint8_t v___x_76_; 
v_cancelledByEdit_75_ = lean_ctor_get(v_tk_73_, 1);
v___x_76_ = l_IO_CancelToken_isSet(v_cancelledByEdit_75_);
return v___x_76_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestCancellationToken_wasCancelledByEdit_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_73_ = stack[0].m_obj;
uint8_t v_res_77_;
v_res_77_ = l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(v_tk_73_);
stack->m_num = v_res_77_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelledByEdit___boxed(lean_object* v_tk_78_, lean_object* v_a_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(v_tk_78_);
lean_dec_ref(v_tk_78_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
uint8_t l_Lean_Server_RequestCancellationToken_wasCancelled(lean_object* v_tk_82_){
_start:
{
uint8_t v___x_84_; uint8_t v___x_85_; 
v___x_84_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_tk_82_);
v___x_85_ = l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(v_tk_82_);
if (v___x_84_ == 0)
{
return v___x_85_;
}
else
{
return v___x_84_;
}
}
}
LEAN_EXPORT void l_Lean_Server_RequestCancellationToken_wasCancelled_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_82_ = stack[0].m_obj;
uint8_t v_res_86_;
v_res_86_ = l_Lean_Server_RequestCancellationToken_wasCancelled(v_tk_82_);
stack->m_num = v_res_86_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellationToken_wasCancelled___boxed(lean_object* v_tk_87_, lean_object* v_a_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Lean_Server_RequestCancellationToken_wasCancelled(v_tk_87_);
lean_dec_ref(v_tk_87_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
static lean_object* _init_l_Lean_Server_RequestCancellation_requestCancelled(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_box(0);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_run___redArg(lean_object* v_tk_92_, lean_object* v_x_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_apply_1(v_x_93_, v_tk_92_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_run(lean_object* v_m_95_, lean_object* v_00_u03b1_96_, lean_object* v_tk_97_, lean_object* v_x_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_apply_1(v_x_98_, v_tk_97_);
return v___x_99_;
}
}
lean_object* l_Lean_Server_CancellableM_run___redArg(lean_object* v_tk_100_, lean_object* v_x_101_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lean_apply_2(v_x_101_, v_tk_100_, lean_box(0));
return v___x_103_;
}
}
LEAN_EXPORT void l_Lean_Server_CancellableM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_100_ = stack[0].m_obj;
lean_object* v_x_101_ = stack[1].m_obj;
lean_object* v_res_104_;
v_res_104_ = l_Lean_Server_CancellableM_run___redArg(v_tk_100_, v_x_101_);
stack->m_obj
 = v_res_104_;
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_run___redArg___boxed(lean_object* v_tk_105_, lean_object* v_x_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Server_CancellableM_run___redArg(v_tk_105_, v_x_106_);
return v_res_108_;
}
}
lean_object* l_Lean_Server_CancellableM_run(lean_object* v_00_u03b1_109_, lean_object* v_tk_110_, lean_object* v_x_111_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_apply_2(v_x_111_, v_tk_110_, lean_box(0));
return v___x_113_;
}
}
LEAN_EXPORT void l_Lean_Server_CancellableM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_110_ = stack[1].m_obj;
lean_object* v_x_111_ = stack[2].m_obj;
lean_object* v_res_114_;
v_res_114_ = l_Lean_Server_CancellableM_run(lean_box(0), v_tk_110_, v_x_111_);
stack->m_obj
 = v_res_114_;
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_run___boxed(lean_object* v_00_u03b1_115_, lean_object* v_tk_116_, lean_object* v_x_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Server_CancellableM_run(v_00_u03b1_115_, v_tk_116_, v_x_117_);
return v_res_119_;
}
}
lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0(uint8_t v_a_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_box(v_a_120_);
v___x_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT void l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_120_ = stack[0].m_num;
lean_object* v_res_123_;
v_res_123_ = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0(v_a_120_);
stack->m_obj
 = v_res_123_;
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0___boxed(lean_object* v_a_124_){
_start:
{
uint8_t v_a_626__boxed_125_; lean_object* v_res_126_; 
v_a_626__boxed_125_ = lean_unbox(v_a_124_);
v_res_126_ = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0(v_a_626__boxed_125_);
return v_res_126_;
}
}
lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1(lean_object* v_toPure_131_, uint8_t v_a_132_){
_start:
{
if (v_a_132_ == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0));
v___x_134_ = lean_apply_2(v_toPure_131_, lean_box(0), v___x_133_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1));
v___x_136_ = lean_apply_2(v_toPure_131_, lean_box(0), v___x_135_);
return v___x_136_;
}
}
}
LEAN_EXPORT void l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_131_ = stack[0].m_obj;
uint8_t v_a_132_ = stack[1].m_num;
lean_object* v_res_137_;
v_res_137_ = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1(v_toPure_131_, v_a_132_);
stack->m_obj
 = v_res_137_;
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___boxed(lean_object* v_toPure_138_, lean_object* v_a_139_){
_start:
{
uint8_t v_a_boxed_140_; lean_object* v_res_141_; 
v_a_boxed_140_ = lean_unbox(v_a_139_);
v_res_141_ = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1(v_toPure_138_, v_a_boxed_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___lam__2(lean_object* v_toFunctor_142_, lean_object* v_inst_143_, lean_object* v___f_144_, lean_object* v_inst_145_, lean_object* v___f_146_, lean_object* v_toBind_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_map_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_map_149_ = lean_ctor_get(v_toFunctor_142_, 0);
lean_inc(v_map_149_);
lean_dec_ref(v_toFunctor_142_);
v___x_150_ = lean_alloc_closure((void*)(l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest___boxed), 2, 1);
lean_closure_set(v___x_150_, 0, v_a_148_);
v___x_151_ = lean_apply_2(v_inst_143_, lean_box(0), v___x_150_);
v___x_152_ = lean_apply_4(v_map_149_, lean_box(0), lean_box(0), v___f_144_, v___x_151_);
v___x_153_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_153_, 0, lean_box(0));
lean_closure_set(v___x_153_, 1, lean_box(0));
lean_closure_set(v___x_153_, 2, v_inst_145_);
lean_closure_set(v___x_153_, 3, lean_box(0));
lean_closure_set(v___x_153_, 4, lean_box(0));
lean_closure_set(v___x_153_, 5, v___f_146_);
v___x_154_ = lean_apply_4(v_toBind_147_, lean_box(0), lean_box(0), v___x_152_, v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg(lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_a_158_){
_start:
{
lean_object* v_toApplicative_159_; lean_object* v_toBind_160_; lean_object* v_toFunctor_161_; lean_object* v_toPure_162_; lean_object* v___f_163_; lean_object* v___f_164_; lean_object* v___f_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_toApplicative_159_ = lean_ctor_get(v_inst_156_, 0);
v_toBind_160_ = lean_ctor_get(v_inst_156_, 1);
lean_inc_n(v_toBind_160_, 2);
v_toFunctor_161_ = lean_ctor_get(v_toApplicative_159_, 0);
v_toPure_162_ = lean_ctor_get(v_toApplicative_159_, 1);
v___f_163_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___redArg___closed__0));
lean_inc_n(v_toPure_162_, 2);
v___f_164_ = lean_alloc_closure((void*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_164_, 0, v_toPure_162_);
lean_inc_ref(v_inst_156_);
lean_inc_ref(v_toFunctor_161_);
v___f_165_ = lean_alloc_closure((void*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__2), 7, 6);
lean_closure_set(v___f_165_, 0, v_toFunctor_161_);
lean_closure_set(v___f_165_, 1, v_inst_157_);
lean_closure_set(v___f_165_, 2, v___f_163_);
lean_closure_set(v___f_165_, 3, v_inst_156_);
lean_closure_set(v___f_165_, 4, v___f_164_);
lean_closure_set(v___f_165_, 5, v_toBind_160_);
lean_inc_ref(v_a_158_);
v___x_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_166_, 0, v_a_158_);
v___x_167_ = lean_apply_2(v_toPure_162_, lean_box(0), v___x_166_);
v___x_168_ = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(v___x_168_, 0, lean_box(0));
lean_closure_set(v___x_168_, 1, lean_box(0));
lean_closure_set(v___x_168_, 2, v_inst_156_);
lean_closure_set(v___x_168_, 3, lean_box(0));
lean_closure_set(v___x_168_, 4, lean_box(0));
lean_closure_set(v___x_168_, 5, v___f_165_);
v___x_169_ = lean_apply_4(v_toBind_160_, lean_box(0), lean_box(0), v___x_167_, v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___redArg___boxed(lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Server_CancellableT_checkCancelled___redArg(v_inst_170_, v_inst_171_, v_a_172_);
lean_dec_ref(v_a_172_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled(lean_object* v_m_174_, lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Server_CancellableT_checkCancelled___redArg(v_inst_175_, v_inst_176_, v_a_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___boxed(lean_object* v_m_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Server_CancellableT_checkCancelled(v_m_179_, v_inst_180_, v_inst_181_, v_a_182_);
lean_dec_ref(v_a_182_);
return v_res_183_;
}
}
lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0(lean_object* v_a_184_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_a_184_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0));
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
return v___x_188_;
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1));
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
}
}
LEAN_EXPORT void l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_184_ = stack[0].m_obj;
lean_object* v_res_191_;
v_res_191_ = l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0(v_a_184_);
stack->m_obj
 = v_res_191_;
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0___boxed(lean_object* v_a_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0(v_a_192_);
lean_dec_ref(v_a_192_);
return v_res_194_;
}
}
lean_object* l_Lean_Server_CancellableM_checkCancelled(lean_object* v_a_195_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0(v_a_195_);
return v___x_197_;
}
}
LEAN_EXPORT void l_Lean_Server_CancellableM_checkCancelled_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_195_ = stack[0].m_obj;
lean_object* v_res_198_;
v_res_198_ = l_Lean_Server_CancellableM_checkCancelled(v_a_195_);
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l_Lean_Server_CancellableM_checkCancelled___boxed(lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Server_CancellableM_checkCancelled(v_a_199_);
lean_dec_ref(v_a_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableOfMonadLift___redArg(lean_object* v_inst_202_, lean_object* v_inst_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_apply_2(v_inst_202_, lean_box(0), v_inst_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableOfMonadLift(lean_object* v_m_205_, lean_object* v_n_206_, lean_object* v_inst_207_, lean_object* v_inst_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_apply_2(v_inst_207_, lean_box(0), v_inst_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableCancellableTOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_210_, lean_object* v_inst_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = lean_alloc_closure((void*)(l_Lean_Server_CancellableT_checkCancelled___boxed), 4, 3);
lean_closure_set(v___x_212_, 0, lean_box(0));
lean_closure_set(v___x_212_, 1, v_inst_210_);
lean_closure_set(v___x_212_, 2, v_inst_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadCancellableCancellableTOfMonadOfMonadLiftTBaseIO(lean_object* v_m_213_, lean_object* v_inst_214_, lean_object* v_inst_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_alloc_closure((void*)(l_Lean_Server_CancellableT_checkCancelled___boxed), 4, 3);
lean_closure_set(v___x_216_, 0, lean_box(0));
lean_closure_set(v___x_216_, 1, v_inst_214_);
lean_closure_set(v___x_216_, 2, v_inst_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check___redArg(lean_object* v_inst_217_){
_start:
{
lean_inc(v_inst_217_);
return v_inst_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check___redArg___boxed(lean_object* v_inst_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Server_RequestCancellation_check___redArg(v_inst_218_);
lean_dec(v_inst_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check(lean_object* v_m_220_, lean_object* v_inst_221_){
_start:
{
lean_inc(v_inst_221_);
return v_inst_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestCancellation_check___boxed(lean_object* v_m_222_, lean_object* v_inst_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_Server_RequestCancellation_check(v_m_222_, v_inst_223_);
lean_dec(v_inst_223_);
return v_res_224_;
}
}
lean_object* runtime_initialize_Lean_Server_ServerTask(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Promise(uint8_t builtin);
lean_object* runtime_initialize_Init_System_CancelToken(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_RequestCancellation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
