// Lean compiler output
// Module: Init.Task
// Imports: public import Init.Core import Init.Data.List.Basic import Init.Data.Nat.Bitwise.Basic
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_task_spawn(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Task_0__Task_mapList_go___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Task_0__Task_mapList_go___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Task_0__Task_mapList_go___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Task_0__Task_mapList_go___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Task_0__Task_mapList_go___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Task_0__Task_mapList_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Task_0__Task_mapList_go(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Task_0__Task_mapList_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Task_mapList___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Task_mapList___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Task_mapList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Task_mapList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Task_0__Task_mapList_go___redArg___lam__0(lean_object* v_x_1_, lean_object* v_f_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = l_List_reverse___redArg(v_x_1_);
v___x_5_ = lean_apply_1(v_f_2_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Task_0__Task_mapList_go___redArg___lam__1(lean_object* v_x_6_, lean_object* v_f_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_9_, 0, v_a_8_);
lean_ctor_set(v___x_9_, 1, v_x_6_);
v___x_10_ = l_List_reverse___redArg(v___x_9_);
v___x_11_ = lean_apply_1(v_f_7_, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Task_0__Task_mapList_go___redArg___lam__2___boxed(lean_object* v_x_12_, lean_object* v_f_13_, lean_object* v_prio_14_, lean_object* v_sync_15_, lean_object* v_tail_16_, lean_object* v_a_17_){
_start:
{
uint8_t v_sync_boxed_18_; lean_object* v_res_19_; 
v_sync_boxed_18_ = lean_unbox(v_sync_15_);
v_res_19_ = l___private_Init_Task_0__Task_mapList_go___redArg___lam__2(v_x_12_, v_f_13_, v_prio_14_, v_sync_boxed_18_, v_tail_16_, v_a_17_);
return v_res_19_;
}
}
lean_object* l___private_Init_Task_0__Task_mapList_go___redArg(lean_object* v_f_20_, lean_object* v_prio_21_, uint8_t v_sync_22_, lean_object* v_x_23_, lean_object* v_x_24_){
_start:
{
if (lean_obj_tag(v_x_23_) == 0)
{
if (v_sync_22_ == 0)
{
lean_object* v___f_25_; lean_object* v___x_26_; 
v___f_25_ = lean_alloc_closure((void*)(l___private_Init_Task_0__Task_mapList_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_25_, 0, v_x_24_);
lean_closure_set(v___f_25_, 1, v_f_20_);
v___x_26_ = lean_task_spawn(v___f_25_, v_prio_21_);
return v___x_26_;
}
else
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
lean_dec(v_prio_21_);
v___x_27_ = l_List_reverse___redArg(v_x_24_);
v___x_28_ = lean_apply_1(v_f_20_, v___x_27_);
v___x_29_ = lean_task_pure(v___x_28_);
return v___x_29_;
}
}
else
{
lean_object* v_tail_30_; 
v_tail_30_ = lean_ctor_get(v_x_23_, 1);
if (lean_obj_tag(v_tail_30_) == 0)
{
lean_object* v_head_31_; lean_object* v___f_32_; lean_object* v___x_33_; 
v_head_31_ = lean_ctor_get(v_x_23_, 0);
lean_inc(v_head_31_);
lean_dec_ref_known(v_x_23_, 2);
v___f_32_ = lean_alloc_closure((void*)(l___private_Init_Task_0__Task_mapList_go___redArg___lam__1), 3, 2);
lean_closure_set(v___f_32_, 0, v_x_24_);
lean_closure_set(v___f_32_, 1, v_f_20_);
v___x_33_ = lean_task_map(v___f_32_, v_head_31_, v_prio_21_, v_sync_22_);
return v___x_33_;
}
else
{
lean_object* v_head_34_; lean_object* v___x_35_; lean_object* v___f_36_; lean_object* v___x_37_; 
lean_inc(v_tail_30_);
v_head_34_ = lean_ctor_get(v_x_23_, 0);
lean_inc(v_head_34_);
lean_dec_ref_known(v_x_23_, 2);
v___x_35_ = lean_box(v_sync_22_);
lean_inc(v_prio_21_);
v___f_36_ = lean_alloc_closure((void*)(l___private_Init_Task_0__Task_mapList_go___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_36_, 0, v_x_24_);
lean_closure_set(v___f_36_, 1, v_f_20_);
lean_closure_set(v___f_36_, 2, v_prio_21_);
lean_closure_set(v___f_36_, 3, v___x_35_);
lean_closure_set(v___f_36_, 4, v_tail_30_);
v___x_37_ = lean_task_bind(v_head_34_, v___f_36_, v_prio_21_, v_sync_22_);
return v___x_37_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Task_0__Task_mapList_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_20_ = stack[0].m_obj;
lean_object* v_prio_21_ = stack[1].m_obj;
uint8_t v_sync_22_ = stack[2].m_num;
lean_object* v_x_23_ = stack[3].m_obj;
lean_object* v_x_24_ = stack[4].m_obj;
lean_object* v_res_38_;
v_res_38_ = l___private_Init_Task_0__Task_mapList_go___redArg(v_f_20_, v_prio_21_, v_sync_22_, v_x_23_, v_x_24_);
stack->m_obj
 = v_res_38_;
}
lean_object* l___private_Init_Task_0__Task_mapList_go___redArg___lam__2(lean_object* v_x_39_, lean_object* v_f_40_, lean_object* v_prio_41_, uint8_t v_sync_42_, lean_object* v_tail_43_, lean_object* v_a_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_45_, 0, v_a_44_);
lean_ctor_set(v___x_45_, 1, v_x_39_);
v___x_46_ = l___private_Init_Task_0__Task_mapList_go___redArg(v_f_40_, v_prio_41_, v_sync_42_, v_tail_43_, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT void l___private_Init_Task_0__Task_mapList_go___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_39_ = stack[0].m_obj;
lean_object* v_f_40_ = stack[1].m_obj;
lean_object* v_prio_41_ = stack[2].m_obj;
uint8_t v_sync_42_ = stack[3].m_num;
lean_object* v_tail_43_ = stack[4].m_obj;
lean_object* v_a_44_ = stack[5].m_obj;
lean_object* v_res_47_;
v_res_47_ = l___private_Init_Task_0__Task_mapList_go___redArg___lam__2(v_x_39_, v_f_40_, v_prio_41_, v_sync_42_, v_tail_43_, v_a_44_);
stack->m_obj
 = v_res_47_;
}
LEAN_EXPORT lean_object* l___private_Init_Task_0__Task_mapList_go___redArg___boxed(lean_object* v_f_48_, lean_object* v_prio_49_, lean_object* v_sync_50_, lean_object* v_x_51_, lean_object* v_x_52_){
_start:
{
uint8_t v_sync_boxed_53_; lean_object* v_res_54_; 
v_sync_boxed_53_ = lean_unbox(v_sync_50_);
v_res_54_ = l___private_Init_Task_0__Task_mapList_go___redArg(v_f_48_, v_prio_49_, v_sync_boxed_53_, v_x_51_, v_x_52_);
return v_res_54_;
}
}
lean_object* l___private_Init_Task_0__Task_mapList_go(lean_object* v_00_u03b1_55_, lean_object* v_00_u03b2_56_, lean_object* v_f_57_, lean_object* v_prio_58_, uint8_t v_sync_59_, lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l___private_Init_Task_0__Task_mapList_go___redArg(v_f_57_, v_prio_58_, v_sync_59_, v_x_60_, v_x_61_);
return v___x_62_;
}
}
LEAN_EXPORT void l___private_Init_Task_0__Task_mapList_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_57_ = stack[2].m_obj;
lean_object* v_prio_58_ = stack[3].m_obj;
uint8_t v_sync_59_ = stack[4].m_num;
lean_object* v_x_60_ = stack[5].m_obj;
lean_object* v_x_61_ = stack[6].m_obj;
lean_object* v_res_63_;
v_res_63_ = l___private_Init_Task_0__Task_mapList_go(lean_box(0), lean_box(0), v_f_57_, v_prio_58_, v_sync_59_, v_x_60_, v_x_61_);
stack->m_obj
 = v_res_63_;
}
LEAN_EXPORT lean_object* l___private_Init_Task_0__Task_mapList_go___boxed(lean_object* v_00_u03b1_64_, lean_object* v_00_u03b2_65_, lean_object* v_f_66_, lean_object* v_prio_67_, lean_object* v_sync_68_, lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
uint8_t v_sync_boxed_71_; lean_object* v_res_72_; 
v_sync_boxed_71_ = lean_unbox(v_sync_68_);
v_res_72_ = l___private_Init_Task_0__Task_mapList_go(v_00_u03b1_64_, v_00_u03b2_65_, v_f_66_, v_prio_67_, v_sync_boxed_71_, v_x_69_, v_x_70_);
return v_res_72_;
}
}
lean_object* l_Task_mapList___redArg(lean_object* v_f_73_, lean_object* v_tasks_74_, lean_object* v_prio_75_, uint8_t v_sync_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_box(0);
v___x_78_ = l___private_Init_Task_0__Task_mapList_go___redArg(v_f_73_, v_prio_75_, v_sync_76_, v_tasks_74_, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT void l_Task_mapList___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_73_ = stack[0].m_obj;
lean_object* v_tasks_74_ = stack[1].m_obj;
lean_object* v_prio_75_ = stack[2].m_obj;
uint8_t v_sync_76_ = stack[3].m_num;
lean_object* v_res_79_;
v_res_79_ = l_Task_mapList___redArg(v_f_73_, v_tasks_74_, v_prio_75_, v_sync_76_);
stack->m_obj
 = v_res_79_;
}
LEAN_EXPORT lean_object* l_Task_mapList___redArg___boxed(lean_object* v_f_80_, lean_object* v_tasks_81_, lean_object* v_prio_82_, lean_object* v_sync_83_){
_start:
{
uint8_t v_sync_boxed_84_; lean_object* v_res_85_; 
v_sync_boxed_84_ = lean_unbox(v_sync_83_);
v_res_85_ = l_Task_mapList___redArg(v_f_80_, v_tasks_81_, v_prio_82_, v_sync_boxed_84_);
return v_res_85_;
}
}
lean_object* l_Task_mapList(lean_object* v_00_u03b1_86_, lean_object* v_00_u03b2_87_, lean_object* v_f_88_, lean_object* v_tasks_89_, lean_object* v_prio_90_, uint8_t v_sync_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Task_mapList___redArg(v_f_88_, v_tasks_89_, v_prio_90_, v_sync_91_);
return v___x_92_;
}
}
LEAN_EXPORT void l_Task_mapList_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_88_ = stack[2].m_obj;
lean_object* v_tasks_89_ = stack[3].m_obj;
lean_object* v_prio_90_ = stack[4].m_obj;
uint8_t v_sync_91_ = stack[5].m_num;
lean_object* v_res_93_;
v_res_93_ = l_Task_mapList(lean_box(0), lean_box(0), v_f_88_, v_tasks_89_, v_prio_90_, v_sync_91_);
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l_Task_mapList___boxed(lean_object* v_00_u03b1_94_, lean_object* v_00_u03b2_95_, lean_object* v_f_96_, lean_object* v_tasks_97_, lean_object* v_prio_98_, lean_object* v_sync_99_){
_start:
{
uint8_t v_sync_boxed_100_; lean_object* v_res_101_; 
v_sync_boxed_100_ = lean_unbox(v_sync_99_);
v_res_101_ = l_Task_mapList(v_00_u03b1_94_, v_00_u03b2_95_, v_f_96_, v_tasks_97_, v_prio_98_, v_sync_boxed_100_);
return v_res_101_;
}
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Task(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Task(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Core(uint8_t builtin);
lean_object* initialize_Init_Data_List_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Task(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Task(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Task(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Task(builtin);
}
#ifdef __cplusplus
}
#endif
