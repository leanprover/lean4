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
LEAN_EXPORT lean_object* l___private_Init_Task_0__Task_mapList_go___redArg(lean_object* v_f_20_, lean_object* v_prio_21_, uint8_t v_sync_22_, lean_object* v_x_23_, lean_object* v_x_24_){
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
lean_dec_ref(v_x_23_);
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
lean_dec_ref(v_x_23_);
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
LEAN_EXPORT lean_object* l___private_Init_Task_0__Task_mapList_go___redArg___lam__2(lean_object* v_x_38_, lean_object* v_f_39_, lean_object* v_prio_40_, uint8_t v_sync_41_, lean_object* v_tail_42_, lean_object* v_a_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_44_, 0, v_a_43_);
lean_ctor_set(v___x_44_, 1, v_x_38_);
v___x_45_ = l___private_Init_Task_0__Task_mapList_go___redArg(v_f_39_, v_prio_40_, v_sync_41_, v_tail_42_, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Task_0__Task_mapList_go___redArg___boxed(lean_object* v_f_46_, lean_object* v_prio_47_, lean_object* v_sync_48_, lean_object* v_x_49_, lean_object* v_x_50_){
_start:
{
uint8_t v_sync_boxed_51_; lean_object* v_res_52_; 
v_sync_boxed_51_ = lean_unbox(v_sync_48_);
v_res_52_ = l___private_Init_Task_0__Task_mapList_go___redArg(v_f_46_, v_prio_47_, v_sync_boxed_51_, v_x_49_, v_x_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Task_0__Task_mapList_go(lean_object* v_00_u03b1_53_, lean_object* v_00_u03b2_54_, lean_object* v_f_55_, lean_object* v_prio_56_, uint8_t v_sync_57_, lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l___private_Init_Task_0__Task_mapList_go___redArg(v_f_55_, v_prio_56_, v_sync_57_, v_x_58_, v_x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Task_0__Task_mapList_go___boxed(lean_object* v_00_u03b1_61_, lean_object* v_00_u03b2_62_, lean_object* v_f_63_, lean_object* v_prio_64_, lean_object* v_sync_65_, lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
uint8_t v_sync_boxed_68_; lean_object* v_res_69_; 
v_sync_boxed_68_ = lean_unbox(v_sync_65_);
v_res_69_ = l___private_Init_Task_0__Task_mapList_go(v_00_u03b1_61_, v_00_u03b2_62_, v_f_63_, v_prio_64_, v_sync_boxed_68_, v_x_66_, v_x_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Task_mapList___redArg(lean_object* v_f_70_, lean_object* v_tasks_71_, lean_object* v_prio_72_, uint8_t v_sync_73_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_box(0);
v___x_75_ = l___private_Init_Task_0__Task_mapList_go___redArg(v_f_70_, v_prio_72_, v_sync_73_, v_tasks_71_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Task_mapList___redArg___boxed(lean_object* v_f_76_, lean_object* v_tasks_77_, lean_object* v_prio_78_, lean_object* v_sync_79_){
_start:
{
uint8_t v_sync_boxed_80_; lean_object* v_res_81_; 
v_sync_boxed_80_ = lean_unbox(v_sync_79_);
v_res_81_ = l_Task_mapList___redArg(v_f_76_, v_tasks_77_, v_prio_78_, v_sync_boxed_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Task_mapList(lean_object* v_00_u03b1_82_, lean_object* v_00_u03b2_83_, lean_object* v_f_84_, lean_object* v_tasks_85_, lean_object* v_prio_86_, uint8_t v_sync_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Task_mapList___redArg(v_f_84_, v_tasks_85_, v_prio_86_, v_sync_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Task_mapList___boxed(lean_object* v_00_u03b1_89_, lean_object* v_00_u03b2_90_, lean_object* v_f_91_, lean_object* v_tasks_92_, lean_object* v_prio_93_, lean_object* v_sync_94_){
_start:
{
uint8_t v_sync_boxed_95_; lean_object* v_res_96_; 
v_sync_boxed_95_ = lean_unbox(v_sync_94_);
v_res_96_ = l_Task_mapList(v_00_u03b1_89_, v_00_u03b2_90_, v_f_91_, v_tasks_92_, v_prio_93_, v_sync_boxed_95_);
return v_res_96_;
}
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Task(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
