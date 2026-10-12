// Lean compiler output
// Module: Lean.Server.AsyncList
// Imports: public import Lean.Server.ServerTask
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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_IO_sleep(uint32_t);
lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___redArg(lean_object*);
uint8_t l_Lean_Server_ServerTask_hasFinished___redArg(lean_object*);
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_waitAny___redArg(lean_object*);
lean_object* lean_io_wait(lean_object*);
lean_object* lean_task_pure(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_IO_sleep___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_bindCheap___redArg(lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorIdx___impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_cons_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_cons_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_delayed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_delayed_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_nil_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_nil_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Lean_AsyncList_instInhabited___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_ofList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_ofList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_AsyncList_instCoeList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_AsyncList_ofList, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_AsyncList_instCoeList___redArg___closed__0 = (const lean_object*)&l_Lean_AsyncList_instCoeList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_AsyncList_instCoeList___redArg();
LEAN_EXPORT lean_object* l_Lean_AsyncList_instCoeList___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_instCoeList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil___redArg___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_AsyncList_waitUntil___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_AsyncList_waitUntil___redArg___closed__0 = (const lean_object*)&l_Lean_AsyncList_waitUntil___redArg___closed__0_value;
static lean_once_cell_t l_Lean_AsyncList_waitUntil___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AsyncList_waitUntil___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AsyncList_waitAll___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitAll___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_AsyncList_waitAll___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_AsyncList_waitAll___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_AsyncList_waitAll___redArg___closed__0 = (const lean_object*)&l_Lean_AsyncList_waitAll___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitAll___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitAll(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_AsyncList_waitFind_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_AsyncList_waitFind_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_AsyncList_waitFind_x3f___redArg___closed__0_value;
static lean_once_cell_t l_Lean_AsyncList_waitFind_x3f___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AsyncList_waitFind_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitFind_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitFind_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitFind_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_AsyncList_getFinishedPrefix___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_AsyncList_getFinishedPrefix___redArg___closed__0 = (const lean_object*)&l_Lean_AsyncList_getFinishedPrefix___redArg___closed__0_value;
static const lean_ctor_object l_Lean_AsyncList_getFinishedPrefix___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AsyncList_getFinishedPrefix___redArg___closed__0_value)}};
static const lean_object* l_Lean_AsyncList_getFinishedPrefix___redArg___closed__1 = (const lean_object*)&l_Lean_AsyncList_getFinishedPrefix___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___lam__0(lean_object*);
static const lean_closure_object l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_AsyncList_ctorIdx___impl___redArg(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorIdx___impl(lean_object* v_00_u03b5_5_, lean_object* v_00_u03b1_6_, lean_object* v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_obj_tag_nat(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorIdx___impl___boxed(lean_object* v_00_u03b5_9_, lean_object* v_00_u03b1_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_AsyncList_ctorIdx___impl(v_00_u03b5_9_, v_00_u03b1_10_, v_x_11_);
lean_dec(v_x_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorElim___redArg(lean_object* v_t_13_, lean_object* v_k_14_){
_start:
{
switch(lean_obj_tag(v_t_13_))
{
case 0:
{
lean_object* v_hd_15_; lean_object* v_tl_16_; lean_object* v___x_17_; 
v_hd_15_ = lean_ctor_get(v_t_13_, 0);
lean_inc(v_hd_15_);
v_tl_16_ = lean_ctor_get(v_t_13_, 1);
lean_inc(v_tl_16_);
lean_dec_ref_known(v_t_13_, 2);
v___x_17_ = lean_apply_2(v_k_14_, v_hd_15_, v_tl_16_);
return v___x_17_;
}
case 1:
{
lean_object* v_tl_18_; lean_object* v___x_19_; 
v_tl_18_ = lean_ctor_get(v_t_13_, 0);
lean_inc_ref(v_tl_18_);
lean_dec_ref_known(v_t_13_, 1);
v___x_19_ = lean_apply_1(v_k_14_, v_tl_18_);
return v___x_19_;
}
default: 
{
return v_k_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorElim(lean_object* v_00_u03b5_20_, lean_object* v_00_u03b1_21_, lean_object* v_motive__1_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_AsyncList_ctorElim___redArg(v_t_24_, v_k_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorElim___boxed(lean_object* v_00_u03b5_28_, lean_object* v_00_u03b1_29_, lean_object* v_motive__1_30_, lean_object* v_ctorIdx_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_k_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_AsyncList_ctorElim(v_00_u03b5_28_, v_00_u03b1_29_, v_motive__1_30_, v_ctorIdx_31_, v_t_32_, v_h_33_, v_k_34_);
lean_dec(v_ctorIdx_31_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_cons_elim___redArg(lean_object* v_t_36_, lean_object* v_cons_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_AsyncList_ctorElim___redArg(v_t_36_, v_cons_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_cons_elim(lean_object* v_00_u03b5_39_, lean_object* v_00_u03b1_40_, lean_object* v_motive__1_41_, lean_object* v_t_42_, lean_object* v_h_43_, lean_object* v_cons_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_AsyncList_ctorElim___redArg(v_t_42_, v_cons_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_delayed_elim___redArg(lean_object* v_t_46_, lean_object* v_delayed_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_AsyncList_ctorElim___redArg(v_t_46_, v_delayed_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_delayed_elim(lean_object* v_00_u03b5_49_, lean_object* v_00_u03b1_50_, lean_object* v_motive__1_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_delayed_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_AsyncList_ctorElim___redArg(v_t_52_, v_delayed_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_nil_elim___redArg(lean_object* v_t_56_, lean_object* v_nil_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_AsyncList_ctorElim___redArg(v_t_56_, v_nil_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_nil_elim(lean_object* v_00_u03b5_59_, lean_object* v_00_u03b1_60_, lean_object* v_motive__1_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_nil_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_AsyncList_ctorElim___redArg(v_t_62_, v_nil_64_);
return v___x_65_;
}
}
lean_object* l_Lean_AsyncList_instInhabited___redArg(){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_box(2);
return v___x_67_;
}
}
LEAN_EXPORT void l_Lean_AsyncList_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_68_;
v_res_68_ = l_Lean_AsyncList_instInhabited___redArg();
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_instInhabited___redArg___boxed(lean_object* v___dummy_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_AsyncList_instInhabited___redArg();
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_instInhabited(lean_object* v_00_u03b5_71_, lean_object* v_00_u03b1_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_box(2);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(lean_object* v_init_74_, lean_object* v_x_75_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
lean_inc(v_init_74_);
return v_init_74_;
}
else
{
lean_object* v_head_76_; lean_object* v_tail_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_85_; 
v_head_76_ = lean_ctor_get(v_x_75_, 0);
v_tail_77_ = lean_ctor_get(v_x_75_, 1);
v_isSharedCheck_85_ = !lean_is_exclusive(v_x_75_);
if (v_isSharedCheck_85_ == 0)
{
v___x_79_ = v_x_75_;
v_isShared_80_ = v_isSharedCheck_85_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_tail_77_);
lean_inc(v_head_76_);
lean_dec(v_x_75_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_85_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_81_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(v_init_74_, v_tail_77_);
if (v_isShared_80_ == 0)
{
lean_ctor_set_tag(v___x_79_, 0);
lean_ctor_set(v___x_79_, 1, v___x_81_);
v___x_83_ = v___x_79_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_head_76_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v___x_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg___boxed(lean_object* v_init_86_, lean_object* v_x_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(v_init_86_, v_x_87_);
lean_dec(v_init_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ofList___redArg(lean_object* v_l_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_box(2);
v___x_91_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(v___x_90_, v_l_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ofList(lean_object* v_00_u03b1_92_, lean_object* v_00_u03b5_93_, lean_object* v_l_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_AsyncList_ofList___redArg(v_l_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0(lean_object* v_00_u03b1_96_, lean_object* v_00_u03b5_97_, lean_object* v_init_98_, lean_object* v_x_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(v_init_98_, v_x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___boxed(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b5_102_, lean_object* v_init_103_, lean_object* v_x_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0(v_00_u03b1_101_, v_00_u03b5_102_, v_init_103_, v_x_104_);
lean_dec(v_init_103_);
return v_res_105_;
}
}
lean_object* l_Lean_AsyncList_instCoeList___redArg(){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = ((lean_object*)(l_Lean_AsyncList_instCoeList___redArg___closed__0));
return v___x_108_;
}
}
LEAN_EXPORT void l_Lean_AsyncList_instCoeList___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_109_;
v_res_109_ = l_Lean_AsyncList_instCoeList___redArg();
stack->m_obj
 = v_res_109_;
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_instCoeList___redArg___boxed(lean_object* v___dummy_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_AsyncList_instCoeList___redArg();
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_instCoeList(lean_object* v_00_u03b1_112_, lean_object* v_00_u03b5_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = ((lean_object*)(l_Lean_AsyncList_instCoeList___redArg___closed__0));
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil___redArg___lam__0(lean_object* v_hd_115_, lean_object* v_x_116_){
_start:
{
lean_object* v_fst_117_; lean_object* v_snd_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_126_; 
v_fst_117_ = lean_ctor_get(v_x_116_, 0);
v_snd_118_ = lean_ctor_get(v_x_116_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v_x_116_);
if (v_isSharedCheck_126_ == 0)
{
v___x_120_ = v_x_116_;
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_snd_118_);
lean_inc(v_fst_117_);
lean_dec(v_x_116_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_122_, 0, v_hd_115_);
lean_ctor_set(v___x_122_, 1, v_fst_117_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_122_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_snd_118_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
static lean_object* _init_l_Lean_AsyncList_waitUntil___redArg___closed__1(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(l_Lean_AsyncList_waitUntil___redArg___closed__0));
v___x_131_ = lean_task_pure(v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil___redArg(lean_object* v_p_132_, lean_object* v_x_133_){
_start:
{
switch(lean_obj_tag(v_x_133_))
{
case 0:
{
lean_object* v_hd_134_; lean_object* v_tl_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_151_; 
v_hd_134_ = lean_ctor_get(v_x_133_, 0);
v_tl_135_ = lean_ctor_get(v_x_133_, 1);
v_isSharedCheck_151_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_151_ == 0)
{
v___x_137_ = v_x_133_;
v_isShared_138_ = v_isSharedCheck_151_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_tl_135_);
lean_inc(v_hd_134_);
lean_dec(v_x_133_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_151_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; uint8_t v___x_140_; 
lean_inc_ref(v_p_132_);
lean_inc(v_hd_134_);
v___x_139_ = lean_apply_1(v_p_132_, v_hd_134_);
v___x_140_ = lean_unbox(v___x_139_);
if (v___x_140_ == 0)
{
lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
lean_del_object(v___x_137_);
v___f_141_ = lean_alloc_closure((void*)(l_Lean_AsyncList_waitUntil___redArg___lam__0), 2, 1);
lean_closure_set(v___f_141_, 0, v_hd_134_);
v___x_142_ = l_Lean_AsyncList_waitUntil___redArg(v_p_132_, v_tl_135_);
v___x_143_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_141_, v___x_142_);
return v___x_143_;
}
else
{
lean_object* v___x_144_; lean_object* v___x_146_; 
lean_dec(v_tl_135_);
lean_dec_ref(v_p_132_);
v___x_144_ = lean_box(0);
if (v_isShared_138_ == 0)
{
lean_ctor_set_tag(v___x_137_, 1);
lean_ctor_set(v___x_137_, 1, v___x_144_);
v___x_146_ = v___x_137_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_hd_134_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v___x_144_);
v___x_146_ = v_reuseFailAlloc_150_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_box(0);
v___x_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_146_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = lean_task_pure(v___x_148_);
return v___x_149_;
}
}
}
}
case 1:
{
lean_object* v_tl_152_; lean_object* v___f_153_; lean_object* v___x_154_; 
v_tl_152_ = lean_ctor_get(v_x_133_, 0);
lean_inc_ref(v_tl_152_);
lean_dec_ref_known(v_x_133_, 1);
v___f_153_ = lean_alloc_closure((void*)(l_Lean_AsyncList_waitUntil___redArg___lam__1), 2, 1);
lean_closure_set(v___f_153_, 0, v_p_132_);
v___x_154_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_tl_152_, v___f_153_);
return v___x_154_;
}
default: 
{
lean_object* v___x_155_; 
lean_dec_ref(v_p_132_);
v___x_155_ = lean_obj_once(&l_Lean_AsyncList_waitUntil___redArg___closed__1, &l_Lean_AsyncList_waitUntil___redArg___closed__1_once, _init_l_Lean_AsyncList_waitUntil___redArg___closed__1);
return v___x_155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil___redArg___lam__1(lean_object* v_p_156_, lean_object* v_x_157_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_168_; 
lean_dec_ref(v_p_156_);
v_a_158_ = lean_ctor_get(v_x_157_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v_x_157_);
if (v_isSharedCheck_168_ == 0)
{
v___x_160_ = v_x_157_;
v_isShared_161_ = v_isSharedCheck_168_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v_x_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_168_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_box(0);
if (v_isShared_161_ == 0)
{
lean_ctor_set_tag(v___x_160_, 1);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_158_);
v___x_164_ = v_reuseFailAlloc_167_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_162_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = lean_task_pure(v___x_165_);
return v___x_166_;
}
}
}
else
{
lean_object* v_a_169_; lean_object* v___x_170_; 
v_a_169_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_a_169_);
lean_dec_ref_known(v_x_157_, 1);
v___x_170_ = l_Lean_AsyncList_waitUntil___redArg(v_p_156_, v_a_169_);
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil(lean_object* v_00_u03b1_171_, lean_object* v_00_u03b5_172_, lean_object* v_p_173_, lean_object* v_x_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_AsyncList_waitUntil___redArg(v_p_173_, v_x_174_);
return v___x_175_;
}
}
uint8_t l_Lean_AsyncList_waitAll___redArg___lam__0(lean_object* v_x_176_){
_start:
{
uint8_t v___x_177_; 
v___x_177_ = 0;
return v___x_177_;
}
}
LEAN_EXPORT void l_Lean_AsyncList_waitAll___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_176_ = stack[0].m_obj;
uint8_t v_res_178_;
v_res_178_ = l_Lean_AsyncList_waitAll___redArg___lam__0(v_x_176_);
stack->m_num = v_res_178_;
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitAll___redArg___lam__0___boxed(lean_object* v_x_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Lean_AsyncList_waitAll___redArg___lam__0(v_x_179_);
lean_dec(v_x_179_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitAll___redArg(lean_object* v_a_183_){
_start:
{
lean_object* v___f_184_; lean_object* v___x_185_; 
v___f_184_ = ((lean_object*)(l_Lean_AsyncList_waitAll___redArg___closed__0));
v___x_185_ = l_Lean_AsyncList_waitUntil___redArg(v___f_184_, v_a_183_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitAll(lean_object* v_00_u03b5_186_, lean_object* v_00_u03b1_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_AsyncList_waitAll___redArg(v_a_188_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_AsyncList_waitFind_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l_Lean_AsyncList_waitFind_x3f___redArg___closed__0));
v___x_193_ = lean_task_pure(v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitFind_x3f___redArg(lean_object* v_p_194_, lean_object* v_x_195_){
_start:
{
switch(lean_obj_tag(v_x_195_))
{
case 0:
{
lean_object* v_hd_196_; lean_object* v_tl_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_hd_196_ = lean_ctor_get(v_x_195_, 0);
lean_inc_n(v_hd_196_, 2);
v_tl_197_ = lean_ctor_get(v_x_195_, 1);
lean_inc(v_tl_197_);
lean_dec_ref_known(v_x_195_, 2);
lean_inc_ref(v_p_194_);
v___x_198_ = lean_apply_1(v_p_194_, v_hd_196_);
v___x_199_ = lean_unbox(v___x_198_);
if (v___x_199_ == 0)
{
lean_dec(v_hd_196_);
v_x_195_ = v_tl_197_;
goto _start;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec(v_tl_197_);
lean_dec_ref(v_p_194_);
v___x_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_201_, 0, v_hd_196_);
v___x_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
v___x_203_ = lean_task_pure(v___x_202_);
return v___x_203_;
}
}
case 1:
{
lean_object* v_tl_204_; lean_object* v___f_205_; lean_object* v___x_206_; 
v_tl_204_ = lean_ctor_get(v_x_195_, 0);
lean_inc_ref(v_tl_204_);
lean_dec_ref_known(v_x_195_, 1);
v___f_205_ = lean_alloc_closure((void*)(l_Lean_AsyncList_waitFind_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_205_, 0, v_p_194_);
v___x_206_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_tl_204_, v___f_205_);
return v___x_206_;
}
default: 
{
lean_object* v___x_207_; 
lean_dec_ref(v_p_194_);
v___x_207_ = lean_obj_once(&l_Lean_AsyncList_waitFind_x3f___redArg___closed__1, &l_Lean_AsyncList_waitFind_x3f___redArg___closed__1_once, _init_l_Lean_AsyncList_waitFind_x3f___redArg___closed__1);
return v___x_207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitFind_x3f___redArg___lam__0(lean_object* v_p_208_, lean_object* v_x_209_){
_start:
{
if (lean_obj_tag(v_x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_218_; 
lean_dec_ref(v_p_208_);
v_a_210_ = lean_ctor_get(v_x_209_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v_x_209_);
if (v_isSharedCheck_218_ == 0)
{
v___x_212_ = v_x_209_;
v_isShared_213_ = v_isSharedCheck_218_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v_x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_218_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_217_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_216_; 
v___x_216_ = lean_task_pure(v___x_215_);
return v___x_216_;
}
}
}
else
{
lean_object* v_a_219_; lean_object* v___x_220_; 
v_a_219_ = lean_ctor_get(v_x_209_, 0);
lean_inc(v_a_219_);
lean_dec_ref_known(v_x_209_, 1);
v___x_220_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_208_, v_a_219_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitFind_x3f(lean_object* v_00_u03b1_221_, lean_object* v_00_u03b5_222_, lean_object* v_p_223_, lean_object* v_x_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_223_, v_x_224_);
return v___x_225_;
}
}
lean_object* l_Lean_AsyncList_getFinishedPrefix___redArg(lean_object* v_x_233_){
_start:
{
switch(lean_obj_tag(v_x_233_))
{
case 0:
{
lean_object* v_hd_235_; lean_object* v_tl_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_253_; 
v_hd_235_ = lean_ctor_get(v_x_233_, 0);
v_tl_236_ = lean_ctor_get(v_x_233_, 1);
v_isSharedCheck_253_ = !lean_is_exclusive(v_x_233_);
if (v_isSharedCheck_253_ == 0)
{
v___x_238_ = v_x_233_;
v_isShared_239_ = v_isSharedCheck_253_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_tl_236_);
lean_inc(v_hd_235_);
lean_dec(v_x_233_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_253_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v_fst_241_; lean_object* v_snd_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_252_; 
v___x_240_ = l_Lean_AsyncList_getFinishedPrefix___redArg(v_tl_236_);
v_fst_241_ = lean_ctor_get(v___x_240_, 0);
v_snd_242_ = lean_ctor_get(v___x_240_, 1);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_252_ == 0)
{
v___x_244_ = v___x_240_;
v_isShared_245_ = v_isSharedCheck_252_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_snd_242_);
lean_inc(v_fst_241_);
lean_dec(v___x_240_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_252_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set_tag(v___x_238_, 1);
lean_ctor_set(v___x_238_, 1, v_fst_241_);
v___x_247_ = v___x_238_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_hd_235_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_fst_241_);
v___x_247_ = v_reuseFailAlloc_251_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_249_; 
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_247_);
v___x_249_ = v___x_244_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_snd_242_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
case 1:
{
lean_object* v_tl_254_; uint8_t v___x_255_; 
v_tl_254_ = lean_ctor_get(v_x_233_, 0);
lean_inc_ref(v_tl_254_);
lean_dec_ref_known(v_x_233_, 1);
v___x_255_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_tl_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec_ref(v_tl_254_);
v___x_256_ = lean_box(0);
v___x_257_ = lean_box(0);
v___x_258_ = lean_box(v___x_255_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_257_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_256_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
return v___x_260_;
}
else
{
lean_object* v___x_261_; 
v___x_261_ = lean_io_wait(v_tl_254_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_273_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_273_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_273_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_273_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_266_ = lean_box(0);
if (v_isShared_265_ == 0)
{
lean_ctor_set_tag(v___x_264_, 1);
v___x_268_ = v___x_264_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_262_);
v___x_268_ = v_reuseFailAlloc_272_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = lean_box(v___x_255_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_266_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
return v___x_271_;
}
}
}
else
{
lean_object* v_a_274_; 
v_a_274_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_274_);
lean_dec_ref_known(v___x_261_, 1);
v_x_233_ = v_a_274_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_276_; 
v___x_276_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefix___redArg___closed__1));
return v___x_276_;
}
}
}
}
LEAN_EXPORT void l_Lean_AsyncList_getFinishedPrefix___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_233_ = stack[0].m_obj;
lean_object* v_res_277_;
v_res_277_ = l_Lean_AsyncList_getFinishedPrefix___redArg(v_x_233_);
stack->m_obj
 = v_res_277_;
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix___redArg___boxed(lean_object* v_x_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_AsyncList_getFinishedPrefix___redArg(v_x_278_);
return v_res_280_;
}
}
lean_object* l_Lean_AsyncList_getFinishedPrefix(lean_object* v_00_u03b5_281_, lean_object* v_00_u03b1_282_, lean_object* v_x_283_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_AsyncList_getFinishedPrefix___redArg(v_x_283_);
return v___x_285_;
}
}
LEAN_EXPORT void l_Lean_AsyncList_getFinishedPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_283_ = stack[2].m_obj;
lean_object* v_res_286_;
v_res_286_ = l_Lean_AsyncList_getFinishedPrefix(lean_box(0), lean_box(0), v_x_283_);
stack->m_obj
 = v_res_286_;
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix___boxed(lean_object* v_00_u03b5_287_, lean_object* v_00_u03b1_288_, lean_object* v_x_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_AsyncList_getFinishedPrefix(v_00_u03b5_287_, v_00_u03b1_288_, v_x_289_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___lam__0(lean_object* v_val_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_293_, 0, v_val_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___lam__0(lean_object* v_val_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v_val_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
if (lean_obj_tag(v_a_297_) == 0)
{
lean_object* v___x_299_; 
v___x_299_ = l_List_reverse___redArg(v_a_298_);
return v___x_299_;
}
else
{
lean_object* v_head_300_; lean_object* v_tail_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_311_; 
v_head_300_ = lean_ctor_get(v_a_297_, 0);
v_tail_301_ = lean_ctor_get(v_a_297_, 1);
v_isSharedCheck_311_ = !lean_is_exclusive(v_a_297_);
if (v_isSharedCheck_311_ == 0)
{
v___x_303_ = v_a_297_;
v_isShared_304_ = v_isSharedCheck_311_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_tail_301_);
lean_inc(v_head_300_);
lean_dec(v_a_297_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_311_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___f_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
v___f_305_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0));
v___x_306_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_305_, v_head_300_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v_a_298_);
lean_ctor_set(v___x_303_, 0, v___x_306_);
v___x_308_ = v___x_303_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_a_298_);
v___x_308_ = v_reuseFailAlloc_310_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
v_a_297_ = v_tail_301_;
v_a_298_ = v___x_308_;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(lean_object* v_cancelTks_313_, lean_object* v_timeoutTask_314_, lean_object* v_xs_315_){
_start:
{
switch(lean_obj_tag(v_xs_315_))
{
case 0:
{
lean_object* v_hd_317_; lean_object* v_tl_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_335_; 
v_hd_317_ = lean_ctor_get(v_xs_315_, 0);
v_tl_318_ = lean_ctor_get(v_xs_315_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v_xs_315_);
if (v_isSharedCheck_335_ == 0)
{
v___x_320_ = v_xs_315_;
v_isShared_321_ = v_isSharedCheck_335_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_tl_318_);
lean_inc(v_hd_317_);
lean_dec(v_xs_315_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_335_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v_fst_323_; lean_object* v_snd_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_334_; 
v___x_322_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_313_, v_timeoutTask_314_, v_tl_318_);
v_fst_323_ = lean_ctor_get(v___x_322_, 0);
v_snd_324_ = lean_ctor_get(v___x_322_, 1);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_334_ == 0)
{
v___x_326_ = v___x_322_;
v_isShared_327_ = v_isSharedCheck_334_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_snd_324_);
lean_inc(v_fst_323_);
lean_dec(v___x_322_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_334_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set_tag(v___x_320_, 1);
lean_ctor_set(v___x_320_, 1, v_fst_323_);
v___x_329_ = v___x_320_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_hd_317_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_fst_323_);
v___x_329_ = v_reuseFailAlloc_333_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_331_; 
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_329_);
v___x_331_ = v___x_326_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_snd_324_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
case 1:
{
lean_object* v_tl_336_; lean_object* v___f_337_; uint8_t v___x_338_; uint8_t v___x_339_; 
v_tl_336_ = lean_ctor_get(v_xs_315_, 0);
lean_inc_ref(v_tl_336_);
lean_dec_ref_known(v_xs_315_, 1);
v___f_337_ = ((lean_object*)(l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0));
v___x_338_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_tl_336_);
v___x_339_ = 1;
if (v___x_338_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_340_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_337_, v_tl_336_);
v___x_341_ = lean_box(0);
lean_inc(v_cancelTks_313_);
v___x_342_ = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(v_cancelTks_313_, v___x_341_);
v___x_343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_340_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
lean_inc_ref(v_timeoutTask_314_);
v___x_344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_344_, 0, v_timeoutTask_314_);
lean_ctor_set(v___x_344_, 1, v___x_341_);
v___x_345_ = l_List_appendTR___redArg(v___x_343_, v___x_344_);
v___x_346_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_345_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec_ref_known(v___x_346_, 1);
lean_dec_ref(v_timeoutTask_314_);
lean_dec(v_cancelTks_313_);
v___x_347_ = lean_box(0);
v___x_348_ = lean_box(v___x_338_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_347_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_341_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
return v___x_350_;
}
else
{
lean_object* v_val_351_; 
v_val_351_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_val_351_);
lean_dec_ref_known(v___x_346_, 1);
if (lean_obj_tag(v_val_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_362_; 
lean_dec_ref(v_timeoutTask_314_);
lean_dec(v_cancelTks_313_);
v_a_352_ = lean_ctor_get(v_val_351_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v_val_351_);
if (v_isSharedCheck_362_ == 0)
{
v___x_354_ = v_val_351_;
v_isShared_355_ = v_isSharedCheck_362_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v_val_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_362_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
lean_ctor_set_tag(v___x_354_, 1);
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_361_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = lean_box(v___x_339_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_341_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
return v___x_360_;
}
}
}
else
{
lean_object* v_a_363_; 
v_a_363_ = lean_ctor_get(v_val_351_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v_val_351_, 1);
v_xs_315_ = v_a_363_;
goto _start;
}
}
}
else
{
lean_object* v___x_365_; 
v___x_365_ = lean_io_wait(v_tl_336_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_377_; 
lean_dec_ref(v_timeoutTask_314_);
lean_dec(v_cancelTks_313_);
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_377_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_377_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_377_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_370_ = lean_box(0);
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 1);
v___x_372_ = v___x_368_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_366_);
v___x_372_ = v_reuseFailAlloc_376_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = lean_box(v___x_339_);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_370_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
return v___x_375_;
}
}
}
else
{
lean_object* v_a_378_; 
v_a_378_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_a_378_);
lean_dec_ref_known(v___x_365_, 1);
v_xs_315_ = v_a_378_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_380_; 
lean_dec_ref(v_timeoutTask_314_);
lean_dec(v_cancelTks_313_);
v___x_380_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefix___redArg___closed__1));
return v___x_380_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cancelTks_313_ = stack[0].m_obj;
lean_object* v_timeoutTask_314_ = stack[1].m_obj;
lean_object* v_xs_315_ = stack[2].m_obj;
lean_object* v_res_381_;
v_res_381_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_313_, v_timeoutTask_314_, v_xs_315_);
stack->m_obj
 = v_res_381_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___boxed(lean_object* v_cancelTks_382_, lean_object* v_timeoutTask_383_, lean_object* v_xs_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_382_, v_timeoutTask_383_, v_xs_384_);
return v_res_386_;
}
}
lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go(lean_object* v_00_u03b5_387_, lean_object* v_00_u03b1_388_, lean_object* v_cancelTks_389_, lean_object* v_timeoutTask_390_, lean_object* v_xs_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_389_, v_timeoutTask_390_, v_xs_391_);
return v___x_393_;
}
}
LEAN_EXPORT void l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_cancelTks_389_ = stack[2].m_obj;
lean_object* v_timeoutTask_390_ = stack[3].m_obj;
lean_object* v_xs_391_ = stack[4].m_obj;
lean_object* v_res_394_;
v_res_394_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go(lean_box(0), lean_box(0), v_cancelTks_389_, v_timeoutTask_390_, v_xs_391_);
stack->m_obj
 = v_res_394_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___boxed(lean_object* v_00_u03b5_395_, lean_object* v_00_u03b1_396_, lean_object* v_cancelTks_397_, lean_object* v_timeoutTask_398_, lean_object* v_xs_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go(v_00_u03b5_395_, v_00_u03b1_396_, v_cancelTks_397_, v_timeoutTask_398_, v_xs_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0(lean_object* v_00_u03b5_402_, lean_object* v_00_u03b1_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(v_a_404_, v_a_405_);
return v___x_406_;
}
}
lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(uint32_t v_timeoutMs_409_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = l_IO_sleep(v_timeoutMs_409_);
v___x_412_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0));
return v___x_412_;
}
}
LEAN_EXPORT void l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_timeoutMs_409_ = stack[0].m_num;
lean_object* v_res_413_;
v_res_413_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(v_timeoutMs_409_);
stack->m_obj
 = v_res_413_;
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed(lean_object* v_timeoutMs_414_, lean_object* v___y_415_){
_start:
{
uint32_t v_timeoutMs_boxed_416_; lean_object* v_res_417_; 
v_timeoutMs_boxed_416_ = lean_unbox_uint32(v_timeoutMs_414_);
lean_dec(v_timeoutMs_414_);
v_res_417_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(v_timeoutMs_boxed_416_);
return v_res_417_;
}
}
static lean_object* _init_l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0));
v___x_419_ = lean_task_pure(v___x_418_);
return v___x_419_;
}
}
lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(lean_object* v_xs_420_, uint32_t v_timeoutMs_421_, lean_object* v_cancelTks_422_){
_start:
{
uint32_t v___x_424_; uint8_t v___x_425_; 
v___x_424_ = 0;
v___x_425_ = lean_uint32_dec_eq(v_timeoutMs_421_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___f_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_426_ = lean_box_uint32(v_timeoutMs_421_);
v___f_427_ = lean_alloc_closure((void*)(l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_427_, 0, v___x_426_);
v___x_428_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v___f_427_);
v___x_429_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_422_, v___x_428_, v_xs_420_);
return v___x_429_;
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_obj_once(&l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0, &l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0_once, _init_l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0);
v___x_431_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_422_, v___x_430_, v_xs_420_);
return v___x_431_;
}
}
}
LEAN_EXPORT void l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_420_ = stack[0].m_obj;
uint32_t v_timeoutMs_421_ = stack[1].m_num;
lean_object* v_cancelTks_422_ = stack[2].m_obj;
lean_object* v_res_432_;
v_res_432_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_420_, v_timeoutMs_421_, v_cancelTks_422_);
stack->m_obj
 = v_res_432_;
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___boxed(lean_object* v_xs_433_, lean_object* v_timeoutMs_434_, lean_object* v_cancelTks_435_, lean_object* v_a_436_){
_start:
{
uint32_t v_timeoutMs_boxed_437_; lean_object* v_res_438_; 
v_timeoutMs_boxed_437_ = lean_unbox_uint32(v_timeoutMs_434_);
lean_dec(v_timeoutMs_434_);
v_res_438_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_433_, v_timeoutMs_boxed_437_, v_cancelTks_435_);
return v_res_438_;
}
}
lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout(lean_object* v_00_u03b5_439_, lean_object* v_00_u03b1_440_, lean_object* v_xs_441_, uint32_t v_timeoutMs_442_, lean_object* v_cancelTks_443_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_441_, v_timeoutMs_442_, v_cancelTks_443_);
return v___x_445_;
}
}
LEAN_EXPORT void l_Lean_AsyncList_getFinishedPrefixWithTimeout_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_441_ = stack[2].m_obj;
uint32_t v_timeoutMs_442_ = stack[3].m_num;
lean_object* v_cancelTks_443_ = stack[4].m_obj;
lean_object* v_res_446_;
v_res_446_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout(lean_box(0), lean_box(0), v_xs_441_, v_timeoutMs_442_, v_cancelTks_443_);
stack->m_obj
 = v_res_446_;
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___boxed(lean_object* v_00_u03b5_447_, lean_object* v_00_u03b1_448_, lean_object* v_xs_449_, lean_object* v_timeoutMs_450_, lean_object* v_cancelTks_451_, lean_object* v_a_452_){
_start:
{
uint32_t v_timeoutMs_boxed_453_; lean_object* v_res_454_; 
v_timeoutMs_boxed_453_ = lean_unbox_uint32(v_timeoutMs_450_);
lean_dec(v_timeoutMs_450_);
v_res_454_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout(v_00_u03b5_447_, v_00_u03b1_448_, v_xs_449_, v_timeoutMs_boxed_453_, v_cancelTks_451_);
return v_res_454_;
}
}
uint8_t l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(lean_object* v_x_455_){
_start:
{
if (lean_obj_tag(v_x_455_) == 0)
{
uint8_t v___x_457_; 
v___x_457_ = 0;
return v___x_457_;
}
else
{
lean_object* v_head_458_; lean_object* v_tail_459_; uint8_t v___x_460_; 
v_head_458_ = lean_ctor_get(v_x_455_, 0);
v_tail_459_ = lean_ctor_get(v_x_455_, 1);
v___x_460_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_head_458_);
if (v___x_460_ == 0)
{
v_x_455_ = v_tail_459_;
goto _start;
}
else
{
return v___x_460_;
}
}
}
}
LEAN_EXPORT void l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_455_ = stack[0].m_obj;
uint8_t v_res_462_;
v_res_462_ = l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(v_x_455_);
stack->m_num = v_res_462_;
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0___boxed(lean_object* v_x_463_, lean_object* v___y_464_){
_start:
{
uint8_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(v_x_463_);
lean_dec(v_x_463_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(lean_object* v_cancelTks_467_, uint32_t v_sleepDurationMs_468_){
_start:
{
uint32_t v___x_470_; uint8_t v___x_471_; 
v___x_470_ = 0;
v___x_471_ = lean_uint32_dec_eq(v_sleepDurationMs_468_, v___x_470_);
if (v___x_471_ == 0)
{
uint8_t v___x_472_; 
v___x_472_ = l_List_isEmpty___redArg(v_cancelTks_467_);
if (v___x_472_ == 0)
{
uint8_t v___x_473_; 
v___x_473_ = l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(v_cancelTks_467_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_474_ = lean_box_uint32(v_sleepDurationMs_468_);
v___x_475_ = lean_alloc_closure((void*)(l_IO_sleep___boxed), 2, 1);
lean_closure_set(v___x_475_, 0, v___x_474_);
v___x_476_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v___x_475_);
v___x_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v_cancelTks_467_);
v___x_478_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_477_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; 
lean_dec(v_cancelTks_467_);
v___x_479_ = lean_box(0);
return v___x_479_;
}
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v_cancelTks_467_);
v___x_480_ = l_IO_sleep(v_sleepDurationMs_468_);
v___x_481_ = lean_box(0);
return v___x_481_;
}
}
else
{
lean_object* v___x_482_; 
lean_dec(v_cancelTks_467_);
v___x_482_ = lean_box(0);
return v___x_482_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_0interp(lean_interpreter_value* stack)
{
lean_object* v_cancelTks_467_ = stack[0].m_obj;
uint32_t v_sleepDurationMs_468_ = stack[1].m_num;
lean_object* v_res_483_;
v_res_483_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(v_cancelTks_467_, v_sleepDurationMs_468_);
stack->m_obj
 = v_res_483_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___boxed(lean_object* v_cancelTks_484_, lean_object* v_sleepDurationMs_485_, lean_object* v_a_486_){
_start:
{
uint32_t v_sleepDurationMs_boxed_487_; lean_object* v_res_488_; 
v_sleepDurationMs_boxed_487_ = lean_unbox_uint32(v_sleepDurationMs_485_);
lean_dec(v_sleepDurationMs_485_);
v_res_488_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(v_cancelTks_484_, v_sleepDurationMs_boxed_487_);
return v_res_488_;
}
}
lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(lean_object* v_xs_489_, uint32_t v_latencyMs_490_, lean_object* v_cancelTks_491_){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; uint32_t v___x_499_; lean_object* v___x_500_; 
v___x_493_ = lean_io_mono_ms_now();
lean_inc(v_cancelTks_491_);
v___x_494_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_489_, v_latencyMs_490_, v_cancelTks_491_);
v___x_495_ = lean_io_mono_ms_now();
v___x_496_ = lean_nat_sub(v___x_495_, v___x_493_);
lean_dec(v___x_493_);
lean_dec(v___x_495_);
v___x_497_ = lean_uint32_to_nat(v_latencyMs_490_);
v___x_498_ = lean_nat_sub(v___x_497_, v___x_496_);
lean_dec(v___x_496_);
lean_dec(v___x_497_);
v___x_499_ = lean_uint32_of_nat(v___x_498_);
lean_dec(v___x_498_);
v___x_500_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(v_cancelTks_491_, v___x_499_);
return v___x_494_;
}
}
LEAN_EXPORT void l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_489_ = stack[0].m_obj;
uint32_t v_latencyMs_490_ = stack[1].m_num;
lean_object* v_cancelTks_491_ = stack[2].m_obj;
lean_object* v_res_501_;
v_res_501_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(v_xs_489_, v_latencyMs_490_, v_cancelTks_491_);
stack->m_obj
 = v_res_501_;
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg___boxed(lean_object* v_xs_502_, lean_object* v_latencyMs_503_, lean_object* v_cancelTks_504_, lean_object* v_a_505_){
_start:
{
uint32_t v_latencyMs_boxed_506_; lean_object* v_res_507_; 
v_latencyMs_boxed_506_ = lean_unbox_uint32(v_latencyMs_503_);
lean_dec(v_latencyMs_503_);
v_res_507_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(v_xs_502_, v_latencyMs_boxed_506_, v_cancelTks_504_);
return v_res_507_;
}
}
lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency(lean_object* v_00_u03b5_508_, lean_object* v_00_u03b1_509_, lean_object* v_xs_510_, uint32_t v_latencyMs_511_, lean_object* v_cancelTks_512_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(v_xs_510_, v_latencyMs_511_, v_cancelTks_512_);
return v___x_514_;
}
}
LEAN_EXPORT void l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_510_ = stack[2].m_obj;
uint32_t v_latencyMs_511_ = stack[3].m_num;
lean_object* v_cancelTks_512_ = stack[4].m_obj;
lean_object* v_res_515_;
v_res_515_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency(lean_box(0), lean_box(0), v_xs_510_, v_latencyMs_511_, v_cancelTks_512_);
stack->m_obj
 = v_res_515_;
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___boxed(lean_object* v_00_u03b5_516_, lean_object* v_00_u03b1_517_, lean_object* v_xs_518_, lean_object* v_latencyMs_519_, lean_object* v_cancelTks_520_, lean_object* v_a_521_){
_start:
{
uint32_t v_latencyMs_boxed_522_; lean_object* v_res_523_; 
v_latencyMs_boxed_522_ = lean_unbox_uint32(v_latencyMs_519_);
lean_dec(v_latencyMs_519_);
v_res_523_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency(v_00_u03b5_516_, v_00_u03b1_517_, v_xs_518_, v_latencyMs_boxed_522_, v_cancelTks_520_);
return v_res_523_;
}
}
lean_object* runtime_initialize_Lean_Server_ServerTask(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_AsyncList(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Server_ServerTask(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_AsyncList(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_ServerTask(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_AsyncList(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_ServerTask(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_AsyncList(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_AsyncList(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_AsyncList(builtin);
}
#ifdef __cplusplus
}
#endif
