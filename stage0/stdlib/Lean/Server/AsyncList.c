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
LEAN_EXPORT lean_object* l_Lean_AsyncList_instInhabited___redArg(){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_box(2);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_instInhabited___redArg___boxed(lean_object* v___dummy_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_AsyncList_instInhabited___redArg();
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_instInhabited(lean_object* v_00_u03b5_70_, lean_object* v_00_u03b1_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_box(2);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(lean_object* v_init_73_, lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_x_74_) == 0)
{
lean_inc(v_init_73_);
return v_init_73_;
}
else
{
lean_object* v_head_75_; lean_object* v_tail_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_84_; 
v_head_75_ = lean_ctor_get(v_x_74_, 0);
v_tail_76_ = lean_ctor_get(v_x_74_, 1);
v_isSharedCheck_84_ = !lean_is_exclusive(v_x_74_);
if (v_isSharedCheck_84_ == 0)
{
v___x_78_ = v_x_74_;
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_tail_76_);
lean_inc(v_head_75_);
lean_dec(v_x_74_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_80_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(v_init_73_, v_tail_76_);
if (v_isShared_79_ == 0)
{
lean_ctor_set_tag(v___x_78_, 0);
lean_ctor_set(v___x_78_, 1, v___x_80_);
v___x_82_ = v___x_78_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_head_75_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg___boxed(lean_object* v_init_85_, lean_object* v_x_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(v_init_85_, v_x_86_);
lean_dec(v_init_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ofList___redArg(lean_object* v_l_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_box(2);
v___x_90_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(v___x_89_, v_l_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ofList(lean_object* v_00_u03b1_91_, lean_object* v_00_u03b5_92_, lean_object* v_l_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Lean_AsyncList_ofList___redArg(v_l_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0(lean_object* v_00_u03b1_95_, lean_object* v_00_u03b5_96_, lean_object* v_init_97_, lean_object* v_x_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(v_init_97_, v_x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___boxed(lean_object* v_00_u03b1_100_, lean_object* v_00_u03b5_101_, lean_object* v_init_102_, lean_object* v_x_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0(v_00_u03b1_100_, v_00_u03b5_101_, v_init_102_, v_x_103_);
lean_dec(v_init_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_instCoeList___redArg(){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = ((lean_object*)(l_Lean_AsyncList_instCoeList___redArg___closed__0));
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_instCoeList___redArg___boxed(lean_object* v___dummy_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_AsyncList_instCoeList___redArg();
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_instCoeList(lean_object* v_00_u03b1_110_, lean_object* v_00_u03b5_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = ((lean_object*)(l_Lean_AsyncList_instCoeList___redArg___closed__0));
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil___redArg___lam__0(lean_object* v_hd_113_, lean_object* v_x_114_){
_start:
{
lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_124_; 
v_fst_115_ = lean_ctor_get(v_x_114_, 0);
v_snd_116_ = lean_ctor_get(v_x_114_, 1);
v_isSharedCheck_124_ = !lean_is_exclusive(v_x_114_);
if (v_isSharedCheck_124_ == 0)
{
v___x_118_ = v_x_114_;
v_isShared_119_ = v_isSharedCheck_124_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_snd_116_);
lean_inc(v_fst_115_);
lean_dec(v_x_114_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_124_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_120_, 0, v_hd_113_);
lean_ctor_set(v___x_120_, 1, v_fst_115_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_120_);
v___x_122_ = v___x_118_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_snd_116_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
static lean_object* _init_l_Lean_AsyncList_waitUntil___redArg___closed__1(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_Lean_AsyncList_waitUntil___redArg___closed__0));
v___x_129_ = lean_task_pure(v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil___redArg(lean_object* v_p_130_, lean_object* v_x_131_){
_start:
{
switch(lean_obj_tag(v_x_131_))
{
case 0:
{
lean_object* v_hd_132_; lean_object* v_tl_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_149_; 
v_hd_132_ = lean_ctor_get(v_x_131_, 0);
v_tl_133_ = lean_ctor_get(v_x_131_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_x_131_);
if (v_isSharedCheck_149_ == 0)
{
v___x_135_ = v_x_131_;
v_isShared_136_ = v_isSharedCheck_149_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_tl_133_);
lean_inc(v_hd_132_);
lean_dec(v_x_131_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_149_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; uint8_t v___x_138_; 
lean_inc_ref(v_p_130_);
lean_inc(v_hd_132_);
v___x_137_ = lean_apply_1(v_p_130_, v_hd_132_);
v___x_138_ = lean_unbox(v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___f_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
lean_del_object(v___x_135_);
v___f_139_ = lean_alloc_closure((void*)(l_Lean_AsyncList_waitUntil___redArg___lam__0), 2, 1);
lean_closure_set(v___f_139_, 0, v_hd_132_);
v___x_140_ = l_Lean_AsyncList_waitUntil___redArg(v_p_130_, v_tl_133_);
v___x_141_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_139_, v___x_140_);
return v___x_141_;
}
else
{
lean_object* v___x_142_; lean_object* v___x_144_; 
lean_dec(v_tl_133_);
lean_dec_ref(v_p_130_);
v___x_142_ = lean_box(0);
if (v_isShared_136_ == 0)
{
lean_ctor_set_tag(v___x_135_, 1);
lean_ctor_set(v___x_135_, 1, v___x_142_);
v___x_144_ = v___x_135_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_hd_132_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_142_);
v___x_144_ = v_reuseFailAlloc_148_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_box(0);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = lean_task_pure(v___x_146_);
return v___x_147_;
}
}
}
}
case 1:
{
lean_object* v_tl_150_; lean_object* v___f_151_; lean_object* v___x_152_; 
v_tl_150_ = lean_ctor_get(v_x_131_, 0);
lean_inc_ref(v_tl_150_);
lean_dec_ref_known(v_x_131_, 1);
v___f_151_ = lean_alloc_closure((void*)(l_Lean_AsyncList_waitUntil___redArg___lam__1), 2, 1);
lean_closure_set(v___f_151_, 0, v_p_130_);
v___x_152_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_tl_150_, v___f_151_);
return v___x_152_;
}
default: 
{
lean_object* v___x_153_; 
lean_dec_ref(v_p_130_);
v___x_153_ = lean_obj_once(&l_Lean_AsyncList_waitUntil___redArg___closed__1, &l_Lean_AsyncList_waitUntil___redArg___closed__1_once, _init_l_Lean_AsyncList_waitUntil___redArg___closed__1);
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil___redArg___lam__1(lean_object* v_p_154_, lean_object* v_x_155_){
_start:
{
if (lean_obj_tag(v_x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_166_; 
lean_dec_ref(v_p_154_);
v_a_156_ = lean_ctor_get(v_x_155_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v_x_155_);
if (v_isSharedCheck_166_ == 0)
{
v___x_158_ = v_x_155_;
v_isShared_159_ = v_isSharedCheck_166_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v_x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_166_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = lean_box(0);
if (v_isShared_159_ == 0)
{
lean_ctor_set_tag(v___x_158_, 1);
v___x_162_ = v___x_158_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_156_);
v___x_162_ = v_reuseFailAlloc_165_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_160_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = lean_task_pure(v___x_163_);
return v___x_164_;
}
}
}
else
{
lean_object* v_a_167_; lean_object* v___x_168_; 
v_a_167_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_a_167_);
lean_dec_ref_known(v_x_155_, 1);
v___x_168_ = l_Lean_AsyncList_waitUntil___redArg(v_p_154_, v_a_167_);
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil(lean_object* v_00_u03b1_169_, lean_object* v_00_u03b5_170_, lean_object* v_p_171_, lean_object* v_x_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_AsyncList_waitUntil___redArg(v_p_171_, v_x_172_);
return v___x_173_;
}
}
LEAN_EXPORT uint8_t l_Lean_AsyncList_waitAll___redArg___lam__0(lean_object* v_x_174_){
_start:
{
uint8_t v___x_175_; 
v___x_175_ = 0;
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitAll___redArg___lam__0___boxed(lean_object* v_x_176_){
_start:
{
uint8_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = l_Lean_AsyncList_waitAll___redArg___lam__0(v_x_176_);
lean_dec(v_x_176_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitAll___redArg(lean_object* v_a_180_){
_start:
{
lean_object* v___f_181_; lean_object* v___x_182_; 
v___f_181_ = ((lean_object*)(l_Lean_AsyncList_waitAll___redArg___closed__0));
v___x_182_ = l_Lean_AsyncList_waitUntil___redArg(v___f_181_, v_a_180_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitAll(lean_object* v_00_u03b5_183_, lean_object* v_00_u03b1_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_AsyncList_waitAll___redArg(v_a_185_);
return v___x_186_;
}
}
static lean_object* _init_l_Lean_AsyncList_waitFind_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l_Lean_AsyncList_waitFind_x3f___redArg___closed__0));
v___x_190_ = lean_task_pure(v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitFind_x3f___redArg(lean_object* v_p_191_, lean_object* v_x_192_){
_start:
{
switch(lean_obj_tag(v_x_192_))
{
case 0:
{
lean_object* v_hd_193_; lean_object* v_tl_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_hd_193_ = lean_ctor_get(v_x_192_, 0);
lean_inc_n(v_hd_193_, 2);
v_tl_194_ = lean_ctor_get(v_x_192_, 1);
lean_inc(v_tl_194_);
lean_dec_ref_known(v_x_192_, 2);
lean_inc_ref(v_p_191_);
v___x_195_ = lean_apply_1(v_p_191_, v_hd_193_);
v___x_196_ = lean_unbox(v___x_195_);
if (v___x_196_ == 0)
{
lean_dec(v_hd_193_);
v_x_192_ = v_tl_194_;
goto _start;
}
else
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec(v_tl_194_);
lean_dec_ref(v_p_191_);
v___x_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_198_, 0, v_hd_193_);
v___x_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
v___x_200_ = lean_task_pure(v___x_199_);
return v___x_200_;
}
}
case 1:
{
lean_object* v_tl_201_; lean_object* v___f_202_; lean_object* v___x_203_; 
v_tl_201_ = lean_ctor_get(v_x_192_, 0);
lean_inc_ref(v_tl_201_);
lean_dec_ref_known(v_x_192_, 1);
v___f_202_ = lean_alloc_closure((void*)(l_Lean_AsyncList_waitFind_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_202_, 0, v_p_191_);
v___x_203_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_tl_201_, v___f_202_);
return v___x_203_;
}
default: 
{
lean_object* v___x_204_; 
lean_dec_ref(v_p_191_);
v___x_204_ = lean_obj_once(&l_Lean_AsyncList_waitFind_x3f___redArg___closed__1, &l_Lean_AsyncList_waitFind_x3f___redArg___closed__1_once, _init_l_Lean_AsyncList_waitFind_x3f___redArg___closed__1);
return v___x_204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitFind_x3f___redArg___lam__0(lean_object* v_p_205_, lean_object* v_x_206_){
_start:
{
if (lean_obj_tag(v_x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_215_; 
lean_dec_ref(v_p_205_);
v_a_207_ = lean_ctor_get(v_x_206_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v_x_206_);
if (v_isSharedCheck_215_ == 0)
{
v___x_209_ = v_x_206_;
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v_x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_214_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; 
v___x_213_ = lean_task_pure(v___x_212_);
return v___x_213_;
}
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_217_; 
v_a_216_ = lean_ctor_get(v_x_206_, 0);
lean_inc(v_a_216_);
lean_dec_ref_known(v_x_206_, 1);
v___x_217_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_205_, v_a_216_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitFind_x3f(lean_object* v_00_u03b1_218_, lean_object* v_00_u03b5_219_, lean_object* v_p_220_, lean_object* v_x_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_220_, v_x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix___redArg(lean_object* v_x_230_){
_start:
{
switch(lean_obj_tag(v_x_230_))
{
case 0:
{
lean_object* v_hd_232_; lean_object* v_tl_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_250_; 
v_hd_232_ = lean_ctor_get(v_x_230_, 0);
v_tl_233_ = lean_ctor_get(v_x_230_, 1);
v_isSharedCheck_250_ = !lean_is_exclusive(v_x_230_);
if (v_isSharedCheck_250_ == 0)
{
v___x_235_ = v_x_230_;
v_isShared_236_ = v_isSharedCheck_250_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_tl_233_);
lean_inc(v_hd_232_);
lean_dec(v_x_230_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_250_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v_fst_238_; lean_object* v_snd_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_249_; 
v___x_237_ = l_Lean_AsyncList_getFinishedPrefix___redArg(v_tl_233_);
v_fst_238_ = lean_ctor_get(v___x_237_, 0);
v_snd_239_ = lean_ctor_get(v___x_237_, 1);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_249_ == 0)
{
v___x_241_ = v___x_237_;
v_isShared_242_ = v_isSharedCheck_249_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_snd_239_);
lean_inc(v_fst_238_);
lean_dec(v___x_237_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_249_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set_tag(v___x_235_, 1);
lean_ctor_set(v___x_235_, 1, v_fst_238_);
v___x_244_ = v___x_235_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_hd_232_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_fst_238_);
v___x_244_ = v_reuseFailAlloc_248_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_246_; 
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v___x_244_);
v___x_246_ = v___x_241_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_snd_239_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
case 1:
{
lean_object* v_tl_251_; uint8_t v___x_252_; 
v_tl_251_ = lean_ctor_get(v_x_230_, 0);
lean_inc_ref(v_tl_251_);
lean_dec_ref_known(v_x_230_, 1);
v___x_252_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_tl_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec_ref(v_tl_251_);
v___x_253_ = lean_box(0);
v___x_254_ = lean_box(0);
v___x_255_ = lean_box(v___x_252_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_253_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
return v___x_257_;
}
else
{
lean_object* v___x_258_; 
v___x_258_ = lean_io_wait(v_tl_251_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_270_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_270_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_270_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_270_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_263_ = lean_box(0);
if (v_isShared_262_ == 0)
{
lean_ctor_set_tag(v___x_261_, 1);
v___x_265_ = v___x_261_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_259_);
v___x_265_ = v_reuseFailAlloc_269_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_box(v___x_252_);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_263_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
return v___x_268_;
}
}
}
else
{
lean_object* v_a_271_; 
v_a_271_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_a_271_);
lean_dec_ref_known(v___x_258_, 1);
v_x_230_ = v_a_271_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_273_; 
v___x_273_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefix___redArg___closed__1));
return v___x_273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix___redArg___boxed(lean_object* v_x_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_AsyncList_getFinishedPrefix___redArg(v_x_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix(lean_object* v_00_u03b5_277_, lean_object* v_00_u03b1_278_, lean_object* v_x_279_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Lean_AsyncList_getFinishedPrefix___redArg(v_x_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix___boxed(lean_object* v_00_u03b5_282_, lean_object* v_00_u03b1_283_, lean_object* v_x_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_AsyncList_getFinishedPrefix(v_00_u03b5_282_, v_00_u03b1_283_, v_x_284_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___lam__0(lean_object* v_val_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_288_, 0, v_val_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___lam__0(lean_object* v_val_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v_val_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
if (lean_obj_tag(v_a_292_) == 0)
{
lean_object* v___x_294_; 
v___x_294_ = l_List_reverse___redArg(v_a_293_);
return v___x_294_;
}
else
{
lean_object* v_head_295_; lean_object* v_tail_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_306_; 
v_head_295_ = lean_ctor_get(v_a_292_, 0);
v_tail_296_ = lean_ctor_get(v_a_292_, 1);
v_isSharedCheck_306_ = !lean_is_exclusive(v_a_292_);
if (v_isSharedCheck_306_ == 0)
{
v___x_298_ = v_a_292_;
v_isShared_299_ = v_isSharedCheck_306_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_tail_296_);
lean_inc(v_head_295_);
lean_dec(v_a_292_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_306_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___f_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v___f_300_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0));
v___x_301_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_300_, v_head_295_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v_a_293_);
lean_ctor_set(v___x_298_, 0, v___x_301_);
v___x_303_ = v___x_298_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_a_293_);
v___x_303_ = v_reuseFailAlloc_305_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
v_a_292_ = v_tail_296_;
v_a_293_ = v___x_303_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(lean_object* v_cancelTks_308_, lean_object* v_timeoutTask_309_, lean_object* v_xs_310_){
_start:
{
switch(lean_obj_tag(v_xs_310_))
{
case 0:
{
lean_object* v_hd_312_; lean_object* v_tl_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_330_; 
v_hd_312_ = lean_ctor_get(v_xs_310_, 0);
v_tl_313_ = lean_ctor_get(v_xs_310_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_xs_310_);
if (v_isSharedCheck_330_ == 0)
{
v___x_315_ = v_xs_310_;
v_isShared_316_ = v_isSharedCheck_330_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_tl_313_);
lean_inc(v_hd_312_);
lean_dec(v_xs_310_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_330_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v_fst_318_; lean_object* v_snd_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_329_; 
v___x_317_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_308_, v_timeoutTask_309_, v_tl_313_);
v_fst_318_ = lean_ctor_get(v___x_317_, 0);
v_snd_319_ = lean_ctor_get(v___x_317_, 1);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_329_ == 0)
{
v___x_321_ = v___x_317_;
v_isShared_322_ = v_isSharedCheck_329_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_snd_319_);
lean_inc(v_fst_318_);
lean_dec(v___x_317_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_329_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set_tag(v___x_315_, 1);
lean_ctor_set(v___x_315_, 1, v_fst_318_);
v___x_324_ = v___x_315_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_hd_312_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_fst_318_);
v___x_324_ = v_reuseFailAlloc_328_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_326_; 
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_324_);
v___x_326_ = v___x_321_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_snd_319_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
case 1:
{
lean_object* v_tl_331_; lean_object* v___f_332_; uint8_t v___x_333_; uint8_t v___x_334_; 
v_tl_331_ = lean_ctor_get(v_xs_310_, 0);
lean_inc_ref(v_tl_331_);
lean_dec_ref_known(v_xs_310_, 1);
v___f_332_ = ((lean_object*)(l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0));
v___x_333_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_tl_331_);
v___x_334_ = 1;
if (v___x_333_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_335_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_332_, v_tl_331_);
v___x_336_ = lean_box(0);
lean_inc(v_cancelTks_308_);
v___x_337_ = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(v_cancelTks_308_, v___x_336_);
v___x_338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_335_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
lean_inc_ref(v_timeoutTask_309_);
v___x_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_339_, 0, v_timeoutTask_309_);
lean_ctor_set(v___x_339_, 1, v___x_336_);
v___x_340_ = l_List_appendTR___redArg(v___x_338_, v___x_339_);
v___x_341_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_340_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
lean_dec_ref_known(v___x_341_, 1);
lean_dec_ref(v_timeoutTask_309_);
lean_dec(v_cancelTks_308_);
v___x_342_ = lean_box(0);
v___x_343_ = lean_box(v___x_333_);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_336_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
return v___x_345_;
}
else
{
lean_object* v_val_346_; 
v_val_346_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_val_346_);
lean_dec_ref_known(v___x_341_, 1);
if (lean_obj_tag(v_val_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_357_; 
lean_dec_ref(v_timeoutTask_309_);
lean_dec(v_cancelTks_308_);
v_a_347_ = lean_ctor_get(v_val_346_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v_val_346_);
if (v_isSharedCheck_357_ == 0)
{
v___x_349_ = v_val_346_;
v_isShared_350_ = v_isSharedCheck_357_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v_val_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_357_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
lean_ctor_set_tag(v___x_349_, 1);
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_356_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_box(v___x_334_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_352_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_336_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
return v___x_355_;
}
}
}
else
{
lean_object* v_a_358_; 
v_a_358_ = lean_ctor_get(v_val_346_, 0);
lean_inc(v_a_358_);
lean_dec_ref_known(v_val_346_, 1);
v_xs_310_ = v_a_358_;
goto _start;
}
}
}
else
{
lean_object* v___x_360_; 
v___x_360_ = lean_io_wait(v_tl_331_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_372_; 
lean_dec_ref(v_timeoutTask_309_);
lean_dec(v_cancelTks_308_);
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_372_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_372_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_372_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_365_ = lean_box(0);
if (v_isShared_364_ == 0)
{
lean_ctor_set_tag(v___x_363_, 1);
v___x_367_ = v___x_363_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_361_);
v___x_367_ = v_reuseFailAlloc_371_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = lean_box(v___x_334_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_367_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_365_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
return v___x_370_;
}
}
}
else
{
lean_object* v_a_373_; 
v_a_373_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_a_373_);
lean_dec_ref_known(v___x_360_, 1);
v_xs_310_ = v_a_373_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_375_; 
lean_dec_ref(v_timeoutTask_309_);
lean_dec(v_cancelTks_308_);
v___x_375_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefix___redArg___closed__1));
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___boxed(lean_object* v_cancelTks_376_, lean_object* v_timeoutTask_377_, lean_object* v_xs_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_376_, v_timeoutTask_377_, v_xs_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go(lean_object* v_00_u03b5_381_, lean_object* v_00_u03b1_382_, lean_object* v_cancelTks_383_, lean_object* v_timeoutTask_384_, lean_object* v_xs_385_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_383_, v_timeoutTask_384_, v_xs_385_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___boxed(lean_object* v_00_u03b5_388_, lean_object* v_00_u03b1_389_, lean_object* v_cancelTks_390_, lean_object* v_timeoutTask_391_, lean_object* v_xs_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go(v_00_u03b5_388_, v_00_u03b1_389_, v_cancelTks_390_, v_timeoutTask_391_, v_xs_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0(lean_object* v_00_u03b5_395_, lean_object* v_00_u03b1_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(v_a_397_, v_a_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(uint32_t v_timeoutMs_402_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = l_IO_sleep(v_timeoutMs_402_);
v___x_405_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0));
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed(lean_object* v_timeoutMs_406_, lean_object* v___y_407_){
_start:
{
uint32_t v_timeoutMs_boxed_408_; lean_object* v_res_409_; 
v_timeoutMs_boxed_408_ = lean_unbox_uint32(v_timeoutMs_406_);
lean_dec(v_timeoutMs_406_);
v_res_409_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(v_timeoutMs_boxed_408_);
return v_res_409_;
}
}
static lean_object* _init_l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0));
v___x_411_ = lean_task_pure(v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(lean_object* v_xs_412_, uint32_t v_timeoutMs_413_, lean_object* v_cancelTks_414_){
_start:
{
uint32_t v___x_416_; uint8_t v___x_417_; 
v___x_416_ = 0;
v___x_417_ = lean_uint32_dec_eq(v_timeoutMs_413_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___f_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_418_ = lean_box_uint32(v_timeoutMs_413_);
v___f_419_ = lean_alloc_closure((void*)(l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_419_, 0, v___x_418_);
v___x_420_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v___f_419_);
v___x_421_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_414_, v___x_420_, v_xs_412_);
return v___x_421_;
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_obj_once(&l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0, &l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0_once, _init_l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0);
v___x_423_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_414_, v___x_422_, v_xs_412_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___boxed(lean_object* v_xs_424_, lean_object* v_timeoutMs_425_, lean_object* v_cancelTks_426_, lean_object* v_a_427_){
_start:
{
uint32_t v_timeoutMs_boxed_428_; lean_object* v_res_429_; 
v_timeoutMs_boxed_428_ = lean_unbox_uint32(v_timeoutMs_425_);
lean_dec(v_timeoutMs_425_);
v_res_429_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_424_, v_timeoutMs_boxed_428_, v_cancelTks_426_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout(lean_object* v_00_u03b5_430_, lean_object* v_00_u03b1_431_, lean_object* v_xs_432_, uint32_t v_timeoutMs_433_, lean_object* v_cancelTks_434_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_432_, v_timeoutMs_433_, v_cancelTks_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___boxed(lean_object* v_00_u03b5_437_, lean_object* v_00_u03b1_438_, lean_object* v_xs_439_, lean_object* v_timeoutMs_440_, lean_object* v_cancelTks_441_, lean_object* v_a_442_){
_start:
{
uint32_t v_timeoutMs_boxed_443_; lean_object* v_res_444_; 
v_timeoutMs_boxed_443_ = lean_unbox_uint32(v_timeoutMs_440_);
lean_dec(v_timeoutMs_440_);
v_res_444_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout(v_00_u03b5_437_, v_00_u03b1_438_, v_xs_439_, v_timeoutMs_boxed_443_, v_cancelTks_441_);
return v_res_444_;
}
}
LEAN_EXPORT uint8_t l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(lean_object* v_x_445_){
_start:
{
if (lean_obj_tag(v_x_445_) == 0)
{
uint8_t v___x_447_; 
v___x_447_ = 0;
return v___x_447_;
}
else
{
lean_object* v_head_448_; lean_object* v_tail_449_; uint8_t v___x_450_; 
v_head_448_ = lean_ctor_get(v_x_445_, 0);
v_tail_449_ = lean_ctor_get(v_x_445_, 1);
v___x_450_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_head_448_);
if (v___x_450_ == 0)
{
v_x_445_ = v_tail_449_;
goto _start;
}
else
{
return v___x_450_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0___boxed(lean_object* v_x_452_, lean_object* v___y_453_){
_start:
{
uint8_t v_res_454_; lean_object* v_r_455_; 
v_res_454_ = l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(v_x_452_);
lean_dec(v_x_452_);
v_r_455_ = lean_box(v_res_454_);
return v_r_455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(lean_object* v_cancelTks_456_, uint32_t v_sleepDurationMs_457_){
_start:
{
uint32_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = 0;
v___x_460_ = lean_uint32_dec_eq(v_sleepDurationMs_457_, v___x_459_);
if (v___x_460_ == 0)
{
uint8_t v___x_461_; 
v___x_461_ = l_List_isEmpty___redArg(v_cancelTks_456_);
if (v___x_461_ == 0)
{
uint8_t v___x_462_; 
v___x_462_ = l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(v_cancelTks_456_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_463_ = lean_box_uint32(v_sleepDurationMs_457_);
v___x_464_ = lean_alloc_closure((void*)(l_IO_sleep___boxed), 2, 1);
lean_closure_set(v___x_464_, 0, v___x_463_);
v___x_465_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v___x_464_);
v___x_466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v_cancelTks_456_);
v___x_467_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_466_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; 
lean_dec(v_cancelTks_456_);
v___x_468_ = lean_box(0);
return v___x_468_;
}
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v_cancelTks_456_);
v___x_469_ = l_IO_sleep(v_sleepDurationMs_457_);
v___x_470_ = lean_box(0);
return v___x_470_;
}
}
else
{
lean_object* v___x_471_; 
lean_dec(v_cancelTks_456_);
v___x_471_ = lean_box(0);
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___boxed(lean_object* v_cancelTks_472_, lean_object* v_sleepDurationMs_473_, lean_object* v_a_474_){
_start:
{
uint32_t v_sleepDurationMs_boxed_475_; lean_object* v_res_476_; 
v_sleepDurationMs_boxed_475_ = lean_unbox_uint32(v_sleepDurationMs_473_);
lean_dec(v_sleepDurationMs_473_);
v_res_476_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(v_cancelTks_472_, v_sleepDurationMs_boxed_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(lean_object* v_xs_477_, uint32_t v_latencyMs_478_, lean_object* v_cancelTks_479_){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint32_t v___x_487_; lean_object* v___x_488_; 
v___x_481_ = lean_io_mono_ms_now();
lean_inc(v_cancelTks_479_);
v___x_482_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_477_, v_latencyMs_478_, v_cancelTks_479_);
v___x_483_ = lean_io_mono_ms_now();
v___x_484_ = lean_nat_sub(v___x_483_, v___x_481_);
lean_dec(v___x_481_);
lean_dec(v___x_483_);
v___x_485_ = lean_uint32_to_nat(v_latencyMs_478_);
v___x_486_ = lean_nat_sub(v___x_485_, v___x_484_);
lean_dec(v___x_484_);
lean_dec(v___x_485_);
v___x_487_ = lean_uint32_of_nat(v___x_486_);
lean_dec(v___x_486_);
v___x_488_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(v_cancelTks_479_, v___x_487_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg___boxed(lean_object* v_xs_489_, lean_object* v_latencyMs_490_, lean_object* v_cancelTks_491_, lean_object* v_a_492_){
_start:
{
uint32_t v_latencyMs_boxed_493_; lean_object* v_res_494_; 
v_latencyMs_boxed_493_ = lean_unbox_uint32(v_latencyMs_490_);
lean_dec(v_latencyMs_490_);
v_res_494_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(v_xs_489_, v_latencyMs_boxed_493_, v_cancelTks_491_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency(lean_object* v_00_u03b5_495_, lean_object* v_00_u03b1_496_, lean_object* v_xs_497_, uint32_t v_latencyMs_498_, lean_object* v_cancelTks_499_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(v_xs_497_, v_latencyMs_498_, v_cancelTks_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___boxed(lean_object* v_00_u03b5_502_, lean_object* v_00_u03b1_503_, lean_object* v_xs_504_, lean_object* v_latencyMs_505_, lean_object* v_cancelTks_506_, lean_object* v_a_507_){
_start:
{
uint32_t v_latencyMs_boxed_508_; lean_object* v_res_509_; 
v_latencyMs_boxed_508_ = lean_unbox_uint32(v_latencyMs_505_);
lean_dec(v_latencyMs_505_);
v_res_509_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency(v_00_u03b5_502_, v_00_u03b1_503_, v_xs_504_, v_latencyMs_boxed_508_, v_cancelTks_506_);
return v_res_509_;
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
