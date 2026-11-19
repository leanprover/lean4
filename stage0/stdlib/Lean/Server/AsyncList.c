// Lean compiler output
// Module: Lean.Server.AsyncList
// Imports: public import Lean.Server.ServerTask import Init.Data.List.Impl
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
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_AsyncList_ofList_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_AsyncList_ofList_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_AsyncList_ofList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_ofList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_ofList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_AsyncList_ofList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_AsyncList_ofList_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_AsyncList_ofList_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_AsyncList_ofList_spec__0_spec__0___redArg(lean_object* v_as_73_, size_t v_i_74_, size_t v_stop_75_, lean_object* v_b_76_){
_start:
{
uint8_t v___x_77_; 
v___x_77_ = lean_usize_dec_eq(v_i_74_, v_stop_75_);
if (v___x_77_ == 0)
{
size_t v___x_78_; size_t v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = ((size_t)1ULL);
v___x_79_ = lean_usize_sub(v_i_74_, v___x_78_);
v___x_80_ = lean_array_uget_borrowed(v_as_73_, v___x_79_);
lean_inc(v___x_80_);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v_b_76_);
v_i_74_ = v___x_79_;
v_b_76_ = v___x_81_;
goto _start;
}
else
{
return v_b_76_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_AsyncList_ofList_spec__0_spec__0___redArg___boxed(lean_object* v_as_83_, lean_object* v_i_84_, lean_object* v_stop_85_, lean_object* v_b_86_){
_start:
{
size_t v_i_boxed_87_; size_t v_stop_boxed_88_; lean_object* v_res_89_; 
v_i_boxed_87_ = lean_unbox_usize(v_i_84_);
lean_dec(v_i_84_);
v_stop_boxed_88_ = lean_unbox_usize(v_stop_85_);
lean_dec(v_stop_85_);
v_res_89_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_AsyncList_ofList_spec__0_spec__0___redArg(v_as_83_, v_i_boxed_87_, v_stop_boxed_88_, v_b_86_);
lean_dec_ref(v_as_83_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_AsyncList_ofList_spec__0___redArg(lean_object* v_init_90_, lean_object* v_l_91_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_92_ = lean_array_mk(v_l_91_);
v___x_93_ = lean_array_get_size(v___x_92_);
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_nat_dec_lt(v___x_94_, v___x_93_);
if (v___x_95_ == 0)
{
lean_dec_ref(v___x_92_);
return v_init_90_;
}
else
{
size_t v___x_96_; size_t v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_usize_of_nat(v___x_93_);
v___x_97_ = ((size_t)0ULL);
v___x_98_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_AsyncList_ofList_spec__0_spec__0___redArg(v___x_92_, v___x_96_, v___x_97_, v_init_90_);
lean_dec_ref(v___x_92_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ofList___redArg(lean_object* v_l_99_){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_box(2);
v___x_101_ = l_List_foldrTR___at___00Lean_AsyncList_ofList_spec__0___redArg(v___x_100_, v_l_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ofList(lean_object* v_00_u03b1_102_, lean_object* v_00_u03b5_103_, lean_object* v_l_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_AsyncList_ofList___redArg(v_l_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_AsyncList_ofList_spec__0(lean_object* v_00_u03b1_106_, lean_object* v_00_u03b5_107_, lean_object* v_init_108_, lean_object* v_l_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_List_foldrTR___at___00Lean_AsyncList_ofList_spec__0___redArg(v_init_108_, v_l_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_AsyncList_ofList_spec__0_spec__0(lean_object* v_00_u03b1_111_, lean_object* v_00_u03b5_112_, lean_object* v_as_113_, size_t v_i_114_, size_t v_stop_115_, lean_object* v_b_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_AsyncList_ofList_spec__0_spec__0___redArg(v_as_113_, v_i_114_, v_stop_115_, v_b_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_AsyncList_ofList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_118_, lean_object* v_00_u03b5_119_, lean_object* v_as_120_, lean_object* v_i_121_, lean_object* v_stop_122_, lean_object* v_b_123_){
_start:
{
size_t v_i_boxed_124_; size_t v_stop_boxed_125_; lean_object* v_res_126_; 
v_i_boxed_124_ = lean_unbox_usize(v_i_121_);
lean_dec(v_i_121_);
v_stop_boxed_125_ = lean_unbox_usize(v_stop_122_);
lean_dec(v_stop_122_);
v_res_126_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_AsyncList_ofList_spec__0_spec__0(v_00_u03b1_118_, v_00_u03b5_119_, v_as_120_, v_i_boxed_124_, v_stop_boxed_125_, v_b_123_);
lean_dec_ref(v_as_120_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_instCoeList___redArg(){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = ((lean_object*)(l_Lean_AsyncList_instCoeList___redArg___closed__0));
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_instCoeList___redArg___boxed(lean_object* v___dummy_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_AsyncList_instCoeList___redArg();
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_instCoeList(lean_object* v_00_u03b1_132_, lean_object* v_00_u03b5_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = ((lean_object*)(l_Lean_AsyncList_instCoeList___redArg___closed__0));
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil___redArg___lam__0(lean_object* v_hd_135_, lean_object* v_x_136_){
_start:
{
lean_object* v_fst_137_; lean_object* v_snd_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_146_; 
v_fst_137_ = lean_ctor_get(v_x_136_, 0);
v_snd_138_ = lean_ctor_get(v_x_136_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_x_136_);
if (v_isSharedCheck_146_ == 0)
{
v___x_140_ = v_x_136_;
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_snd_138_);
lean_inc(v_fst_137_);
lean_dec(v_x_136_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_142_, 0, v_hd_135_);
lean_ctor_set(v___x_142_, 1, v_fst_137_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_142_);
v___x_144_ = v___x_140_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_snd_138_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
static lean_object* _init_l_Lean_AsyncList_waitUntil___redArg___closed__1(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l_Lean_AsyncList_waitUntil___redArg___closed__0));
v___x_151_ = lean_task_pure(v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil___redArg(lean_object* v_p_152_, lean_object* v_x_153_){
_start:
{
switch(lean_obj_tag(v_x_153_))
{
case 0:
{
lean_object* v_hd_154_; lean_object* v_tl_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_171_; 
v_hd_154_ = lean_ctor_get(v_x_153_, 0);
v_tl_155_ = lean_ctor_get(v_x_153_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v_x_153_);
if (v_isSharedCheck_171_ == 0)
{
v___x_157_ = v_x_153_;
v_isShared_158_ = v_isSharedCheck_171_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_tl_155_);
lean_inc(v_hd_154_);
lean_dec(v_x_153_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_171_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; uint8_t v___x_160_; 
lean_inc_ref(v_p_152_);
lean_inc(v_hd_154_);
v___x_159_ = lean_apply_1(v_p_152_, v_hd_154_);
v___x_160_ = lean_unbox(v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___f_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
lean_del_object(v___x_157_);
v___f_161_ = lean_alloc_closure((void*)(l_Lean_AsyncList_waitUntil___redArg___lam__0), 2, 1);
lean_closure_set(v___f_161_, 0, v_hd_154_);
v___x_162_ = l_Lean_AsyncList_waitUntil___redArg(v_p_152_, v_tl_155_);
v___x_163_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_161_, v___x_162_);
return v___x_163_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_166_; 
lean_dec(v_tl_155_);
lean_dec_ref(v_p_152_);
v___x_164_ = lean_box(0);
if (v_isShared_158_ == 0)
{
lean_ctor_set_tag(v___x_157_, 1);
lean_ctor_set(v___x_157_, 1, v___x_164_);
v___x_166_ = v___x_157_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_hd_154_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v___x_164_);
v___x_166_ = v_reuseFailAlloc_170_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_box(0);
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = lean_task_pure(v___x_168_);
return v___x_169_;
}
}
}
}
case 1:
{
lean_object* v_tl_172_; lean_object* v___f_173_; lean_object* v___x_174_; 
v_tl_172_ = lean_ctor_get(v_x_153_, 0);
lean_inc_ref(v_tl_172_);
lean_dec_ref_known(v_x_153_, 1);
v___f_173_ = lean_alloc_closure((void*)(l_Lean_AsyncList_waitUntil___redArg___lam__1), 2, 1);
lean_closure_set(v___f_173_, 0, v_p_152_);
v___x_174_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_tl_172_, v___f_173_);
return v___x_174_;
}
default: 
{
lean_object* v___x_175_; 
lean_dec_ref(v_p_152_);
v___x_175_ = lean_obj_once(&l_Lean_AsyncList_waitUntil___redArg___closed__1, &l_Lean_AsyncList_waitUntil___redArg___closed__1_once, _init_l_Lean_AsyncList_waitUntil___redArg___closed__1);
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil___redArg___lam__1(lean_object* v_p_176_, lean_object* v_x_177_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_188_; 
lean_dec_ref(v_p_176_);
v_a_178_ = lean_ctor_get(v_x_177_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v_x_177_);
if (v_isSharedCheck_188_ == 0)
{
v___x_180_ = v_x_177_;
v_isShared_181_ = v_isSharedCheck_188_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v_x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_188_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_182_ = lean_box(0);
if (v_isShared_181_ == 0)
{
lean_ctor_set_tag(v___x_180_, 1);
v___x_184_ = v___x_180_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_178_);
v___x_184_ = v_reuseFailAlloc_187_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_182_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_task_pure(v___x_185_);
return v___x_186_;
}
}
}
else
{
lean_object* v_a_189_; lean_object* v___x_190_; 
v_a_189_ = lean_ctor_get(v_x_177_, 0);
lean_inc(v_a_189_);
lean_dec_ref_known(v_x_177_, 1);
v___x_190_ = l_Lean_AsyncList_waitUntil___redArg(v_p_176_, v_a_189_);
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil(lean_object* v_00_u03b1_191_, lean_object* v_00_u03b5_192_, lean_object* v_p_193_, lean_object* v_x_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_AsyncList_waitUntil___redArg(v_p_193_, v_x_194_);
return v___x_195_;
}
}
LEAN_EXPORT uint8_t l_Lean_AsyncList_waitAll___redArg___lam__0(lean_object* v_x_196_){
_start:
{
uint8_t v___x_197_; 
v___x_197_ = 0;
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitAll___redArg___lam__0___boxed(lean_object* v_x_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = l_Lean_AsyncList_waitAll___redArg___lam__0(v_x_198_);
lean_dec(v_x_198_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitAll___redArg(lean_object* v_a_202_){
_start:
{
lean_object* v___f_203_; lean_object* v___x_204_; 
v___f_203_ = ((lean_object*)(l_Lean_AsyncList_waitAll___redArg___closed__0));
v___x_204_ = l_Lean_AsyncList_waitUntil___redArg(v___f_203_, v_a_202_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitAll(lean_object* v_00_u03b5_205_, lean_object* v_00_u03b1_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_AsyncList_waitAll___redArg(v_a_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_AsyncList_waitFind_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l_Lean_AsyncList_waitFind_x3f___redArg___closed__0));
v___x_212_ = lean_task_pure(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitFind_x3f___redArg(lean_object* v_p_213_, lean_object* v_x_214_){
_start:
{
switch(lean_obj_tag(v_x_214_))
{
case 0:
{
lean_object* v_hd_215_; lean_object* v_tl_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v_hd_215_ = lean_ctor_get(v_x_214_, 0);
lean_inc_n(v_hd_215_, 2);
v_tl_216_ = lean_ctor_get(v_x_214_, 1);
lean_inc(v_tl_216_);
lean_dec_ref_known(v_x_214_, 2);
lean_inc_ref(v_p_213_);
v___x_217_ = lean_apply_1(v_p_213_, v_hd_215_);
v___x_218_ = lean_unbox(v___x_217_);
if (v___x_218_ == 0)
{
lean_dec(v_hd_215_);
v_x_214_ = v_tl_216_;
goto _start;
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec(v_tl_216_);
lean_dec_ref(v_p_213_);
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v_hd_215_);
v___x_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
v___x_222_ = lean_task_pure(v___x_221_);
return v___x_222_;
}
}
case 1:
{
lean_object* v_tl_223_; lean_object* v___f_224_; lean_object* v___x_225_; 
v_tl_223_ = lean_ctor_get(v_x_214_, 0);
lean_inc_ref(v_tl_223_);
lean_dec_ref_known(v_x_214_, 1);
v___f_224_ = lean_alloc_closure((void*)(l_Lean_AsyncList_waitFind_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_224_, 0, v_p_213_);
v___x_225_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_tl_223_, v___f_224_);
return v___x_225_;
}
default: 
{
lean_object* v___x_226_; 
lean_dec_ref(v_p_213_);
v___x_226_ = lean_obj_once(&l_Lean_AsyncList_waitFind_x3f___redArg___closed__1, &l_Lean_AsyncList_waitFind_x3f___redArg___closed__1_once, _init_l_Lean_AsyncList_waitFind_x3f___redArg___closed__1);
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitFind_x3f___redArg___lam__0(lean_object* v_p_227_, lean_object* v_x_228_){
_start:
{
if (lean_obj_tag(v_x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_237_; 
lean_dec_ref(v_p_227_);
v_a_229_ = lean_ctor_get(v_x_228_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v_x_228_);
if (v_isSharedCheck_237_ == 0)
{
v___x_231_ = v_x_228_;
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v_x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_229_);
v___x_234_ = v_reuseFailAlloc_236_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; 
v___x_235_ = lean_task_pure(v___x_234_);
return v___x_235_;
}
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_239_; 
v_a_238_ = lean_ctor_get(v_x_228_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v_x_228_, 1);
v___x_239_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_227_, v_a_238_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitFind_x3f(lean_object* v_00_u03b1_240_, lean_object* v_00_u03b5_241_, lean_object* v_p_242_, lean_object* v_x_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_242_, v_x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix___redArg(lean_object* v_x_252_){
_start:
{
switch(lean_obj_tag(v_x_252_))
{
case 0:
{
lean_object* v_hd_254_; lean_object* v_tl_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_272_; 
v_hd_254_ = lean_ctor_get(v_x_252_, 0);
v_tl_255_ = lean_ctor_get(v_x_252_, 1);
v_isSharedCheck_272_ = !lean_is_exclusive(v_x_252_);
if (v_isSharedCheck_272_ == 0)
{
v___x_257_ = v_x_252_;
v_isShared_258_ = v_isSharedCheck_272_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_tl_255_);
lean_inc(v_hd_254_);
lean_dec(v_x_252_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_272_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v_fst_260_; lean_object* v_snd_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_271_; 
v___x_259_ = l_Lean_AsyncList_getFinishedPrefix___redArg(v_tl_255_);
v_fst_260_ = lean_ctor_get(v___x_259_, 0);
v_snd_261_ = lean_ctor_get(v___x_259_, 1);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_271_ == 0)
{
v___x_263_ = v___x_259_;
v_isShared_264_ = v_isSharedCheck_271_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_snd_261_);
lean_inc(v_fst_260_);
lean_dec(v___x_259_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_271_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 1);
lean_ctor_set(v___x_257_, 1, v_fst_260_);
v___x_266_ = v___x_257_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_hd_254_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_fst_260_);
v___x_266_ = v_reuseFailAlloc_270_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_268_; 
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_266_);
v___x_268_ = v___x_263_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_snd_261_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
case 1:
{
lean_object* v_tl_273_; uint8_t v___x_274_; 
v_tl_273_ = lean_ctor_get(v_x_252_, 0);
lean_inc_ref(v_tl_273_);
lean_dec_ref_known(v_x_252_, 1);
v___x_274_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_tl_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec_ref(v_tl_273_);
v___x_275_ = lean_box(0);
v___x_276_ = lean_box(0);
v___x_277_ = lean_box(v___x_274_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_275_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; 
v___x_280_ = lean_io_wait(v_tl_273_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_292_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_292_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_292_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_292_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = lean_box(0);
if (v_isShared_284_ == 0)
{
lean_ctor_set_tag(v___x_283_, 1);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_281_);
v___x_287_ = v_reuseFailAlloc_291_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = lean_box(v___x_274_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_287_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_285_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
return v___x_290_;
}
}
}
else
{
lean_object* v_a_293_; 
v_a_293_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_293_);
lean_dec_ref_known(v___x_280_, 1);
v_x_252_ = v_a_293_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_295_; 
v___x_295_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefix___redArg___closed__1));
return v___x_295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix___redArg___boxed(lean_object* v_x_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_AsyncList_getFinishedPrefix___redArg(v_x_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix(lean_object* v_00_u03b5_299_, lean_object* v_00_u03b1_300_, lean_object* v_x_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_AsyncList_getFinishedPrefix___redArg(v_x_301_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix___boxed(lean_object* v_00_u03b5_304_, lean_object* v_00_u03b1_305_, lean_object* v_x_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_AsyncList_getFinishedPrefix(v_00_u03b5_304_, v_00_u03b1_305_, v_x_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___lam__0(lean_object* v_val_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v_val_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___lam__0(lean_object* v_val_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v_val_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
if (lean_obj_tag(v_a_314_) == 0)
{
lean_object* v___x_316_; 
v___x_316_ = l_List_reverse___redArg(v_a_315_);
return v___x_316_;
}
else
{
lean_object* v_head_317_; lean_object* v_tail_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_328_; 
v_head_317_ = lean_ctor_get(v_a_314_, 0);
v_tail_318_ = lean_ctor_get(v_a_314_, 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_a_314_);
if (v_isSharedCheck_328_ == 0)
{
v___x_320_ = v_a_314_;
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_tail_318_);
lean_inc(v_head_317_);
lean_dec(v_a_314_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___f_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
v___f_322_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0));
v___x_323_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_322_, v_head_317_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v_a_315_);
lean_ctor_set(v___x_320_, 0, v___x_323_);
v___x_325_ = v___x_320_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_a_315_);
v___x_325_ = v_reuseFailAlloc_327_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
v_a_314_ = v_tail_318_;
v_a_315_ = v___x_325_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(lean_object* v_cancelTks_330_, lean_object* v_timeoutTask_331_, lean_object* v_xs_332_){
_start:
{
switch(lean_obj_tag(v_xs_332_))
{
case 0:
{
lean_object* v_hd_334_; lean_object* v_tl_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_352_; 
v_hd_334_ = lean_ctor_get(v_xs_332_, 0);
v_tl_335_ = lean_ctor_get(v_xs_332_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v_xs_332_);
if (v_isSharedCheck_352_ == 0)
{
v___x_337_ = v_xs_332_;
v_isShared_338_ = v_isSharedCheck_352_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_tl_335_);
lean_inc(v_hd_334_);
lean_dec(v_xs_332_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_352_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v_fst_340_; lean_object* v_snd_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_351_; 
v___x_339_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_330_, v_timeoutTask_331_, v_tl_335_);
v_fst_340_ = lean_ctor_get(v___x_339_, 0);
v_snd_341_ = lean_ctor_get(v___x_339_, 1);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_351_ == 0)
{
v___x_343_ = v___x_339_;
v_isShared_344_ = v_isSharedCheck_351_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_snd_341_);
lean_inc(v_fst_340_);
lean_dec(v___x_339_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_351_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set_tag(v___x_337_, 1);
lean_ctor_set(v___x_337_, 1, v_fst_340_);
v___x_346_ = v___x_337_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_hd_334_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_fst_340_);
v___x_346_ = v_reuseFailAlloc_350_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_348_; 
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_346_);
v___x_348_ = v___x_343_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_snd_341_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
case 1:
{
lean_object* v_tl_353_; lean_object* v___f_354_; uint8_t v___x_355_; uint8_t v___x_356_; 
v_tl_353_ = lean_ctor_get(v_xs_332_, 0);
lean_inc_ref(v_tl_353_);
lean_dec_ref_known(v_xs_332_, 1);
v___f_354_ = ((lean_object*)(l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0));
v___x_355_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_tl_353_);
v___x_356_ = 1;
if (v___x_355_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_357_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_354_, v_tl_353_);
v___x_358_ = lean_box(0);
lean_inc(v_cancelTks_330_);
v___x_359_ = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(v_cancelTks_330_, v___x_358_);
v___x_360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_357_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
lean_inc_ref(v_timeoutTask_331_);
v___x_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_361_, 0, v_timeoutTask_331_);
lean_ctor_set(v___x_361_, 1, v___x_358_);
v___x_362_ = l_List_appendTR___redArg(v___x_360_, v___x_361_);
v___x_363_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_362_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
lean_dec_ref_known(v___x_363_, 1);
lean_dec_ref(v_timeoutTask_331_);
lean_dec(v_cancelTks_330_);
v___x_364_ = lean_box(0);
v___x_365_ = lean_box(v___x_355_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_358_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
return v___x_367_;
}
else
{
lean_object* v_val_368_; 
v_val_368_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_val_368_);
lean_dec_ref_known(v___x_363_, 1);
if (lean_obj_tag(v_val_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_379_; 
lean_dec_ref(v_timeoutTask_331_);
lean_dec(v_cancelTks_330_);
v_a_369_ = lean_ctor_get(v_val_368_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v_val_368_);
if (v_isSharedCheck_379_ == 0)
{
v___x_371_ = v_val_368_;
v_isShared_372_ = v_isSharedCheck_379_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v_val_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_379_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 1);
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_378_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = lean_box(v___x_356_);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_358_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
return v___x_377_;
}
}
}
else
{
lean_object* v_a_380_; 
v_a_380_ = lean_ctor_get(v_val_368_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v_val_368_, 1);
v_xs_332_ = v_a_380_;
goto _start;
}
}
}
else
{
lean_object* v___x_382_; 
v___x_382_ = lean_io_wait(v_tl_353_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_394_; 
lean_dec_ref(v_timeoutTask_331_);
lean_dec(v_cancelTks_330_);
v_a_383_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_394_ == 0)
{
v___x_385_ = v___x_382_;
v_isShared_386_ = v_isSharedCheck_394_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_394_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_387_ = lean_box(0);
if (v_isShared_386_ == 0)
{
lean_ctor_set_tag(v___x_385_, 1);
v___x_389_ = v___x_385_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_383_);
v___x_389_ = v_reuseFailAlloc_393_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_390_ = lean_box(v___x_356_);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_389_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_387_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
return v___x_392_;
}
}
}
else
{
lean_object* v_a_395_; 
v_a_395_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_382_, 1);
v_xs_332_ = v_a_395_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_397_; 
lean_dec_ref(v_timeoutTask_331_);
lean_dec(v_cancelTks_330_);
v___x_397_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefix___redArg___closed__1));
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___boxed(lean_object* v_cancelTks_398_, lean_object* v_timeoutTask_399_, lean_object* v_xs_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_398_, v_timeoutTask_399_, v_xs_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go(lean_object* v_00_u03b5_403_, lean_object* v_00_u03b1_404_, lean_object* v_cancelTks_405_, lean_object* v_timeoutTask_406_, lean_object* v_xs_407_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_405_, v_timeoutTask_406_, v_xs_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___boxed(lean_object* v_00_u03b5_410_, lean_object* v_00_u03b1_411_, lean_object* v_cancelTks_412_, lean_object* v_timeoutTask_413_, lean_object* v_xs_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go(v_00_u03b5_410_, v_00_u03b1_411_, v_cancelTks_412_, v_timeoutTask_413_, v_xs_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0(lean_object* v_00_u03b5_417_, lean_object* v_00_u03b1_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(v_a_419_, v_a_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(uint32_t v_timeoutMs_424_){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = l_IO_sleep(v_timeoutMs_424_);
v___x_427_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0));
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed(lean_object* v_timeoutMs_428_, lean_object* v___y_429_){
_start:
{
uint32_t v_timeoutMs_boxed_430_; lean_object* v_res_431_; 
v_timeoutMs_boxed_430_ = lean_unbox_uint32(v_timeoutMs_428_);
lean_dec(v_timeoutMs_428_);
v_res_431_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(v_timeoutMs_boxed_430_);
return v_res_431_;
}
}
static lean_object* _init_l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0));
v___x_433_ = lean_task_pure(v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(lean_object* v_xs_434_, uint32_t v_timeoutMs_435_, lean_object* v_cancelTks_436_){
_start:
{
uint32_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = 0;
v___x_439_ = lean_uint32_dec_eq(v_timeoutMs_435_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___f_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_440_ = lean_box_uint32(v_timeoutMs_435_);
v___f_441_ = lean_alloc_closure((void*)(l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_441_, 0, v___x_440_);
v___x_442_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v___f_441_);
v___x_443_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_436_, v___x_442_, v_xs_434_);
return v___x_443_;
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_obj_once(&l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0, &l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0_once, _init_l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0);
v___x_445_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_436_, v___x_444_, v_xs_434_);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___boxed(lean_object* v_xs_446_, lean_object* v_timeoutMs_447_, lean_object* v_cancelTks_448_, lean_object* v_a_449_){
_start:
{
uint32_t v_timeoutMs_boxed_450_; lean_object* v_res_451_; 
v_timeoutMs_boxed_450_ = lean_unbox_uint32(v_timeoutMs_447_);
lean_dec(v_timeoutMs_447_);
v_res_451_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_446_, v_timeoutMs_boxed_450_, v_cancelTks_448_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout(lean_object* v_00_u03b5_452_, lean_object* v_00_u03b1_453_, lean_object* v_xs_454_, uint32_t v_timeoutMs_455_, lean_object* v_cancelTks_456_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_454_, v_timeoutMs_455_, v_cancelTks_456_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___boxed(lean_object* v_00_u03b5_459_, lean_object* v_00_u03b1_460_, lean_object* v_xs_461_, lean_object* v_timeoutMs_462_, lean_object* v_cancelTks_463_, lean_object* v_a_464_){
_start:
{
uint32_t v_timeoutMs_boxed_465_; lean_object* v_res_466_; 
v_timeoutMs_boxed_465_ = lean_unbox_uint32(v_timeoutMs_462_);
lean_dec(v_timeoutMs_462_);
v_res_466_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout(v_00_u03b5_459_, v_00_u03b1_460_, v_xs_461_, v_timeoutMs_boxed_465_, v_cancelTks_463_);
return v_res_466_;
}
}
LEAN_EXPORT uint8_t l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(lean_object* v_x_467_){
_start:
{
if (lean_obj_tag(v_x_467_) == 0)
{
uint8_t v___x_469_; 
v___x_469_ = 0;
return v___x_469_;
}
else
{
lean_object* v_head_470_; lean_object* v_tail_471_; uint8_t v___x_472_; 
v_head_470_ = lean_ctor_get(v_x_467_, 0);
v_tail_471_ = lean_ctor_get(v_x_467_, 1);
v___x_472_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_head_470_);
if (v___x_472_ == 0)
{
v_x_467_ = v_tail_471_;
goto _start;
}
else
{
return v___x_472_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0___boxed(lean_object* v_x_474_, lean_object* v___y_475_){
_start:
{
uint8_t v_res_476_; lean_object* v_r_477_; 
v_res_476_ = l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(v_x_474_);
lean_dec(v_x_474_);
v_r_477_ = lean_box(v_res_476_);
return v_r_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(lean_object* v_cancelTks_478_, uint32_t v_sleepDurationMs_479_){
_start:
{
uint32_t v___x_481_; uint8_t v___x_482_; 
v___x_481_ = 0;
v___x_482_ = lean_uint32_dec_eq(v_sleepDurationMs_479_, v___x_481_);
if (v___x_482_ == 0)
{
uint8_t v___x_483_; 
v___x_483_ = l_List_isEmpty___redArg(v_cancelTks_478_);
if (v___x_483_ == 0)
{
uint8_t v___x_484_; 
v___x_484_ = l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(v_cancelTks_478_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_485_ = lean_box_uint32(v_sleepDurationMs_479_);
v___x_486_ = lean_alloc_closure((void*)(l_IO_sleep___boxed), 2, 1);
lean_closure_set(v___x_486_, 0, v___x_485_);
v___x_487_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v___x_486_);
v___x_488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v_cancelTks_478_);
v___x_489_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_488_);
return v___x_489_;
}
else
{
lean_object* v___x_490_; 
lean_dec(v_cancelTks_478_);
v___x_490_ = lean_box(0);
return v___x_490_;
}
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v_cancelTks_478_);
v___x_491_ = l_IO_sleep(v_sleepDurationMs_479_);
v___x_492_ = lean_box(0);
return v___x_492_;
}
}
else
{
lean_object* v___x_493_; 
lean_dec(v_cancelTks_478_);
v___x_493_ = lean_box(0);
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___boxed(lean_object* v_cancelTks_494_, lean_object* v_sleepDurationMs_495_, lean_object* v_a_496_){
_start:
{
uint32_t v_sleepDurationMs_boxed_497_; lean_object* v_res_498_; 
v_sleepDurationMs_boxed_497_ = lean_unbox_uint32(v_sleepDurationMs_495_);
lean_dec(v_sleepDurationMs_495_);
v_res_498_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(v_cancelTks_494_, v_sleepDurationMs_boxed_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(lean_object* v_xs_499_, uint32_t v_latencyMs_500_, lean_object* v_cancelTks_501_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint32_t v___x_509_; lean_object* v___x_510_; 
v___x_503_ = lean_io_mono_ms_now();
lean_inc(v_cancelTks_501_);
v___x_504_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_499_, v_latencyMs_500_, v_cancelTks_501_);
v___x_505_ = lean_io_mono_ms_now();
v___x_506_ = lean_nat_sub(v___x_505_, v___x_503_);
lean_dec(v___x_503_);
lean_dec(v___x_505_);
v___x_507_ = lean_uint32_to_nat(v_latencyMs_500_);
v___x_508_ = lean_nat_sub(v___x_507_, v___x_506_);
lean_dec(v___x_506_);
lean_dec(v___x_507_);
v___x_509_ = lean_uint32_of_nat(v___x_508_);
lean_dec(v___x_508_);
v___x_510_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(v_cancelTks_501_, v___x_509_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg___boxed(lean_object* v_xs_511_, lean_object* v_latencyMs_512_, lean_object* v_cancelTks_513_, lean_object* v_a_514_){
_start:
{
uint32_t v_latencyMs_boxed_515_; lean_object* v_res_516_; 
v_latencyMs_boxed_515_ = lean_unbox_uint32(v_latencyMs_512_);
lean_dec(v_latencyMs_512_);
v_res_516_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(v_xs_511_, v_latencyMs_boxed_515_, v_cancelTks_513_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency(lean_object* v_00_u03b5_517_, lean_object* v_00_u03b1_518_, lean_object* v_xs_519_, uint32_t v_latencyMs_520_, lean_object* v_cancelTks_521_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(v_xs_519_, v_latencyMs_520_, v_cancelTks_521_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___boxed(lean_object* v_00_u03b5_524_, lean_object* v_00_u03b1_525_, lean_object* v_xs_526_, lean_object* v_latencyMs_527_, lean_object* v_cancelTks_528_, lean_object* v_a_529_){
_start:
{
uint32_t v_latencyMs_boxed_530_; lean_object* v_res_531_; 
v_latencyMs_boxed_530_ = lean_unbox_uint32(v_latencyMs_527_);
lean_dec(v_latencyMs_527_);
v_res_531_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency(v_00_u03b5_524_, v_00_u03b1_525_, v_xs_526_, v_latencyMs_boxed_530_, v_cancelTks_528_);
return v_res_531_;
}
}
lean_object* runtime_initialize_Lean_Server_ServerTask(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
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
res = runtime_initialize_Init_Data_List_Impl(builtin);
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
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_AsyncList(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_ServerTask(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin);
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
