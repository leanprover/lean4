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
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorIdx___redArg___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_AsyncList_ctorIdx___redArg(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorIdx(lean_object* v_00_u03b5_7_, lean_object* v_00_u03b1_8_, lean_object* v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_AsyncList_ctorIdx___redArg(v_x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorIdx___boxed(lean_object* v_00_u03b5_11_, lean_object* v_00_u03b1_12_, lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_AsyncList_ctorIdx(v_00_u03b5_11_, v_00_u03b1_12_, v_x_13_);
lean_dec(v_x_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorElim___redArg(lean_object* v_t_15_, lean_object* v_k_16_){
_start:
{
switch(lean_obj_tag(v_t_15_))
{
case 0:
{
lean_object* v_hd_17_; lean_object* v_tl_18_; lean_object* v___x_19_; 
v_hd_17_ = lean_ctor_get(v_t_15_, 0);
lean_inc(v_hd_17_);
v_tl_18_ = lean_ctor_get(v_t_15_, 1);
lean_inc(v_tl_18_);
lean_dec_ref_known(v_t_15_, 2);
v___x_19_ = lean_apply_2(v_k_16_, v_hd_17_, v_tl_18_);
return v___x_19_;
}
case 1:
{
lean_object* v_tl_20_; lean_object* v___x_21_; 
v_tl_20_ = lean_ctor_get(v_t_15_, 0);
lean_inc_ref(v_tl_20_);
lean_dec_ref_known(v_t_15_, 1);
v___x_21_ = lean_apply_1(v_k_16_, v_tl_20_);
return v___x_21_;
}
default: 
{
return v_k_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorElim(lean_object* v_00_u03b5_22_, lean_object* v_00_u03b1_23_, lean_object* v_motive__1_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_AsyncList_ctorElim___redArg(v_t_26_, v_k_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ctorElim___boxed(lean_object* v_00_u03b5_30_, lean_object* v_00_u03b1_31_, lean_object* v_motive__1_32_, lean_object* v_ctorIdx_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_k_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_AsyncList_ctorElim(v_00_u03b5_30_, v_00_u03b1_31_, v_motive__1_32_, v_ctorIdx_33_, v_t_34_, v_h_35_, v_k_36_);
lean_dec(v_ctorIdx_33_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_cons_elim___redArg(lean_object* v_t_38_, lean_object* v_cons_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_AsyncList_ctorElim___redArg(v_t_38_, v_cons_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_cons_elim(lean_object* v_00_u03b5_41_, lean_object* v_00_u03b1_42_, lean_object* v_motive__1_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_cons_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_AsyncList_ctorElim___redArg(v_t_44_, v_cons_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_delayed_elim___redArg(lean_object* v_t_48_, lean_object* v_delayed_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_AsyncList_ctorElim___redArg(v_t_48_, v_delayed_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_delayed_elim(lean_object* v_00_u03b5_51_, lean_object* v_00_u03b1_52_, lean_object* v_motive__1_53_, lean_object* v_t_54_, lean_object* v_h_55_, lean_object* v_delayed_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_AsyncList_ctorElim___redArg(v_t_54_, v_delayed_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_nil_elim___redArg(lean_object* v_t_58_, lean_object* v_nil_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_AsyncList_ctorElim___redArg(v_t_58_, v_nil_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_nil_elim(lean_object* v_00_u03b5_61_, lean_object* v_00_u03b1_62_, lean_object* v_motive__1_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_nil_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_AsyncList_ctorElim___redArg(v_t_64_, v_nil_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_instInhabited___redArg(){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_box(2);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_instInhabited___redArg___boxed(lean_object* v___dummy_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_AsyncList_instInhabited___redArg();
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_instInhabited(lean_object* v_00_u03b5_72_, lean_object* v_00_u03b1_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(2);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(lean_object* v_init_75_, lean_object* v_x_76_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
lean_inc(v_init_75_);
return v_init_75_;
}
else
{
lean_object* v_head_77_; lean_object* v_tail_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_86_; 
v_head_77_ = lean_ctor_get(v_x_76_, 0);
v_tail_78_ = lean_ctor_get(v_x_76_, 1);
v_isSharedCheck_86_ = !lean_is_exclusive(v_x_76_);
if (v_isSharedCheck_86_ == 0)
{
v___x_80_ = v_x_76_;
v_isShared_81_ = v_isSharedCheck_86_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_tail_78_);
lean_inc(v_head_77_);
lean_dec(v_x_76_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_86_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; lean_object* v___x_84_; 
v___x_82_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(v_init_75_, v_tail_78_);
if (v_isShared_81_ == 0)
{
lean_ctor_set_tag(v___x_80_, 0);
lean_ctor_set(v___x_80_, 1, v___x_82_);
v___x_84_ = v___x_80_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_head_77_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v___x_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg___boxed(lean_object* v_init_87_, lean_object* v_x_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(v_init_87_, v_x_88_);
lean_dec(v_init_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ofList___redArg(lean_object* v_l_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_box(2);
v___x_92_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(v___x_91_, v_l_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ofList(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b5_94_, lean_object* v_l_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_AsyncList_ofList___redArg(v_l_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0(lean_object* v_00_u03b1_97_, lean_object* v_00_u03b5_98_, lean_object* v_init_99_, lean_object* v_x_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(v_init_99_, v_x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___boxed(lean_object* v_00_u03b1_102_, lean_object* v_00_u03b5_103_, lean_object* v_init_104_, lean_object* v_x_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0(v_00_u03b1_102_, v_00_u03b5_103_, v_init_104_, v_x_105_);
lean_dec(v_init_104_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_instCoeList___redArg(){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = ((lean_object*)(l_Lean_AsyncList_instCoeList___redArg___closed__0));
return v___x_109_;
}
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
LEAN_EXPORT uint8_t l_Lean_AsyncList_waitAll___redArg___lam__0(lean_object* v_x_176_){
_start:
{
uint8_t v___x_177_; 
v___x_177_ = 0;
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitAll___redArg___lam__0___boxed(lean_object* v_x_178_){
_start:
{
uint8_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = l_Lean_AsyncList_waitAll___redArg___lam__0(v_x_178_);
lean_dec(v_x_178_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitAll___redArg(lean_object* v_a_182_){
_start:
{
lean_object* v___f_183_; lean_object* v___x_184_; 
v___f_183_ = ((lean_object*)(l_Lean_AsyncList_waitAll___redArg___closed__0));
v___x_184_ = l_Lean_AsyncList_waitUntil___redArg(v___f_183_, v_a_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitAll(lean_object* v_00_u03b5_185_, lean_object* v_00_u03b1_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_AsyncList_waitAll___redArg(v_a_187_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_AsyncList_waitFind_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = ((lean_object*)(l_Lean_AsyncList_waitFind_x3f___redArg___closed__0));
v___x_192_ = lean_task_pure(v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitFind_x3f___redArg(lean_object* v_p_193_, lean_object* v_x_194_){
_start:
{
switch(lean_obj_tag(v_x_194_))
{
case 0:
{
lean_object* v_hd_195_; lean_object* v_tl_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v_hd_195_ = lean_ctor_get(v_x_194_, 0);
lean_inc_n(v_hd_195_, 2);
v_tl_196_ = lean_ctor_get(v_x_194_, 1);
lean_inc(v_tl_196_);
lean_dec_ref_known(v_x_194_, 2);
lean_inc_ref(v_p_193_);
v___x_197_ = lean_apply_1(v_p_193_, v_hd_195_);
v___x_198_ = lean_unbox(v___x_197_);
if (v___x_198_ == 0)
{
lean_dec(v_hd_195_);
v_x_194_ = v_tl_196_;
goto _start;
}
else
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec(v_tl_196_);
lean_dec_ref(v_p_193_);
v___x_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_200_, 0, v_hd_195_);
v___x_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
v___x_202_ = lean_task_pure(v___x_201_);
return v___x_202_;
}
}
case 1:
{
lean_object* v_tl_203_; lean_object* v___f_204_; lean_object* v___x_205_; 
v_tl_203_ = lean_ctor_get(v_x_194_, 0);
lean_inc_ref(v_tl_203_);
lean_dec_ref_known(v_x_194_, 1);
v___f_204_ = lean_alloc_closure((void*)(l_Lean_AsyncList_waitFind_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_204_, 0, v_p_193_);
v___x_205_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_tl_203_, v___f_204_);
return v___x_205_;
}
default: 
{
lean_object* v___x_206_; 
lean_dec_ref(v_p_193_);
v___x_206_ = lean_obj_once(&l_Lean_AsyncList_waitFind_x3f___redArg___closed__1, &l_Lean_AsyncList_waitFind_x3f___redArg___closed__1_once, _init_l_Lean_AsyncList_waitFind_x3f___redArg___closed__1);
return v___x_206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitFind_x3f___redArg___lam__0(lean_object* v_p_207_, lean_object* v_x_208_){
_start:
{
if (lean_obj_tag(v_x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_217_; 
lean_dec_ref(v_p_207_);
v_a_209_ = lean_ctor_get(v_x_208_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v_x_208_);
if (v_isSharedCheck_217_ == 0)
{
v___x_211_ = v_x_208_;
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v_x_208_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_216_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_215_; 
v___x_215_ = lean_task_pure(v___x_214_);
return v___x_215_;
}
}
}
else
{
lean_object* v_a_218_; lean_object* v___x_219_; 
v_a_218_ = lean_ctor_get(v_x_208_, 0);
lean_inc(v_a_218_);
lean_dec_ref_known(v_x_208_, 1);
v___x_219_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_207_, v_a_218_);
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitFind_x3f(lean_object* v_00_u03b1_220_, lean_object* v_00_u03b5_221_, lean_object* v_p_222_, lean_object* v_x_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_222_, v_x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix___redArg(lean_object* v_x_232_){
_start:
{
switch(lean_obj_tag(v_x_232_))
{
case 0:
{
lean_object* v_hd_234_; lean_object* v_tl_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_252_; 
v_hd_234_ = lean_ctor_get(v_x_232_, 0);
v_tl_235_ = lean_ctor_get(v_x_232_, 1);
v_isSharedCheck_252_ = !lean_is_exclusive(v_x_232_);
if (v_isSharedCheck_252_ == 0)
{
v___x_237_ = v_x_232_;
v_isShared_238_ = v_isSharedCheck_252_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_tl_235_);
lean_inc(v_hd_234_);
lean_dec(v_x_232_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_252_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v_fst_240_; lean_object* v_snd_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_251_; 
v___x_239_ = l_Lean_AsyncList_getFinishedPrefix___redArg(v_tl_235_);
v_fst_240_ = lean_ctor_get(v___x_239_, 0);
v_snd_241_ = lean_ctor_get(v___x_239_, 1);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_251_ == 0)
{
v___x_243_ = v___x_239_;
v_isShared_244_ = v_isSharedCheck_251_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_snd_241_);
lean_inc(v_fst_240_);
lean_dec(v___x_239_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_251_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set_tag(v___x_237_, 1);
lean_ctor_set(v___x_237_, 1, v_fst_240_);
v___x_246_ = v___x_237_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_hd_234_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_fst_240_);
v___x_246_ = v_reuseFailAlloc_250_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_248_; 
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_246_);
v___x_248_ = v___x_243_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_snd_241_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
case 1:
{
lean_object* v_tl_253_; uint8_t v___x_254_; 
v_tl_253_ = lean_ctor_get(v_x_232_, 0);
lean_inc_ref(v_tl_253_);
lean_dec_ref_known(v_x_232_, 1);
v___x_254_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_tl_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec_ref(v_tl_253_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_box(0);
v___x_257_ = lean_box(v___x_254_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_255_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
return v___x_259_;
}
else
{
lean_object* v___x_260_; 
v___x_260_ = lean_io_wait(v_tl_253_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_272_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_272_ == 0)
{
v___x_263_ = v___x_260_;
v_isShared_264_ = v_isSharedCheck_272_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_260_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_272_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_265_ = lean_box(0);
if (v_isShared_264_ == 0)
{
lean_ctor_set_tag(v___x_263_, 1);
v___x_267_ = v___x_263_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_261_);
v___x_267_ = v_reuseFailAlloc_271_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_box(v___x_254_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_265_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
return v___x_270_;
}
}
}
else
{
lean_object* v_a_273_; 
v_a_273_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_273_);
lean_dec_ref_known(v___x_260_, 1);
v_x_232_ = v_a_273_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_275_; 
v___x_275_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefix___redArg___closed__1));
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix___redArg___boxed(lean_object* v_x_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_AsyncList_getFinishedPrefix___redArg(v_x_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix(lean_object* v_00_u03b5_279_, lean_object* v_00_u03b1_280_, lean_object* v_x_281_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_AsyncList_getFinishedPrefix___redArg(v_x_281_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix___boxed(lean_object* v_00_u03b5_284_, lean_object* v_00_u03b1_285_, lean_object* v_x_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_AsyncList_getFinishedPrefix(v_00_u03b5_284_, v_00_u03b1_285_, v_x_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___lam__0(lean_object* v_val_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v_val_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___lam__0(lean_object* v_val_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v_val_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
if (lean_obj_tag(v_a_294_) == 0)
{
lean_object* v___x_296_; 
v___x_296_ = l_List_reverse___redArg(v_a_295_);
return v___x_296_;
}
else
{
lean_object* v_head_297_; lean_object* v_tail_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_308_; 
v_head_297_ = lean_ctor_get(v_a_294_, 0);
v_tail_298_ = lean_ctor_get(v_a_294_, 1);
v_isSharedCheck_308_ = !lean_is_exclusive(v_a_294_);
if (v_isSharedCheck_308_ == 0)
{
v___x_300_ = v_a_294_;
v_isShared_301_ = v_isSharedCheck_308_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_tail_298_);
lean_inc(v_head_297_);
lean_dec(v_a_294_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_308_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___f_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v___f_302_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0));
v___x_303_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_302_, v_head_297_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v_a_295_);
lean_ctor_set(v___x_300_, 0, v___x_303_);
v___x_305_ = v___x_300_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_a_295_);
v___x_305_ = v_reuseFailAlloc_307_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
v_a_294_ = v_tail_298_;
v_a_295_ = v___x_305_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(lean_object* v_cancelTks_310_, lean_object* v_timeoutTask_311_, lean_object* v_xs_312_){
_start:
{
switch(lean_obj_tag(v_xs_312_))
{
case 0:
{
lean_object* v_hd_314_; lean_object* v_tl_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_332_; 
v_hd_314_ = lean_ctor_get(v_xs_312_, 0);
v_tl_315_ = lean_ctor_get(v_xs_312_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_xs_312_);
if (v_isSharedCheck_332_ == 0)
{
v___x_317_ = v_xs_312_;
v_isShared_318_ = v_isSharedCheck_332_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_tl_315_);
lean_inc(v_hd_314_);
lean_dec(v_xs_312_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_332_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v_fst_320_; lean_object* v_snd_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_331_; 
v___x_319_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_310_, v_timeoutTask_311_, v_tl_315_);
v_fst_320_ = lean_ctor_get(v___x_319_, 0);
v_snd_321_ = lean_ctor_get(v___x_319_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_331_ == 0)
{
v___x_323_ = v___x_319_;
v_isShared_324_ = v_isSharedCheck_331_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_snd_321_);
lean_inc(v_fst_320_);
lean_dec(v___x_319_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_331_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_318_ == 0)
{
lean_ctor_set_tag(v___x_317_, 1);
lean_ctor_set(v___x_317_, 1, v_fst_320_);
v___x_326_ = v___x_317_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_hd_314_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_fst_320_);
v___x_326_ = v_reuseFailAlloc_330_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_328_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_326_);
v___x_328_ = v___x_323_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_snd_321_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
case 1:
{
lean_object* v_tl_333_; lean_object* v___f_334_; uint8_t v___x_335_; uint8_t v___x_336_; 
v_tl_333_ = lean_ctor_get(v_xs_312_, 0);
lean_inc_ref(v_tl_333_);
lean_dec_ref_known(v_xs_312_, 1);
v___f_334_ = ((lean_object*)(l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0));
v___x_335_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_tl_333_);
v___x_336_ = 1;
if (v___x_335_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_337_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_334_, v_tl_333_);
v___x_338_ = lean_box(0);
lean_inc(v_cancelTks_310_);
v___x_339_ = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(v_cancelTks_310_, v___x_338_);
v___x_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_337_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
lean_inc_ref(v_timeoutTask_311_);
v___x_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_341_, 0, v_timeoutTask_311_);
lean_ctor_set(v___x_341_, 1, v___x_338_);
v___x_342_ = l_List_appendTR___redArg(v___x_340_, v___x_341_);
v___x_343_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_342_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
lean_dec_ref_known(v___x_343_, 1);
lean_dec_ref(v_timeoutTask_311_);
lean_dec(v_cancelTks_310_);
v___x_344_ = lean_box(0);
v___x_345_ = lean_box(v___x_335_);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_338_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
return v___x_347_;
}
else
{
lean_object* v_val_348_; 
v_val_348_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_val_348_);
lean_dec_ref_known(v___x_343_, 1);
if (lean_obj_tag(v_val_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_359_; 
lean_dec_ref(v_timeoutTask_311_);
lean_dec(v_cancelTks_310_);
v_a_349_ = lean_ctor_get(v_val_348_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v_val_348_);
if (v_isSharedCheck_359_ == 0)
{
v___x_351_ = v_val_348_;
v_isShared_352_ = v_isSharedCheck_359_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v_val_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_359_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
lean_ctor_set_tag(v___x_351_, 1);
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_358_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = lean_box(v___x_336_);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_338_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
return v___x_357_;
}
}
}
else
{
lean_object* v_a_360_; 
v_a_360_ = lean_ctor_get(v_val_348_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v_val_348_, 1);
v_xs_312_ = v_a_360_;
goto _start;
}
}
}
else
{
lean_object* v___x_362_; 
v___x_362_ = lean_io_wait(v_tl_333_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_374_; 
lean_dec_ref(v_timeoutTask_311_);
lean_dec(v_cancelTks_310_);
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_374_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_374_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_374_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_367_ = lean_box(0);
if (v_isShared_366_ == 0)
{
lean_ctor_set_tag(v___x_365_, 1);
v___x_369_ = v___x_365_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_363_);
v___x_369_ = v_reuseFailAlloc_373_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_370_ = lean_box(v___x_336_);
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_369_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_367_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
return v___x_372_;
}
}
}
else
{
lean_object* v_a_375_; 
v_a_375_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v___x_362_, 1);
v_xs_312_ = v_a_375_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_377_; 
lean_dec_ref(v_timeoutTask_311_);
lean_dec(v_cancelTks_310_);
v___x_377_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefix___redArg___closed__1));
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___boxed(lean_object* v_cancelTks_378_, lean_object* v_timeoutTask_379_, lean_object* v_xs_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_378_, v_timeoutTask_379_, v_xs_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go(lean_object* v_00_u03b5_383_, lean_object* v_00_u03b1_384_, lean_object* v_cancelTks_385_, lean_object* v_timeoutTask_386_, lean_object* v_xs_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_385_, v_timeoutTask_386_, v_xs_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___boxed(lean_object* v_00_u03b5_390_, lean_object* v_00_u03b1_391_, lean_object* v_cancelTks_392_, lean_object* v_timeoutTask_393_, lean_object* v_xs_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go(v_00_u03b5_390_, v_00_u03b1_391_, v_cancelTks_392_, v_timeoutTask_393_, v_xs_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0(lean_object* v_00_u03b5_397_, lean_object* v_00_u03b1_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(v_a_399_, v_a_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(uint32_t v_timeoutMs_404_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = l_IO_sleep(v_timeoutMs_404_);
v___x_407_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0));
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed(lean_object* v_timeoutMs_408_, lean_object* v___y_409_){
_start:
{
uint32_t v_timeoutMs_boxed_410_; lean_object* v_res_411_; 
v_timeoutMs_boxed_410_ = lean_unbox_uint32(v_timeoutMs_408_);
lean_dec(v_timeoutMs_408_);
v_res_411_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(v_timeoutMs_boxed_410_);
return v_res_411_;
}
}
static lean_object* _init_l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0));
v___x_413_ = lean_task_pure(v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(lean_object* v_xs_414_, uint32_t v_timeoutMs_415_, lean_object* v_cancelTks_416_){
_start:
{
uint32_t v___x_418_; uint8_t v___x_419_; 
v___x_418_ = 0;
v___x_419_ = lean_uint32_dec_eq(v_timeoutMs_415_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___f_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_420_ = lean_box_uint32(v_timeoutMs_415_);
v___f_421_ = lean_alloc_closure((void*)(l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_421_, 0, v___x_420_);
v___x_422_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v___f_421_);
v___x_423_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_416_, v___x_422_, v_xs_414_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_obj_once(&l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0, &l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0_once, _init_l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0);
v___x_425_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_416_, v___x_424_, v_xs_414_);
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___boxed(lean_object* v_xs_426_, lean_object* v_timeoutMs_427_, lean_object* v_cancelTks_428_, lean_object* v_a_429_){
_start:
{
uint32_t v_timeoutMs_boxed_430_; lean_object* v_res_431_; 
v_timeoutMs_boxed_430_ = lean_unbox_uint32(v_timeoutMs_427_);
lean_dec(v_timeoutMs_427_);
v_res_431_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_426_, v_timeoutMs_boxed_430_, v_cancelTks_428_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout(lean_object* v_00_u03b5_432_, lean_object* v_00_u03b1_433_, lean_object* v_xs_434_, uint32_t v_timeoutMs_435_, lean_object* v_cancelTks_436_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_434_, v_timeoutMs_435_, v_cancelTks_436_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___boxed(lean_object* v_00_u03b5_439_, lean_object* v_00_u03b1_440_, lean_object* v_xs_441_, lean_object* v_timeoutMs_442_, lean_object* v_cancelTks_443_, lean_object* v_a_444_){
_start:
{
uint32_t v_timeoutMs_boxed_445_; lean_object* v_res_446_; 
v_timeoutMs_boxed_445_ = lean_unbox_uint32(v_timeoutMs_442_);
lean_dec(v_timeoutMs_442_);
v_res_446_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout(v_00_u03b5_439_, v_00_u03b1_440_, v_xs_441_, v_timeoutMs_boxed_445_, v_cancelTks_443_);
return v_res_446_;
}
}
LEAN_EXPORT uint8_t l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_447_) == 0)
{
uint8_t v___x_449_; 
v___x_449_ = 0;
return v___x_449_;
}
else
{
lean_object* v_head_450_; lean_object* v_tail_451_; uint8_t v___x_452_; 
v_head_450_ = lean_ctor_get(v_x_447_, 0);
v_tail_451_ = lean_ctor_get(v_x_447_, 1);
v___x_452_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_head_450_);
if (v___x_452_ == 0)
{
v_x_447_ = v_tail_451_;
goto _start;
}
else
{
return v___x_452_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0___boxed(lean_object* v_x_454_, lean_object* v___y_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(v_x_454_);
lean_dec(v_x_454_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(lean_object* v_cancelTks_458_, uint32_t v_sleepDurationMs_459_){
_start:
{
uint32_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = 0;
v___x_462_ = lean_uint32_dec_eq(v_sleepDurationMs_459_, v___x_461_);
if (v___x_462_ == 0)
{
uint8_t v___x_463_; 
v___x_463_ = l_List_isEmpty___redArg(v_cancelTks_458_);
if (v___x_463_ == 0)
{
uint8_t v___x_464_; 
v___x_464_ = l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(v_cancelTks_458_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_465_ = lean_box_uint32(v_sleepDurationMs_459_);
v___x_466_ = lean_alloc_closure((void*)(l_IO_sleep___boxed), 2, 1);
lean_closure_set(v___x_466_, 0, v___x_465_);
v___x_467_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v___x_466_);
v___x_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v_cancelTks_458_);
v___x_469_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_468_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; 
lean_dec(v_cancelTks_458_);
v___x_470_ = lean_box(0);
return v___x_470_;
}
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec(v_cancelTks_458_);
v___x_471_ = l_IO_sleep(v_sleepDurationMs_459_);
v___x_472_ = lean_box(0);
return v___x_472_;
}
}
else
{
lean_object* v___x_473_; 
lean_dec(v_cancelTks_458_);
v___x_473_ = lean_box(0);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___boxed(lean_object* v_cancelTks_474_, lean_object* v_sleepDurationMs_475_, lean_object* v_a_476_){
_start:
{
uint32_t v_sleepDurationMs_boxed_477_; lean_object* v_res_478_; 
v_sleepDurationMs_boxed_477_ = lean_unbox_uint32(v_sleepDurationMs_475_);
lean_dec(v_sleepDurationMs_475_);
v_res_478_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(v_cancelTks_474_, v_sleepDurationMs_boxed_477_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(lean_object* v_xs_479_, uint32_t v_latencyMs_480_, lean_object* v_cancelTks_481_){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint32_t v___x_489_; lean_object* v___x_490_; 
v___x_483_ = lean_io_mono_ms_now();
lean_inc(v_cancelTks_481_);
v___x_484_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_479_, v_latencyMs_480_, v_cancelTks_481_);
v___x_485_ = lean_io_mono_ms_now();
v___x_486_ = lean_nat_sub(v___x_485_, v___x_483_);
lean_dec(v___x_483_);
lean_dec(v___x_485_);
v___x_487_ = lean_uint32_to_nat(v_latencyMs_480_);
v___x_488_ = lean_nat_sub(v___x_487_, v___x_486_);
lean_dec(v___x_486_);
lean_dec(v___x_487_);
v___x_489_ = lean_uint32_of_nat(v___x_488_);
lean_dec(v___x_488_);
v___x_490_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(v_cancelTks_481_, v___x_489_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg___boxed(lean_object* v_xs_491_, lean_object* v_latencyMs_492_, lean_object* v_cancelTks_493_, lean_object* v_a_494_){
_start:
{
uint32_t v_latencyMs_boxed_495_; lean_object* v_res_496_; 
v_latencyMs_boxed_495_ = lean_unbox_uint32(v_latencyMs_492_);
lean_dec(v_latencyMs_492_);
v_res_496_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(v_xs_491_, v_latencyMs_boxed_495_, v_cancelTks_493_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency(lean_object* v_00_u03b5_497_, lean_object* v_00_u03b1_498_, lean_object* v_xs_499_, uint32_t v_latencyMs_500_, lean_object* v_cancelTks_501_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(v_xs_499_, v_latencyMs_500_, v_cancelTks_501_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___boxed(lean_object* v_00_u03b5_504_, lean_object* v_00_u03b1_505_, lean_object* v_xs_506_, lean_object* v_latencyMs_507_, lean_object* v_cancelTks_508_, lean_object* v_a_509_){
_start:
{
uint32_t v_latencyMs_boxed_510_; lean_object* v_res_511_; 
v_latencyMs_boxed_510_ = lean_unbox_uint32(v_latencyMs_507_);
lean_dec(v_latencyMs_507_);
v_res_511_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency(v_00_u03b5_504_, v_00_u03b1_505_, v_xs_506_, v_latencyMs_boxed_510_, v_cancelTks_508_);
return v_res_511_;
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
