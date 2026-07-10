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
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_AsyncList_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_ofList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncList_ofList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_AsyncList_instCoeList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_AsyncList_ofList, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_AsyncList_instCoeList___closed__0 = (const lean_object*)&l_Lean_AsyncList_instCoeList___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lean_AsyncList_instInhabited(lean_object* v_00_u03b5_68_, lean_object* v_00_u03b1_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_box(2);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(lean_object* v_init_71_, lean_object* v_x_72_){
_start:
{
if (lean_obj_tag(v_x_72_) == 0)
{
lean_inc(v_init_71_);
return v_init_71_;
}
else
{
lean_object* v_head_73_; lean_object* v_tail_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_82_; 
v_head_73_ = lean_ctor_get(v_x_72_, 0);
v_tail_74_ = lean_ctor_get(v_x_72_, 1);
v_isSharedCheck_82_ = !lean_is_exclusive(v_x_72_);
if (v_isSharedCheck_82_ == 0)
{
v___x_76_ = v_x_72_;
v_isShared_77_ = v_isSharedCheck_82_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_tail_74_);
lean_inc(v_head_73_);
lean_dec(v_x_72_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_82_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_78_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(v_init_71_, v_tail_74_);
if (v_isShared_77_ == 0)
{
lean_ctor_set_tag(v___x_76_, 0);
lean_ctor_set(v___x_76_, 1, v___x_78_);
v___x_80_ = v___x_76_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_head_73_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg___boxed(lean_object* v_init_83_, lean_object* v_x_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(v_init_83_, v_x_84_);
lean_dec(v_init_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ofList___redArg(lean_object* v_l_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_box(2);
v___x_88_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(v___x_87_, v_l_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_ofList(lean_object* v_00_u03b1_89_, lean_object* v_00_u03b5_90_, lean_object* v_l_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_AsyncList_ofList___redArg(v_l_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b5_94_, lean_object* v_init_95_, lean_object* v_x_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___redArg(v_init_95_, v_x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_AsyncList_ofList_spec__0___boxed(lean_object* v_00_u03b1_98_, lean_object* v_00_u03b5_99_, lean_object* v_init_100_, lean_object* v_x_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_List_foldr___at___00Lean_AsyncList_ofList_spec__0(v_00_u03b1_98_, v_00_u03b5_99_, v_init_100_, v_x_101_);
lean_dec(v_init_100_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_instCoeList(lean_object* v_00_u03b1_104_, lean_object* v_00_u03b5_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = ((lean_object*)(l_Lean_AsyncList_instCoeList___closed__0));
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil___redArg___lam__0(lean_object* v_hd_107_, lean_object* v_x_108_){
_start:
{
lean_object* v_fst_109_; lean_object* v_snd_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_118_; 
v_fst_109_ = lean_ctor_get(v_x_108_, 0);
v_snd_110_ = lean_ctor_get(v_x_108_, 1);
v_isSharedCheck_118_ = !lean_is_exclusive(v_x_108_);
if (v_isSharedCheck_118_ == 0)
{
v___x_112_ = v_x_108_;
v_isShared_113_ = v_isSharedCheck_118_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_snd_110_);
lean_inc(v_fst_109_);
lean_dec(v_x_108_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_118_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_114_, 0, v_hd_107_);
lean_ctor_set(v___x_114_, 1, v_fst_109_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_114_);
v___x_116_ = v___x_112_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_snd_110_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
static lean_object* _init_l_Lean_AsyncList_waitUntil___redArg___closed__1(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = ((lean_object*)(l_Lean_AsyncList_waitUntil___redArg___closed__0));
v___x_123_ = lean_task_pure(v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil___redArg(lean_object* v_p_124_, lean_object* v_x_125_){
_start:
{
switch(lean_obj_tag(v_x_125_))
{
case 0:
{
lean_object* v_hd_126_; lean_object* v_tl_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_144_; 
v_hd_126_ = lean_ctor_get(v_x_125_, 0);
v_tl_127_ = lean_ctor_get(v_x_125_, 1);
v_isSharedCheck_144_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_144_ == 0)
{
v___x_129_ = v_x_125_;
v_isShared_130_ = v_isSharedCheck_144_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_tl_127_);
lean_inc(v_hd_126_);
lean_dec(v_x_125_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_144_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; uint8_t v___x_132_; uint8_t v___x_133_; 
lean_inc_ref(v_p_124_);
lean_inc(v_hd_126_);
v___x_131_ = lean_apply_1(v_p_124_, v_hd_126_);
v___x_132_ = lean_unbox(v___x_131_);
v___x_133_ = lean_bool_not(v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_136_; 
lean_dec(v_tl_127_);
lean_dec_ref(v_p_124_);
v___x_134_ = lean_box(0);
if (v_isShared_130_ == 0)
{
lean_ctor_set_tag(v___x_129_, 1);
lean_ctor_set(v___x_129_, 1, v___x_134_);
v___x_136_ = v___x_129_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_hd_126_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v___x_134_);
v___x_136_ = v_reuseFailAlloc_140_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_box(0);
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_136_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = lean_task_pure(v___x_138_);
return v___x_139_;
}
}
else
{
lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
lean_del_object(v___x_129_);
v___f_141_ = lean_alloc_closure((void*)(l_Lean_AsyncList_waitUntil___redArg___lam__0), 2, 1);
lean_closure_set(v___f_141_, 0, v_hd_126_);
v___x_142_ = l_Lean_AsyncList_waitUntil___redArg(v_p_124_, v_tl_127_);
v___x_143_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_141_, v___x_142_);
return v___x_143_;
}
}
}
case 1:
{
lean_object* v_tl_145_; lean_object* v___f_146_; lean_object* v___x_147_; 
v_tl_145_ = lean_ctor_get(v_x_125_, 0);
lean_inc_ref(v_tl_145_);
lean_dec_ref_known(v_x_125_, 1);
v___f_146_ = lean_alloc_closure((void*)(l_Lean_AsyncList_waitUntil___redArg___lam__1), 2, 1);
lean_closure_set(v___f_146_, 0, v_p_124_);
v___x_147_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_tl_145_, v___f_146_);
return v___x_147_;
}
default: 
{
lean_object* v___x_148_; 
lean_dec_ref(v_p_124_);
v___x_148_ = lean_obj_once(&l_Lean_AsyncList_waitUntil___redArg___closed__1, &l_Lean_AsyncList_waitUntil___redArg___closed__1_once, _init_l_Lean_AsyncList_waitUntil___redArg___closed__1);
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil___redArg___lam__1(lean_object* v_p_149_, lean_object* v_x_150_){
_start:
{
if (lean_obj_tag(v_x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_161_; 
lean_dec_ref(v_p_149_);
v_a_151_ = lean_ctor_get(v_x_150_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v_x_150_);
if (v_isSharedCheck_161_ == 0)
{
v___x_153_ = v_x_150_;
v_isShared_154_ = v_isSharedCheck_161_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v_x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_161_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_155_ = lean_box(0);
if (v_isShared_154_ == 0)
{
lean_ctor_set_tag(v___x_153_, 1);
v___x_157_ = v___x_153_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_151_);
v___x_157_ = v_reuseFailAlloc_160_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_155_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = lean_task_pure(v___x_158_);
return v___x_159_;
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_163_; 
v_a_162_ = lean_ctor_get(v_x_150_, 0);
lean_inc(v_a_162_);
lean_dec_ref_known(v_x_150_, 1);
v___x_163_ = l_Lean_AsyncList_waitUntil___redArg(v_p_149_, v_a_162_);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitUntil(lean_object* v_00_u03b1_164_, lean_object* v_00_u03b5_165_, lean_object* v_p_166_, lean_object* v_x_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_AsyncList_waitUntil___redArg(v_p_166_, v_x_167_);
return v___x_168_;
}
}
LEAN_EXPORT uint8_t l_Lean_AsyncList_waitAll___redArg___lam__0(lean_object* v_x_169_){
_start:
{
uint8_t v___x_170_; 
v___x_170_ = 0;
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitAll___redArg___lam__0___boxed(lean_object* v_x_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Lean_AsyncList_waitAll___redArg___lam__0(v_x_171_);
lean_dec(v_x_171_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitAll___redArg(lean_object* v_a_175_){
_start:
{
lean_object* v___f_176_; lean_object* v___x_177_; 
v___f_176_ = ((lean_object*)(l_Lean_AsyncList_waitAll___redArg___closed__0));
v___x_177_ = l_Lean_AsyncList_waitUntil___redArg(v___f_176_, v_a_175_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitAll(lean_object* v_00_u03b5_178_, lean_object* v_00_u03b1_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_AsyncList_waitAll___redArg(v_a_180_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_AsyncList_waitFind_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = ((lean_object*)(l_Lean_AsyncList_waitFind_x3f___redArg___closed__0));
v___x_185_ = lean_task_pure(v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitFind_x3f___redArg(lean_object* v_p_186_, lean_object* v_x_187_){
_start:
{
switch(lean_obj_tag(v_x_187_))
{
case 0:
{
lean_object* v_hd_188_; lean_object* v_tl_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v_hd_188_ = lean_ctor_get(v_x_187_, 0);
lean_inc_n(v_hd_188_, 2);
v_tl_189_ = lean_ctor_get(v_x_187_, 1);
lean_inc(v_tl_189_);
lean_dec_ref_known(v_x_187_, 2);
lean_inc_ref(v_p_186_);
v___x_190_ = lean_apply_1(v_p_186_, v_hd_188_);
v___x_191_ = lean_unbox(v___x_190_);
if (v___x_191_ == 0)
{
lean_dec(v_hd_188_);
v_x_187_ = v_tl_189_;
goto _start;
}
else
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec(v_tl_189_);
lean_dec_ref(v_p_186_);
v___x_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_193_, 0, v_hd_188_);
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
v___x_195_ = lean_task_pure(v___x_194_);
return v___x_195_;
}
}
case 1:
{
lean_object* v_tl_196_; lean_object* v___f_197_; lean_object* v___x_198_; 
v_tl_196_ = lean_ctor_get(v_x_187_, 0);
lean_inc_ref(v_tl_196_);
lean_dec_ref_known(v_x_187_, 1);
v___f_197_ = lean_alloc_closure((void*)(l_Lean_AsyncList_waitFind_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_197_, 0, v_p_186_);
v___x_198_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_tl_196_, v___f_197_);
return v___x_198_;
}
default: 
{
lean_object* v___x_199_; 
lean_dec_ref(v_p_186_);
v___x_199_ = lean_obj_once(&l_Lean_AsyncList_waitFind_x3f___redArg___closed__1, &l_Lean_AsyncList_waitFind_x3f___redArg___closed__1_once, _init_l_Lean_AsyncList_waitFind_x3f___redArg___closed__1);
return v___x_199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitFind_x3f___redArg___lam__0(lean_object* v_p_200_, lean_object* v_x_201_){
_start:
{
if (lean_obj_tag(v_x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_210_; 
lean_dec_ref(v_p_200_);
v_a_202_ = lean_ctor_get(v_x_201_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v_x_201_);
if (v_isSharedCheck_210_ == 0)
{
v___x_204_ = v_x_201_;
v_isShared_205_ = v_isSharedCheck_210_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v_x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_210_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_209_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_208_; 
v___x_208_ = lean_task_pure(v___x_207_);
return v___x_208_;
}
}
}
else
{
lean_object* v_a_211_; lean_object* v___x_212_; 
v_a_211_ = lean_ctor_get(v_x_201_, 0);
lean_inc(v_a_211_);
lean_dec_ref_known(v_x_201_, 1);
v___x_212_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_200_, v_a_211_);
return v___x_212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_waitFind_x3f(lean_object* v_00_u03b1_213_, lean_object* v_00_u03b5_214_, lean_object* v_p_215_, lean_object* v_x_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_AsyncList_waitFind_x3f___redArg(v_p_215_, v_x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix___redArg(lean_object* v_x_225_){
_start:
{
switch(lean_obj_tag(v_x_225_))
{
case 0:
{
lean_object* v_hd_227_; lean_object* v_tl_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_245_; 
v_hd_227_ = lean_ctor_get(v_x_225_, 0);
v_tl_228_ = lean_ctor_get(v_x_225_, 1);
v_isSharedCheck_245_ = !lean_is_exclusive(v_x_225_);
if (v_isSharedCheck_245_ == 0)
{
v___x_230_ = v_x_225_;
v_isShared_231_ = v_isSharedCheck_245_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_tl_228_);
lean_inc(v_hd_227_);
lean_dec(v_x_225_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_245_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v_fst_233_; lean_object* v_snd_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_244_; 
v___x_232_ = l_Lean_AsyncList_getFinishedPrefix___redArg(v_tl_228_);
v_fst_233_ = lean_ctor_get(v___x_232_, 0);
v_snd_234_ = lean_ctor_get(v___x_232_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_244_ == 0)
{
v___x_236_ = v___x_232_;
v_isShared_237_ = v_isSharedCheck_244_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_snd_234_);
lean_inc(v_fst_233_);
lean_dec(v___x_232_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_244_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_231_ == 0)
{
lean_ctor_set_tag(v___x_230_, 1);
lean_ctor_set(v___x_230_, 1, v_fst_233_);
v___x_239_ = v___x_230_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_hd_227_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_fst_233_);
v___x_239_ = v_reuseFailAlloc_243_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_241_; 
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_239_);
v___x_241_ = v___x_236_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_snd_234_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
case 1:
{
lean_object* v_tl_246_; uint8_t v___x_247_; 
v_tl_246_ = lean_ctor_get(v_x_225_, 0);
lean_inc_ref(v_tl_246_);
lean_dec_ref_known(v_x_225_, 1);
v___x_247_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_tl_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec_ref(v_tl_246_);
v___x_248_ = lean_box(0);
v___x_249_ = lean_box(0);
v___x_250_ = lean_box(v___x_247_);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_248_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
return v___x_252_;
}
else
{
lean_object* v___x_253_; 
v___x_253_ = lean_io_wait(v_tl_246_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_265_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_265_ == 0)
{
v___x_256_ = v___x_253_;
v_isShared_257_ = v_isSharedCheck_265_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_253_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_265_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_258_ = lean_box(0);
if (v_isShared_257_ == 0)
{
lean_ctor_set_tag(v___x_256_, 1);
v___x_260_ = v___x_256_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_254_);
v___x_260_ = v_reuseFailAlloc_264_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = lean_box(v___x_247_);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_258_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
return v___x_263_;
}
}
}
else
{
lean_object* v_a_266_; 
v_a_266_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_266_);
lean_dec_ref_known(v___x_253_, 1);
v_x_225_ = v_a_266_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_268_; 
v___x_268_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefix___redArg___closed__1));
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix___redArg___boxed(lean_object* v_x_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_AsyncList_getFinishedPrefix___redArg(v_x_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix(lean_object* v_00_u03b5_272_, lean_object* v_00_u03b1_273_, lean_object* v_x_274_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_AsyncList_getFinishedPrefix___redArg(v_x_274_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefix___boxed(lean_object* v_00_u03b5_277_, lean_object* v_00_u03b1_278_, lean_object* v_x_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_AsyncList_getFinishedPrefix(v_00_u03b5_277_, v_00_u03b1_278_, v_x_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___lam__0(lean_object* v_val_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_283_, 0, v_val_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___lam__0(lean_object* v_val_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v_val_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
if (lean_obj_tag(v_a_287_) == 0)
{
lean_object* v___x_289_; 
v___x_289_ = l_List_reverse___redArg(v_a_288_);
return v___x_289_;
}
else
{
lean_object* v_head_290_; lean_object* v_tail_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_301_; 
v_head_290_ = lean_ctor_get(v_a_287_, 0);
v_tail_291_ = lean_ctor_get(v_a_287_, 1);
v_isSharedCheck_301_ = !lean_is_exclusive(v_a_287_);
if (v_isSharedCheck_301_ == 0)
{
v___x_293_ = v_a_287_;
v_isShared_294_ = v_isSharedCheck_301_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_tail_291_);
lean_inc(v_head_290_);
lean_dec(v_a_287_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_301_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___f_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
v___f_295_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0));
v___x_296_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_295_, v_head_290_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v_a_288_);
lean_ctor_set(v___x_293_, 0, v___x_296_);
v___x_298_ = v___x_293_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_a_288_);
v___x_298_ = v_reuseFailAlloc_300_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
v_a_287_ = v_tail_291_;
v_a_288_ = v___x_298_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(lean_object* v_cancelTks_303_, lean_object* v_timeoutTask_304_, lean_object* v_xs_305_){
_start:
{
switch(lean_obj_tag(v_xs_305_))
{
case 0:
{
lean_object* v_hd_307_; lean_object* v_tl_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_325_; 
v_hd_307_ = lean_ctor_get(v_xs_305_, 0);
v_tl_308_ = lean_ctor_get(v_xs_305_, 1);
v_isSharedCheck_325_ = !lean_is_exclusive(v_xs_305_);
if (v_isSharedCheck_325_ == 0)
{
v___x_310_ = v_xs_305_;
v_isShared_311_ = v_isSharedCheck_325_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_tl_308_);
lean_inc(v_hd_307_);
lean_dec(v_xs_305_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_325_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v_fst_313_; lean_object* v_snd_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_324_; 
v___x_312_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_303_, v_timeoutTask_304_, v_tl_308_);
v_fst_313_ = lean_ctor_get(v___x_312_, 0);
v_snd_314_ = lean_ctor_get(v___x_312_, 1);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_324_ == 0)
{
v___x_316_ = v___x_312_;
v_isShared_317_ = v_isSharedCheck_324_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_snd_314_);
lean_inc(v_fst_313_);
lean_dec(v___x_312_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_324_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set_tag(v___x_310_, 1);
lean_ctor_set(v___x_310_, 1, v_fst_313_);
v___x_319_ = v___x_310_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_hd_307_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_fst_313_);
v___x_319_ = v_reuseFailAlloc_323_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_321_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_319_);
v___x_321_ = v___x_316_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_snd_314_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
case 1:
{
lean_object* v_tl_326_; uint8_t v___x_327_; uint8_t v___x_328_; 
v_tl_326_ = lean_ctor_get(v_xs_305_, 0);
lean_inc_ref(v_tl_326_);
lean_dec_ref_known(v_xs_305_, 1);
v___x_327_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_tl_326_);
v___x_328_ = 1;
if (v___x_327_ == 0)
{
lean_object* v___f_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___f_329_ = ((lean_object*)(l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0));
v___x_330_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_329_, v_tl_326_);
v___x_331_ = lean_box(0);
lean_inc(v_cancelTks_303_);
v___x_332_ = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(v_cancelTks_303_, v___x_331_);
v___x_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_330_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
lean_inc_ref(v_timeoutTask_304_);
v___x_334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_334_, 0, v_timeoutTask_304_);
lean_ctor_set(v___x_334_, 1, v___x_331_);
v___x_335_ = l_List_appendTR___redArg(v___x_333_, v___x_334_);
v___x_336_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_335_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec_ref_known(v___x_336_, 1);
lean_dec_ref(v_timeoutTask_304_);
lean_dec(v_cancelTks_303_);
v___x_337_ = lean_box(0);
v___x_338_ = lean_box(v___x_327_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_331_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
return v___x_340_;
}
else
{
lean_object* v_val_341_; 
v_val_341_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_val_341_);
lean_dec_ref_known(v___x_336_, 1);
if (lean_obj_tag(v_val_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_352_; 
lean_dec_ref(v_timeoutTask_304_);
lean_dec(v_cancelTks_303_);
v_a_342_ = lean_ctor_get(v_val_341_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v_val_341_);
if (v_isSharedCheck_352_ == 0)
{
v___x_344_ = v_val_341_;
v_isShared_345_ = v_isSharedCheck_352_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v_val_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_352_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
lean_ctor_set_tag(v___x_344_, 1);
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_351_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = lean_box(v___x_328_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_347_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_331_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
return v___x_350_;
}
}
}
else
{
lean_object* v_a_353_; 
v_a_353_ = lean_ctor_get(v_val_341_, 0);
lean_inc(v_a_353_);
lean_dec_ref_known(v_val_341_, 1);
v_xs_305_ = v_a_353_;
goto _start;
}
}
}
else
{
lean_object* v___x_355_; 
v___x_355_ = lean_io_wait(v_tl_326_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_367_; 
lean_dec_ref(v_timeoutTask_304_);
lean_dec(v_cancelTks_303_);
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_367_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_367_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_367_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = lean_box(0);
if (v_isShared_359_ == 0)
{
lean_ctor_set_tag(v___x_358_, 1);
v___x_362_ = v___x_358_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_356_);
v___x_362_ = v_reuseFailAlloc_366_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = lean_box(v___x_328_);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_362_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_360_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
return v___x_365_;
}
}
}
else
{
lean_object* v_a_368_; 
v_a_368_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v___x_355_, 1);
v_xs_305_ = v_a_368_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_370_; 
lean_dec_ref(v_timeoutTask_304_);
lean_dec(v_cancelTks_303_);
v___x_370_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefix___redArg___closed__1));
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg___boxed(lean_object* v_cancelTks_371_, lean_object* v_timeoutTask_372_, lean_object* v_xs_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_371_, v_timeoutTask_372_, v_xs_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go(lean_object* v_00_u03b5_376_, lean_object* v_00_u03b1_377_, lean_object* v_cancelTks_378_, lean_object* v_timeoutTask_379_, lean_object* v_xs_380_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_378_, v_timeoutTask_379_, v_xs_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___boxed(lean_object* v_00_u03b5_383_, lean_object* v_00_u03b1_384_, lean_object* v_cancelTks_385_, lean_object* v_timeoutTask_386_, lean_object* v_xs_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go(v_00_u03b5_383_, v_00_u03b1_384_, v_cancelTks_385_, v_timeoutTask_386_, v_xs_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0(lean_object* v_00_u03b5_390_, lean_object* v_00_u03b1_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(v_a_392_, v_a_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(uint32_t v_timeoutMs_397_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = l_IO_sleep(v_timeoutMs_397_);
v___x_400_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0));
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed(lean_object* v_timeoutMs_401_, lean_object* v___y_402_){
_start:
{
uint32_t v_timeoutMs_boxed_403_; lean_object* v_res_404_; 
v_timeoutMs_boxed_403_ = lean_unbox_uint32(v_timeoutMs_401_);
lean_dec(v_timeoutMs_401_);
v_res_404_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(v_timeoutMs_boxed_403_);
return v_res_404_;
}
}
static lean_object* _init_l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0));
v___x_406_ = lean_task_pure(v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(lean_object* v_xs_407_, uint32_t v_timeoutMs_408_, lean_object* v_cancelTks_409_){
_start:
{
uint32_t v___x_411_; uint8_t v___x_412_; 
v___x_411_ = 0;
v___x_412_ = lean_uint32_dec_eq(v_timeoutMs_408_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___f_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_413_ = lean_box_uint32(v_timeoutMs_408_);
v___f_414_ = lean_alloc_closure((void*)(l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_414_, 0, v___x_413_);
v___x_415_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v___f_414_);
v___x_416_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_409_, v___x_415_, v_xs_407_);
return v___x_416_;
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_obj_once(&l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0, &l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0_once, _init_l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0);
v___x_418_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_409_, v___x_417_, v_xs_407_);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg___boxed(lean_object* v_xs_419_, lean_object* v_timeoutMs_420_, lean_object* v_cancelTks_421_, lean_object* v_a_422_){
_start:
{
uint32_t v_timeoutMs_boxed_423_; lean_object* v_res_424_; 
v_timeoutMs_boxed_423_ = lean_unbox_uint32(v_timeoutMs_420_);
lean_dec(v_timeoutMs_420_);
v_res_424_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_419_, v_timeoutMs_boxed_423_, v_cancelTks_421_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout(lean_object* v_00_u03b5_425_, lean_object* v_00_u03b1_426_, lean_object* v_xs_427_, uint32_t v_timeoutMs_428_, lean_object* v_cancelTks_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_427_, v_timeoutMs_428_, v_cancelTks_429_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithTimeout___boxed(lean_object* v_00_u03b5_432_, lean_object* v_00_u03b1_433_, lean_object* v_xs_434_, lean_object* v_timeoutMs_435_, lean_object* v_cancelTks_436_, lean_object* v_a_437_){
_start:
{
uint32_t v_timeoutMs_boxed_438_; lean_object* v_res_439_; 
v_timeoutMs_boxed_438_ = lean_unbox_uint32(v_timeoutMs_435_);
lean_dec(v_timeoutMs_435_);
v_res_439_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout(v_00_u03b5_432_, v_00_u03b1_433_, v_xs_434_, v_timeoutMs_boxed_438_, v_cancelTks_436_);
return v_res_439_;
}
}
LEAN_EXPORT uint8_t l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(lean_object* v_x_440_){
_start:
{
if (lean_obj_tag(v_x_440_) == 0)
{
uint8_t v___x_442_; 
v___x_442_ = 0;
return v___x_442_;
}
else
{
lean_object* v_head_443_; lean_object* v_tail_444_; uint8_t v___x_445_; 
v_head_443_ = lean_ctor_get(v_x_440_, 0);
v_tail_444_ = lean_ctor_get(v_x_440_, 1);
v___x_445_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_head_443_);
if (v___x_445_ == 0)
{
v_x_440_ = v_tail_444_;
goto _start;
}
else
{
return v___x_445_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0___boxed(lean_object* v_x_447_, lean_object* v___y_448_){
_start:
{
uint8_t v_res_449_; lean_object* v_r_450_; 
v_res_449_ = l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(v_x_447_);
lean_dec(v_x_447_);
v_r_450_ = lean_box(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(lean_object* v_cancelTks_451_, uint32_t v_sleepDurationMs_452_){
_start:
{
uint32_t v___x_454_; uint8_t v___x_455_; 
v___x_454_ = 0;
v___x_455_ = lean_uint32_dec_eq(v_sleepDurationMs_452_, v___x_454_);
if (v___x_455_ == 0)
{
uint8_t v___x_456_; 
v___x_456_ = l_List_isEmpty___redArg(v_cancelTks_451_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; 
v___x_457_ = l_List_anyM___at___00__private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(v_cancelTks_451_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_458_ = lean_box_uint32(v_sleepDurationMs_452_);
v___x_459_ = lean_alloc_closure((void*)(l_IO_sleep___boxed), 2, 1);
lean_closure_set(v___x_459_, 0, v___x_458_);
v___x_460_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v___x_459_);
v___x_461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v_cancelTks_451_);
v___x_462_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_461_);
return v___x_462_;
}
else
{
lean_object* v___x_463_; 
lean_dec(v_cancelTks_451_);
v___x_463_ = lean_box(0);
return v___x_463_;
}
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec(v_cancelTks_451_);
v___x_464_ = l_IO_sleep(v_sleepDurationMs_452_);
v___x_465_ = lean_box(0);
return v___x_465_;
}
}
else
{
lean_object* v___x_466_; 
lean_dec(v_cancelTks_451_);
v___x_466_ = lean_box(0);
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___boxed(lean_object* v_cancelTks_467_, lean_object* v_sleepDurationMs_468_, lean_object* v_a_469_){
_start:
{
uint32_t v_sleepDurationMs_boxed_470_; lean_object* v_res_471_; 
v_sleepDurationMs_boxed_470_ = lean_unbox_uint32(v_sleepDurationMs_468_);
lean_dec(v_sleepDurationMs_468_);
v_res_471_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(v_cancelTks_467_, v_sleepDurationMs_boxed_470_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(lean_object* v_xs_472_, uint32_t v_latencyMs_473_, lean_object* v_cancelTks_474_){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint32_t v___x_482_; lean_object* v___x_483_; 
v___x_476_ = lean_io_mono_ms_now();
lean_inc(v_cancelTks_474_);
v___x_477_ = l_Lean_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_472_, v_latencyMs_473_, v_cancelTks_474_);
v___x_478_ = lean_io_mono_ms_now();
v___x_479_ = lean_nat_sub(v___x_478_, v___x_476_);
lean_dec(v___x_476_);
lean_dec(v___x_478_);
v___x_480_ = lean_uint32_to_nat(v_latencyMs_473_);
v___x_481_ = lean_nat_sub(v___x_480_, v___x_479_);
lean_dec(v___x_479_);
lean_dec(v___x_480_);
v___x_482_ = lean_uint32_of_nat(v___x_481_);
lean_dec(v___x_481_);
v___x_483_ = l___private_Lean_Server_AsyncList_0__Lean_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(v_cancelTks_474_, v___x_482_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg___boxed(lean_object* v_xs_484_, lean_object* v_latencyMs_485_, lean_object* v_cancelTks_486_, lean_object* v_a_487_){
_start:
{
uint32_t v_latencyMs_boxed_488_; lean_object* v_res_489_; 
v_latencyMs_boxed_488_ = lean_unbox_uint32(v_latencyMs_485_);
lean_dec(v_latencyMs_485_);
v_res_489_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(v_xs_484_, v_latencyMs_boxed_488_, v_cancelTks_486_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency(lean_object* v_00_u03b5_490_, lean_object* v_00_u03b1_491_, lean_object* v_xs_492_, uint32_t v_latencyMs_493_, lean_object* v_cancelTks_494_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(v_xs_492_, v_latencyMs_493_, v_cancelTks_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___boxed(lean_object* v_00_u03b5_497_, lean_object* v_00_u03b1_498_, lean_object* v_xs_499_, lean_object* v_latencyMs_500_, lean_object* v_cancelTks_501_, lean_object* v_a_502_){
_start:
{
uint32_t v_latencyMs_boxed_503_; lean_object* v_res_504_; 
v_latencyMs_boxed_503_ = lean_unbox_uint32(v_latencyMs_500_);
lean_dec(v_latencyMs_500_);
v_res_504_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency(v_00_u03b5_497_, v_00_u03b1_498_, v_xs_499_, v_latencyMs_boxed_503_, v_cancelTks_501_);
return v_res_504_;
}
}
lean_object* runtime_initialize_Lean_Server_ServerTask(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_AsyncList(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
