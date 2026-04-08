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
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Lean_Server_ServerTask_bindCheap___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Server_ServerTask_hasFinished___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_waitAny___redArg(lean_object*);
lean_object* lean_io_wait(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_IO_sleep___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___redArg(lean_object*);
lean_object* l_IO_sleep(uint32_t);
lean_object* lean_io_mono_ms_now();
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_cons_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_cons_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_delayed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_delayed_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_nil_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_nil_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00IO_AsyncList_ofList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00IO_AsyncList_ofList_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ofList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ofList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00IO_AsyncList_ofList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00IO_AsyncList_ofList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_IO_AsyncList_instCoeList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_AsyncList_ofList, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_IO_AsyncList_instCoeList___closed__0 = (const lean_object*)&l_IO_AsyncList_instCoeList___closed__0_value;
LEAN_EXPORT lean_object* l_IO_AsyncList_instCoeList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___redArg___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l_IO_AsyncList_waitUntil___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_IO_AsyncList_waitUntil___redArg___closed__0 = (const lean_object*)&l_IO_AsyncList_waitUntil___redArg___closed__0_value;
static lean_once_cell_t l_IO_AsyncList_waitUntil___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_AsyncList_waitUntil___redArg___closed__1;
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_AsyncList_waitAll___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_IO_AsyncList_waitAll___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_AsyncList_waitAll___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_AsyncList_waitAll___redArg___closed__0 = (const lean_object*)&l_IO_AsyncList_waitAll___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_IO_AsyncList_waitFind_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_IO_AsyncList_waitFind_x3f___redArg___closed__0 = (const lean_object*)&l_IO_AsyncList_waitFind_x3f___redArg___closed__0_value;
static lean_once_cell_t l_IO_AsyncList_waitFind_x3f___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_AsyncList_waitFind_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_IO_AsyncList_getFinishedPrefix___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_IO_AsyncList_getFinishedPrefix___redArg___closed__0 = (const lean_object*)&l_IO_AsyncList_getFinishedPrefix___redArg___closed__0_value;
static const lean_ctor_object l_IO_AsyncList_getFinishedPrefix___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_AsyncList_getFinishedPrefix___redArg___closed__0_value)}};
static const lean_object* l_IO_AsyncList_getFinishedPrefix___redArg___closed__1 = (const lean_object*)&l_IO_AsyncList_getFinishedPrefix___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___lam__0(lean_object*);
static const lean_closure_object l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0 = (const lean_object*)&l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0;
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_anyM___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorIdx___redArg(lean_object* v_x_1_){
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
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorIdx___redArg___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_IO_AsyncList_ctorIdx___redArg(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorIdx(lean_object* v_00_u03b5_7_, lean_object* v_00_u03b1_8_, lean_object* v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_IO_AsyncList_ctorIdx___redArg(v_x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorIdx___boxed(lean_object* v_00_u03b5_11_, lean_object* v_00_u03b1_12_, lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_IO_AsyncList_ctorIdx(v_00_u03b5_11_, v_00_u03b1_12_, v_x_13_);
lean_dec(v_x_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorElim___redArg(lean_object* v_t_15_, lean_object* v_k_16_){
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
lean_dec_ref(v_t_15_);
v___x_19_ = lean_apply_2(v_k_16_, v_hd_17_, v_tl_18_);
return v___x_19_;
}
case 1:
{
lean_object* v_tl_20_; lean_object* v___x_21_; 
v_tl_20_ = lean_ctor_get(v_t_15_, 0);
lean_inc_ref(v_tl_20_);
lean_dec_ref(v_t_15_);
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
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorElim(lean_object* v_00_u03b5_22_, lean_object* v_00_u03b1_23_, lean_object* v_motive__1_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_IO_AsyncList_ctorElim___redArg(v_t_26_, v_k_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorElim___boxed(lean_object* v_00_u03b5_30_, lean_object* v_00_u03b1_31_, lean_object* v_motive__1_32_, lean_object* v_ctorIdx_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_k_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_IO_AsyncList_ctorElim(v_00_u03b5_30_, v_00_u03b1_31_, v_motive__1_32_, v_ctorIdx_33_, v_t_34_, v_h_35_, v_k_36_);
lean_dec(v_ctorIdx_33_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_cons_elim___redArg(lean_object* v_t_38_, lean_object* v_cons_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_IO_AsyncList_ctorElim___redArg(v_t_38_, v_cons_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_cons_elim(lean_object* v_00_u03b5_41_, lean_object* v_00_u03b1_42_, lean_object* v_motive__1_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_cons_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_IO_AsyncList_ctorElim___redArg(v_t_44_, v_cons_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_delayed_elim___redArg(lean_object* v_t_48_, lean_object* v_delayed_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_IO_AsyncList_ctorElim___redArg(v_t_48_, v_delayed_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_delayed_elim(lean_object* v_00_u03b5_51_, lean_object* v_00_u03b1_52_, lean_object* v_motive__1_53_, lean_object* v_t_54_, lean_object* v_h_55_, lean_object* v_delayed_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_IO_AsyncList_ctorElim___redArg(v_t_54_, v_delayed_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_nil_elim___redArg(lean_object* v_t_58_, lean_object* v_nil_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_IO_AsyncList_ctorElim___redArg(v_t_58_, v_nil_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_nil_elim(lean_object* v_00_u03b5_61_, lean_object* v_00_u03b1_62_, lean_object* v_motive__1_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_nil_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_IO_AsyncList_ctorElim___redArg(v_t_64_, v_nil_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_instInhabited(lean_object* v_00_u03b5_68_, lean_object* v_00_u03b1_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_box(2);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00IO_AsyncList_ofList_spec__0___redArg(lean_object* v_init_71_, lean_object* v_x_72_){
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
v___x_78_ = l_List_foldr___at___00IO_AsyncList_ofList_spec__0___redArg(v_init_71_, v_tail_74_);
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
LEAN_EXPORT lean_object* l_List_foldr___at___00IO_AsyncList_ofList_spec__0___redArg___boxed(lean_object* v_init_83_, lean_object* v_x_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_List_foldr___at___00IO_AsyncList_ofList_spec__0___redArg(v_init_83_, v_x_84_);
lean_dec(v_init_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_ofList___redArg(lean_object* v_l_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_box(2);
v___x_88_ = l_List_foldr___at___00IO_AsyncList_ofList_spec__0___redArg(v___x_87_, v_l_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_ofList(lean_object* v_00_u03b1_89_, lean_object* v_00_u03b5_90_, lean_object* v_l_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_IO_AsyncList_ofList___redArg(v_l_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00IO_AsyncList_ofList_spec__0(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b5_94_, lean_object* v_init_95_, lean_object* v_x_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_List_foldr___at___00IO_AsyncList_ofList_spec__0___redArg(v_init_95_, v_x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00IO_AsyncList_ofList_spec__0___boxed(lean_object* v_00_u03b1_98_, lean_object* v_00_u03b5_99_, lean_object* v_init_100_, lean_object* v_x_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_List_foldr___at___00IO_AsyncList_ofList_spec__0(v_00_u03b1_98_, v_00_u03b5_99_, v_init_100_, v_x_101_);
lean_dec(v_init_100_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_instCoeList(lean_object* v_00_u03b1_104_, lean_object* v_00_u03b5_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = ((lean_object*)(l_IO_AsyncList_instCoeList___closed__0));
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___redArg___lam__0(lean_object* v_hd_107_, lean_object* v_x_108_){
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
static lean_object* _init_l_IO_AsyncList_waitUntil___redArg___closed__1(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = ((lean_object*)(l_IO_AsyncList_waitUntil___redArg___closed__0));
v___x_123_ = lean_task_pure(v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___redArg(lean_object* v_p_124_, lean_object* v_x_125_){
_start:
{
switch(lean_obj_tag(v_x_125_))
{
case 0:
{
lean_object* v_hd_126_; lean_object* v_tl_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_143_; 
v_hd_126_ = lean_ctor_get(v_x_125_, 0);
v_tl_127_ = lean_ctor_get(v_x_125_, 1);
v_isSharedCheck_143_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_143_ == 0)
{
v___x_129_ = v_x_125_;
v_isShared_130_ = v_isSharedCheck_143_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_tl_127_);
lean_inc(v_hd_126_);
lean_dec(v_x_125_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_143_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; uint8_t v___x_132_; 
lean_inc_ref(v_p_124_);
lean_inc(v_hd_126_);
v___x_131_ = lean_apply_1(v_p_124_, v_hd_126_);
v___x_132_ = lean_unbox(v___x_131_);
if (v___x_132_ == 0)
{
lean_object* v___f_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
lean_del_object(v___x_129_);
v___f_133_ = lean_alloc_closure((void*)(l_IO_AsyncList_waitUntil___redArg___lam__0), 2, 1);
lean_closure_set(v___f_133_, 0, v_hd_126_);
v___x_134_ = l_IO_AsyncList_waitUntil___redArg(v_p_124_, v_tl_127_);
v___x_135_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_133_, v___x_134_);
return v___x_135_;
}
else
{
lean_object* v___x_136_; lean_object* v___x_138_; 
lean_dec(v_tl_127_);
lean_dec_ref(v_p_124_);
v___x_136_ = lean_box(0);
if (v_isShared_130_ == 0)
{
lean_ctor_set_tag(v___x_129_, 1);
lean_ctor_set(v___x_129_, 1, v___x_136_);
v___x_138_ = v___x_129_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_hd_126_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___x_136_);
v___x_138_ = v_reuseFailAlloc_142_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_box(0);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = lean_task_pure(v___x_140_);
return v___x_141_;
}
}
}
}
case 1:
{
lean_object* v_tl_144_; lean_object* v___f_145_; lean_object* v___x_146_; 
v_tl_144_ = lean_ctor_get(v_x_125_, 0);
lean_inc_ref(v_tl_144_);
lean_dec_ref(v_x_125_);
v___f_145_ = lean_alloc_closure((void*)(l_IO_AsyncList_waitUntil___redArg___lam__1), 2, 1);
lean_closure_set(v___f_145_, 0, v_p_124_);
v___x_146_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_tl_144_, v___f_145_);
return v___x_146_;
}
default: 
{
lean_object* v___x_147_; 
lean_dec_ref(v_p_124_);
v___x_147_ = lean_obj_once(&l_IO_AsyncList_waitUntil___redArg___closed__1, &l_IO_AsyncList_waitUntil___redArg___closed__1_once, _init_l_IO_AsyncList_waitUntil___redArg___closed__1);
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___redArg___lam__1(lean_object* v_p_148_, lean_object* v_x_149_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_160_; 
lean_dec_ref(v_p_148_);
v_a_150_ = lean_ctor_get(v_x_149_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v_x_149_);
if (v_isSharedCheck_160_ == 0)
{
v___x_152_ = v_x_149_;
v_isShared_153_ = v_isSharedCheck_160_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v_x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_160_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_154_ = lean_box(0);
if (v_isShared_153_ == 0)
{
lean_ctor_set_tag(v___x_152_, 1);
v___x_156_ = v___x_152_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_150_);
v___x_156_ = v_reuseFailAlloc_159_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_154_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = lean_task_pure(v___x_157_);
return v___x_158_;
}
}
}
else
{
lean_object* v_a_161_; lean_object* v___x_162_; 
v_a_161_ = lean_ctor_get(v_x_149_, 0);
lean_inc(v_a_161_);
lean_dec_ref(v_x_149_);
v___x_162_ = l_IO_AsyncList_waitUntil___redArg(v_p_148_, v_a_161_);
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil(lean_object* v_00_u03b1_163_, lean_object* v_00_u03b5_164_, lean_object* v_p_165_, lean_object* v_x_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_IO_AsyncList_waitUntil___redArg(v_p_165_, v_x_166_);
return v___x_167_;
}
}
LEAN_EXPORT uint8_t l_IO_AsyncList_waitAll___redArg___lam__0(lean_object* v_x_168_){
_start:
{
uint8_t v___x_169_; 
v___x_169_ = 0;
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___redArg___lam__0___boxed(lean_object* v_x_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_IO_AsyncList_waitAll___redArg___lam__0(v_x_170_);
lean_dec(v_x_170_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___redArg(lean_object* v_a_174_){
_start:
{
lean_object* v___f_175_; lean_object* v___x_176_; 
v___f_175_ = ((lean_object*)(l_IO_AsyncList_waitAll___redArg___closed__0));
v___x_176_ = l_IO_AsyncList_waitUntil___redArg(v___f_175_, v_a_174_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll(lean_object* v_00_u03b5_177_, lean_object* v_00_u03b1_178_, lean_object* v_a_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_IO_AsyncList_waitAll___redArg(v_a_179_);
return v___x_180_;
}
}
static lean_object* _init_l_IO_AsyncList_waitFind_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = ((lean_object*)(l_IO_AsyncList_waitFind_x3f___redArg___closed__0));
v___x_184_ = lean_task_pure(v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___redArg(lean_object* v_p_185_, lean_object* v_x_186_){
_start:
{
switch(lean_obj_tag(v_x_186_))
{
case 0:
{
lean_object* v_hd_187_; lean_object* v_tl_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v_hd_187_ = lean_ctor_get(v_x_186_, 0);
lean_inc_n(v_hd_187_, 2);
v_tl_188_ = lean_ctor_get(v_x_186_, 1);
lean_inc(v_tl_188_);
lean_dec_ref(v_x_186_);
lean_inc_ref(v_p_185_);
v___x_189_ = lean_apply_1(v_p_185_, v_hd_187_);
v___x_190_ = lean_unbox(v___x_189_);
if (v___x_190_ == 0)
{
lean_dec(v_hd_187_);
v_x_186_ = v_tl_188_;
goto _start;
}
else
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v_tl_188_);
lean_dec_ref(v_p_185_);
v___x_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_192_, 0, v_hd_187_);
v___x_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
v___x_194_ = lean_task_pure(v___x_193_);
return v___x_194_;
}
}
case 1:
{
lean_object* v_tl_195_; lean_object* v___f_196_; lean_object* v___x_197_; 
v_tl_195_ = lean_ctor_get(v_x_186_, 0);
lean_inc_ref(v_tl_195_);
lean_dec_ref(v_x_186_);
v___f_196_ = lean_alloc_closure((void*)(l_IO_AsyncList_waitFind_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_196_, 0, v_p_185_);
v___x_197_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_tl_195_, v___f_196_);
return v___x_197_;
}
default: 
{
lean_object* v___x_198_; 
lean_dec_ref(v_p_185_);
v___x_198_ = lean_obj_once(&l_IO_AsyncList_waitFind_x3f___redArg___closed__1, &l_IO_AsyncList_waitFind_x3f___redArg___closed__1_once, _init_l_IO_AsyncList_waitFind_x3f___redArg___closed__1);
return v___x_198_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___redArg___lam__0(lean_object* v_p_199_, lean_object* v_x_200_){
_start:
{
if (lean_obj_tag(v_x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_209_; 
lean_dec_ref(v_p_199_);
v_a_201_ = lean_ctor_get(v_x_200_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v_x_200_);
if (v_isSharedCheck_209_ == 0)
{
v___x_203_ = v_x_200_;
v_isShared_204_ = v_isSharedCheck_209_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v_x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_209_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_208_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; 
v___x_207_ = lean_task_pure(v___x_206_);
return v___x_207_;
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_211_; 
v_a_210_ = lean_ctor_get(v_x_200_, 0);
lean_inc(v_a_210_);
lean_dec_ref(v_x_200_);
v___x_211_ = l_IO_AsyncList_waitFind_x3f___redArg(v_p_199_, v_a_210_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f(lean_object* v_00_u03b1_212_, lean_object* v_00_u03b5_213_, lean_object* v_p_214_, lean_object* v_x_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_IO_AsyncList_waitFind_x3f___redArg(v_p_214_, v_x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix___redArg(lean_object* v_x_224_){
_start:
{
switch(lean_obj_tag(v_x_224_))
{
case 0:
{
lean_object* v_hd_226_; lean_object* v_tl_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_244_; 
v_hd_226_ = lean_ctor_get(v_x_224_, 0);
v_tl_227_ = lean_ctor_get(v_x_224_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v_x_224_);
if (v_isSharedCheck_244_ == 0)
{
v___x_229_ = v_x_224_;
v_isShared_230_ = v_isSharedCheck_244_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_tl_227_);
lean_inc(v_hd_226_);
lean_dec(v_x_224_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_244_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v_fst_232_; lean_object* v_snd_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_243_; 
v___x_231_ = l_IO_AsyncList_getFinishedPrefix___redArg(v_tl_227_);
v_fst_232_ = lean_ctor_get(v___x_231_, 0);
v_snd_233_ = lean_ctor_get(v___x_231_, 1);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_243_ == 0)
{
v___x_235_ = v___x_231_;
v_isShared_236_ = v_isSharedCheck_243_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_snd_233_);
lean_inc(v_fst_232_);
lean_dec(v___x_231_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_243_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_230_ == 0)
{
lean_ctor_set_tag(v___x_229_, 1);
lean_ctor_set(v___x_229_, 1, v_fst_232_);
v___x_238_ = v___x_229_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_hd_226_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_fst_232_);
v___x_238_ = v_reuseFailAlloc_242_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_240_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_238_);
v___x_240_ = v___x_235_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_snd_233_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
case 1:
{
lean_object* v_tl_245_; uint8_t v___x_246_; 
v_tl_245_ = lean_ctor_get(v_x_224_, 0);
lean_inc_ref(v_tl_245_);
lean_dec_ref(v_x_224_);
v___x_246_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_tl_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec_ref(v_tl_245_);
v___x_247_ = lean_box(0);
v___x_248_ = lean_box(0);
v___x_249_ = lean_box(v___x_246_);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_247_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
return v___x_251_;
}
else
{
lean_object* v___x_252_; 
v___x_252_ = lean_io_wait(v_tl_245_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_264_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_264_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_264_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_264_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_257_ = lean_box(0);
if (v_isShared_256_ == 0)
{
lean_ctor_set_tag(v___x_255_, 1);
v___x_259_ = v___x_255_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_253_);
v___x_259_ = v_reuseFailAlloc_263_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_box(v___x_246_);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_259_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_257_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
return v___x_262_;
}
}
}
else
{
lean_object* v_a_265_; 
v_a_265_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_265_);
lean_dec_ref(v___x_252_);
v_x_224_ = v_a_265_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_267_; 
v___x_267_ = ((lean_object*)(l_IO_AsyncList_getFinishedPrefix___redArg___closed__1));
return v___x_267_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix___redArg___boxed(lean_object* v_x_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_IO_AsyncList_getFinishedPrefix___redArg(v_x_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix(lean_object* v_00_u03b5_271_, lean_object* v_00_u03b1_272_, lean_object* v_x_273_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_IO_AsyncList_getFinishedPrefix___redArg(v_x_273_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix___boxed(lean_object* v_00_u03b5_276_, lean_object* v_00_u03b1_277_, lean_object* v_x_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_IO_AsyncList_getFinishedPrefix(v_00_u03b5_276_, v_00_u03b1_277_, v_x_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___lam__0(lean_object* v_val_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v_val_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___lam__0(lean_object* v_val_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v_val_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
if (lean_obj_tag(v_a_286_) == 0)
{
lean_object* v___x_288_; 
v___x_288_ = l_List_reverse___redArg(v_a_287_);
return v___x_288_;
}
else
{
lean_object* v_head_289_; lean_object* v_tail_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_300_; 
v_head_289_ = lean_ctor_get(v_a_286_, 0);
v_tail_290_ = lean_ctor_get(v_a_286_, 1);
v_isSharedCheck_300_ = !lean_is_exclusive(v_a_286_);
if (v_isSharedCheck_300_ == 0)
{
v___x_292_ = v_a_286_;
v_isShared_293_ = v_isSharedCheck_300_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_tail_290_);
lean_inc(v_head_289_);
lean_dec(v_a_286_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_300_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___f_294_; lean_object* v___x_295_; lean_object* v___x_297_; 
v___f_294_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0));
v___x_295_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_294_, v_head_289_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v_a_287_);
lean_ctor_set(v___x_292_, 0, v___x_295_);
v___x_297_ = v___x_292_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_a_287_);
v___x_297_ = v_reuseFailAlloc_299_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
v_a_286_ = v_tail_290_;
v_a_287_ = v___x_297_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(lean_object* v_cancelTks_302_, lean_object* v_timeoutTask_303_, lean_object* v_xs_304_){
_start:
{
switch(lean_obj_tag(v_xs_304_))
{
case 0:
{
lean_object* v_hd_306_; lean_object* v_tl_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_324_; 
v_hd_306_ = lean_ctor_get(v_xs_304_, 0);
v_tl_307_ = lean_ctor_get(v_xs_304_, 1);
v_isSharedCheck_324_ = !lean_is_exclusive(v_xs_304_);
if (v_isSharedCheck_324_ == 0)
{
v___x_309_ = v_xs_304_;
v_isShared_310_ = v_isSharedCheck_324_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_tl_307_);
lean_inc(v_hd_306_);
lean_dec(v_xs_304_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_324_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; lean_object* v_fst_312_; lean_object* v_snd_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_323_; 
v___x_311_ = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_302_, v_timeoutTask_303_, v_tl_307_);
v_fst_312_ = lean_ctor_get(v___x_311_, 0);
v_snd_313_ = lean_ctor_get(v___x_311_, 1);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_323_ == 0)
{
v___x_315_ = v___x_311_;
v_isShared_316_ = v_isSharedCheck_323_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_snd_313_);
lean_inc(v_fst_312_);
lean_dec(v___x_311_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_323_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set_tag(v___x_309_, 1);
lean_ctor_set(v___x_309_, 1, v_fst_312_);
v___x_318_ = v___x_309_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_hd_306_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_fst_312_);
v___x_318_ = v_reuseFailAlloc_322_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_320_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_318_);
v___x_320_ = v___x_315_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_snd_313_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
case 1:
{
lean_object* v_tl_325_; uint8_t v___x_326_; uint8_t v___x_327_; 
v_tl_325_ = lean_ctor_get(v_xs_304_, 0);
lean_inc_ref(v_tl_325_);
lean_dec_ref(v_xs_304_);
v___x_326_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_tl_325_);
v___x_327_ = 1;
if (v___x_326_ == 0)
{
lean_object* v___f_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___f_328_ = ((lean_object*)(l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0));
v___x_329_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_328_, v_tl_325_);
v___x_330_ = lean_box(0);
lean_inc(v_cancelTks_302_);
v___x_331_ = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(v_cancelTks_302_, v___x_330_);
v___x_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_329_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
lean_inc_ref(v_timeoutTask_303_);
v___x_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_333_, 0, v_timeoutTask_303_);
lean_ctor_set(v___x_333_, 1, v___x_330_);
v___x_334_ = l_List_appendTR___redArg(v___x_332_, v___x_333_);
v___x_335_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_334_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec_ref(v___x_335_);
lean_dec_ref(v_timeoutTask_303_);
lean_dec(v_cancelTks_302_);
v___x_336_ = lean_box(0);
v___x_337_ = lean_box(v___x_326_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_330_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
return v___x_339_;
}
else
{
lean_object* v_val_340_; 
v_val_340_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_val_340_);
lean_dec_ref(v___x_335_);
if (lean_obj_tag(v_val_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_351_; 
lean_dec_ref(v_timeoutTask_303_);
lean_dec(v_cancelTks_302_);
v_a_341_ = lean_ctor_get(v_val_340_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v_val_340_);
if (v_isSharedCheck_351_ == 0)
{
v___x_343_ = v_val_340_;
v_isShared_344_ = v_isSharedCheck_351_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v_val_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_351_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
lean_ctor_set_tag(v___x_343_, 1);
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_350_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = lean_box(v___x_327_);
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_346_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_330_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
return v___x_349_;
}
}
}
else
{
lean_object* v_a_352_; 
v_a_352_ = lean_ctor_get(v_val_340_, 0);
lean_inc(v_a_352_);
lean_dec_ref(v_val_340_);
v_xs_304_ = v_a_352_;
goto _start;
}
}
}
else
{
lean_object* v___x_354_; 
v___x_354_ = lean_io_wait(v_tl_325_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_366_; 
lean_dec_ref(v_timeoutTask_303_);
lean_dec(v_cancelTks_302_);
v_a_355_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_366_ == 0)
{
v___x_357_ = v___x_354_;
v_isShared_358_ = v_isSharedCheck_366_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_366_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = lean_box(0);
if (v_isShared_358_ == 0)
{
lean_ctor_set_tag(v___x_357_, 1);
v___x_361_ = v___x_357_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_355_);
v___x_361_ = v_reuseFailAlloc_365_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = lean_box(v___x_327_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_359_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
return v___x_364_;
}
}
}
else
{
lean_object* v_a_367_; 
v_a_367_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_367_);
lean_dec_ref(v___x_354_);
v_xs_304_ = v_a_367_;
goto _start;
}
}
}
default: 
{
lean_object* v___x_369_; 
lean_dec_ref(v_timeoutTask_303_);
lean_dec(v_cancelTks_302_);
v___x_369_ = ((lean_object*)(l_IO_AsyncList_getFinishedPrefix___redArg___closed__1));
return v___x_369_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___boxed(lean_object* v_cancelTks_370_, lean_object* v_timeoutTask_371_, lean_object* v_xs_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_370_, v_timeoutTask_371_, v_xs_372_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go(lean_object* v_00_u03b5_375_, lean_object* v_00_u03b1_376_, lean_object* v_cancelTks_377_, lean_object* v_timeoutTask_378_, lean_object* v_xs_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_377_, v_timeoutTask_378_, v_xs_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___boxed(lean_object* v_00_u03b5_382_, lean_object* v_00_u03b1_383_, lean_object* v_cancelTks_384_, lean_object* v_timeoutTask_385_, lean_object* v_xs_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go(v_00_u03b5_382_, v_00_u03b1_383_, v_cancelTks_384_, v_timeoutTask_385_, v_xs_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0(lean_object* v_00_u03b5_389_, lean_object* v_00_u03b1_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(v_a_391_, v_a_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(uint32_t v_timeoutMs_396_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = l_IO_sleep(v_timeoutMs_396_);
v___x_399_ = ((lean_object*)(l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0));
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed(lean_object* v_timeoutMs_400_, lean_object* v___y_401_){
_start:
{
uint32_t v_timeoutMs_boxed_402_; lean_object* v_res_403_; 
v_timeoutMs_boxed_402_ = lean_unbox_uint32(v_timeoutMs_400_);
lean_dec(v_timeoutMs_400_);
v_res_403_ = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(v_timeoutMs_boxed_402_);
return v_res_403_;
}
}
static lean_object* _init_l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0));
v___x_405_ = lean_task_pure(v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(lean_object* v_xs_406_, uint32_t v_timeoutMs_407_, lean_object* v_cancelTks_408_){
_start:
{
uint32_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = 0;
v___x_411_ = lean_uint32_dec_eq(v_timeoutMs_407_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___f_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_412_ = lean_box_uint32(v_timeoutMs_407_);
v___f_413_ = lean_alloc_closure((void*)(l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_413_, 0, v___x_412_);
v___x_414_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v___f_413_);
v___x_415_ = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_408_, v___x_414_, v_xs_406_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_obj_once(&l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0, &l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0_once, _init_l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0);
v___x_417_ = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_408_, v___x_416_, v_xs_406_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___boxed(lean_object* v_xs_418_, lean_object* v_timeoutMs_419_, lean_object* v_cancelTks_420_, lean_object* v_a_421_){
_start:
{
uint32_t v_timeoutMs_boxed_422_; lean_object* v_res_423_; 
v_timeoutMs_boxed_422_ = lean_unbox_uint32(v_timeoutMs_419_);
lean_dec(v_timeoutMs_419_);
v_res_423_ = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_418_, v_timeoutMs_boxed_422_, v_cancelTks_420_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout(lean_object* v_00_u03b5_424_, lean_object* v_00_u03b1_425_, lean_object* v_xs_426_, uint32_t v_timeoutMs_427_, lean_object* v_cancelTks_428_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_426_, v_timeoutMs_427_, v_cancelTks_428_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___boxed(lean_object* v_00_u03b5_431_, lean_object* v_00_u03b1_432_, lean_object* v_xs_433_, lean_object* v_timeoutMs_434_, lean_object* v_cancelTks_435_, lean_object* v_a_436_){
_start:
{
uint32_t v_timeoutMs_boxed_437_; lean_object* v_res_438_; 
v_timeoutMs_boxed_437_ = lean_unbox_uint32(v_timeoutMs_434_);
lean_dec(v_timeoutMs_434_);
v_res_438_ = l_IO_AsyncList_getFinishedPrefixWithTimeout(v_00_u03b5_431_, v_00_u03b1_432_, v_xs_433_, v_timeoutMs_boxed_437_, v_cancelTks_435_);
return v_res_438_;
}
}
LEAN_EXPORT uint8_t l_List_anyM___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(lean_object* v_x_439_){
_start:
{
if (lean_obj_tag(v_x_439_) == 0)
{
uint8_t v___x_441_; 
v___x_441_ = 0;
return v___x_441_;
}
else
{
lean_object* v_head_442_; lean_object* v_tail_443_; uint8_t v___x_444_; 
v_head_442_ = lean_ctor_get(v_x_439_, 0);
v_tail_443_ = lean_ctor_get(v_x_439_, 1);
v___x_444_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_head_442_);
if (v___x_444_ == 0)
{
v_x_439_ = v_tail_443_;
goto _start;
}
else
{
return v___x_444_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0___boxed(lean_object* v_x_446_, lean_object* v___y_447_){
_start:
{
uint8_t v_res_448_; lean_object* v_r_449_; 
v_res_448_ = l_List_anyM___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(v_x_446_);
lean_dec(v_x_446_);
v_r_449_ = lean_box(v_res_448_);
return v_r_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(lean_object* v_cancelTks_450_, uint32_t v_sleepDurationMs_451_){
_start:
{
uint32_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = 0;
v___x_454_ = lean_uint32_dec_eq(v_sleepDurationMs_451_, v___x_453_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; 
v___x_455_ = l_List_isEmpty___redArg(v_cancelTks_450_);
if (v___x_455_ == 0)
{
uint8_t v___x_456_; 
v___x_456_ = l_List_anyM___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(v_cancelTks_450_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_457_ = lean_box_uint32(v_sleepDurationMs_451_);
v___x_458_ = lean_alloc_closure((void*)(l_IO_sleep___boxed), 2, 1);
lean_closure_set(v___x_458_, 0, v___x_457_);
v___x_459_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v___x_458_);
v___x_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v_cancelTks_450_);
v___x_461_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_460_);
return v___x_461_;
}
else
{
lean_object* v___x_462_; 
lean_dec(v_cancelTks_450_);
v___x_462_ = lean_box(0);
return v___x_462_;
}
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec(v_cancelTks_450_);
v___x_463_ = l_IO_sleep(v_sleepDurationMs_451_);
v___x_464_ = lean_box(0);
return v___x_464_;
}
}
else
{
lean_object* v___x_465_; 
lean_dec(v_cancelTks_450_);
v___x_465_ = lean_box(0);
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___boxed(lean_object* v_cancelTks_466_, lean_object* v_sleepDurationMs_467_, lean_object* v_a_468_){
_start:
{
uint32_t v_sleepDurationMs_boxed_469_; lean_object* v_res_470_; 
v_sleepDurationMs_boxed_469_ = lean_unbox_uint32(v_sleepDurationMs_467_);
lean_dec(v_sleepDurationMs_467_);
v_res_470_ = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(v_cancelTks_466_, v_sleepDurationMs_boxed_469_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(lean_object* v_xs_471_, uint32_t v_latencyMs_472_, lean_object* v_cancelTks_473_){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; uint32_t v___x_481_; lean_object* v___x_482_; 
v___x_475_ = lean_io_mono_ms_now();
lean_inc(v_cancelTks_473_);
v___x_476_ = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(v_xs_471_, v_latencyMs_472_, v_cancelTks_473_);
v___x_477_ = lean_io_mono_ms_now();
v___x_478_ = lean_nat_sub(v___x_477_, v___x_475_);
lean_dec(v___x_475_);
lean_dec(v___x_477_);
v___x_479_ = lean_uint32_to_nat(v_latencyMs_472_);
v___x_480_ = lean_nat_sub(v___x_479_, v___x_478_);
lean_dec(v___x_478_);
lean_dec(v___x_479_);
v___x_481_ = lean_uint32_of_nat(v___x_480_);
lean_dec(v___x_480_);
v___x_482_ = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(v_cancelTks_473_, v___x_481_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___redArg___boxed(lean_object* v_xs_483_, lean_object* v_latencyMs_484_, lean_object* v_cancelTks_485_, lean_object* v_a_486_){
_start:
{
uint32_t v_latencyMs_boxed_487_; lean_object* v_res_488_; 
v_latencyMs_boxed_487_ = lean_unbox_uint32(v_latencyMs_484_);
lean_dec(v_latencyMs_484_);
v_res_488_ = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(v_xs_483_, v_latencyMs_boxed_487_, v_cancelTks_485_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency(lean_object* v_00_u03b5_489_, lean_object* v_00_u03b1_490_, lean_object* v_xs_491_, uint32_t v_latencyMs_492_, lean_object* v_cancelTks_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(v_xs_491_, v_latencyMs_492_, v_cancelTks_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___boxed(lean_object* v_00_u03b5_496_, lean_object* v_00_u03b1_497_, lean_object* v_xs_498_, lean_object* v_latencyMs_499_, lean_object* v_cancelTks_500_, lean_object* v_a_501_){
_start:
{
uint32_t v_latencyMs_boxed_502_; lean_object* v_res_503_; 
v_latencyMs_boxed_502_ = lean_unbox_uint32(v_latencyMs_499_);
lean_dec(v_latencyMs_499_);
v_res_503_ = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency(v_00_u03b5_496_, v_00_u03b1_497_, v_xs_498_, v_latencyMs_boxed_502_, v_cancelTks_500_);
return v_res_503_;
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
