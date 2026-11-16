// Lean compiler output
// Module: Std.Async.Watchdog
// Imports: public import Std.Time public import Std.Internal.UV.Timer public import Std.Sync.CancellationContext
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_CancellationContext_cancel(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_getCancellationReason(lean_object*);
uint8_t l_Std_instBEqCancellationReason_beq(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_io_promise_new();
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_wait(lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
uint8_t l_Std_CancellationToken_isCancelled(lean_object*);
lean_object* lean_io_mono_ms_now();
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint64_t l_UInt64_ofNatClamp(lean_object*);
lean_object* lean_uv_timer_mk(uint64_t, uint8_t);
lean_object* lean_uv_timer_next(lean_object*);
lean_object* lean_uv_timer_stop(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_stop_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_stop_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_fire_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_fire_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_park_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_park_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_sleep_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_sleep_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_State_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_State_next___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_fire(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_fire___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_new___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_new___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Watchdog_new___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Async_Watchdog_new___closed__0 = (const lean_object*)&l_Std_Async_Watchdog_new___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_new(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_new___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_armUntilIf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_armUntilIf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_armUntil(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_armUntil___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_armAfter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_armAfter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_armAfter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_armAfter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_armAfter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_armAfter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_arm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_arm___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Std_Async_Watchdog_0__Std_Async_Watchdog_settle_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Std_Async_Watchdog_0__Std_Async_Watchdog_settle_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_settle___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_settle___closed__0 = (const lean_object*)&l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_settle___closed__0_value;
LEAN_EXPORT uint8_t l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_settle(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_settle___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_Watchdog_disarm(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_disarm___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_Watchdog_hasFired(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_hasFired___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 3)
{
lean_object* v_ms_7_; lean_object* v___x_8_; 
v_ms_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_ms_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_ms_7_);
return v___x_8_;
}
else
{
lean_dec(v_t_5_);
return v_k_6_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_stop_elim___redArg(lean_object* v_t_21_, lean_object* v_stop_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorElim___redArg(v_t_21_, v_stop_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_stop_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_stop_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorElim___redArg(v_t_25_, v_stop_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_fire_elim___redArg(lean_object* v_t_29_, lean_object* v_fire_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorElim___redArg(v_t_29_, v_fire_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_fire_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_fire_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorElim___redArg(v_t_33_, v_fire_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_park_elim___redArg(lean_object* v_t_37_, lean_object* v_park_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorElim___redArg(v_t_37_, v_park_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_park_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_park_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorElim___redArg(v_t_41_, v_park_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_sleep_elim___redArg(lean_object* v_t_45_, lean_object* v_sleep_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorElim___redArg(v_t_45_, v_sleep_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_sleep_elim(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_sleep_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_Step_ctorElim___redArg(v_t_49_, v_sleep_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_State_next(lean_object* v_now_53_, lean_object* v_s_54_){
_start:
{
uint8_t v_fired_55_; 
v_fired_55_ = lean_ctor_get_uint8(v_s_54_, sizeof(void*)*3 + 1);
if (v_fired_55_ == 0)
{
uint8_t v_waiting_56_; 
v_waiting_56_ = lean_ctor_get_uint8(v_s_54_, sizeof(void*)*3);
if (v_waiting_56_ == 0)
{
lean_object* v_deadline_57_; lean_object* v_epoch_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_68_; 
v_deadline_57_ = lean_ctor_get(v_s_54_, 0);
v_epoch_58_ = lean_ctor_get(v_s_54_, 2);
v_isSharedCheck_68_ = !lean_is_exclusive(v_s_54_);
if (v_isSharedCheck_68_ == 0)
{
lean_object* v_unused_69_; 
v_unused_69_ = lean_ctor_get(v_s_54_, 1);
lean_dec(v_unused_69_);
v___x_60_ = v_s_54_;
v_isShared_61_ = v_isSharedCheck_68_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_epoch_58_);
lean_inc(v_deadline_57_);
lean_dec(v_s_54_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_68_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_62_ = lean_box(2);
v___x_63_ = lean_box(0);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 1, v___x_63_);
v___x_65_ = v___x_60_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_deadline_57_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v___x_63_);
lean_ctor_set(v_reuseFailAlloc_67_, 2, v_epoch_58_);
lean_ctor_set_uint8(v_reuseFailAlloc_67_, sizeof(void*)*3, v_waiting_56_);
lean_ctor_set_uint8(v_reuseFailAlloc_67_, sizeof(void*)*3 + 1, v_fired_55_);
v___x_65_ = v_reuseFailAlloc_67_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
lean_object* v___x_66_; 
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_62_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
return v___x_66_;
}
}
}
else
{
lean_object* v_deadline_70_; lean_object* v_epoch_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_89_; 
v_deadline_70_ = lean_ctor_get(v_s_54_, 0);
v_epoch_71_ = lean_ctor_get(v_s_54_, 2);
v_isSharedCheck_89_ = !lean_is_exclusive(v_s_54_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v_s_54_, 1);
lean_dec(v_unused_90_);
v___x_73_ = v_s_54_;
v_isShared_74_ = v_isSharedCheck_89_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_epoch_71_);
lean_inc(v_deadline_70_);
lean_dec(v_s_54_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_89_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
uint8_t v___x_75_; 
v___x_75_ = lean_nat_dec_le(v_deadline_70_, v_now_53_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_76_ = lean_nat_sub(v_deadline_70_, v_now_53_);
v___x_77_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_inc(v_deadline_70_);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v_deadline_70_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v___x_78_);
v___x_80_ = v___x_73_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_deadline_70_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v___x_78_);
lean_ctor_set(v_reuseFailAlloc_82_, 2, v_epoch_71_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, sizeof(void*)*3, v_waiting_56_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, sizeof(void*)*3 + 1, v_fired_55_);
v___x_80_ = v_reuseFailAlloc_82_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_object* v___x_81_; 
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_77_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
return v___x_81_;
}
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_83_ = lean_box(1);
v___x_84_ = lean_box(0);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v___x_84_);
v___x_86_ = v___x_73_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_deadline_70_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_88_, 2, v_epoch_71_);
v___x_86_ = v_reuseFailAlloc_88_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_87_; 
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*3, v_fired_55_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*3 + 1, v___x_75_);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_83_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
return v___x_87_;
}
}
}
}
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_box(0);
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
lean_ctor_set(v___x_92_, 1, v_s_54_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_State_next___boxed(lean_object* v_now_93_, lean_object* v_s_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_State_next(v_now_93_, v_s_94_);
lean_dec(v_now_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_fire(lean_object* v_wd_96_){
_start:
{
lean_object* v_ctx_98_; lean_object* v_state_99_; lean_object* v___x_100_; lean_object* v_deadline_101_; lean_object* v_epoch_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_115_; 
v_ctx_98_ = lean_ctor_get(v_wd_96_, 0);
lean_inc_ref(v_ctx_98_);
v_state_99_ = lean_ctor_get(v_wd_96_, 1);
lean_inc(v_state_99_);
lean_dec_ref(v_wd_96_);
v___x_100_ = lean_st_ref_take(v_state_99_);
v_deadline_101_ = lean_ctor_get(v___x_100_, 0);
v_epoch_102_ = lean_ctor_get(v___x_100_, 2);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_115_ == 0)
{
lean_object* v_unused_116_; 
v_unused_116_ = lean_ctor_get(v___x_100_, 1);
lean_dec(v_unused_116_);
v___x_104_ = v___x_100_;
v_isShared_105_ = v_isSharedCheck_115_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_epoch_102_);
lean_inc(v_deadline_101_);
lean_dec(v___x_100_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_115_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
uint8_t v___x_106_; uint8_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_106_ = 0;
v___x_107_ = 1;
v___x_108_ = lean_box(0);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v___x_108_);
v___x_110_ = v___x_104_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_deadline_101_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_114_, 2, v_epoch_102_);
v___x_110_ = v_reuseFailAlloc_114_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*3, v___x_106_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*3 + 1, v___x_107_);
v___x_111_ = lean_st_ref_put(v_state_99_, v___x_110_);
lean_dec(v_state_99_);
v___x_112_ = lean_box(0);
v___x_113_ = l_Std_CancellationContext_cancel(v_ctx_98_, v___x_112_);
return v___x_113_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_fire___boxed(lean_object* v_wd_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_fire(v_wd_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round___lam__1(lean_object* v_val_120_, lean_object* v_x_121_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_box(0);
v___x_124_ = lean_io_promise_resolve(v___x_123_, v_val_120_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round___lam__1___boxed(lean_object* v_val_125_, lean_object* v_x_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round___lam__1(v_val_125_, v_x_126_);
lean_dec(v_x_126_);
lean_dec(v_val_125_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round___lam__0___boxed(lean_object* v_wd_129_, lean_object* v_x_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round___lam__0(v_wd_129_, v_x_130_);
lean_dec(v_x_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round(lean_object* v_wd_133_){
_start:
{
lean_object* v_ctx_135_; lean_object* v_state_136_; lean_object* v_wake_137_; lean_object* v_timer_138_; lean_object* v___f_139_; uint8_t v___y_141_; lean_object* v___y_142_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_ctx_135_ = lean_ctor_get(v_wd_133_, 0);
v_state_136_ = lean_ctor_get(v_wd_133_, 1);
v_wake_137_ = lean_ctor_get(v_wd_133_, 2);
v_timer_138_ = lean_ctor_get(v_wd_133_, 3);
lean_inc_ref(v_wd_133_);
v___f_139_ = lean_alloc_closure((void*)(l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round___lam__0___boxed), 3, 1);
lean_closure_set(v___f_139_, 0, v_wd_133_);
v___x_182_ = lean_box(0);
v___x_183_ = lean_st_ref_swap(v_timer_138_, v___x_182_);
if (lean_obj_tag(v___x_183_) == 1)
{
lean_object* v_val_184_; lean_object* v___x_185_; 
v_val_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_val_184_);
lean_dec_ref_known(v___x_183_, 1);
v___x_185_ = lean_uv_timer_stop(v_val_184_);
lean_dec(v_val_184_);
lean_dec_ref(v___x_185_);
goto v___jp_146_;
}
else
{
lean_dec(v___x_183_);
goto v___jp_146_;
}
v___jp_140_:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_io_promise_result_opt(v___y_142_);
lean_dec(v___y_142_);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = l_BaseIO_chainTask___redArg(v___x_143_, v___f_139_, v___x_144_, v___y_141_);
return v___x_145_;
}
v___jp_146_:
{
lean_object* v___x_147_; lean_object* v___f_148_; lean_object* v___x_149_; lean_object* v_token_150_; uint8_t v___x_151_; 
v___x_147_ = lean_io_promise_new();
lean_inc_n(v___x_147_, 2);
v___f_148_ = lean_alloc_closure((void*)(l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round___lam__1___boxed), 3, 1);
lean_closure_set(v___f_148_, 0, v___x_147_);
v___x_149_ = lean_st_ref_swap(v_wake_137_, v___x_147_);
lean_dec(v___x_149_);
v_token_150_ = lean_ctor_get(v_ctx_135_, 1);
lean_inc_ref(v_token_150_);
v___x_151_ = l_Std_CancellationToken_isCancelled(v_token_150_);
if (v___x_151_ == 0)
{
uint8_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v_fst_156_; lean_object* v_snd_157_; lean_object* v___x_158_; 
v___x_152_ = 1;
v___x_153_ = lean_io_mono_ms_now();
v___x_154_ = lean_st_ref_take(v_state_136_);
v___x_155_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_State_next(v___x_153_, v___x_154_);
lean_dec(v___x_153_);
v_fst_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_fst_156_);
v_snd_157_ = lean_ctor_get(v___x_155_, 1);
lean_inc(v_snd_157_);
lean_dec_ref(v___x_155_);
v___x_158_ = lean_st_ref_put(v_state_136_, v_snd_157_);
switch(lean_obj_tag(v_fst_156_))
{
case 0:
{
lean_object* v___x_159_; 
lean_dec_ref(v___f_148_);
lean_dec(v___x_147_);
lean_dec_ref(v___f_139_);
lean_dec_ref(v_wd_133_);
v___x_159_ = lean_box(0);
return v___x_159_;
}
case 1:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_inc_ref(v_ctx_135_);
lean_dec_ref(v___f_148_);
lean_dec(v___x_147_);
lean_dec_ref(v___f_139_);
lean_dec_ref(v_wd_133_);
v___x_160_ = lean_box(0);
v___x_161_ = l_Std_CancellationContext_cancel(v_ctx_135_, v___x_160_);
return v___x_161_;
}
case 2:
{
lean_dec_ref(v___f_148_);
lean_dec_ref(v_wd_133_);
v___y_141_ = v___x_151_;
v___y_142_ = v___x_147_;
goto v___jp_140_;
}
default: 
{
lean_object* v_ms_162_; uint64_t v___x_163_; lean_object* v___x_164_; 
v_ms_162_ = lean_ctor_get(v_fst_156_, 0);
lean_inc(v_ms_162_);
lean_dec_ref_known(v_fst_156_, 1);
v___x_163_ = l_UInt64_ofNatClamp(v_ms_162_);
lean_dec(v_ms_162_);
v___x_164_ = lean_uv_timer_mk(v___x_163_, v___x_151_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v___x_166_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_a_165_);
lean_dec_ref_known(v___x_164_, 1);
v___x_166_ = lean_uv_timer_next(v_a_165_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_178_; 
lean_inc(v_timer_138_);
lean_dec_ref(v_wd_133_);
v_a_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_178_ == 0)
{
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_178_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_178_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
lean_ctor_set_tag(v___x_169_, 1);
lean_ctor_set(v___x_169_, 0, v_a_165_);
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_165_);
v___x_172_ = v_reuseFailAlloc_177_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_173_ = lean_st_ref_swap(v_timer_138_, v___x_172_);
lean_dec(v_timer_138_);
lean_dec(v___x_173_);
v___x_174_ = lean_io_promise_result_opt(v_a_167_);
lean_dec(v_a_167_);
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = l_BaseIO_chainTask___redArg(v___x_174_, v___f_148_, v___x_175_, v___x_152_);
v___y_141_ = v___x_151_;
v___y_142_ = v___x_147_;
goto v___jp_140_;
}
}
}
else
{
lean_object* v___x_179_; 
lean_dec_ref_known(v___x_166_, 1);
lean_dec(v_a_165_);
lean_dec_ref(v___f_148_);
lean_dec(v___x_147_);
lean_dec_ref(v___f_139_);
v___x_179_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_fire(v_wd_133_);
return v___x_179_;
}
}
else
{
lean_object* v___x_180_; 
lean_dec_ref_known(v___x_164_, 1);
lean_dec_ref(v___f_148_);
lean_dec(v___x_147_);
lean_dec_ref(v___f_139_);
v___x_180_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_fire(v_wd_133_);
return v___x_180_;
}
}
}
}
else
{
lean_object* v___x_181_; 
lean_dec_ref(v___f_148_);
lean_dec(v___x_147_);
lean_dec_ref(v___f_139_);
lean_dec_ref(v_wd_133_);
v___x_181_ = lean_box(0);
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round___lam__0(lean_object* v_wd_186_, lean_object* v_x_187_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round(v_wd_186_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round___boxed(lean_object* v_wd_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round(v_wd_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_new___lam__0(lean_object* v_val_193_, lean_object* v_x_194_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = lean_st_ref_get(v_val_193_);
v___x_197_ = lean_box(0);
v___x_198_ = lean_io_promise_resolve(v___x_197_, v___x_196_);
lean_dec(v___x_196_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_new___lam__0___boxed(lean_object* v_val_199_, lean_object* v_x_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_Async_Watchdog_new___lam__0(v_val_199_, v_x_200_);
lean_dec_ref(v_x_200_);
lean_dec(v_val_199_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_new(lean_object* v_ctx_207_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___f_215_; lean_object* v___x_216_; lean_object* v_token_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_box(0);
v___x_211_ = ((lean_object*)(l_Std_Async_Watchdog_new___closed__0));
v___x_212_ = lean_st_mk_ref(v___x_211_);
v___x_213_ = lean_io_promise_new();
v___x_214_ = lean_st_mk_ref(v___x_213_);
lean_inc(v___x_214_);
v___f_215_ = lean_alloc_closure((void*)(l_Std_Async_Watchdog_new___lam__0___boxed), 3, 1);
lean_closure_set(v___f_215_, 0, v___x_214_);
v___x_216_ = lean_st_mk_ref(v___x_210_);
v_token_217_ = lean_ctor_get(v_ctx_207_, 1);
lean_inc_ref(v_token_217_);
v___x_218_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_218_, 0, v_ctx_207_);
lean_ctor_set(v___x_218_, 1, v___x_212_);
lean_ctor_set(v___x_218_, 2, v___x_214_);
lean_ctor_set(v___x_218_, 3, v___x_216_);
v___x_219_ = l_Std_CancellationToken_wait(v_token_217_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_230_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_230_ == 0)
{
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_230_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_230_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_224_ = 1;
v___x_225_ = l_BaseIO_chainTask___redArg(v_a_220_, v___f_215_, v___x_209_, v___x_224_);
lean_inc_ref(v___x_218_);
v___x_226_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_round(v___x_218_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v___x_218_);
v___x_228_ = v___x_222_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_218_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_dec_ref_known(v___x_218_, 4);
lean_dec_ref(v___f_215_);
v_a_231_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_219_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_219_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_new___boxed(lean_object* v_ctx_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Std_Async_Watchdog_new(v_ctx_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_armUntilIf(lean_object* v_wd_242_, lean_object* v_epoch_243_, lean_object* v_deadline_244_){
_start:
{
lean_object* v_state_246_; lean_object* v_wake_247_; lean_object* v___x_248_; uint8_t v_fst_250_; lean_object* v_snd_251_; uint8_t v_fired_259_; lean_object* v_scheduled_260_; lean_object* v_epoch_261_; uint8_t v___y_263_; uint8_t v___y_264_; 
v_state_246_ = lean_ctor_get(v_wd_242_, 1);
v_wake_247_ = lean_ctor_get(v_wd_242_, 2);
v___x_248_ = lean_st_ref_take(v_state_246_);
v_fired_259_ = lean_ctor_get_uint8(v___x_248_, sizeof(void*)*3 + 1);
v_scheduled_260_ = lean_ctor_get(v___x_248_, 1);
v_epoch_261_ = lean_ctor_get(v___x_248_, 2);
if (v_fired_259_ == 0)
{
if (lean_obj_tag(v_epoch_243_) == 0)
{
lean_inc(v_epoch_261_);
lean_inc(v_scheduled_260_);
lean_dec(v___x_248_);
goto v___jp_268_;
}
else
{
lean_object* v_val_272_; uint8_t v___x_273_; 
v_val_272_ = lean_ctor_get(v_epoch_243_, 0);
v___x_273_ = lean_nat_dec_eq(v_val_272_, v_epoch_261_);
if (v___x_273_ == 0)
{
lean_dec(v_deadline_244_);
goto v___jp_257_;
}
else
{
lean_inc(v_epoch_261_);
lean_inc(v_scheduled_260_);
lean_dec(v___x_248_);
goto v___jp_268_;
}
}
}
else
{
lean_dec(v_deadline_244_);
goto v___jp_257_;
}
v___jp_249_:
{
lean_object* v___x_252_; 
v___x_252_ = lean_st_ref_put(v_state_246_, v_snd_251_);
if (v_fst_250_ == 0)
{
lean_object* v___x_253_; 
v___x_253_ = lean_box(0);
return v___x_253_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_st_ref_get(v_wake_247_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_io_promise_resolve(v___x_255_, v___x_254_);
lean_dec(v___x_254_);
return v___x_256_;
}
}
v___jp_257_:
{
uint8_t v___x_258_; 
v___x_258_ = 0;
v_fst_250_ = v___x_258_;
v_snd_251_ = v___x_248_;
goto v___jp_249_;
}
v___jp_262_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_add(v_epoch_261_, v___x_265_);
lean_dec(v_epoch_261_);
v___x_267_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_267_, 0, v_deadline_244_);
lean_ctor_set(v___x_267_, 1, v_scheduled_260_);
lean_ctor_set(v___x_267_, 2, v___x_266_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*3, v___y_263_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*3 + 1, v_fired_259_);
v_fst_250_ = v___y_264_;
v_snd_251_ = v___x_267_;
goto v___jp_249_;
}
v___jp_268_:
{
uint8_t v___x_269_; 
v___x_269_ = 1;
if (lean_obj_tag(v_scheduled_260_) == 0)
{
v___y_263_ = v___x_269_;
v___y_264_ = v___x_269_;
goto v___jp_262_;
}
else
{
lean_object* v_val_270_; uint8_t v___x_271_; 
v_val_270_ = lean_ctor_get(v_scheduled_260_, 0);
v___x_271_ = lean_nat_dec_lt(v_deadline_244_, v_val_270_);
v___y_263_ = v___x_269_;
v___y_264_ = v___x_271_;
goto v___jp_262_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_armUntilIf___boxed(lean_object* v_wd_274_, lean_object* v_epoch_275_, lean_object* v_deadline_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_armUntilIf(v_wd_274_, v_epoch_275_, v_deadline_276_);
lean_dec(v_epoch_275_);
lean_dec_ref(v_wd_274_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_armUntil(lean_object* v_wd_279_, lean_object* v_deadline_280_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_box(0);
v___x_283_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_armUntilIf(v_wd_279_, v___x_282_, v_deadline_280_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_armUntil___boxed(lean_object* v_wd_284_, lean_object* v_deadline_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Std_Async_Watchdog_armUntil(v_wd_284_, v_deadline_285_);
lean_dec_ref(v_wd_284_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_armAfter___redArg___lam__0(lean_object* v_fst_288_, lean_object* v_timeout_289_, lean_object* v_wd_290_, lean_object* v_x_291_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_293_ = lean_io_mono_ms_now();
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v_fst_288_);
v___x_295_ = l_Int_toNat(v_timeout_289_);
v___x_296_ = lean_nat_add(v___x_293_, v___x_295_);
lean_dec(v___x_295_);
lean_dec(v___x_293_);
v___x_297_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_armUntilIf(v_wd_290_, v___x_294_, v___x_296_);
lean_dec_ref_known(v___x_294_, 1);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_armAfter___redArg___lam__0___boxed(lean_object* v_fst_298_, lean_object* v_timeout_299_, lean_object* v_wd_300_, lean_object* v_x_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Std_Async_Watchdog_armAfter___redArg___lam__0(v_fst_298_, v_timeout_299_, v_wd_300_, v_x_301_);
lean_dec(v_x_301_);
lean_dec_ref(v_wd_300_);
lean_dec(v_timeout_299_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_armAfter___redArg(lean_object* v_wd_304_, lean_object* v_task_305_, lean_object* v_timeout_306_){
_start:
{
lean_object* v_state_308_; lean_object* v___x_309_; lean_object* v_fst_311_; lean_object* v_snd_312_; uint8_t v_fired_318_; 
v_state_308_ = lean_ctor_get(v_wd_304_, 1);
lean_inc(v_state_308_);
v___x_309_ = lean_st_ref_take(v_state_308_);
v_fired_318_ = lean_ctor_get_uint8(v___x_309_, sizeof(void*)*3 + 1);
if (v_fired_318_ == 0)
{
lean_object* v_deadline_319_; lean_object* v_scheduled_320_; lean_object* v_epoch_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_330_; 
v_deadline_319_ = lean_ctor_get(v___x_309_, 0);
v_scheduled_320_ = lean_ctor_get(v___x_309_, 1);
v_epoch_321_ = lean_ctor_get(v___x_309_, 2);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_330_ == 0)
{
v___x_323_ = v___x_309_;
v_isShared_324_ = v_isSharedCheck_330_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_epoch_321_);
lean_inc(v_scheduled_320_);
lean_inc(v_deadline_319_);
lean_dec(v___x_309_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_330_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_325_ = lean_unsigned_to_nat(1u);
v___x_326_ = lean_nat_add(v_epoch_321_, v___x_325_);
lean_dec(v_epoch_321_);
lean_inc(v___x_326_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 2, v___x_326_);
v___x_328_ = v___x_323_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_deadline_319_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_scheduled_320_);
lean_ctor_set(v_reuseFailAlloc_329_, 2, v___x_326_);
lean_ctor_set_uint8(v_reuseFailAlloc_329_, sizeof(void*)*3 + 1, v_fired_318_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_ctor_set_uint8(v___x_328_, sizeof(void*)*3, v_fired_318_);
v_fst_311_ = v___x_326_;
v_snd_312_ = v___x_328_;
goto v___jp_310_;
}
}
}
else
{
lean_object* v_epoch_331_; 
v_epoch_331_ = lean_ctor_get(v___x_309_, 2);
lean_inc(v_epoch_331_);
v_fst_311_ = v_epoch_331_;
v_snd_312_ = v___x_309_;
goto v___jp_310_;
}
v___jp_310_:
{
lean_object* v___f_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; lean_object* v___x_317_; 
v___f_313_ = lean_alloc_closure((void*)(l_Std_Async_Watchdog_armAfter___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_313_, 0, v_fst_311_);
lean_closure_set(v___f_313_, 1, v_timeout_306_);
lean_closure_set(v___f_313_, 2, v_wd_304_);
v___x_314_ = lean_st_ref_put(v_state_308_, v_snd_312_);
lean_dec(v_state_308_);
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = 1;
v___x_317_ = l_BaseIO_chainTask___redArg(v_task_305_, v___f_313_, v___x_315_, v___x_316_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_armAfter___redArg___boxed(lean_object* v_wd_332_, lean_object* v_task_333_, lean_object* v_timeout_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Std_Async_Watchdog_armAfter___redArg(v_wd_332_, v_task_333_, v_timeout_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_armAfter(lean_object* v_00_u03b1_337_, lean_object* v_wd_338_, lean_object* v_task_339_, lean_object* v_timeout_340_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Std_Async_Watchdog_armAfter___redArg(v_wd_338_, v_task_339_, v_timeout_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_armAfter___boxed(lean_object* v_00_u03b1_343_, lean_object* v_wd_344_, lean_object* v_task_345_, lean_object* v_timeout_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_Async_Watchdog_armAfter(v_00_u03b1_343_, v_wd_344_, v_task_345_, v_timeout_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_arm(lean_object* v_wd_349_, lean_object* v_timeout_350_){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_352_ = lean_io_mono_ms_now();
v___x_353_ = l_Int_toNat(v_timeout_350_);
v___x_354_ = lean_nat_add(v___x_352_, v___x_353_);
lean_dec(v___x_353_);
lean_dec(v___x_352_);
v___x_355_ = l_Std_Async_Watchdog_armUntil(v_wd_349_, v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_arm___boxed(lean_object* v_wd_356_, lean_object* v_timeout_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Std_Async_Watchdog_arm(v_wd_356_, v_timeout_357_);
lean_dec(v_timeout_357_);
lean_dec_ref(v_wd_356_);
return v_res_359_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Std_Async_Watchdog_0__Std_Async_Watchdog_settle_spec__0(lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
if (lean_obj_tag(v_x_360_) == 0)
{
if (lean_obj_tag(v_x_361_) == 0)
{
uint8_t v___x_362_; 
v___x_362_ = 1;
return v___x_362_;
}
else
{
uint8_t v___x_363_; 
v___x_363_ = 0;
return v___x_363_;
}
}
else
{
if (lean_obj_tag(v_x_361_) == 0)
{
uint8_t v___x_364_; 
v___x_364_ = 0;
return v___x_364_;
}
else
{
lean_object* v_val_365_; lean_object* v_val_366_; uint8_t v___x_367_; 
v_val_365_ = lean_ctor_get(v_x_360_, 0);
v_val_366_ = lean_ctor_get(v_x_361_, 0);
v___x_367_ = l_Std_instBEqCancellationReason_beq(v_val_365_, v_val_366_);
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Std_Async_Watchdog_0__Std_Async_Watchdog_settle_spec__0___boxed(lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
uint8_t v_res_370_; lean_object* v_r_371_; 
v_res_370_ = l_instBEqOption_beq___at___00__private_Std_Async_Watchdog_0__Std_Async_Watchdog_settle_spec__0(v_x_368_, v_x_369_);
lean_dec(v_x_369_);
lean_dec(v_x_368_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_settle(lean_object* v_wd_374_){
_start:
{
lean_object* v_ctx_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v_token_379_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_ctx_376_ = lean_ctor_get(v_wd_374_, 0);
lean_inc_ref_n(v_ctx_376_, 2);
lean_dec_ref(v_wd_374_);
v___x_377_ = lean_box(0);
v___x_378_ = l_Std_CancellationContext_cancel(v_ctx_376_, v___x_377_);
v_token_379_ = lean_ctor_get(v_ctx_376_, 1);
lean_inc_ref(v_token_379_);
lean_dec_ref(v_ctx_376_);
v___x_380_ = l_Std_CancellationToken_getCancellationReason(v_token_379_);
v___x_381_ = ((lean_object*)(l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_settle___closed__0));
v___x_382_ = l_instBEqOption_beq___at___00__private_Std_Async_Watchdog_0__Std_Async_Watchdog_settle_spec__0(v___x_380_, v___x_381_);
lean_dec(v___x_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_settle___boxed(lean_object* v_wd_383_, lean_object* v_a_384_){
_start:
{
uint8_t v_res_385_; lean_object* v_r_386_; 
v_res_385_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_settle(v_wd_383_);
v_r_386_ = lean_box(v_res_385_);
return v_r_386_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Watchdog_disarm(lean_object* v_wd_387_){
_start:
{
lean_object* v___x_389_; lean_object* v_state_390_; lean_object* v___x_391_; uint8_t v_fst_393_; lean_object* v_snd_394_; uint8_t v_waiting_397_; lean_object* v_deadline_398_; uint8_t v_fired_399_; lean_object* v_scheduled_400_; lean_object* v_epoch_401_; uint8_t v___y_403_; uint8_t v___x_407_; 
v___x_389_ = lean_io_mono_ms_now();
v_state_390_ = lean_ctor_get(v_wd_387_, 1);
v___x_391_ = lean_st_ref_take(v_state_390_);
v_waiting_397_ = lean_ctor_get_uint8(v___x_391_, sizeof(void*)*3);
v_deadline_398_ = lean_ctor_get(v___x_391_, 0);
v_fired_399_ = lean_ctor_get_uint8(v___x_391_, sizeof(void*)*3 + 1);
v_scheduled_400_ = lean_ctor_get(v___x_391_, 1);
v_epoch_401_ = lean_ctor_get(v___x_391_, 2);
v___x_407_ = 1;
if (v_fired_399_ == 0)
{
lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_416_; 
lean_inc(v_epoch_401_);
lean_inc(v_scheduled_400_);
lean_inc(v_deadline_398_);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_416_ == 0)
{
lean_object* v_unused_417_; lean_object* v_unused_418_; lean_object* v_unused_419_; 
v_unused_417_ = lean_ctor_get(v___x_391_, 2);
lean_dec(v_unused_417_);
v_unused_418_ = lean_ctor_get(v___x_391_, 1);
lean_dec(v_unused_418_);
v_unused_419_ = lean_ctor_get(v___x_391_, 0);
lean_dec(v_unused_419_);
v___x_409_ = v___x_391_;
v_isShared_410_ = v_isSharedCheck_416_;
goto v_resetjp_408_;
}
else
{
lean_dec(v___x_391_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_416_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
if (v_waiting_397_ == 0)
{
lean_del_object(v___x_409_);
lean_dec(v___x_389_);
v___y_403_ = v_fired_399_;
goto v___jp_402_;
}
else
{
uint8_t v___x_411_; 
v___x_411_ = lean_nat_dec_le(v_deadline_398_, v___x_389_);
lean_dec(v___x_389_);
if (v___x_411_ == 0)
{
lean_del_object(v___x_409_);
v___y_403_ = v___x_411_;
goto v___jp_402_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_414_; 
lean_dec(v_scheduled_400_);
v___x_412_ = lean_box(0);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 1, v___x_412_);
v___x_414_ = v___x_409_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_deadline_398_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_415_, 2, v_epoch_401_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_ctor_set_uint8(v___x_414_, sizeof(void*)*3, v_fired_399_);
lean_ctor_set_uint8(v___x_414_, sizeof(void*)*3 + 1, v___x_407_);
v_fst_393_ = v___x_407_;
v_snd_394_ = v___x_414_;
goto v___jp_392_;
}
}
}
}
}
else
{
lean_dec(v___x_389_);
v_fst_393_ = v___x_407_;
v_snd_394_ = v___x_391_;
goto v___jp_392_;
}
v___jp_392_:
{
lean_object* v___x_395_; 
v___x_395_ = lean_st_ref_put(v_state_390_, v_snd_394_);
if (v_fst_393_ == 0)
{
lean_dec_ref(v_wd_387_);
return v_fst_393_;
}
else
{
uint8_t v___x_396_; 
v___x_396_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_settle(v_wd_387_);
return v___x_396_;
}
}
v___jp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = lean_unsigned_to_nat(1u);
v___x_405_ = lean_nat_add(v_epoch_401_, v___x_404_);
lean_dec(v_epoch_401_);
v___x_406_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_406_, 0, v_deadline_398_);
lean_ctor_set(v___x_406_, 1, v_scheduled_400_);
lean_ctor_set(v___x_406_, 2, v___x_405_);
lean_ctor_set_uint8(v___x_406_, sizeof(void*)*3, v___y_403_);
lean_ctor_set_uint8(v___x_406_, sizeof(void*)*3 + 1, v_fired_399_);
v_fst_393_ = v___y_403_;
v_snd_394_ = v___x_406_;
goto v___jp_392_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_disarm___boxed(lean_object* v_wd_420_, lean_object* v_a_421_){
_start:
{
uint8_t v_res_422_; lean_object* v_r_423_; 
v_res_422_ = l_Std_Async_Watchdog_disarm(v_wd_420_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Watchdog_hasFired(lean_object* v_wd_424_){
_start:
{
lean_object* v_state_426_; lean_object* v___x_427_; uint8_t v_fired_428_; 
v_state_426_ = lean_ctor_get(v_wd_424_, 1);
v___x_427_ = lean_st_ref_get(v_state_426_);
v_fired_428_ = lean_ctor_get_uint8(v___x_427_, sizeof(void*)*3 + 1);
lean_dec(v___x_427_);
if (v_fired_428_ == 0)
{
lean_dec_ref(v_wd_424_);
return v_fired_428_;
}
else
{
uint8_t v___x_429_; 
v___x_429_ = l___private_Std_Async_Watchdog_0__Std_Async_Watchdog_settle(v_wd_424_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Watchdog_hasFired___boxed(lean_object* v_wd_430_, lean_object* v_a_431_){
_start:
{
uint8_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l_Std_Async_Watchdog_hasFired(v_wd_430_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_UV_Timer(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_CancellationContext(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_Watchdog(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_UV_Timer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_CancellationContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Async_Watchdog(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_UV_Timer(uint8_t builtin);
lean_object* initialize_Std_Sync_CancellationContext(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Async_Watchdog(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV_Timer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_CancellationContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_Watchdog(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Async_Watchdog(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Async_Watchdog(builtin);
}
#ifdef __cplusplus
}
#endif
