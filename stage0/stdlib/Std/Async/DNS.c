// Lean compiler output
// Module: Std.Async.DNS
// Imports: public import Std.Time public import Std.Internal.UV public import Std.Async.Basic public import Init.Data.Function
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
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Function_uncurry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_uv_dns_get_info(lean_object*, lean_object*, uint8_t);
lean_object* lean_uv_dns_get_name(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_DNS_getAddrInfo___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_DNS_getAddrInfo___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_DNS_getAddrInfo___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_DNS_getAddrInfo___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Async_DNS_getAddrInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "the promise linked to the Async was dropped"};
static const lean_object* l_Std_Async_DNS_getAddrInfo___closed__0 = (const lean_object*)&l_Std_Async_DNS_getAddrInfo___closed__0_value;
static const lean_closure_object l_Std_Async_DNS_getAddrInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_DNS_getAddrInfo___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_DNS_getAddrInfo___closed__0_value)} };
static const lean_object* l_Std_Async_DNS_getAddrInfo___closed__1 = (const lean_object*)&l_Std_Async_DNS_getAddrInfo___closed__1_value;
static const lean_closure_object l_Std_Async_DNS_getAddrInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_DNS_getAddrInfo___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_DNS_getAddrInfo___closed__1_value)} };
static const lean_object* l_Std_Async_DNS_getAddrInfo___closed__2 = (const lean_object*)&l_Std_Async_DNS_getAddrInfo___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_DNS_getAddrInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_DNS_getAddrInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_DNS_getNameInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_DNS_getNameInfo___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_DNS_getNameInfo___closed__0 = (const lean_object*)&l_Std_Async_DNS_getNameInfo___closed__0_value;
static const lean_closure_object l_Std_Async_DNS_getNameInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_uncurry, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_DNS_getNameInfo___closed__0_value)} };
static const lean_object* l_Std_Async_DNS_getNameInfo___closed__1 = (const lean_object*)&l_Std_Async_DNS_getNameInfo___closed__1_value;
static const lean_closure_object l_Std_Async_DNS_getNameInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_DNS_getNameInfo___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_DNS_getAddrInfo___closed__0_value)} };
static const lean_object* l_Std_Async_DNS_getNameInfo___closed__2 = (const lean_object*)&l_Std_Async_DNS_getNameInfo___closed__2_value;
static const lean_closure_object l_Std_Async_DNS_getNameInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_DNS_getNameInfo___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_DNS_getNameInfo___closed__2_value)} };
static const lean_object* l_Std_Async_DNS_getNameInfo___closed__3 = (const lean_object*)&l_Std_Async_DNS_getNameInfo___closed__3_value;
static const lean_closure_object l_Std_Async_DNS_getNameInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_DNS_getNameInfo___closed__1_value)} };
static const lean_object* l_Std_Async_DNS_getNameInfo___closed__4 = (const lean_object*)&l_Std_Async_DNS_getNameInfo___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_DNS_getAddrInfo___lam__0(lean_object* v___x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_mk_io_user_error(v___x_1_);
v___x_4_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
return v___x_4_;
}
else
{
lean_object* v_val_5_; 
lean_dec_ref(v___x_1_);
v_val_5_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_val_5_);
return v_val_5_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getAddrInfo___lam__0___boxed(lean_object* v___x_6_, lean_object* v_x_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Std_Async_DNS_getAddrInfo___lam__0(v___x_6_, v_x_7_);
lean_dec(v_x_7_);
return v_res_8_;
}
}
lean_object* l_Std_Async_DNS_getAddrInfo___lam__1(lean_object* v___f_9_, lean_object* v_x_10_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v_a_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_20_; 
lean_dec_ref(v___f_9_);
v_a_12_ = lean_ctor_get(v_x_10_, 0);
v_isSharedCheck_20_ = !lean_is_exclusive(v_x_10_);
if (v_isSharedCheck_20_ == 0)
{
v___x_14_ = v_x_10_;
v_isShared_15_ = v_isSharedCheck_20_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_a_12_);
lean_dec(v_x_10_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_20_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_17_; 
if (v_isShared_15_ == 0)
{
v___x_17_ = v___x_14_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v_a_12_);
v___x_17_ = v_reuseFailAlloc_19_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
lean_object* v___x_18_; 
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
}
else
{
lean_object* v_a_21_; 
v_a_21_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_a_21_);
lean_dec_ref_known(v_x_10_, 1);
if (lean_obj_tag(v_a_21_) == 0)
{
lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_30_; 
lean_dec_ref(v___f_9_);
v_a_22_ = lean_ctor_get(v_a_21_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v_a_21_);
if (v_isSharedCheck_30_ == 0)
{
v___x_24_ = v_a_21_;
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_dec(v_a_21_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_a_22_);
v___x_27_ = v_reuseFailAlloc_29_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
lean_object* v___x_28_; 
v___x_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
return v___x_28_;
}
}
}
else
{
lean_object* v_a_31_; lean_object* v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_a_31_ = lean_ctor_get(v_a_21_, 0);
lean_inc(v_a_31_);
lean_dec_ref_known(v_a_21_, 1);
v___x_32_ = lean_io_promise_result_opt(v_a_31_);
lean_dec(v_a_31_);
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = 0;
v___x_35_ = lean_task_map(v___f_9_, v___x_32_, v___x_33_, v___x_34_);
v___x_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
return v___x_36_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_DNS_getAddrInfo___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_9_ = stack[0].m_obj;
lean_object* v_x_10_ = stack[1].m_obj;
lean_object* v_res_37_;
v_res_37_ = l_Std_Async_DNS_getAddrInfo___lam__1(v___f_9_, v_x_10_);
stack->m_obj
 = v_res_37_;
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getAddrInfo___lam__1___boxed(lean_object* v___f_38_, lean_object* v_x_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Std_Async_DNS_getAddrInfo___lam__1(v___f_38_, v_x_39_);
return v_res_41_;
}
}
lean_object* l_Std_Async_DNS_getAddrInfo(lean_object* v_host_47_, lean_object* v_service_48_, lean_object* v_addrFamily_49_){
_start:
{
lean_object* v___y_52_; lean_object* v___y_53_; uint8_t v___y_54_; lean_object* v_val_55_; uint8_t v___y_60_; 
if (lean_obj_tag(v_addrFamily_49_) == 0)
{
uint8_t v___x_81_; 
v___x_81_ = 0;
v___y_60_ = v___x_81_;
goto v___jp_59_;
}
else
{
lean_object* v_val_82_; uint8_t v___x_83_; 
v_val_82_ = lean_ctor_get(v_addrFamily_49_, 0);
v___x_83_ = lean_unbox(v_val_82_);
if (v___x_83_ == 0)
{
uint8_t v___x_84_; 
v___x_84_ = 1;
v___y_60_ = v___x_84_;
goto v___jp_59_;
}
else
{
uint8_t v___x_85_; 
v___x_85_ = 2;
v___y_60_ = v___x_85_;
goto v___jp_59_;
}
}
v___jp_51_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_56_, 0, v_val_55_);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_inc_ref(v___y_53_);
v___x_58_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_52_, v___y_54_, v___x_57_, v___y_53_);
return v___x_58_;
}
v___jp_59_:
{
lean_object* v___f_61_; lean_object* v___x_62_; uint8_t v___x_63_; lean_object* v___x_64_; 
v___f_61_ = ((lean_object*)(l_Std_Async_DNS_getAddrInfo___closed__2));
v___x_62_ = lean_unsigned_to_nat(0u);
v___x_63_ = 0;
v___x_64_ = lean_uv_dns_get_info(v_host_47_, v_service_48_, v___y_60_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_72_; 
v_a_65_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_72_ == 0)
{
v___x_67_ = v___x_64_;
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v___x_64_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_70_; 
if (v_isShared_68_ == 0)
{
lean_ctor_set_tag(v___x_67_, 1);
v___x_70_ = v___x_67_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_a_65_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
v___y_52_ = v___x_62_;
v___y_53_ = v___f_61_;
v___y_54_ = v___x_63_;
v_val_55_ = v___x_70_;
goto v___jp_51_;
}
}
}
else
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
v_a_73_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v___x_64_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_64_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
lean_ctor_set_tag(v___x_75_, 0);
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
v___y_52_ = v___x_62_;
v___y_53_ = v___f_61_;
v___y_54_ = v___x_63_;
v_val_55_ = v___x_78_;
goto v___jp_51_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_DNS_getAddrInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_host_47_ = stack[0].m_obj;
lean_object* v_service_48_ = stack[1].m_obj;
lean_object* v_addrFamily_49_ = stack[2].m_obj;
lean_object* v_res_86_;
v_res_86_ = l_Std_Async_DNS_getAddrInfo(v_host_47_, v_service_48_, v_addrFamily_49_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getAddrInfo___boxed(lean_object* v_host_87_, lean_object* v_service_88_, lean_object* v_addrFamily_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Std_Async_DNS_getAddrInfo(v_host_87_, v_service_88_, v_addrFamily_89_);
lean_dec(v_addrFamily_89_);
lean_dec_ref(v_service_88_);
lean_dec_ref(v_host_87_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__0(lean_object* v_host_92_, lean_object* v_service_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v_host_92_);
lean_ctor_set(v___x_94_, 1, v_service_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__1(lean_object* v___x_95_, lean_object* v_x_96_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_mk_io_user_error(v___x_95_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
else
{
lean_object* v_val_99_; 
lean_dec_ref(v___x_95_);
v_val_99_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_val_99_);
return v_val_99_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__1___boxed(lean_object* v___x_100_, lean_object* v_x_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_Async_DNS_getNameInfo___lam__1(v___x_100_, v_x_101_);
lean_dec(v_x_101_);
return v_res_102_;
}
}
lean_object* l_Std_Async_DNS_getNameInfo___lam__2(lean_object* v___f_103_, lean_object* v_x_104_){
_start:
{
if (lean_obj_tag(v_x_104_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_114_; 
lean_dec_ref(v___f_103_);
v_a_106_ = lean_ctor_get(v_x_104_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v_x_104_);
if (v_isSharedCheck_114_ == 0)
{
v___x_108_ = v_x_104_;
v_isShared_109_ = v_isSharedCheck_114_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v_x_104_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_114_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_113_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_112_; 
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
}
}
else
{
lean_object* v_a_115_; 
v_a_115_ = lean_ctor_get(v_x_104_, 0);
lean_inc(v_a_115_);
lean_dec_ref_known(v_x_104_, 1);
if (lean_obj_tag(v_a_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_124_; 
lean_dec_ref(v___f_103_);
v_a_116_ = lean_ctor_get(v_a_115_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v_a_115_);
if (v_isSharedCheck_124_ == 0)
{
v___x_118_ = v_a_115_;
v_isShared_119_ = v_isSharedCheck_124_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v_a_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_124_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_123_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v___x_122_; 
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
return v___x_122_;
}
}
}
else
{
lean_object* v_a_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_a_125_ = lean_ctor_get(v_a_115_, 0);
lean_inc(v_a_125_);
lean_dec_ref_known(v_a_115_, 1);
v___x_126_ = lean_io_promise_result_opt(v_a_125_);
lean_dec(v_a_125_);
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = 0;
v___x_129_ = lean_task_map(v___f_103_, v___x_126_, v___x_127_, v___x_128_);
v___x_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_DNS_getNameInfo___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_103_ = stack[0].m_obj;
lean_object* v_x_104_ = stack[1].m_obj;
lean_object* v_res_131_;
v_res_131_ = l_Std_Async_DNS_getNameInfo___lam__2(v___f_103_, v_x_104_);
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__2___boxed(lean_object* v___f_132_, lean_object* v_x_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Std_Async_DNS_getNameInfo___lam__2(v___f_132_, v_x_133_);
return v_res_135_;
}
}
lean_object* l_Std_Async_DNS_getNameInfo(lean_object* v_host_145_){
_start:
{
lean_object* v___y_148_; lean_object* v___f_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; lean_object* v_val_155_; lean_object* v___x_194_; 
v___f_150_ = ((lean_object*)(l_Std_Async_DNS_getNameInfo___closed__3));
v___x_151_ = ((lean_object*)(l_Std_Async_DNS_getNameInfo___closed__4));
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = 0;
v___x_194_ = lean_uv_dns_get_name(v_host_145_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
lean_ctor_set_tag(v___x_197_, 1);
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
v_val_155_ = v___x_200_;
goto v___jp_154_;
}
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
v_a_203_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_194_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_194_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
lean_ctor_set_tag(v___x_205_, 0);
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
v_val_155_ = v___x_208_;
goto v___jp_154_;
}
}
}
v___jp_147_:
{
lean_object* v___x_149_; 
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v___y_148_);
return v___x_149_;
}
v___jp_154_:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_156_, 0, v_val_155_);
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
v___x_158_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_152_, v___x_153_, v___x_157_, v___f_150_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v___x_158_, 1);
if (lean_obj_tag(v_a_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_a_160_ = lean_ctor_get(v_a_159_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v_a_159_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v_a_159_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v_a_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
v___y_148_ = v___x_165_;
goto v___jp_147_;
}
}
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_184_; 
v_a_168_ = lean_ctor_get(v_a_159_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v_a_159_);
if (v_isSharedCheck_184_ == 0)
{
v___x_170_ = v_a_159_;
v_isShared_171_ = v_isSharedCheck_184_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v_a_159_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_184_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v_fst_172_; lean_object* v_snd_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_183_; 
v_fst_172_ = lean_ctor_get(v_a_168_, 0);
v_snd_173_ = lean_ctor_get(v_a_168_, 1);
v_isSharedCheck_183_ = !lean_is_exclusive(v_a_168_);
if (v_isSharedCheck_183_ == 0)
{
v___x_175_ = v_a_168_;
v_isShared_176_ = v_isSharedCheck_183_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_snd_173_);
lean_inc(v_fst_172_);
lean_dec(v_a_168_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_183_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_fst_172_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_snd_173_);
v___x_178_ = v_reuseFailAlloc_182_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_180_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_178_);
v___x_180_ = v___x_170_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
v___y_148_ = v___x_180_;
goto v___jp_147_;
}
}
}
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_193_; 
v_a_185_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_193_ == 0)
{
v___x_187_ = v___x_158_;
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_158_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_189_ = lean_task_map(v___x_151_, v_a_185_, v___x_152_, v___x_153_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_189_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_DNS_getNameInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_host_145_ = stack[0].m_obj;
lean_object* v_res_211_;
v_res_211_ = l_Std_Async_DNS_getNameInfo(v_host_145_);
stack->m_obj
 = v_res_211_;
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___boxed(lean_object* v_host_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_Async_DNS_getNameInfo(v_host_212_);
lean_dec_ref(v_host_212_);
return v_res_214_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_UV(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Function(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_DNS(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_UV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Async_DNS(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_UV(uint8_t builtin);
lean_object* initialize_Std_Async_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Function(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Async_DNS(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_DNS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Async_DNS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Async_DNS(builtin);
}
#ifdef __cplusplus
}
#endif
