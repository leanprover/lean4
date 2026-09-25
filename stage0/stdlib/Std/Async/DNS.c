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
LEAN_EXPORT lean_object* l_Std_Async_DNS_getAddrInfo___lam__1(lean_object* v___f_9_, lean_object* v_x_10_){
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
LEAN_EXPORT lean_object* l_Std_Async_DNS_getAddrInfo___lam__1___boxed(lean_object* v___f_37_, lean_object* v_x_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Async_DNS_getAddrInfo___lam__1(v___f_37_, v_x_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getAddrInfo(lean_object* v_host_46_, lean_object* v_service_47_, lean_object* v_addrFamily_48_){
_start:
{
lean_object* v___y_51_; lean_object* v___y_52_; uint8_t v___y_53_; lean_object* v_val_54_; uint8_t v___y_59_; 
if (lean_obj_tag(v_addrFamily_48_) == 0)
{
uint8_t v___x_80_; 
v___x_80_ = 0;
v___y_59_ = v___x_80_;
goto v___jp_58_;
}
else
{
lean_object* v_val_81_; uint8_t v___x_82_; 
v_val_81_ = lean_ctor_get(v_addrFamily_48_, 0);
v___x_82_ = lean_unbox(v_val_81_);
if (v___x_82_ == 0)
{
uint8_t v___x_83_; 
v___x_83_ = 1;
v___y_59_ = v___x_83_;
goto v___jp_58_;
}
else
{
uint8_t v___x_84_; 
v___x_84_ = 2;
v___y_59_ = v___x_84_;
goto v___jp_58_;
}
}
v___jp_50_:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_55_, 0, v_val_54_);
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_inc_ref(v___y_52_);
v___x_57_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_51_, v___y_53_, v___x_56_, v___y_52_);
return v___x_57_;
}
v___jp_58_:
{
lean_object* v___f_60_; lean_object* v___x_61_; uint8_t v___x_62_; lean_object* v___x_63_; 
v___f_60_ = ((lean_object*)(l_Std_Async_DNS_getAddrInfo___closed__2));
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = 0;
v___x_63_ = lean_uv_dns_get_info(v_host_46_, v_service_47_, v___y_59_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_71_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_71_ == 0)
{
v___x_66_ = v___x_63_;
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___x_63_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_69_; 
if (v_isShared_67_ == 0)
{
lean_ctor_set_tag(v___x_66_, 1);
v___x_69_ = v___x_66_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_a_64_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
v___y_51_ = v___x_61_;
v___y_52_ = v___f_60_;
v___y_53_ = v___x_62_;
v_val_54_ = v___x_69_;
goto v___jp_50_;
}
}
}
else
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_79_; 
v_a_72_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_79_ == 0)
{
v___x_74_ = v___x_63_;
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___x_63_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_77_; 
if (v_isShared_75_ == 0)
{
lean_ctor_set_tag(v___x_74_, 0);
v___x_77_ = v___x_74_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_a_72_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
v___y_51_ = v___x_61_;
v___y_52_ = v___f_60_;
v___y_53_ = v___x_62_;
v_val_54_ = v___x_77_;
goto v___jp_50_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getAddrInfo___boxed(lean_object* v_host_85_, lean_object* v_service_86_, lean_object* v_addrFamily_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Std_Async_DNS_getAddrInfo(v_host_85_, v_service_86_, v_addrFamily_87_);
lean_dec(v_addrFamily_87_);
lean_dec_ref(v_service_86_);
lean_dec_ref(v_host_85_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__0(lean_object* v_host_90_, lean_object* v_service_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v_host_90_);
lean_ctor_set(v___x_92_, 1, v_service_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__1(lean_object* v___x_93_, lean_object* v_x_94_){
_start:
{
if (lean_obj_tag(v_x_94_) == 0)
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_mk_io_user_error(v___x_93_);
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
else
{
lean_object* v_val_97_; 
lean_dec_ref(v___x_93_);
v_val_97_ = lean_ctor_get(v_x_94_, 0);
lean_inc(v_val_97_);
return v_val_97_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__1___boxed(lean_object* v___x_98_, lean_object* v_x_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_Async_DNS_getNameInfo___lam__1(v___x_98_, v_x_99_);
lean_dec(v_x_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__2(lean_object* v___f_101_, lean_object* v_x_102_){
_start:
{
if (lean_obj_tag(v_x_102_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_112_; 
lean_dec_ref(v___f_101_);
v_a_104_ = lean_ctor_get(v_x_102_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v_x_102_);
if (v_isSharedCheck_112_ == 0)
{
v___x_106_ = v_x_102_;
v_isShared_107_ = v_isSharedCheck_112_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v_x_102_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_112_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_104_);
v___x_109_ = v_reuseFailAlloc_111_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; 
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
}
else
{
lean_object* v_a_113_; 
v_a_113_ = lean_ctor_get(v_x_102_, 0);
lean_inc(v_a_113_);
lean_dec_ref_known(v_x_102_, 1);
if (lean_obj_tag(v_a_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_122_; 
lean_dec_ref(v___f_101_);
v_a_114_ = lean_ctor_get(v_a_113_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v_a_113_);
if (v_isSharedCheck_122_ == 0)
{
v___x_116_ = v_a_113_;
v_isShared_117_ = v_isSharedCheck_122_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v_a_113_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_122_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_114_);
v___x_119_ = v_reuseFailAlloc_121_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_120_; 
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
return v___x_120_;
}
}
}
else
{
lean_object* v_a_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v_a_123_ = lean_ctor_get(v_a_113_, 0);
lean_inc(v_a_123_);
lean_dec_ref_known(v_a_113_, 1);
v___x_124_ = lean_io_promise_result_opt(v_a_123_);
lean_dec(v_a_123_);
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = 0;
v___x_127_ = lean_task_map(v___f_101_, v___x_124_, v___x_125_, v___x_126_);
v___x_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__2___boxed(lean_object* v___f_129_, lean_object* v_x_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Std_Async_DNS_getNameInfo___lam__2(v___f_129_, v_x_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo(lean_object* v_host_142_){
_start:
{
lean_object* v___y_145_; lean_object* v___f_147_; lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; lean_object* v_val_152_; lean_object* v___x_191_; 
v___f_147_ = ((lean_object*)(l_Std_Async_DNS_getNameInfo___closed__3));
v___x_148_ = ((lean_object*)(l_Std_Async_DNS_getNameInfo___closed__4));
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = 0;
v___x_191_ = lean_uv_dns_get_name(v_host_142_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_191_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
lean_ctor_set_tag(v___x_194_, 1);
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
v_val_152_ = v___x_197_;
goto v___jp_151_;
}
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
v_a_200_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_191_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_191_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
lean_ctor_set_tag(v___x_202_, 0);
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
v_val_152_ = v___x_205_;
goto v___jp_151_;
}
}
}
v___jp_144_:
{
lean_object* v___x_146_; 
v___x_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_146_, 0, v___y_145_);
return v___x_146_;
}
v___jp_151_:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_153_, 0, v_val_152_);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
v___x_155_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_149_, v___x_150_, v___x_154_, v___f_147_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_a_156_);
lean_dec_ref_known(v___x_155_, 1);
if (lean_obj_tag(v_a_156_) == 0)
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
v_a_157_ = lean_ctor_get(v_a_156_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v_a_156_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v_a_156_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v_a_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
v___y_145_ = v___x_162_;
goto v___jp_144_;
}
}
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_181_; 
v_a_165_ = lean_ctor_get(v_a_156_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v_a_156_);
if (v_isSharedCheck_181_ == 0)
{
v___x_167_ = v_a_156_;
v_isShared_168_ = v_isSharedCheck_181_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v_a_156_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_181_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v_fst_169_; lean_object* v_snd_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_180_; 
v_fst_169_ = lean_ctor_get(v_a_165_, 0);
v_snd_170_ = lean_ctor_get(v_a_165_, 1);
v_isSharedCheck_180_ = !lean_is_exclusive(v_a_165_);
if (v_isSharedCheck_180_ == 0)
{
v___x_172_ = v_a_165_;
v_isShared_173_ = v_isSharedCheck_180_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_snd_170_);
lean_inc(v_fst_169_);
lean_dec(v_a_165_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_180_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_fst_169_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_snd_170_);
v___x_175_ = v_reuseFailAlloc_179_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_177_; 
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_175_);
v___x_177_ = v___x_167_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
v___y_145_ = v___x_177_;
goto v___jp_144_;
}
}
}
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_190_; 
v_a_182_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_190_ == 0)
{
v___x_184_ = v___x_155_;
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_155_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_186_ = lean_task_map(v___x_148_, v_a_182_, v___x_149_, v___x_150_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_186_);
v___x_188_ = v___x_184_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___boxed(lean_object* v_host_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_Async_DNS_getNameInfo(v_host_208_);
lean_dec_ref(v_host_208_);
return v_res_210_;
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
