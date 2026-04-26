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
lean_dec_ref(v_x_10_);
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
lean_dec_ref(v_a_21_);
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
lean_object* v___y_51_; lean_object* v_val_52_; uint8_t v___y_59_; 
if (lean_obj_tag(v_addrFamily_48_) == 0)
{
uint8_t v___x_78_; 
v___x_78_ = 0;
v___y_59_ = v___x_78_;
goto v___jp_58_;
}
else
{
lean_object* v_val_79_; uint8_t v___x_80_; 
v_val_79_ = lean_ctor_get(v_addrFamily_48_, 0);
v___x_80_ = lean_unbox(v_val_79_);
if (v___x_80_ == 0)
{
uint8_t v___x_81_; 
v___x_81_ = 1;
v___y_59_ = v___x_81_;
goto v___jp_58_;
}
else
{
uint8_t v___x_82_; 
v___x_82_ = 2;
v___y_59_ = v___x_82_;
goto v___jp_58_;
}
}
v___jp_50_:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; lean_object* v___x_57_; 
v___x_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_53_, 0, v_val_52_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = 0;
lean_inc_ref(v___y_51_);
v___x_57_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_55_, v___x_56_, v___x_54_, v___y_51_);
return v___x_57_;
}
v___jp_58_:
{
lean_object* v___f_60_; lean_object* v___x_61_; 
v___f_60_ = ((lean_object*)(l_Std_Async_DNS_getAddrInfo___closed__2));
v___x_61_ = lean_uv_dns_get_info(v_host_46_, v_service_47_, v___y_59_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_69_; 
v_a_62_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_69_ == 0)
{
v___x_64_ = v___x_61_;
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_61_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
lean_ctor_set_tag(v___x_64_, 1);
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_a_62_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
v___y_51_ = v___f_60_;
v_val_52_ = v___x_67_;
goto v___jp_50_;
}
}
}
else
{
lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_77_; 
v_a_70_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_77_ == 0)
{
v___x_72_ = v___x_61_;
v_isShared_73_ = v_isSharedCheck_77_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___x_61_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_77_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_75_; 
if (v_isShared_73_ == 0)
{
lean_ctor_set_tag(v___x_72_, 0);
v___x_75_ = v___x_72_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_a_70_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
v___y_51_ = v___f_60_;
v_val_52_ = v___x_75_;
goto v___jp_50_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getAddrInfo___boxed(lean_object* v_host_83_, lean_object* v_service_84_, lean_object* v_addrFamily_85_, lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Std_Async_DNS_getAddrInfo(v_host_83_, v_service_84_, v_addrFamily_85_);
lean_dec(v_addrFamily_85_);
lean_dec_ref(v_service_84_);
lean_dec_ref(v_host_83_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__0(lean_object* v_host_88_, lean_object* v_service_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v_host_88_);
lean_ctor_set(v___x_90_, 1, v_service_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__1(lean_object* v___x_91_, lean_object* v_x_92_){
_start:
{
if (lean_obj_tag(v_x_92_) == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_mk_io_user_error(v___x_91_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
else
{
lean_object* v_val_95_; 
lean_dec_ref(v___x_91_);
v_val_95_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_val_95_);
return v_val_95_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__1___boxed(lean_object* v___x_96_, lean_object* v_x_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Std_Async_DNS_getNameInfo___lam__1(v___x_96_, v_x_97_);
lean_dec(v_x_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__2(lean_object* v___f_99_, lean_object* v_x_100_){
_start:
{
if (lean_obj_tag(v_x_100_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_110_; 
lean_dec_ref(v___f_99_);
v_a_102_ = lean_ctor_get(v_x_100_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v_x_100_);
if (v_isSharedCheck_110_ == 0)
{
v___x_104_ = v_x_100_;
v_isShared_105_ = v_isSharedCheck_110_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v_x_100_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_110_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_109_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_108_; 
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
}
else
{
lean_object* v_a_111_; 
v_a_111_ = lean_ctor_get(v_x_100_, 0);
lean_inc(v_a_111_);
lean_dec_ref(v_x_100_);
if (lean_obj_tag(v_a_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_120_; 
lean_dec_ref(v___f_99_);
v_a_112_ = lean_ctor_get(v_a_111_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v_a_111_);
if (v_isSharedCheck_120_ == 0)
{
v___x_114_ = v_a_111_;
v_isShared_115_ = v_isSharedCheck_120_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v_a_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_120_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_119_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; 
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
return v___x_118_;
}
}
}
else
{
lean_object* v_a_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_a_121_ = lean_ctor_get(v_a_111_, 0);
lean_inc(v_a_121_);
lean_dec_ref(v_a_111_);
v___x_122_ = lean_io_promise_result_opt(v_a_121_);
lean_dec(v_a_121_);
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = 0;
v___x_125_ = lean_task_map(v___f_99_, v___x_122_, v___x_123_, v___x_124_);
v___x_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
return v___x_126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___lam__2___boxed(lean_object* v___f_127_, lean_object* v_x_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Std_Async_DNS_getNameInfo___lam__2(v___f_127_, v_x_128_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo(lean_object* v_host_140_){
_start:
{
lean_object* v___y_143_; lean_object* v___f_145_; lean_object* v_val_147_; lean_object* v___x_189_; 
v___f_145_ = ((lean_object*)(l_Std_Async_DNS_getNameInfo___closed__3));
v___x_189_ = lean_uv_dns_get_name(v_host_140_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_189_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
lean_ctor_set_tag(v___x_192_, 1);
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
v_val_147_ = v___x_195_;
goto v___jp_146_;
}
}
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
v_a_198_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_189_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_189_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set_tag(v___x_200_, 0);
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
v_val_147_ = v___x_203_;
goto v___jp_146_;
}
}
}
v___jp_142_:
{
lean_object* v___x_144_; 
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___y_143_);
return v___x_144_;
}
v___jp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; lean_object* v___x_152_; 
v___x_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_148_, 0, v_val_147_);
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = 0;
v___x_152_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_150_, v___x_151_, v___x_149_, v___f_145_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_a_153_);
lean_dec_ref(v___x_152_);
if (lean_obj_tag(v_a_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v_a_154_ = lean_ctor_get(v_a_153_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v_a_153_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v_a_153_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v_a_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
v___y_143_ = v___x_159_;
goto v___jp_142_;
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_178_; 
v_a_162_ = lean_ctor_get(v_a_153_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v_a_153_);
if (v_isSharedCheck_178_ == 0)
{
v___x_164_ = v_a_153_;
v_isShared_165_ = v_isSharedCheck_178_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v_a_153_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_178_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v_fst_166_; lean_object* v_snd_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_177_; 
v_fst_166_ = lean_ctor_get(v_a_162_, 0);
v_snd_167_ = lean_ctor_get(v_a_162_, 1);
v_isSharedCheck_177_ = !lean_is_exclusive(v_a_162_);
if (v_isSharedCheck_177_ == 0)
{
v___x_169_ = v_a_162_;
v_isShared_170_ = v_isSharedCheck_177_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_snd_167_);
lean_inc(v_fst_166_);
lean_dec(v_a_162_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_177_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_fst_166_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_snd_167_);
v___x_172_ = v_reuseFailAlloc_176_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_174_; 
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_172_);
v___x_174_ = v___x_164_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
v___y_143_ = v___x_174_;
goto v___jp_142_;
}
}
}
}
}
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_188_; 
v_a_179_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_188_ == 0)
{
v___x_181_ = v___x_152_;
v_isShared_182_ = v_isSharedCheck_188_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_152_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_188_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_183_ = ((lean_object*)(l_Std_Async_DNS_getNameInfo___closed__4));
v___x_184_ = lean_task_map(v___x_183_, v_a_179_, v___x_150_, v___x_151_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_184_);
v___x_186_ = v___x_181_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_DNS_getNameInfo___boxed(lean_object* v_host_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_Async_DNS_getNameInfo(v_host_206_);
lean_dec_ref(v_host_206_);
return v_res_208_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_UV(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Function(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_DNS(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
