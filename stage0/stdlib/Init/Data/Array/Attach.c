// Lean compiler output
// Module: Init.Data.Array.Attach
// Imports: import all Init.Data.List.Attach public import Init.Data.Array.Lemmas import Init.Data.Array.Bootstrap import Init.Data.Array.Count
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
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Array_pmap_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_pmap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_pmap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Array_pmap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_attach___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_attach___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_attach(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_attach___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_pmapImpl___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Array_pmapImpl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_pmapImpl___redArg___closed__0 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__0_value;
static const lean_closure_object l_Array_pmapImpl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_pmapImpl___redArg___closed__1 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__1_value;
static const lean_closure_object l_Array_pmapImpl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_pmapImpl___redArg___closed__2 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__2_value;
static const lean_closure_object l_Array_pmapImpl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_pmapImpl___redArg___closed__3 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__3_value;
static const lean_closure_object l_Array_pmapImpl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_pmapImpl___redArg___closed__4 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__4_value;
static const lean_closure_object l_Array_pmapImpl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_pmapImpl___redArg___closed__5 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__5_value;
static const lean_closure_object l_Array_pmapImpl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_pmapImpl___redArg___closed__6 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__6_value;
static const lean_ctor_object l_Array_pmapImpl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_pmapImpl___redArg___closed__0_value),((lean_object*)&l_Array_pmapImpl___redArg___closed__1_value)}};
static const lean_object* l_Array_pmapImpl___redArg___closed__7 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__7_value;
static const lean_ctor_object l_Array_pmapImpl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_pmapImpl___redArg___closed__7_value),((lean_object*)&l_Array_pmapImpl___redArg___closed__2_value),((lean_object*)&l_Array_pmapImpl___redArg___closed__3_value),((lean_object*)&l_Array_pmapImpl___redArg___closed__4_value),((lean_object*)&l_Array_pmapImpl___redArg___closed__5_value)}};
static const lean_object* l_Array_pmapImpl___redArg___closed__8 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__8_value;
static const lean_ctor_object l_Array_pmapImpl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_pmapImpl___redArg___closed__8_value),((lean_object*)&l_Array_pmapImpl___redArg___closed__6_value)}};
static const lean_object* l_Array_pmapImpl___redArg___closed__9 = (const lean_object*)&l_Array_pmapImpl___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Array_pmapImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_pmapImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_unattach___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_unattach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Array_pmap_spec__0___redArg(lean_object* v_f_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
if (lean_obj_tag(v_a_2_) == 0)
{
lean_object* v___x_4_; 
lean_dec(v_f_1_);
v___x_4_ = l_List_reverse___redArg(v_a_3_);
return v___x_4_;
}
else
{
lean_object* v_head_5_; lean_object* v_tail_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_15_; 
v_head_5_ = lean_ctor_get(v_a_2_, 0);
v_tail_6_ = lean_ctor_get(v_a_2_, 1);
v_isSharedCheck_15_ = !lean_is_exclusive(v_a_2_);
if (v_isSharedCheck_15_ == 0)
{
v___x_8_ = v_a_2_;
v_isShared_9_ = v_isSharedCheck_15_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_tail_6_);
lean_inc(v_head_5_);
lean_dec(v_a_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_15_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; lean_object* v___x_12_; 
lean_inc(v_f_1_);
v___x_10_ = lean_apply_2(v_f_1_, v_head_5_, lean_box(0));
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_a_3_);
lean_ctor_set(v___x_8_, 0, v___x_10_);
v___x_12_ = v___x_8_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v___x_10_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v_a_3_);
v___x_12_ = v_reuseFailAlloc_14_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
v_a_2_ = v_tail_6_;
v_a_3_ = v___x_12_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_pmap___redArg(lean_object* v_f_16_, lean_object* v_xs_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_18_ = lean_array_to_list(v_xs_17_);
v___x_19_ = lean_box(0);
v___x_20_ = l_List_mapTR_loop___at___00Array_pmap_spec__0___redArg(v_f_16_, v___x_18_, v___x_19_);
v___x_21_ = lean_array_mk(v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Array_pmap(lean_object* v_00_u03b1_22_, lean_object* v_00_u03b2_23_, lean_object* v_P_24_, lean_object* v_f_25_, lean_object* v_xs_26_, lean_object* v_H_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Array_pmap___redArg(v_f_25_, v_xs_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Array_pmap_spec__0(lean_object* v_00_u03b1_29_, lean_object* v_00_u03b2_30_, lean_object* v_f_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_List_mapTR_loop___at___00Array_pmap_spec__0___redArg(v_f_31_, v_a_32_, v_a_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___redArg(lean_object* v_xs_35_){
_start:
{
lean_inc_ref(v_xs_35_);
return v_xs_35_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___redArg___boxed(lean_object* v_xs_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___redArg(v_xs_36_);
lean_dec_ref(v_xs_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl(lean_object* v_00_u03b1_38_, lean_object* v_xs_39_, lean_object* v_P_40_, lean_object* v_x_41_){
_start:
{
lean_inc_ref(v_xs_39_);
return v_xs_39_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Attach_0__Array_attachWithImpl___boxed(lean_object* v_00_u03b1_42_, lean_object* v_xs_43_, lean_object* v_P_44_, lean_object* v_x_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l___private_Init_Data_Array_Attach_0__Array_attachWithImpl(v_00_u03b1_42_, v_xs_43_, v_P_44_, v_x_45_);
lean_dec_ref(v_xs_43_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Array_attach___redArg(lean_object* v_xs_47_){
_start:
{
lean_inc_ref(v_xs_47_);
return v_xs_47_;
}
}
LEAN_EXPORT lean_object* l_Array_attach___redArg___boxed(lean_object* v_xs_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Array_attach___redArg(v_xs_48_);
lean_dec_ref(v_xs_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Array_attach(lean_object* v_00_u03b1_50_, lean_object* v_xs_51_){
_start:
{
lean_inc_ref(v_xs_51_);
return v_xs_51_;
}
}
LEAN_EXPORT lean_object* l_Array_attach___boxed(lean_object* v_00_u03b1_52_, lean_object* v_xs_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Array_attach(v_00_u03b1_52_, v_xs_53_);
lean_dec_ref(v_xs_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Array_pmapImpl___redArg___lam__0(lean_object* v_f_55_, lean_object* v_x_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_apply_2(v_f_55_, v_x_56_, lean_box(0));
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Array_pmapImpl___redArg(lean_object* v_f_77_, lean_object* v_xs_78_){
_start:
{
lean_object* v___f_79_; lean_object* v___x_80_; size_t v_sz_81_; size_t v___x_82_; lean_object* v___x_83_; 
v___f_79_ = lean_alloc_closure((void*)(l_Array_pmapImpl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_79_, 0, v_f_77_);
v___x_80_ = ((lean_object*)(l_Array_pmapImpl___redArg___closed__9));
v_sz_81_ = lean_array_size(v_xs_78_);
v___x_82_ = ((size_t)0ULL);
v___x_83_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_80_, v___f_79_, v_sz_81_, v___x_82_, v_xs_78_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Array_pmapImpl(lean_object* v_00_u03b1_84_, lean_object* v_00_u03b2_85_, lean_object* v_P_86_, lean_object* v_f_87_, lean_object* v_xs_88_, lean_object* v_H_89_){
_start:
{
lean_object* v___f_90_; lean_object* v___x_91_; size_t v_sz_92_; size_t v___x_93_; lean_object* v___x_94_; 
v___f_90_ = lean_alloc_closure((void*)(l_Array_pmapImpl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_90_, 0, v_f_87_);
v___x_91_ = ((lean_object*)(l_Array_pmapImpl___redArg___closed__9));
v_sz_92_ = lean_array_size(v_xs_88_);
v___x_93_ = ((size_t)0ULL);
v___x_94_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_91_, v___f_90_, v_sz_92_, v___x_93_, v_xs_88_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(size_t v_sz_95_, size_t v_i_96_, lean_object* v_bs_97_){
_start:
{
uint8_t v___x_98_; 
v___x_98_ = lean_usize_dec_lt(v_i_96_, v_sz_95_);
if (v___x_98_ == 0)
{
return v_bs_97_;
}
else
{
lean_object* v_v_99_; lean_object* v___x_100_; lean_object* v_bs_x27_101_; size_t v___x_102_; size_t v___x_103_; lean_object* v___x_104_; 
v_v_99_ = lean_array_uget(v_bs_97_, v_i_96_);
v___x_100_ = lean_unsigned_to_nat(0u);
v_bs_x27_101_ = lean_array_uset(v_bs_97_, v_i_96_, v___x_100_);
v___x_102_ = ((size_t)1ULL);
v___x_103_ = lean_usize_add(v_i_96_, v___x_102_);
v___x_104_ = lean_array_uset(v_bs_x27_101_, v_i_96_, v_v_99_);
v_i_96_ = v___x_103_;
v_bs_97_ = v___x_104_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg___boxed(lean_object* v_sz_106_, lean_object* v_i_107_, lean_object* v_bs_108_){
_start:
{
size_t v_sz_boxed_109_; size_t v_i_boxed_110_; lean_object* v_res_111_; 
v_sz_boxed_109_ = lean_unbox_usize(v_sz_106_);
lean_dec(v_sz_106_);
v_i_boxed_110_ = lean_unbox_usize(v_i_107_);
lean_dec(v_i_107_);
v_res_111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(v_sz_boxed_109_, v_i_boxed_110_, v_bs_108_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Array_unattach___redArg(lean_object* v_xs_112_){
_start:
{
size_t v_sz_113_; size_t v___x_114_; lean_object* v___x_115_; 
v_sz_113_ = lean_array_size(v_xs_112_);
v___x_114_ = ((size_t)0ULL);
v___x_115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(v_sz_113_, v___x_114_, v_xs_112_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Array_unattach(lean_object* v_00_u03b1_116_, lean_object* v_p_117_, lean_object* v_xs_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Array_unattach___redArg(v_xs_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0(lean_object* v_00_u03b1_120_, size_t v_sz_121_, size_t v_i_122_, lean_object* v_bs_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(v_sz_121_, v_i_122_, v_bs_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___boxed(lean_object* v_00_u03b1_125_, lean_object* v_sz_126_, lean_object* v_i_127_, lean_object* v_bs_128_){
_start:
{
size_t v_sz_boxed_129_; size_t v_i_boxed_130_; lean_object* v_res_131_; 
v_sz_boxed_129_ = lean_unbox_usize(v_sz_126_);
lean_dec(v_sz_126_);
v_i_boxed_130_ = lean_unbox_usize(v_i_127_);
lean_dec(v_i_127_);
v_res_131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0(v_00_u03b1_125_, v_sz_boxed_129_, v_i_boxed_130_, v_bs_128_);
return v_res_131_;
}
}
lean_object* runtime_initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Count(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Attach(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Attach(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Count(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Attach(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Attach(builtin);
}
#ifdef __cplusplus
}
#endif
