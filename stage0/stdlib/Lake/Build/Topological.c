// Lean compiler output
// Module: Lake.Build.Topological
// Imports: public import Lake.Util.Cycle public import Lake.Util.Store public import Lake.Util.EquipT
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
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_partition_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_recFetchAcyclic___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lake_recFetchAcyclic___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_recFetchAcyclic___redArg___lam__3___closed__0 = (const lean_object*)&l_Lake_recFetchAcyclic___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___redArg(lean_object* v_fetch_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
lean_inc(v_fetch_1_);
v___x_3_ = lean_alloc_closure((void*)(l_Lake_recFetch___redArg), 2, 1);
lean_closure_set(v___x_3_, 0, v_fetch_1_);
v___x_4_ = lean_apply_2(v_fetch_1_, v_a_2_, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch(lean_object* v_m_5_, lean_object* v_00_u03b1_6_, lean_object* v_00_u03b2_7_, lean_object* v_inst_8_, lean_object* v_fetch_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Lake_recFetch___redArg(v_fetch_9_, v_a_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__0(lean_object* v___y_12_, lean_object* v_withCallStack_13_, lean_object* v_stack_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_apply_1(v___y_12_, v_a_15_);
v___x_17_ = lean_apply_3(v_withCallStack_13_, lean_box(0), v_stack_14_, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__1(lean_object* v___y_18_, lean_object* v_withCallStack_19_, lean_object* v_fetch_20_, lean_object* v_a_21_, lean_object* v_stack_22_){
_start:
{
lean_object* v___f_23_; lean_object* v___x_24_; 
v___f_23_ = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___redArg___lam__0), 4, 3);
lean_closure_set(v___f_23_, 0, v___y_18_);
lean_closure_set(v___f_23_, 1, v_withCallStack_19_);
lean_closure_set(v___f_23_, 2, v_stack_22_);
v___x_24_ = lean_apply_2(v_fetch_20_, v_a_21_, v___f_23_);
return v___x_24_;
}
}
LEAN_EXPORT uint8_t l_Lake_recFetchAcyclic___redArg___lam__2(lean_object* v_inst_25_, lean_object* v___x_26_, uint8_t v___x_27_, lean_object* v_x_28_){
_start:
{
lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_29_ = lean_apply_2(v_inst_25_, v_x_28_, v___x_26_);
v___x_30_ = lean_unbox(v___x_29_);
if (v___x_30_ == 0)
{
return v___x_27_;
}
else
{
uint8_t v___x_31_; 
v___x_31_ = 0;
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__2___boxed(lean_object* v_inst_32_, lean_object* v___x_33_, lean_object* v___x_34_, lean_object* v_x_35_){
_start:
{
uint8_t v___x_136__boxed_36_; uint8_t v_res_37_; lean_object* v_r_38_; 
v___x_136__boxed_36_ = lean_unbox(v___x_34_);
v_res_37_ = l_Lake_recFetchAcyclic___redArg___lam__2(v_inst_32_, v___x_33_, v___x_136__boxed_36_, v_x_35_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__3(lean_object* v_inst_41_, lean_object* v___x_42_, lean_object* v_withCallStack_43_, lean_object* v___x_44_, lean_object* v_throwCycle_45_, lean_object* v_parents_46_){
_start:
{
uint8_t v___x_47_; 
lean_inc(v_parents_46_);
lean_inc(v___x_42_);
lean_inc_ref(v_inst_41_);
v___x_47_ = l_List_elem___redArg(v_inst_41_, v___x_42_, v_parents_46_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_throwCycle_45_);
lean_dec_ref(v_inst_41_);
v___x_48_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_42_);
lean_ctor_set(v___x_48_, 1, v_parents_46_);
v___x_49_ = lean_apply_3(v_withCallStack_43_, lean_box(0), v___x_48_, v___x_44_);
return v___x_49_;
}
else
{
lean_object* v___x_50_; lean_object* v___f_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v_fst_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_65_; 
lean_dec(v___x_44_);
lean_dec(v_withCallStack_43_);
v___x_50_ = lean_box(v___x_47_);
lean_inc(v___x_42_);
v___f_51_ = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_51_, 0, v_inst_41_);
lean_closure_set(v___f_51_, 1, v___x_42_);
lean_closure_set(v___f_51_, 2, v___x_50_);
v___x_52_ = lean_box(0);
v___x_53_ = ((lean_object*)(l_Lake_recFetchAcyclic___redArg___lam__3___closed__0));
v___x_54_ = l_List_partition_loop___redArg(v___f_51_, v_parents_46_, v___x_53_);
v_fst_55_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_65_ == 0)
{
lean_object* v_unused_66_; 
v_unused_66_ = lean_ctor_get(v___x_54_, 1);
lean_dec(v_unused_66_);
v___x_57_ = v___x_54_;
v_isShared_58_ = v_isSharedCheck_65_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_fst_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_65_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_60_; 
lean_inc(v___x_42_);
if (v_isShared_58_ == 0)
{
lean_ctor_set_tag(v___x_57_, 1);
lean_ctor_set(v___x_57_, 1, v_fst_55_);
lean_ctor_set(v___x_57_, 0, v___x_42_);
v___x_60_ = v___x_57_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_42_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_fst_55_);
v___x_60_ = v_reuseFailAlloc_64_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_42_);
lean_ctor_set(v___x_61_, 1, v___x_52_);
v___x_62_ = l_List_appendTR___redArg(v___x_60_, v___x_61_);
v___x_63_ = lean_apply_2(v_throwCycle_45_, lean_box(0), v___x_62_);
return v___x_63_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__4(lean_object* v_toMonadCallStack_67_, lean_object* v_fetch_68_, lean_object* v_keyOf_69_, lean_object* v_toBind_70_, lean_object* v_inst_71_, lean_object* v_throwCycle_72_, lean_object* v_a_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_getCallStack_75_; lean_object* v_withCallStack_76_; lean_object* v___f_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___f_80_; lean_object* v___x_81_; 
v_getCallStack_75_ = lean_ctor_get(v_toMonadCallStack_67_, 0);
lean_inc(v_getCallStack_75_);
v_withCallStack_76_ = lean_ctor_get(v_toMonadCallStack_67_, 1);
lean_inc(v_withCallStack_76_);
lean_dec_ref(v_toMonadCallStack_67_);
lean_inc(v_a_73_);
lean_inc(v_withCallStack_76_);
v___f_77_ = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___redArg___lam__1), 5, 4);
lean_closure_set(v___f_77_, 0, v___y_74_);
lean_closure_set(v___f_77_, 1, v_withCallStack_76_);
lean_closure_set(v___f_77_, 2, v_fetch_68_);
lean_closure_set(v___f_77_, 3, v_a_73_);
v___x_78_ = lean_apply_1(v_keyOf_69_, v_a_73_);
lean_inc(v_toBind_70_);
lean_inc(v_getCallStack_75_);
v___x_79_ = lean_apply_4(v_toBind_70_, lean_box(0), lean_box(0), v_getCallStack_75_, v___f_77_);
v___f_80_ = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___redArg___lam__3), 6, 5);
lean_closure_set(v___f_80_, 0, v_inst_71_);
lean_closure_set(v___f_80_, 1, v___x_78_);
lean_closure_set(v___f_80_, 2, v_withCallStack_76_);
lean_closure_set(v___f_80_, 3, v___x_79_);
lean_closure_set(v___f_80_, 4, v_throwCycle_72_);
v___x_81_ = lean_apply_4(v_toBind_70_, lean_box(0), lean_box(0), v_getCallStack_75_, v___f_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg(lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_keyOf_85_, lean_object* v_fetch_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_toBind_88_; lean_object* v_toMonadCallStack_89_; lean_object* v_throwCycle_90_; lean_object* v___f_91_; lean_object* v___x_92_; 
v_toBind_88_ = lean_ctor_get(v_inst_83_, 1);
lean_inc(v_toBind_88_);
lean_dec_ref(v_inst_83_);
v_toMonadCallStack_89_ = lean_ctor_get(v_inst_84_, 0);
lean_inc_ref(v_toMonadCallStack_89_);
v_throwCycle_90_ = lean_ctor_get(v_inst_84_, 1);
lean_inc(v_throwCycle_90_);
lean_dec_ref(v_inst_84_);
v___f_91_ = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___redArg___lam__4), 8, 6);
lean_closure_set(v___f_91_, 0, v_toMonadCallStack_89_);
lean_closure_set(v___f_91_, 1, v_fetch_86_);
lean_closure_set(v___f_91_, 2, v_keyOf_85_);
lean_closure_set(v___f_91_, 3, v_toBind_88_);
lean_closure_set(v___f_91_, 4, v_inst_82_);
lean_closure_set(v___f_91_, 5, v_throwCycle_90_);
v___x_92_ = l_Lake_recFetch___redArg(v___f_91_, v_a_87_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic(lean_object* v_00_u03ba_93_, lean_object* v_m_94_, lean_object* v_00_u03b1_95_, lean_object* v_00_u03b2_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_keyOf_100_, lean_object* v_fetch_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lake_recFetchAcyclic___redArg(v_inst_97_, v_inst_98_, v_inst_99_, v_keyOf_100_, v_fetch_101_, v_a_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__0(lean_object* v_toApplicative_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v_toPure_107_; lean_object* v___x_108_; 
v_toPure_107_ = lean_ctor_get(v_toApplicative_104_, 1);
lean_inc(v_toPure_107_);
lean_dec_ref(v_toApplicative_104_);
v___x_108_ = lean_apply_2(v_toPure_107_, lean_box(0), v_a_105_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__1(lean_object* v_toApplicative_109_, lean_object* v_store_110_, lean_object* v___x_111_, lean_object* v_toBind_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
lean_inc(v_a_113_);
v___f_114_ = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___redArg___lam__0), 3, 2);
lean_closure_set(v___f_114_, 0, v_toApplicative_109_);
lean_closure_set(v___f_114_, 1, v_a_113_);
v___x_115_ = lean_apply_2(v_store_110_, v___x_111_, v_a_113_);
v___x_116_ = lean_apply_4(v_toBind_112_, lean_box(0), lean_box(0), v___x_115_, v___f_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__2(lean_object* v_compute_117_, lean_object* v_a_118_, lean_object* v___y_119_, lean_object* v_toBind_120_, lean_object* v___f_121_, lean_object* v_toApplicative_122_, lean_object* v_a_123_){
_start:
{
if (lean_obj_tag(v_a_123_) == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_dec_ref(v_toApplicative_122_);
v___x_124_ = lean_apply_2(v_compute_117_, v_a_118_, v___y_119_);
v___x_125_ = lean_apply_4(v_toBind_120_, lean_box(0), lean_box(0), v___x_124_, v___f_121_);
return v___x_125_;
}
else
{
lean_object* v_val_126_; lean_object* v_toPure_127_; lean_object* v___x_128_; 
lean_dec(v___f_121_);
lean_dec(v_toBind_120_);
lean_dec(v___y_119_);
lean_dec(v_a_118_);
lean_dec(v_compute_117_);
v_val_126_ = lean_ctor_get(v_a_123_, 0);
lean_inc(v_val_126_);
lean_dec_ref(v_a_123_);
v_toPure_127_ = lean_ctor_get(v_toApplicative_122_, 1);
lean_inc(v_toPure_127_);
lean_dec_ref(v_toApplicative_122_);
v___x_128_ = lean_apply_2(v_toPure_127_, lean_box(0), v_val_126_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__3(lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_keyOf_131_, lean_object* v_compute_132_, lean_object* v_a_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_toApplicative_135_; lean_object* v_toBind_136_; lean_object* v_fetch_x3f_137_; lean_object* v_store_138_; lean_object* v___x_139_; lean_object* v___f_140_; lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_toApplicative_135_ = lean_ctor_get(v_inst_129_, 0);
lean_inc_ref(v_toApplicative_135_);
v_toBind_136_ = lean_ctor_get(v_inst_129_, 1);
lean_inc(v_toBind_136_);
lean_dec_ref(v_inst_129_);
v_fetch_x3f_137_ = lean_ctor_get(v_inst_130_, 0);
lean_inc(v_fetch_x3f_137_);
v_store_138_ = lean_ctor_get(v_inst_130_, 1);
lean_inc(v_store_138_);
lean_dec_ref(v_inst_130_);
lean_inc(v_a_133_);
v___x_139_ = lean_apply_1(v_keyOf_131_, v_a_133_);
lean_inc(v_toBind_136_);
lean_inc(v___x_139_);
lean_inc_ref(v_toApplicative_135_);
v___f_140_ = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___redArg___lam__1), 5, 4);
lean_closure_set(v___f_140_, 0, v_toApplicative_135_);
lean_closure_set(v___f_140_, 1, v_store_138_);
lean_closure_set(v___f_140_, 2, v___x_139_);
lean_closure_set(v___f_140_, 3, v_toBind_136_);
lean_inc(v_toBind_136_);
v___f_141_ = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___redArg___lam__2), 7, 6);
lean_closure_set(v___f_141_, 0, v_compute_132_);
lean_closure_set(v___f_141_, 1, v_a_133_);
lean_closure_set(v___f_141_, 2, v___y_134_);
lean_closure_set(v___f_141_, 3, v_toBind_136_);
lean_closure_set(v___f_141_, 4, v___f_140_);
lean_closure_set(v___f_141_, 5, v_toApplicative_135_);
v___x_142_ = lean_apply_1(v_fetch_x3f_137_, v___x_139_);
v___x_143_ = lean_apply_4(v_toBind_136_, lean_box(0), lean_box(0), v___x_142_, v___f_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg(lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_keyOf_148_, lean_object* v_compute_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___f_151_; lean_object* v___x_152_; 
lean_inc(v_keyOf_148_);
lean_inc_ref(v_inst_145_);
v___f_151_ = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___redArg___lam__3), 6, 4);
lean_closure_set(v___f_151_, 0, v_inst_145_);
lean_closure_set(v___f_151_, 1, v_inst_147_);
lean_closure_set(v___f_151_, 2, v_keyOf_148_);
lean_closure_set(v___f_151_, 3, v_compute_149_);
v___x_152_ = l_Lake_recFetchAcyclic___redArg(v_inst_144_, v_inst_145_, v_inst_146_, v_keyOf_148_, v___f_151_, v_a_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize(lean_object* v_00_u03ba_153_, lean_object* v_m_154_, lean_object* v_00_u03b2_155_, lean_object* v_00_u03b1_156_, lean_object* v_inst_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_keyOf_161_, lean_object* v_compute_162_, lean_object* v_a_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lake_recFetchMemoize___redArg(v_inst_157_, v_inst_158_, v_inst_159_, v_inst_160_, v_keyOf_161_, v_compute_162_, v_a_163_);
return v___x_164_;
}
}
lean_object* runtime_initialize_Lake_Util_Cycle(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Store(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_EquipT(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Topological(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Util_Cycle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Store(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_EquipT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Topological(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Util_Cycle(uint8_t builtin);
lean_object* initialize_Lake_Util_Store(uint8_t builtin);
lean_object* initialize_Lake_Util_EquipT(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Topological(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Cycle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Store(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_EquipT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Topological(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Topological(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Topological(builtin);
}
#ifdef __cplusplus
}
#endif
