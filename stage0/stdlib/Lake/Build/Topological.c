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
uint8_t l_Lake_recFetchAcyclic___redArg___lam__2(lean_object* v_inst_25_, lean_object* v___x_26_, uint8_t v___x_27_, lean_object* v_x_28_){
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
LEAN_EXPORT void l_Lake_recFetchAcyclic___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_25_ = stack[0].m_obj;
lean_object* v___x_26_ = stack[1].m_obj;
uint8_t v___x_27_ = stack[2].m_num;
lean_object* v_x_28_ = stack[3].m_obj;
uint8_t v_res_32_;
v_res_32_ = l_Lake_recFetchAcyclic___redArg___lam__2(v_inst_25_, v___x_26_, v___x_27_, v_x_28_);
stack->m_num = v_res_32_;
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__2___boxed(lean_object* v_inst_33_, lean_object* v___x_34_, lean_object* v___x_35_, lean_object* v_x_36_){
_start:
{
uint8_t v___x_146__boxed_37_; uint8_t v_res_38_; lean_object* v_r_39_; 
v___x_146__boxed_37_ = lean_unbox(v___x_35_);
v_res_38_ = l_Lake_recFetchAcyclic___redArg___lam__2(v_inst_33_, v___x_34_, v___x_146__boxed_37_, v_x_36_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__3(lean_object* v_inst_42_, lean_object* v___x_43_, lean_object* v_withCallStack_44_, lean_object* v___x_45_, lean_object* v_throwCycle_46_, lean_object* v_parents_47_){
_start:
{
uint8_t v___x_48_; 
lean_inc(v_parents_47_);
lean_inc(v___x_43_);
lean_inc_ref(v_inst_42_);
v___x_48_ = l_List_elem___redArg(v_inst_42_, v___x_43_, v_parents_47_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_throwCycle_46_);
lean_dec_ref(v_inst_42_);
v___x_49_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_43_);
lean_ctor_set(v___x_49_, 1, v_parents_47_);
v___x_50_ = lean_apply_3(v_withCallStack_44_, lean_box(0), v___x_49_, v___x_45_);
return v___x_50_;
}
else
{
lean_object* v___x_51_; lean_object* v___f_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v_fst_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_66_; 
lean_dec(v___x_45_);
lean_dec(v_withCallStack_44_);
v___x_51_ = lean_box(v___x_48_);
lean_inc(v___x_43_);
v___f_52_ = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_52_, 0, v_inst_42_);
lean_closure_set(v___f_52_, 1, v___x_43_);
lean_closure_set(v___f_52_, 2, v___x_51_);
v___x_53_ = lean_box(0);
v___x_54_ = ((lean_object*)(l_Lake_recFetchAcyclic___redArg___lam__3___closed__0));
v___x_55_ = l_List_partition_loop___redArg(v___f_52_, v_parents_47_, v___x_54_);
v_fst_56_ = lean_ctor_get(v___x_55_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_55_);
if (v_isSharedCheck_66_ == 0)
{
lean_object* v_unused_67_; 
v_unused_67_ = lean_ctor_get(v___x_55_, 1);
lean_dec(v_unused_67_);
v___x_58_ = v___x_55_;
v_isShared_59_ = v_isSharedCheck_66_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_fst_56_);
lean_dec(v___x_55_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_66_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
lean_inc(v___x_43_);
if (v_isShared_59_ == 0)
{
lean_ctor_set_tag(v___x_58_, 1);
lean_ctor_set(v___x_58_, 1, v_fst_56_);
lean_ctor_set(v___x_58_, 0, v___x_43_);
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_43_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v_fst_56_);
v___x_61_ = v_reuseFailAlloc_65_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_43_);
lean_ctor_set(v___x_62_, 1, v___x_53_);
v___x_63_ = l_List_appendTR___redArg(v___x_61_, v___x_62_);
v___x_64_ = lean_apply_2(v_throwCycle_46_, lean_box(0), v___x_63_);
return v___x_64_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__4(lean_object* v_toMonadCallStack_68_, lean_object* v_fetch_69_, lean_object* v_keyOf_70_, lean_object* v_toBind_71_, lean_object* v_inst_72_, lean_object* v_throwCycle_73_, lean_object* v_a_74_, lean_object* v___y_75_){
_start:
{
lean_object* v_getCallStack_76_; lean_object* v_withCallStack_77_; lean_object* v___f_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___f_81_; lean_object* v___x_82_; 
v_getCallStack_76_ = lean_ctor_get(v_toMonadCallStack_68_, 0);
lean_inc_n(v_getCallStack_76_, 2);
v_withCallStack_77_ = lean_ctor_get(v_toMonadCallStack_68_, 1);
lean_inc_n(v_withCallStack_77_, 2);
lean_dec_ref(v_toMonadCallStack_68_);
lean_inc(v_a_74_);
v___f_78_ = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___redArg___lam__1), 5, 4);
lean_closure_set(v___f_78_, 0, v___y_75_);
lean_closure_set(v___f_78_, 1, v_withCallStack_77_);
lean_closure_set(v___f_78_, 2, v_fetch_69_);
lean_closure_set(v___f_78_, 3, v_a_74_);
v___x_79_ = lean_apply_1(v_keyOf_70_, v_a_74_);
lean_inc(v_toBind_71_);
v___x_80_ = lean_apply_4(v_toBind_71_, lean_box(0), lean_box(0), v_getCallStack_76_, v___f_78_);
v___f_81_ = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___redArg___lam__3), 6, 5);
lean_closure_set(v___f_81_, 0, v_inst_72_);
lean_closure_set(v___f_81_, 1, v___x_79_);
lean_closure_set(v___f_81_, 2, v_withCallStack_77_);
lean_closure_set(v___f_81_, 3, v___x_80_);
lean_closure_set(v___f_81_, 4, v_throwCycle_73_);
v___x_82_ = lean_apply_4(v_toBind_71_, lean_box(0), lean_box(0), v_getCallStack_76_, v___f_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg(lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_keyOf_86_, lean_object* v_fetch_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_toBind_89_; lean_object* v_toMonadCallStack_90_; lean_object* v_throwCycle_91_; lean_object* v___f_92_; lean_object* v___x_93_; 
v_toBind_89_ = lean_ctor_get(v_inst_84_, 1);
lean_inc(v_toBind_89_);
lean_dec_ref(v_inst_84_);
v_toMonadCallStack_90_ = lean_ctor_get(v_inst_85_, 0);
lean_inc_ref(v_toMonadCallStack_90_);
v_throwCycle_91_ = lean_ctor_get(v_inst_85_, 1);
lean_inc(v_throwCycle_91_);
lean_dec_ref(v_inst_85_);
v___f_92_ = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___redArg___lam__4), 8, 6);
lean_closure_set(v___f_92_, 0, v_toMonadCallStack_90_);
lean_closure_set(v___f_92_, 1, v_fetch_87_);
lean_closure_set(v___f_92_, 2, v_keyOf_86_);
lean_closure_set(v___f_92_, 3, v_toBind_89_);
lean_closure_set(v___f_92_, 4, v_inst_83_);
lean_closure_set(v___f_92_, 5, v_throwCycle_91_);
v___x_93_ = l_Lake_recFetch___redArg(v___f_92_, v_a_88_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic(lean_object* v_00_u03ba_94_, lean_object* v_m_95_, lean_object* v_00_u03b1_96_, lean_object* v_00_u03b2_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_keyOf_101_, lean_object* v_fetch_102_, lean_object* v_a_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lake_recFetchAcyclic___redArg(v_inst_98_, v_inst_99_, v_inst_100_, v_keyOf_101_, v_fetch_102_, v_a_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__0(lean_object* v_toApplicative_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_toPure_108_; lean_object* v___x_109_; 
v_toPure_108_ = lean_ctor_get(v_toApplicative_105_, 1);
lean_inc(v_toPure_108_);
lean_dec_ref(v_toApplicative_105_);
v___x_109_ = lean_apply_2(v_toPure_108_, lean_box(0), v_a_106_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__1(lean_object* v_toApplicative_110_, lean_object* v_store_111_, lean_object* v___x_112_, lean_object* v_toBind_113_, lean_object* v_a_114_){
_start:
{
lean_object* v___f_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
lean_inc(v_a_114_);
v___f_115_ = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___redArg___lam__0), 3, 2);
lean_closure_set(v___f_115_, 0, v_toApplicative_110_);
lean_closure_set(v___f_115_, 1, v_a_114_);
v___x_116_ = lean_apply_2(v_store_111_, v___x_112_, v_a_114_);
v___x_117_ = lean_apply_4(v_toBind_113_, lean_box(0), lean_box(0), v___x_116_, v___f_115_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__2(lean_object* v_compute_118_, lean_object* v_a_119_, lean_object* v___y_120_, lean_object* v_toBind_121_, lean_object* v___f_122_, lean_object* v_toApplicative_123_, lean_object* v_a_124_){
_start:
{
if (lean_obj_tag(v_a_124_) == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; 
lean_dec_ref(v_toApplicative_123_);
v___x_125_ = lean_apply_2(v_compute_118_, v_a_119_, v___y_120_);
v___x_126_ = lean_apply_4(v_toBind_121_, lean_box(0), lean_box(0), v___x_125_, v___f_122_);
return v___x_126_;
}
else
{
lean_object* v_val_127_; lean_object* v_toPure_128_; lean_object* v___x_129_; 
lean_dec(v___f_122_);
lean_dec(v_toBind_121_);
lean_dec(v___y_120_);
lean_dec(v_a_119_);
lean_dec(v_compute_118_);
v_val_127_ = lean_ctor_get(v_a_124_, 0);
lean_inc(v_val_127_);
lean_dec_ref_known(v_a_124_, 1);
v_toPure_128_ = lean_ctor_get(v_toApplicative_123_, 1);
lean_inc(v_toPure_128_);
lean_dec_ref(v_toApplicative_123_);
v___x_129_ = lean_apply_2(v_toPure_128_, lean_box(0), v_val_127_);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__3(lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_keyOf_132_, lean_object* v_compute_133_, lean_object* v_a_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_toApplicative_136_; lean_object* v_toBind_137_; lean_object* v_fetch_x3f_138_; lean_object* v_store_139_; lean_object* v___x_140_; lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_toApplicative_136_ = lean_ctor_get(v_inst_130_, 0);
lean_inc_ref_n(v_toApplicative_136_, 2);
v_toBind_137_ = lean_ctor_get(v_inst_130_, 1);
lean_inc_n(v_toBind_137_, 3);
lean_dec_ref(v_inst_130_);
v_fetch_x3f_138_ = lean_ctor_get(v_inst_131_, 0);
lean_inc(v_fetch_x3f_138_);
v_store_139_ = lean_ctor_get(v_inst_131_, 1);
lean_inc(v_store_139_);
lean_dec_ref(v_inst_131_);
lean_inc(v_a_134_);
v___x_140_ = lean_apply_1(v_keyOf_132_, v_a_134_);
lean_inc(v___x_140_);
v___f_141_ = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___redArg___lam__1), 5, 4);
lean_closure_set(v___f_141_, 0, v_toApplicative_136_);
lean_closure_set(v___f_141_, 1, v_store_139_);
lean_closure_set(v___f_141_, 2, v___x_140_);
lean_closure_set(v___f_141_, 3, v_toBind_137_);
v___f_142_ = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___redArg___lam__2), 7, 6);
lean_closure_set(v___f_142_, 0, v_compute_133_);
lean_closure_set(v___f_142_, 1, v_a_134_);
lean_closure_set(v___f_142_, 2, v___y_135_);
lean_closure_set(v___f_142_, 3, v_toBind_137_);
lean_closure_set(v___f_142_, 4, v___f_141_);
lean_closure_set(v___f_142_, 5, v_toApplicative_136_);
v___x_143_ = lean_apply_1(v_fetch_x3f_138_, v___x_140_);
v___x_144_ = lean_apply_4(v_toBind_137_, lean_box(0), lean_box(0), v___x_143_, v___f_142_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg(lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_keyOf_149_, lean_object* v_compute_150_, lean_object* v_a_151_){
_start:
{
lean_object* v___f_152_; lean_object* v___x_153_; 
lean_inc(v_keyOf_149_);
lean_inc_ref(v_inst_146_);
v___f_152_ = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___redArg___lam__3), 6, 4);
lean_closure_set(v___f_152_, 0, v_inst_146_);
lean_closure_set(v___f_152_, 1, v_inst_148_);
lean_closure_set(v___f_152_, 2, v_keyOf_149_);
lean_closure_set(v___f_152_, 3, v_compute_150_);
v___x_153_ = l_Lake_recFetchAcyclic___redArg(v_inst_145_, v_inst_146_, v_inst_147_, v_keyOf_149_, v___f_152_, v_a_151_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize(lean_object* v_00_u03ba_154_, lean_object* v_m_155_, lean_object* v_00_u03b2_156_, lean_object* v_00_u03b1_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_keyOf_162_, lean_object* v_compute_163_, lean_object* v_a_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lake_recFetchMemoize___redArg(v_inst_158_, v_inst_159_, v_inst_160_, v_inst_161_, v_keyOf_162_, v_compute_163_, v_a_164_);
return v___x_165_;
}
}
lean_object* runtime_initialize_Lake_Util_Cycle(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Store(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_EquipT(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Topological(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
