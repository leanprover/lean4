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
uint8_t lean_bool_not(uint8_t);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_partition_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_recFetchAcyclic___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lake_recFetchAcyclic___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_recFetchAcyclic___redArg___lam__3___closed__0 = (const lean_object*)&l_Lake_recFetchAcyclic___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lake_recFetchAcyclic___redArg___lam__2(lean_object* v_inst_25_, lean_object* v___x_26_, lean_object* v_x_27_){
_start:
{
lean_object* v___x_28_; uint8_t v___x_29_; uint8_t v___x_30_; 
v___x_28_ = lean_apply_2(v_inst_25_, v_x_27_, v___x_26_);
v___x_29_ = lean_unbox(v___x_28_);
v___x_30_ = lean_bool_not(v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__2___boxed(lean_object* v_inst_31_, lean_object* v___x_32_, lean_object* v_x_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Lake_recFetchAcyclic___redArg___lam__2(v_inst_31_, v___x_32_, v_x_33_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__3(lean_object* v_inst_38_, lean_object* v___x_39_, lean_object* v_withCallStack_40_, lean_object* v___x_41_, lean_object* v___f_42_, lean_object* v_throwCycle_43_, lean_object* v_parents_44_){
_start:
{
uint8_t v___x_45_; 
lean_inc(v_parents_44_);
lean_inc(v___x_39_);
v___x_45_ = l_List_elem___redArg(v_inst_38_, v___x_39_, v_parents_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; lean_object* v___x_47_; 
lean_dec(v_throwCycle_43_);
lean_dec_ref(v___f_42_);
v___x_46_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_39_);
lean_ctor_set(v___x_46_, 1, v_parents_44_);
v___x_47_ = lean_apply_3(v_withCallStack_40_, lean_box(0), v___x_46_, v___x_41_);
return v___x_47_;
}
else
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v_fst_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_61_; 
lean_dec(v___x_41_);
lean_dec(v_withCallStack_40_);
v___x_48_ = lean_box(0);
v___x_49_ = ((lean_object*)(l_Lake_recFetchAcyclic___redArg___lam__3___closed__0));
v___x_50_ = l_List_partition_loop___redArg(v___f_42_, v_parents_44_, v___x_49_);
v_fst_51_ = lean_ctor_get(v___x_50_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_61_ == 0)
{
lean_object* v_unused_62_; 
v_unused_62_ = lean_ctor_get(v___x_50_, 1);
lean_dec(v_unused_62_);
v___x_53_ = v___x_50_;
v_isShared_54_ = v_isSharedCheck_61_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_fst_51_);
lean_dec(v___x_50_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_61_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_56_; 
lean_inc(v___x_39_);
if (v_isShared_54_ == 0)
{
lean_ctor_set_tag(v___x_53_, 1);
lean_ctor_set(v___x_53_, 1, v_fst_51_);
lean_ctor_set(v___x_53_, 0, v___x_39_);
v___x_56_ = v___x_53_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_fst_51_);
v___x_56_ = v_reuseFailAlloc_60_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_39_);
lean_ctor_set(v___x_57_, 1, v___x_48_);
v___x_58_ = l_List_appendTR___redArg(v___x_56_, v___x_57_);
v___x_59_ = lean_apply_2(v_throwCycle_43_, lean_box(0), v___x_58_);
return v___x_59_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg___lam__4(lean_object* v_toMonadCallStack_63_, lean_object* v_fetch_64_, lean_object* v_keyOf_65_, lean_object* v_inst_66_, lean_object* v_toBind_67_, lean_object* v_throwCycle_68_, lean_object* v_a_69_, lean_object* v___y_70_){
_start:
{
lean_object* v_getCallStack_71_; lean_object* v_withCallStack_72_; lean_object* v___f_73_; lean_object* v___x_74_; lean_object* v___f_75_; lean_object* v___x_76_; lean_object* v___f_77_; lean_object* v___x_78_; 
v_getCallStack_71_ = lean_ctor_get(v_toMonadCallStack_63_, 0);
lean_inc_n(v_getCallStack_71_, 2);
v_withCallStack_72_ = lean_ctor_get(v_toMonadCallStack_63_, 1);
lean_inc_n(v_withCallStack_72_, 2);
lean_dec_ref(v_toMonadCallStack_63_);
lean_inc(v_a_69_);
v___f_73_ = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___redArg___lam__1), 5, 4);
lean_closure_set(v___f_73_, 0, v___y_70_);
lean_closure_set(v___f_73_, 1, v_withCallStack_72_);
lean_closure_set(v___f_73_, 2, v_fetch_64_);
lean_closure_set(v___f_73_, 3, v_a_69_);
v___x_74_ = lean_apply_1(v_keyOf_65_, v_a_69_);
lean_inc(v___x_74_);
lean_inc_ref(v_inst_66_);
v___f_75_ = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_75_, 0, v_inst_66_);
lean_closure_set(v___f_75_, 1, v___x_74_);
lean_inc(v_toBind_67_);
v___x_76_ = lean_apply_4(v_toBind_67_, lean_box(0), lean_box(0), v_getCallStack_71_, v___f_73_);
v___f_77_ = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___redArg___lam__3), 7, 6);
lean_closure_set(v___f_77_, 0, v_inst_66_);
lean_closure_set(v___f_77_, 1, v___x_74_);
lean_closure_set(v___f_77_, 2, v_withCallStack_72_);
lean_closure_set(v___f_77_, 3, v___x_76_);
lean_closure_set(v___f_77_, 4, v___f_75_);
lean_closure_set(v___f_77_, 5, v_throwCycle_68_);
v___x_78_ = lean_apply_4(v_toBind_67_, lean_box(0), lean_box(0), v_getCallStack_71_, v___f_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___redArg(lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_keyOf_82_, lean_object* v_fetch_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_toBind_85_; lean_object* v_toMonadCallStack_86_; lean_object* v_throwCycle_87_; lean_object* v___f_88_; lean_object* v___x_89_; 
v_toBind_85_ = lean_ctor_get(v_inst_80_, 1);
lean_inc(v_toBind_85_);
lean_dec_ref(v_inst_80_);
v_toMonadCallStack_86_ = lean_ctor_get(v_inst_81_, 0);
lean_inc_ref(v_toMonadCallStack_86_);
v_throwCycle_87_ = lean_ctor_get(v_inst_81_, 1);
lean_inc(v_throwCycle_87_);
lean_dec_ref(v_inst_81_);
v___f_88_ = lean_alloc_closure((void*)(l_Lake_recFetchAcyclic___redArg___lam__4), 8, 6);
lean_closure_set(v___f_88_, 0, v_toMonadCallStack_86_);
lean_closure_set(v___f_88_, 1, v_fetch_83_);
lean_closure_set(v___f_88_, 2, v_keyOf_82_);
lean_closure_set(v___f_88_, 3, v_inst_79_);
lean_closure_set(v___f_88_, 4, v_toBind_85_);
lean_closure_set(v___f_88_, 5, v_throwCycle_87_);
v___x_89_ = l_Lake_recFetch___redArg(v___f_88_, v_a_84_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic(lean_object* v_00_u03ba_90_, lean_object* v_m_91_, lean_object* v_00_u03b1_92_, lean_object* v_00_u03b2_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_keyOf_97_, lean_object* v_fetch_98_, lean_object* v_a_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lake_recFetchAcyclic___redArg(v_inst_94_, v_inst_95_, v_inst_96_, v_keyOf_97_, v_fetch_98_, v_a_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__0(lean_object* v_toApplicative_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v_toPure_104_; lean_object* v___x_105_; 
v_toPure_104_ = lean_ctor_get(v_toApplicative_101_, 1);
lean_inc(v_toPure_104_);
lean_dec_ref(v_toApplicative_101_);
v___x_105_ = lean_apply_2(v_toPure_104_, lean_box(0), v_a_102_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__1(lean_object* v_toApplicative_106_, lean_object* v_store_107_, lean_object* v___x_108_, lean_object* v_toBind_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___f_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
lean_inc(v_a_110_);
v___f_111_ = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___redArg___lam__0), 3, 2);
lean_closure_set(v___f_111_, 0, v_toApplicative_106_);
lean_closure_set(v___f_111_, 1, v_a_110_);
v___x_112_ = lean_apply_2(v_store_107_, v___x_108_, v_a_110_);
v___x_113_ = lean_apply_4(v_toBind_109_, lean_box(0), lean_box(0), v___x_112_, v___f_111_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__2(lean_object* v_compute_114_, lean_object* v_a_115_, lean_object* v___y_116_, lean_object* v_toBind_117_, lean_object* v___f_118_, lean_object* v_toApplicative_119_, lean_object* v_a_120_){
_start:
{
if (lean_obj_tag(v_a_120_) == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; 
lean_dec_ref(v_toApplicative_119_);
v___x_121_ = lean_apply_2(v_compute_114_, v_a_115_, v___y_116_);
v___x_122_ = lean_apply_4(v_toBind_117_, lean_box(0), lean_box(0), v___x_121_, v___f_118_);
return v___x_122_;
}
else
{
lean_object* v_val_123_; lean_object* v_toPure_124_; lean_object* v___x_125_; 
lean_dec(v___f_118_);
lean_dec(v_toBind_117_);
lean_dec(v___y_116_);
lean_dec(v_a_115_);
lean_dec(v_compute_114_);
v_val_123_ = lean_ctor_get(v_a_120_, 0);
lean_inc(v_val_123_);
lean_dec_ref_known(v_a_120_, 1);
v_toPure_124_ = lean_ctor_get(v_toApplicative_119_, 1);
lean_inc(v_toPure_124_);
lean_dec_ref(v_toApplicative_119_);
v___x_125_ = lean_apply_2(v_toPure_124_, lean_box(0), v_val_123_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg___lam__3(lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_keyOf_128_, lean_object* v_compute_129_, lean_object* v_a_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_toApplicative_132_; lean_object* v_toBind_133_; lean_object* v_fetch_x3f_134_; lean_object* v_store_135_; lean_object* v___x_136_; lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_toApplicative_132_ = lean_ctor_get(v_inst_126_, 0);
lean_inc_ref_n(v_toApplicative_132_, 2);
v_toBind_133_ = lean_ctor_get(v_inst_126_, 1);
lean_inc_n(v_toBind_133_, 3);
lean_dec_ref(v_inst_126_);
v_fetch_x3f_134_ = lean_ctor_get(v_inst_127_, 0);
lean_inc(v_fetch_x3f_134_);
v_store_135_ = lean_ctor_get(v_inst_127_, 1);
lean_inc(v_store_135_);
lean_dec_ref(v_inst_127_);
lean_inc(v_a_130_);
v___x_136_ = lean_apply_1(v_keyOf_128_, v_a_130_);
lean_inc(v___x_136_);
v___f_137_ = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___redArg___lam__1), 5, 4);
lean_closure_set(v___f_137_, 0, v_toApplicative_132_);
lean_closure_set(v___f_137_, 1, v_store_135_);
lean_closure_set(v___f_137_, 2, v___x_136_);
lean_closure_set(v___f_137_, 3, v_toBind_133_);
v___f_138_ = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___redArg___lam__2), 7, 6);
lean_closure_set(v___f_138_, 0, v_compute_129_);
lean_closure_set(v___f_138_, 1, v_a_130_);
lean_closure_set(v___f_138_, 2, v___y_131_);
lean_closure_set(v___f_138_, 3, v_toBind_133_);
lean_closure_set(v___f_138_, 4, v___f_137_);
lean_closure_set(v___f_138_, 5, v_toApplicative_132_);
v___x_139_ = lean_apply_1(v_fetch_x3f_134_, v___x_136_);
v___x_140_ = lean_apply_4(v_toBind_133_, lean_box(0), lean_box(0), v___x_139_, v___f_138_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize___redArg(lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_keyOf_145_, lean_object* v_compute_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___f_148_; lean_object* v___x_149_; 
lean_inc(v_keyOf_145_);
lean_inc_ref(v_inst_142_);
v___f_148_ = lean_alloc_closure((void*)(l_Lake_recFetchMemoize___redArg___lam__3), 6, 4);
lean_closure_set(v___f_148_, 0, v_inst_142_);
lean_closure_set(v___f_148_, 1, v_inst_144_);
lean_closure_set(v___f_148_, 2, v_keyOf_145_);
lean_closure_set(v___f_148_, 3, v_compute_146_);
v___x_149_ = l_Lake_recFetchAcyclic___redArg(v_inst_141_, v_inst_142_, v_inst_143_, v_keyOf_145_, v___f_148_, v_a_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchMemoize(lean_object* v_00_u03ba_150_, lean_object* v_m_151_, lean_object* v_00_u03b2_152_, lean_object* v_00_u03b1_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_keyOf_158_, lean_object* v_compute_159_, lean_object* v_a_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lake_recFetchMemoize___redArg(v_inst_154_, v_inst_155_, v_inst_156_, v_inst_157_, v_keyOf_158_, v_compute_159_, v_a_160_);
return v___x_161_;
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
