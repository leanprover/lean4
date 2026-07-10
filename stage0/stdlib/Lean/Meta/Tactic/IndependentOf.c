// Lean compiler output
// Module: Lean.Meta.Tactic.IndependentOf
// Imports: public import Lean.Meta.CollectMVars public import Lean.Meta.Tactic.Util
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_MVarId_isSubsingleton(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getMVarDependencies(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_MVarId_isIndependentOf_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_MVarId_isIndependentOf_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isIndependentOf___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isIndependentOf___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isIndependentOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isIndependentOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
v___x_5_ = lean_bool_not(v___x_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
else
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_e_1_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg(v_e_31_, v___y_33_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___boxed(lean_object* v_e_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0(v_e_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg(lean_object* v_mvarId_45_, lean_object* v_x_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_45_, v_x_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_60_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_60_ == 0)
{
v___x_55_ = v___x_52_;
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_a_53_);
lean_dec(v___x_52_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_a_53_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
else
{
lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_68_; 
v_a_61_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_68_ == 0)
{
v___x_63_ = v___x_52_;
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_dec(v___x_52_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_a_61_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg___boxed(lean_object* v_mvarId_69_, lean_object* v_x_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg(v_mvarId_69_, v_x_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3(lean_object* v_00_u03b1_77_, lean_object* v_mvarId_78_, lean_object* v_x_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg(v_mvarId_78_, v_x_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___boxed(lean_object* v_00_u03b1_86_, lean_object* v_mvarId_87_, lean_object* v_x_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3(v_00_u03b1_86_, v_mvarId_87_, v_x_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
return v_res_94_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg(lean_object* v_a_95_, lean_object* v_x_96_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
uint8_t v___x_97_; 
v___x_97_ = 0;
return v___x_97_;
}
else
{
lean_object* v_key_98_; lean_object* v_tail_99_; uint8_t v___x_100_; 
v_key_98_ = lean_ctor_get(v_x_96_, 0);
v_tail_99_ = lean_ctor_get(v_x_96_, 2);
v___x_100_ = l_Lean_instBEqMVarId_beq(v_key_98_, v_a_95_);
if (v___x_100_ == 0)
{
v_x_96_ = v_tail_99_;
goto _start;
}
else
{
return v___x_100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg___boxed(lean_object* v_a_102_, lean_object* v_x_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg(v_a_102_, v_x_103_);
lean_dec(v_x_103_);
lean_dec(v_a_102_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg(lean_object* v_m_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_buckets_108_; lean_object* v___x_109_; uint64_t v___x_110_; uint64_t v___x_111_; uint64_t v___x_112_; uint64_t v_fold_113_; uint64_t v___x_114_; uint64_t v___x_115_; uint64_t v___x_116_; size_t v___x_117_; size_t v___x_118_; size_t v___x_119_; size_t v___x_120_; size_t v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v_buckets_108_ = lean_ctor_get(v_m_106_, 1);
v___x_109_ = lean_array_get_size(v_buckets_108_);
v___x_110_ = l_Lean_instHashableMVarId_hash(v_a_107_);
v___x_111_ = 32ULL;
v___x_112_ = lean_uint64_shift_right(v___x_110_, v___x_111_);
v_fold_113_ = lean_uint64_xor(v___x_110_, v___x_112_);
v___x_114_ = 16ULL;
v___x_115_ = lean_uint64_shift_right(v_fold_113_, v___x_114_);
v___x_116_ = lean_uint64_xor(v_fold_113_, v___x_115_);
v___x_117_ = lean_uint64_to_usize(v___x_116_);
v___x_118_ = lean_usize_of_nat(v___x_109_);
v___x_119_ = ((size_t)1ULL);
v___x_120_ = lean_usize_sub(v___x_118_, v___x_119_);
v___x_121_ = lean_usize_land(v___x_117_, v___x_120_);
v___x_122_ = lean_array_uget_borrowed(v_buckets_108_, v___x_121_);
v___x_123_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg(v_a_107_, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg___boxed(lean_object* v_m_124_, lean_object* v_a_125_){
_start:
{
uint8_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg(v_m_124_, v_a_125_);
lean_dec(v_a_125_);
lean_dec_ref(v_m_124_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_MVarId_isIndependentOf_spec__2(uint8_t v_a_128_, lean_object* v_g_129_, lean_object* v_x_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
if (lean_obj_tag(v_x_130_) == 0)
{
uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = 1;
v___x_137_ = lean_box(v___x_136_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
else
{
lean_object* v_head_139_; lean_object* v_tail_140_; lean_object* v___x_141_; 
v_head_139_ = lean_ctor_get(v_x_130_, 0);
lean_inc(v_head_139_);
v_tail_140_ = lean_ctor_get(v_x_130_, 1);
lean_inc(v_tail_140_);
lean_dec_ref_known(v_x_130_, 2);
v___x_141_ = l_Lean_MVarId_getMVarDependencies(v_head_139_, v_a_128_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_153_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_153_ == 0)
{
v___x_144_ = v___x_141_;
v_isShared_145_ = v_isSharedCheck_153_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_141_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_153_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
uint8_t v___x_146_; uint8_t v___x_147_; 
v___x_146_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg(v_a_142_, v_g_129_);
lean_dec(v_a_142_);
v___x_147_ = lean_bool_not(v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v___x_150_; 
lean_dec(v_tail_140_);
v___x_148_ = lean_box(v___x_147_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_148_);
v___x_150_ = v___x_144_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
else
{
lean_del_object(v___x_144_);
v_x_130_ = v_tail_140_;
goto _start;
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_dec(v_tail_140_);
v_a_154_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_141_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_141_);
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
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_MVarId_isIndependentOf_spec__2___boxed(lean_object* v_a_162_, lean_object* v_g_163_, lean_object* v_x_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
uint8_t v_a_2481__boxed_170_; lean_object* v_res_171_; 
v_a_2481__boxed_170_ = lean_unbox(v_a_162_);
v_res_171_ = l_List_allM___at___00Lean_MVarId_isIndependentOf_spec__2(v_a_2481__boxed_170_, v_g_163_, v_x_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v_g_163_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isIndependentOf___lam__0(lean_object* v_g_172_, lean_object* v_L_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___x_179_; 
lean_inc(v_g_172_);
v___x_179_ = l_Lean_MVarId_getType(v_g_172_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_181_; lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_225_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_179_, 1);
v___x_181_ = l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg(v_a_180_, v___y_175_);
v_a_182_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_225_ == 0)
{
v___x_184_ = v___x_181_;
v_isShared_185_ = v_isSharedCheck_225_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_181_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_225_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
uint8_t v___x_186_; 
v___x_186_ = l_Lean_Expr_hasExprMVar(v_a_182_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
lean_del_object(v___x_184_);
lean_inc(v___y_177_);
lean_inc_ref(v___y_176_);
lean_inc(v___y_175_);
lean_inc_ref(v___y_174_);
v___x_187_ = lean_infer_type(v_a_182_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_211_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_211_ == 0)
{
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_211_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_211_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
uint8_t v___x_192_; uint8_t v___x_193_; 
v___x_192_ = 1;
v___x_193_ = l_Lean_Expr_isProp(v_a_188_);
lean_dec(v_a_188_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
lean_del_object(v___x_190_);
lean_inc(v_g_172_);
v___x_194_ = l_Lean_MVarId_isSubsingleton(v_g_172_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_206_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_206_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_206_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_206_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
uint8_t v___x_199_; 
v___x_199_ = lean_unbox(v_a_195_);
if (v___x_199_ == 0)
{
uint8_t v___x_200_; lean_object* v___x_201_; 
lean_del_object(v___x_197_);
v___x_200_ = lean_unbox(v_a_195_);
lean_dec(v_a_195_);
v___x_201_ = l_List_allM___at___00Lean_MVarId_isIndependentOf_spec__2(v___x_200_, v_g_172_, v_L_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v_g_172_);
return v___x_201_;
}
else
{
lean_object* v___x_202_; lean_object* v___x_204_; 
lean_dec(v_a_195_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v_L_173_);
lean_dec(v_g_172_);
v___x_202_ = lean_box(v___x_192_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_202_);
v___x_204_ = v___x_197_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v_L_173_);
lean_dec(v_g_172_);
return v___x_194_;
}
}
else
{
lean_object* v___x_207_; lean_object* v___x_209_; 
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v_L_173_);
lean_dec(v_g_172_);
v___x_207_ = lean_box(v___x_192_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_207_);
v___x_209_ = v___x_190_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
else
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v_L_173_);
lean_dec(v_g_172_);
v_a_212_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_187_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_187_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
else
{
uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
lean_dec(v_a_182_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v_L_173_);
lean_dec(v_g_172_);
v___x_220_ = 0;
v___x_221_ = lean_box(v___x_220_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_221_);
v___x_223_ = v___x_184_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
else
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v_L_173_);
lean_dec(v_g_172_);
v_a_226_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_233_ == 0)
{
v___x_228_ = v___x_179_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_179_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isIndependentOf___lam__0___boxed(lean_object* v_g_234_, lean_object* v_L_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_MVarId_isIndependentOf___lam__0(v_g_234_, v_L_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isIndependentOf(lean_object* v_L_242_, lean_object* v_g_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v___f_249_; lean_object* v___x_250_; 
lean_inc(v_g_243_);
v___f_249_ = lean_alloc_closure((void*)(l_Lean_MVarId_isIndependentOf___lam__0___boxed), 7, 2);
lean_closure_set(v___f_249_, 0, v_g_243_);
lean_closure_set(v___f_249_, 1, v_L_242_);
v___x_250_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg(v_g_243_, v___f_249_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isIndependentOf___boxed(lean_object* v_L_251_, lean_object* v_g_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_MVarId_isIndependentOf(v_L_251_, v_g_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
return v_res_258_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1(lean_object* v_00_u03b2_259_, lean_object* v_m_260_, lean_object* v_a_261_){
_start:
{
uint8_t v___x_262_; 
v___x_262_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg(v_m_260_, v_a_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___boxed(lean_object* v_00_u03b2_263_, lean_object* v_m_264_, lean_object* v_a_265_){
_start:
{
uint8_t v_res_266_; lean_object* v_r_267_; 
v_res_266_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1(v_00_u03b2_263_, v_m_264_, v_a_265_);
lean_dec(v_a_265_);
lean_dec_ref(v_m_264_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1(lean_object* v_00_u03b2_268_, lean_object* v_a_269_, lean_object* v_x_270_){
_start:
{
uint8_t v___x_271_; 
v___x_271_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg(v_a_269_, v_x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___boxed(lean_object* v_00_u03b2_272_, lean_object* v_a_273_, lean_object* v_x_274_){
_start:
{
uint8_t v_res_275_; lean_object* v_r_276_; 
v_res_275_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1(v_00_u03b2_272_, v_a_273_, v_x_274_);
lean_dec(v_x_274_);
lean_dec(v_a_273_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
lean_object* runtime_initialize_Lean_Meta_CollectMVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_IndependentOf(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_CollectMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_IndependentOf(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_CollectMVars(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_IndependentOf(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_CollectMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_IndependentOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_IndependentOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_IndependentOf(builtin);
}
#ifdef __cplusplus
}
#endif
