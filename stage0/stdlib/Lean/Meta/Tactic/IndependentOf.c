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
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_MVarId_isSubsingleton(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getMVarDependencies(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
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
v___x_21_ = lean_st_ref_put(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg(v_e_30_, v___y_32_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___boxed(lean_object* v_e_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0(v_e_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg(lean_object* v_mvarId_44_, lean_object* v_x_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_44_, v_x_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_59_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_59_ == 0)
{
v___x_54_ = v___x_51_;
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_dec(v___x_51_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_a_52_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
else
{
lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
v_a_60_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v___x_51_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v___x_51_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_65_; 
if (v_isShared_63_ == 0)
{
v___x_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_a_60_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg___boxed(lean_object* v_mvarId_68_, lean_object* v_x_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg(v_mvarId_68_, v_x_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3(lean_object* v_00_u03b1_76_, lean_object* v_mvarId_77_, lean_object* v_x_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg(v_mvarId_77_, v_x_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___boxed(lean_object* v_00_u03b1_85_, lean_object* v_mvarId_86_, lean_object* v_x_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3(v_00_u03b1_85_, v_mvarId_86_, v_x_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3_spec__5___redArg(lean_object* v_m_94_, lean_object* v_query_95_, lean_object* v_x_96_, lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
lean_object* v_zero_99_; uint8_t v_isZero_100_; 
v_zero_99_ = lean_unsigned_to_nat(0u);
v_isZero_100_ = lean_nat_dec_eq(v_x_97_, v_zero_99_);
if (v_isZero_100_ == 1)
{
lean_dec(v_x_98_);
lean_dec(v_x_97_);
if (lean_obj_tag(v_x_96_) == 0)
{
lean_object* v___x_101_; 
v___x_101_ = lean_box(2);
return v___x_101_;
}
else
{
lean_object* v_val_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
v_val_102_ = lean_ctor_get(v_x_96_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v_x_96_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v_x_96_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_val_102_);
lean_dec(v_x_96_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
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
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_val_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
else
{
lean_object* v_keyArray_110_; lean_object* v_valueArray_111_; lean_object* v___x_112_; uint8_t v_isSome_113_; 
v_keyArray_110_ = lean_ctor_get(v_m_94_, 1);
v_valueArray_111_ = lean_ctor_get(v_m_94_, 2);
v___x_112_ = lean_array_fget_borrowed(v_keyArray_110_, v_x_98_);
v_isSome_113_ = lean_noption_is_some(v___x_112_);
if (v_isSome_113_ == 0)
{
lean_dec(v_x_97_);
if (lean_obj_tag(v_x_96_) == 0)
{
lean_object* v___x_114_; 
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v_x_98_);
return v___x_114_;
}
else
{
lean_object* v_val_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
lean_dec(v_x_98_);
v_val_115_ = lean_ctor_get(v_x_96_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v_x_96_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v_x_96_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_val_115_);
lean_dec(v_x_96_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_val_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
else
{
lean_object* v_one_123_; lean_object* v_n_124_; lean_object* v___y_126_; 
v_one_123_ = lean_unsigned_to_nat(1u);
v_n_124_ = lean_nat_sub(v_x_97_, v_one_123_);
lean_dec(v_x_97_);
if (v_isSome_113_ == 0)
{
goto v___jp_132_;
}
else
{
lean_object* v___x_134_; uint8_t v_isSome_135_; 
v___x_134_ = lean_array_fget_borrowed(v_valueArray_111_, v_x_98_);
v_isSome_135_ = lean_noption_is_some(v___x_134_);
if (v_isSome_135_ == 0)
{
goto v___jp_132_;
}
else
{
lean_object* v_val_136_; uint8_t v___x_137_; 
lean_inc(v___x_112_);
v_val_136_ = lean_noption_get(v___x_112_);
v___x_137_ = l_Lean_instBEqMVarId_beq(v_val_136_, v_query_95_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
lean_dec(v_val_136_);
v___x_138_ = lean_array_get_size(v_keyArray_110_);
v___x_139_ = lean_nat_add(v_x_98_, v_one_123_);
lean_dec(v_x_98_);
v___x_140_ = lean_nat_dec_lt(v___x_139_, v___x_138_);
if (v___x_140_ == 0)
{
lean_dec(v___x_139_);
v_x_97_ = v_n_124_;
v_x_98_ = v_zero_99_;
goto _start;
}
else
{
v_x_97_ = v_n_124_;
v_x_98_ = v___x_139_;
goto _start;
}
}
else
{
lean_object* v_val_143_; lean_object* v___x_144_; 
lean_dec(v_n_124_);
lean_dec(v_x_96_);
lean_inc(v___x_134_);
v_val_143_ = lean_noption_get(v___x_134_);
v___x_144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_144_, 0, v_x_98_);
lean_ctor_set(v___x_144_, 1, v_val_136_);
lean_ctor_set(v___x_144_, 2, v_val_143_);
return v___x_144_;
}
}
}
v___jp_125_:
{
lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_127_ = lean_array_get_size(v_keyArray_110_);
v___x_128_ = lean_nat_add(v_x_98_, v_one_123_);
lean_dec(v_x_98_);
v___x_129_ = lean_nat_dec_lt(v___x_128_, v___x_127_);
if (v___x_129_ == 0)
{
lean_dec(v___x_128_);
v_x_96_ = v___y_126_;
v_x_97_ = v_n_124_;
v_x_98_ = v_zero_99_;
goto _start;
}
else
{
v_x_96_ = v___y_126_;
v_x_97_ = v_n_124_;
v_x_98_ = v___x_128_;
goto _start;
}
}
v___jp_132_:
{
if (lean_obj_tag(v_x_96_) == 0)
{
lean_object* v___x_133_; 
lean_inc(v_x_98_);
v___x_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_133_, 0, v_x_98_);
v___y_126_ = v___x_133_;
goto v___jp_125_;
}
else
{
v___y_126_ = v_x_96_;
goto v___jp_125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_m_145_, lean_object* v_query_146_, lean_object* v_x_147_, lean_object* v_x_148_, lean_object* v_x_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3_spec__5___redArg(v_m_145_, v_query_146_, v_x_147_, v_x_148_, v_x_149_);
lean_dec(v_query_146_);
lean_dec_ref(v_m_145_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3___redArg(lean_object* v_m_151_, lean_object* v_query_152_){
_start:
{
lean_object* v_keyArray_153_; lean_object* v___x_154_; uint64_t v___x_155_; uint64_t v___x_156_; uint64_t v___x_157_; uint64_t v_fold_158_; uint64_t v___x_159_; uint64_t v___x_160_; uint64_t v___x_161_; size_t v___x_162_; size_t v___x_163_; size_t v___x_164_; size_t v___x_165_; size_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_keyArray_153_ = lean_ctor_get(v_m_151_, 1);
v___x_154_ = lean_array_get_size(v_keyArray_153_);
v___x_155_ = l_Lean_instHashableMVarId_hash(v_query_152_);
v___x_156_ = 32ULL;
v___x_157_ = lean_uint64_shift_right(v___x_155_, v___x_156_);
v_fold_158_ = lean_uint64_xor(v___x_155_, v___x_157_);
v___x_159_ = 16ULL;
v___x_160_ = lean_uint64_shift_right(v_fold_158_, v___x_159_);
v___x_161_ = lean_uint64_xor(v_fold_158_, v___x_160_);
v___x_162_ = lean_uint64_to_usize(v___x_161_);
v___x_163_ = lean_usize_of_nat(v___x_154_);
v___x_164_ = ((size_t)1ULL);
v___x_165_ = lean_usize_sub(v___x_163_, v___x_164_);
v___x_166_ = lean_usize_land(v___x_162_, v___x_165_);
v___x_167_ = lean_usize_to_nat(v___x_166_);
v___x_168_ = lean_box(0);
v___x_169_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3_spec__5___redArg(v_m_151_, v_query_152_, v___x_168_, v___x_154_, v___x_167_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_m_170_, lean_object* v_query_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3___redArg(v_m_170_, v_query_171_);
lean_dec(v_query_171_);
lean_dec_ref(v_m_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg(lean_object* v_m_173_, lean_object* v_query_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3___redArg(v_m_173_, v_query_174_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_index_176_; lean_object* v_key_177_; lean_object* v_value_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
v_index_176_ = lean_ctor_get(v___x_175_, 0);
v_key_177_ = lean_ctor_get(v___x_175_, 1);
v_value_178_ = lean_ctor_get(v___x_175_, 2);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_175_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_value_178_);
lean_inc(v_key_177_);
lean_inc(v_index_176_);
lean_dec(v___x_175_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_index_176_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_key_177_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_value_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
else
{
lean_object* v___x_186_; 
lean_dec(v___x_175_);
v___x_186_ = lean_box(1);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg___boxed(lean_object* v_m_187_, lean_object* v_query_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg(v_m_187_, v_query_188_);
lean_dec(v_query_188_);
lean_dec_ref(v_m_187_);
return v_res_189_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg(lean_object* v_m_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg(v_m_190_, v_a_191_);
if (lean_obj_tag(v___x_192_) == 0)
{
uint8_t v___x_193_; 
lean_dec_ref_known(v___x_192_, 3);
v___x_193_ = 1;
return v___x_193_;
}
else
{
uint8_t v___x_194_; 
v___x_194_ = 0;
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg___boxed(lean_object* v_m_195_, lean_object* v_a_196_){
_start:
{
uint8_t v_res_197_; lean_object* v_r_198_; 
v_res_197_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg(v_m_195_, v_a_196_);
lean_dec(v_a_196_);
lean_dec_ref(v_m_195_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_MVarId_isIndependentOf_spec__2(uint8_t v_a_199_, lean_object* v_g_200_, lean_object* v_x_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
if (lean_obj_tag(v_x_201_) == 0)
{
uint8_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = 1;
v___x_208_ = lean_box(v___x_207_);
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
return v___x_209_;
}
else
{
lean_object* v_head_210_; lean_object* v_tail_211_; lean_object* v___x_212_; 
v_head_210_ = lean_ctor_get(v_x_201_, 0);
lean_inc(v_head_210_);
v_tail_211_ = lean_ctor_get(v_x_201_, 1);
lean_inc(v_tail_211_);
lean_dec_ref_known(v_x_201_, 2);
v___x_212_ = l_Lean_MVarId_getMVarDependencies(v_head_210_, v_a_199_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_224_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_224_ == 0)
{
v___x_215_ = v___x_212_;
v_isShared_216_ = v_isSharedCheck_224_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_212_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_224_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
uint8_t v___x_217_; 
v___x_217_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg(v_a_213_, v_g_200_);
lean_dec(v_a_213_);
if (v___x_217_ == 0)
{
lean_del_object(v___x_215_);
v_x_201_ = v_tail_211_;
goto _start;
}
else
{
if (v_a_199_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_221_; 
lean_dec(v_tail_211_);
v___x_219_ = lean_box(v_a_199_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_219_);
v___x_221_ = v___x_215_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
else
{
lean_del_object(v___x_215_);
v_x_201_ = v_tail_211_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_dec(v_tail_211_);
v_a_225_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_212_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_212_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_MVarId_isIndependentOf_spec__2___boxed(lean_object* v_a_233_, lean_object* v_g_234_, lean_object* v_x_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
uint8_t v_a_2804__boxed_241_; lean_object* v_res_242_; 
v_a_2804__boxed_241_ = lean_unbox(v_a_233_);
v_res_242_ = l_List_allM___at___00Lean_MVarId_isIndependentOf_spec__2(v_a_2804__boxed_241_, v_g_234_, v_x_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v_g_234_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isIndependentOf___lam__0(lean_object* v_g_243_, lean_object* v_L_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v___x_250_; 
lean_inc(v_g_243_);
v___x_250_ = l_Lean_MVarId_getType(v_g_243_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_252_; lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_296_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v___x_250_, 1);
v___x_252_ = l_Lean_instantiateMVars___at___00Lean_MVarId_isIndependentOf_spec__0___redArg(v_a_251_, v___y_246_);
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_296_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_296_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_296_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
uint8_t v___x_257_; 
v___x_257_ = l_Lean_Expr_hasExprMVar(v_a_253_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
lean_del_object(v___x_255_);
lean_inc(v___y_248_);
lean_inc_ref(v___y_247_);
lean_inc(v___y_246_);
lean_inc_ref(v___y_245_);
v___x_258_ = lean_infer_type(v_a_253_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_282_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_282_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_282_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_282_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
uint8_t v___x_263_; uint8_t v___x_264_; 
v___x_263_ = 1;
v___x_264_ = l_Lean_Expr_isProp(v_a_259_);
lean_dec(v_a_259_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
lean_del_object(v___x_261_);
lean_inc(v_g_243_);
v___x_265_ = l_Lean_MVarId_isSubsingleton(v_g_243_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_277_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_277_ == 0)
{
v___x_268_ = v___x_265_;
v_isShared_269_ = v_isSharedCheck_277_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_265_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_277_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
uint8_t v___x_270_; 
v___x_270_ = lean_unbox(v_a_266_);
if (v___x_270_ == 0)
{
uint8_t v___x_271_; lean_object* v___x_272_; 
lean_del_object(v___x_268_);
v___x_271_ = lean_unbox(v_a_266_);
lean_dec(v_a_266_);
v___x_272_ = l_List_allM___at___00Lean_MVarId_isIndependentOf_spec__2(v___x_271_, v_g_243_, v_L_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v_g_243_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; lean_object* v___x_275_; 
lean_dec(v_a_266_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v_L_244_);
lean_dec(v_g_243_);
v___x_273_ = lean_box(v___x_263_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_273_);
v___x_275_ = v___x_268_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
else
{
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v_L_244_);
lean_dec(v_g_243_);
return v___x_265_;
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_280_; 
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v_L_244_);
lean_dec(v_g_243_);
v___x_278_ = lean_box(v___x_263_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_278_);
v___x_280_ = v___x_261_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v_L_244_);
lean_dec(v_g_243_);
v_a_283_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_258_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_258_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
else
{
uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_294_; 
lean_dec(v_a_253_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v_L_244_);
lean_dec(v_g_243_);
v___x_291_ = 0;
v___x_292_ = lean_box(v___x_291_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_292_);
v___x_294_ = v___x_255_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v_L_244_);
lean_dec(v_g_243_);
v_a_297_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_250_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_250_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isIndependentOf___lam__0___boxed(lean_object* v_g_305_, lean_object* v_L_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_MVarId_isIndependentOf___lam__0(v_g_305_, v_L_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isIndependentOf(lean_object* v_L_313_, lean_object* v_g_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v___f_320_; lean_object* v___x_321_; 
lean_inc(v_g_314_);
v___f_320_ = lean_alloc_closure((void*)(l_Lean_MVarId_isIndependentOf___lam__0___boxed), 7, 2);
lean_closure_set(v___f_320_, 0, v_g_314_);
lean_closure_set(v___f_320_, 1, v_L_313_);
v___x_321_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_isIndependentOf_spec__3___redArg(v_g_314_, v___f_320_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isIndependentOf___boxed(lean_object* v_L_322_, lean_object* v_g_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_MVarId_isIndependentOf(v_L_322_, v_g_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
return v_res_329_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1(lean_object* v_00_u03b2_330_, lean_object* v_m_331_, lean_object* v_a_332_){
_start:
{
uint8_t v___x_333_; 
v___x_333_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___redArg(v_m_331_, v_a_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1___boxed(lean_object* v_00_u03b2_334_, lean_object* v_m_335_, lean_object* v_a_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1(v_00_u03b2_334_, v_m_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_m_335_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1(lean_object* v_00_u03b2_339_, lean_object* v_m_340_, lean_object* v_query_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___redArg(v_m_340_, v_query_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1___boxed(lean_object* v_00_u03b2_343_, lean_object* v_m_344_, lean_object* v_query_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1(v_00_u03b2_343_, v_m_344_, v_query_345_);
lean_dec(v_query_345_);
lean_dec_ref(v_m_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_347_, lean_object* v_m_348_, lean_object* v_query_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3___redArg(v_m_348_, v_query_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_351_, lean_object* v_m_352_, lean_object* v_query_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3(v_00_u03b2_351_, v_m_352_, v_query_353_);
lean_dec(v_query_353_);
lean_dec_ref(v_m_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_355_, lean_object* v_m_356_, lean_object* v_query_357_, lean_object* v_x_358_, lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3_spec__5___redArg(v_m_356_, v_query_357_, v_x_358_, v_x_359_, v_x_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_363_, lean_object* v_m_364_, lean_object* v_query_365_, lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_isIndependentOf_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_363_, v_m_364_, v_query_365_, v_x_366_, v_x_367_, v_x_368_, v_x_369_);
lean_dec(v_query_365_);
lean_dec_ref(v_m_364_);
return v_res_370_;
}
}
lean_object* runtime_initialize_Lean_Meta_CollectMVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_IndependentOf(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
