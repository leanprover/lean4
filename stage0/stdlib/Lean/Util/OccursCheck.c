// Lean compiler output
// Module: Lean.Util.OccursCheck
// Imports: public import Lean.MetavarContext
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_lift___redArg___lam__0(lean_object*);
lean_object* l_Lean_getDelayedMVarAssignment_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getExprMVarAssignment_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__5(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__0 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__0_value;
static const lean_closure_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__1 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__1_value;
static const lean_ctor_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__2 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ExceptT_lift___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__0 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__1 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_occursCheck___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_occursCheck___redArg___closed__0;
static lean_once_cell_t l_Lean_occursCheck___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_occursCheck___redArg___closed__1;
static lean_once_cell_t l_Lean_occursCheck___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_occursCheck___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_occursCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__7(lean_object* v_toPure_1_, lean_object* v_____x_2_){
_start:
{
lean_object* v_fst_3_; lean_object* v_snd_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_13_; 
v_fst_3_ = lean_ctor_get(v_____x_2_, 0);
v_snd_4_ = lean_ctor_get(v_____x_2_, 1);
v_isSharedCheck_13_ = !lean_is_exclusive(v_____x_2_);
if (v_isSharedCheck_13_ == 0)
{
v___x_6_ = v_____x_2_;
v_isShared_7_ = v_isSharedCheck_13_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_snd_4_);
lean_inc(v_fst_3_);
lean_dec(v_____x_2_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_13_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_8_; lean_object* v___x_10_; 
v___x_8_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_8_, 0, v_fst_3_);
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 0, v___x_8_);
v___x_10_ = v___x_6_;
goto v_reusejp_9_;
}
else
{
lean_object* v_reuseFailAlloc_12_; 
v_reuseFailAlloc_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v___x_8_);
lean_ctor_set(v_reuseFailAlloc_12_, 1, v_snd_4_);
v___x_10_ = v_reuseFailAlloc_12_;
goto v_reusejp_9_;
}
v_reusejp_9_:
{
lean_object* v___x_11_; 
v___x_11_ = lean_apply_2(v_toPure_1_, lean_box(0), v___x_10_);
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__5(lean_object* v_toPure_14_, lean_object* v_____x_15_){
_start:
{
lean_object* v_fst_16_; lean_object* v_snd_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_26_; 
v_fst_16_ = lean_ctor_get(v_____x_15_, 0);
v_snd_17_ = lean_ctor_get(v_____x_15_, 1);
v_isSharedCheck_26_ = !lean_is_exclusive(v_____x_15_);
if (v_isSharedCheck_26_ == 0)
{
v___x_19_ = v_____x_15_;
v_isShared_20_ = v_isSharedCheck_26_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_snd_17_);
lean_inc(v_fst_16_);
lean_dec(v_____x_15_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_26_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_21_; lean_object* v___x_23_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_fst_16_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 0, v___x_21_);
v___x_23_ = v___x_19_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v___x_21_);
lean_ctor_set(v_reuseFailAlloc_25_, 1, v_snd_17_);
v___x_23_ = v_reuseFailAlloc_25_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
lean_object* v___x_24_; 
v___x_24_ = lean_apply_2(v_toPure_14_, lean_box(0), v___x_23_);
return v___x_24_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6(lean_object* v_toPure_31_, lean_object* v_e_32_, lean_object* v_toBind_33_, lean_object* v___f_34_, lean_object* v_____x_35_){
_start:
{
lean_object* v_fst_36_; 
v_fst_36_ = lean_ctor_get(v_____x_35_, 0);
lean_inc(v_fst_36_);
if (lean_obj_tag(v_fst_36_) == 0)
{
lean_object* v_snd_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_53_; 
lean_dec(v___f_34_);
lean_dec(v_toBind_33_);
lean_dec_ref(v_e_32_);
v_snd_37_ = lean_ctor_get(v_____x_35_, 1);
v_isSharedCheck_53_ = !lean_is_exclusive(v_____x_35_);
if (v_isSharedCheck_53_ == 0)
{
lean_object* v_unused_54_; 
v_unused_54_ = lean_ctor_get(v_____x_35_, 0);
lean_dec(v_unused_54_);
v___x_39_ = v_____x_35_;
v_isShared_40_ = v_isSharedCheck_53_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_snd_37_);
lean_dec(v_____x_35_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_53_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_52_; 
v_a_41_ = lean_ctor_get(v_fst_36_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v_fst_36_);
if (v_isSharedCheck_52_ == 0)
{
v___x_43_ = v_fst_36_;
v_isShared_44_ = v_isSharedCheck_52_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v_fst_36_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_52_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_41_);
v___x_46_ = v_reuseFailAlloc_51_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_48_; 
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 0, v___x_46_);
v___x_48_ = v___x_39_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v_snd_37_);
v___x_48_ = v_reuseFailAlloc_50_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
lean_object* v___x_49_; 
v___x_49_ = lean_apply_2(v_toPure_31_, lean_box(0), v___x_48_);
return v___x_49_;
}
}
}
}
}
else
{
lean_object* v_snd_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_139_; 
v_snd_55_ = lean_ctor_get(v_____x_35_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v_____x_35_);
if (v_isSharedCheck_139_ == 0)
{
lean_object* v_unused_140_; 
v_unused_140_ = lean_ctor_get(v_____x_35_, 0);
lean_dec(v_unused_140_);
v___x_57_ = v_____x_35_;
v_isShared_58_ = v_isSharedCheck_139_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_snd_55_);
lean_dec(v_____x_35_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_139_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v_a_59_; lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_a_59_ = lean_ctor_get(v_fst_36_, 0);
lean_inc(v_a_59_);
lean_dec_ref_known(v_fst_36_, 1);
v___x_60_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__0));
v___x_61_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__1));
lean_inc_ref(v_e_32_);
v___x_62_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_60_, v___x_61_, v_a_59_, v_e_32_);
lean_dec(v_a_59_);
if (v___x_62_ == 0)
{
lean_object* v___f_63_; lean_object* v___x_64_; lean_object* v___y_66_; lean_object* v___y_74_; lean_object* v_i_75_; lean_object* v___y_81_; lean_object* v___y_91_; lean_object* v_i_92_; lean_object* v___x_107_; 
lean_inc(v_toPure_31_);
v___f_63_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__5), 2, 1);
lean_closure_set(v___f_63_, 0, v_toPure_31_);
v___x_64_ = lean_box(0);
lean_inc_ref(v_e_32_);
v___x_107_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_60_, v___x_61_, v_snd_55_, v_e_32_);
switch(lean_obj_tag(v___x_107_))
{
case 0:
{
lean_dec_ref_known(v___x_107_, 3);
lean_dec_ref(v_e_32_);
v___y_66_ = v_snd_55_;
goto v___jp_65_;
}
case 1:
{
lean_object* v_index_108_; lean_object* v_size_109_; lean_object* v_keyArray_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v_index_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_index_108_);
lean_dec_ref_known(v___x_107_, 1);
v_size_109_ = lean_ctor_get(v_snd_55_, 0);
v_keyArray_110_ = lean_ctor_get(v_snd_55_, 1);
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = lean_nat_add(v_size_109_, v___x_111_);
v___x_113_ = lean_array_get_size(v_keyArray_110_);
v___x_114_ = lean_nat_dec_lt(v___x_112_, v___x_113_);
if (v___x_114_ == 0)
{
lean_dec(v___x_112_);
lean_dec(v_index_108_);
goto v___jp_97_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_115_ = lean_unsigned_to_nat(4u);
v___x_116_ = lean_nat_mul(v___x_112_, v___x_115_);
v___x_117_ = lean_unsigned_to_nat(3u);
v___x_118_ = lean_nat_mul(v___x_113_, v___x_117_);
v___x_119_ = lean_nat_dec_le(v___x_116_, v___x_118_);
lean_dec(v___x_118_);
lean_dec(v___x_116_);
if (v___x_119_ == 0)
{
lean_dec(v___x_112_);
lean_dec(v_index_108_);
goto v___jp_97_;
}
else
{
lean_object* v___x_120_; 
v___x_120_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_55_, v___x_112_, v_index_108_, v_e_32_, v___x_64_);
lean_dec(v_index_108_);
v___y_66_ = v___x_120_;
goto v___jp_65_;
}
}
}
default: 
{
lean_object* v_size_121_; lean_object* v_keyArray_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v_size_121_ = lean_ctor_get(v_snd_55_, 0);
v_keyArray_122_ = lean_ctor_get(v_snd_55_, 1);
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_nat_add(v_size_121_, v___x_123_);
v___x_125_ = lean_array_get_size(v_keyArray_122_);
v___x_126_ = lean_nat_dec_lt(v___x_124_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
lean_dec(v___x_124_);
v___x_127_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_60_, v___x_61_, v_snd_55_);
v___y_81_ = v___x_127_;
goto v___jp_80_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_128_ = lean_unsigned_to_nat(4u);
v___x_129_ = lean_nat_mul(v___x_124_, v___x_128_);
lean_dec(v___x_124_);
v___x_130_ = lean_unsigned_to_nat(3u);
v___x_131_ = lean_nat_mul(v___x_125_, v___x_130_);
v___x_132_ = lean_nat_dec_le(v___x_129_, v___x_131_);
lean_dec(v___x_131_);
lean_dec(v___x_129_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
v___x_133_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_60_, v___x_61_, v_snd_55_);
v___y_81_ = v___x_133_;
goto v___jp_80_;
}
else
{
v___y_81_ = v_snd_55_;
goto v___jp_80_;
}
}
}
}
v___jp_65_:
{
lean_object* v___x_68_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 1, v___y_66_);
lean_ctor_set(v___x_57_, 0, v___x_64_);
v___x_68_ = v___x_57_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_64_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v___y_66_);
v___x_68_ = v_reuseFailAlloc_72_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_apply_2(v_toPure_31_, lean_box(0), v___x_68_);
lean_inc(v_toBind_33_);
v___x_70_ = lean_apply_4(v_toBind_33_, lean_box(0), lean_box(0), v___x_69_, v___f_63_);
v___x_71_ = lean_apply_4(v_toBind_33_, lean_box(0), lean_box(0), v___x_70_, v___f_34_);
return v___x_71_;
}
}
v___jp_73_:
{
lean_object* v_size_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_size_76_ = lean_ctor_get(v___y_74_, 0);
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_add(v_size_76_, v___x_77_);
v___x_79_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_74_, v___x_78_, v_i_75_, v_e_32_, v___x_64_);
lean_dec(v_i_75_);
v___y_66_ = v___x_79_;
goto v___jp_65_;
}
v___jp_80_:
{
lean_object* v___x_82_; 
lean_inc_ref(v_e_32_);
v___x_82_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_60_, v___x_61_, v___y_81_, v_e_32_);
switch(lean_obj_tag(v___x_82_))
{
case 0:
{
lean_object* v_index_83_; lean_object* v_size_84_; lean_object* v___x_85_; 
v_index_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_index_83_);
lean_dec_ref_known(v___x_82_, 3);
v_size_84_ = lean_ctor_get(v___y_81_, 0);
lean_inc(v_size_84_);
v___x_85_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_81_, v_size_84_, v_index_83_, v_e_32_, v___x_64_);
lean_dec(v_index_83_);
v___y_66_ = v___x_85_;
goto v___jp_65_;
}
case 1:
{
lean_object* v_index_86_; 
v_index_86_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_index_86_);
lean_dec_ref_known(v___x_82_, 1);
v___y_74_ = v___y_81_;
v_i_75_ = v_index_86_;
goto v___jp_73_;
}
default: 
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_81_, v___x_87_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_index_89_; 
v_index_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_index_89_);
lean_dec_ref_known(v___x_88_, 1);
v___y_74_ = v___y_81_;
v_i_75_ = v_index_89_;
goto v___jp_73_;
}
else
{
lean_dec_ref(v_e_32_);
v___y_66_ = v___y_81_;
goto v___jp_65_;
}
}
}
}
v___jp_90_:
{
lean_object* v_size_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_size_93_ = lean_ctor_get(v___y_91_, 0);
v___x_94_ = lean_unsigned_to_nat(1u);
v___x_95_ = lean_nat_add(v_size_93_, v___x_94_);
v___x_96_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_91_, v___x_95_, v_i_92_, v_e_32_, v___x_64_);
lean_dec(v_i_92_);
v___y_66_ = v___x_96_;
goto v___jp_65_;
}
v___jp_97_:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_60_, v___x_61_, v_snd_55_);
lean_inc_ref(v_e_32_);
v___x_99_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_60_, v___x_61_, v___x_98_, v_e_32_);
switch(lean_obj_tag(v___x_99_))
{
case 0:
{
lean_object* v_index_100_; lean_object* v_size_101_; lean_object* v___x_102_; 
v_index_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_index_100_);
lean_dec_ref_known(v___x_99_, 3);
v_size_101_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_size_101_);
v___x_102_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_98_, v_size_101_, v_index_100_, v_e_32_, v___x_64_);
lean_dec(v_index_100_);
v___y_66_ = v___x_102_;
goto v___jp_65_;
}
case 1:
{
lean_object* v_index_103_; 
v_index_103_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_index_103_);
lean_dec_ref_known(v___x_99_, 1);
v___y_91_ = v___x_98_;
v_i_92_ = v_index_103_;
goto v___jp_90_;
}
default: 
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_98_, v___x_104_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_index_106_; 
v_index_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_index_106_);
lean_dec_ref_known(v___x_105_, 1);
v___y_91_ = v___x_98_;
v_i_92_ = v_index_106_;
goto v___jp_90_;
}
else
{
lean_dec_ref(v_e_32_);
v___y_66_ = v___x_98_;
goto v___jp_65_;
}
}
}
}
}
else
{
lean_object* v___x_134_; lean_object* v___x_136_; 
lean_dec(v___f_34_);
lean_dec(v_toBind_33_);
lean_dec_ref(v_e_32_);
v___x_134_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__2));
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_134_);
v___x_136_ = v___x_57_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_snd_55_);
v___x_136_ = v_reuseFailAlloc_138_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_137_; 
v___x_137_ = lean_apply_2(v_toPure_31_, lean_box(0), v___x_136_);
return v___x_137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__1(lean_object* v_toPure_141_, lean_object* v_inst_142_, lean_object* v_inst_143_, lean_object* v_mvarId_144_, lean_object* v_body_145_, lean_object* v_____x_146_){
_start:
{
lean_object* v_fst_147_; 
v_fst_147_ = lean_ctor_get(v_____x_146_, 0);
if (lean_obj_tag(v_fst_147_) == 0)
{
lean_object* v___x_148_; 
lean_dec_ref(v_body_145_);
lean_dec(v_mvarId_144_);
lean_dec_ref(v_inst_143_);
lean_dec_ref(v_inst_142_);
v___x_148_ = lean_apply_2(v_toPure_141_, lean_box(0), v_____x_146_);
return v___x_148_;
}
else
{
lean_object* v_snd_149_; lean_object* v___x_150_; 
lean_dec(v_toPure_141_);
v_snd_149_ = lean_ctor_get(v_____x_146_, 1);
lean_inc(v_snd_149_);
lean_dec_ref(v_____x_146_);
v___x_150_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_142_, v_inst_143_, v_mvarId_144_, v_body_145_, v_snd_149_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__2(lean_object* v_toPure_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_mvarId_154_, lean_object* v_value_155_, lean_object* v_toBind_156_, lean_object* v___f_157_, lean_object* v_____x_158_){
_start:
{
lean_object* v_fst_159_; 
v_fst_159_ = lean_ctor_get(v_____x_158_, 0);
if (lean_obj_tag(v_fst_159_) == 0)
{
lean_object* v___x_160_; 
lean_dec(v___f_157_);
lean_dec(v_toBind_156_);
lean_dec_ref(v_value_155_);
lean_dec(v_mvarId_154_);
lean_dec_ref(v_inst_153_);
lean_dec_ref(v_inst_152_);
v___x_160_ = lean_apply_2(v_toPure_151_, lean_box(0), v_____x_158_);
return v___x_160_;
}
else
{
lean_object* v_snd_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec(v_toPure_151_);
v_snd_161_ = lean_ctor_get(v_____x_158_, 1);
lean_inc(v_snd_161_);
lean_dec_ref(v_____x_158_);
v___x_162_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_152_, v_inst_153_, v_mvarId_154_, v_value_155_, v_snd_161_);
v___x_163_ = lean_apply_4(v_toBind_156_, lean_box(0), lean_box(0), v___x_162_, v___f_157_);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__3(lean_object* v_toPure_164_, lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_mvarId_167_, lean_object* v_arg_168_, lean_object* v_____x_169_){
_start:
{
lean_object* v_fst_170_; 
v_fst_170_ = lean_ctor_get(v_____x_169_, 0);
if (lean_obj_tag(v_fst_170_) == 0)
{
lean_object* v___x_171_; 
lean_dec_ref(v_arg_168_);
lean_dec(v_mvarId_167_);
lean_dec_ref(v_inst_166_);
lean_dec_ref(v_inst_165_);
v___x_171_ = lean_apply_2(v_toPure_164_, lean_box(0), v_____x_169_);
return v___x_171_;
}
else
{
lean_object* v_snd_172_; lean_object* v___x_173_; 
lean_dec(v_toPure_164_);
v_snd_172_ = lean_ctor_get(v_____x_169_, 1);
lean_inc(v_snd_172_);
lean_dec_ref(v_____x_169_);
v___x_173_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_165_, v_inst_166_, v_mvarId_167_, v_arg_168_, v_snd_172_);
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___lam__0(lean_object* v_toApplicative_175_, lean_object* v_inst_176_, lean_object* v_inst_177_, lean_object* v_mvarId_178_, lean_object* v_____x_179_){
_start:
{
lean_object* v_fst_180_; 
v_fst_180_ = lean_ctor_get(v_____x_179_, 0);
lean_inc(v_fst_180_);
if (lean_obj_tag(v_fst_180_) == 0)
{
lean_object* v_snd_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_198_; 
lean_dec(v_mvarId_178_);
lean_dec_ref(v_inst_177_);
lean_dec_ref(v_inst_176_);
v_snd_181_ = lean_ctor_get(v_____x_179_, 1);
v_isSharedCheck_198_ = !lean_is_exclusive(v_____x_179_);
if (v_isSharedCheck_198_ == 0)
{
lean_object* v_unused_199_; 
v_unused_199_ = lean_ctor_get(v_____x_179_, 0);
lean_dec(v_unused_199_);
v___x_183_ = v_____x_179_;
v_isShared_184_ = v_isSharedCheck_198_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_snd_181_);
lean_dec(v_____x_179_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_198_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_197_; 
v_a_185_ = lean_ctor_get(v_fst_180_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v_fst_180_);
if (v_isSharedCheck_197_ == 0)
{
v___x_187_ = v_fst_180_;
v_isShared_188_ = v_isSharedCheck_197_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v_fst_180_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_197_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v_toPure_189_; lean_object* v___x_191_; 
v_toPure_189_ = lean_ctor_get(v_toApplicative_175_, 1);
lean_inc(v_toPure_189_);
lean_dec_ref(v_toApplicative_175_);
if (v_isShared_188_ == 0)
{
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_185_);
v___x_191_ = v_reuseFailAlloc_196_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_193_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_191_);
v___x_193_ = v___x_183_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_snd_181_);
v___x_193_ = v_reuseFailAlloc_195_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_194_; 
v___x_194_ = lean_apply_2(v_toPure_189_, lean_box(0), v___x_193_);
return v___x_194_;
}
}
}
}
}
else
{
lean_object* v_a_200_; 
v_a_200_ = lean_ctor_get(v_fst_180_, 0);
lean_inc(v_a_200_);
lean_dec_ref_known(v_fst_180_, 1);
if (lean_obj_tag(v_a_200_) == 0)
{
lean_object* v_snd_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_211_; 
lean_dec(v_mvarId_178_);
lean_dec_ref(v_inst_177_);
lean_dec_ref(v_inst_176_);
v_snd_201_ = lean_ctor_get(v_____x_179_, 1);
v_isSharedCheck_211_ = !lean_is_exclusive(v_____x_179_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v_____x_179_, 0);
lean_dec(v_unused_212_);
v___x_203_ = v_____x_179_;
v_isShared_204_ = v_isSharedCheck_211_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_snd_201_);
lean_dec(v_____x_179_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_211_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v_toPure_205_; lean_object* v___x_206_; lean_object* v___x_208_; 
v_toPure_205_ = lean_ctor_get(v_toApplicative_175_, 1);
lean_inc(v_toPure_205_);
lean_dec_ref(v_toApplicative_175_);
v___x_206_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__2));
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_206_);
v___x_208_ = v___x_203_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_snd_201_);
v___x_208_ = v_reuseFailAlloc_210_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_209_; 
v___x_209_ = lean_apply_2(v_toPure_205_, lean_box(0), v___x_208_);
return v___x_209_;
}
}
}
else
{
lean_object* v_val_213_; lean_object* v_snd_214_; lean_object* v_mvarIdPending_215_; lean_object* v___x_216_; 
lean_dec_ref(v_toApplicative_175_);
v_val_213_ = lean_ctor_get(v_a_200_, 0);
lean_inc(v_val_213_);
lean_dec_ref_known(v_a_200_, 1);
v_snd_214_ = lean_ctor_get(v_____x_179_, 1);
lean_inc(v_snd_214_);
lean_dec_ref(v_____x_179_);
v_mvarIdPending_215_ = lean_ctor_get(v_val_213_, 1);
lean_inc(v_mvarIdPending_215_);
lean_dec(v_val_213_);
v___x_216_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg(v_inst_176_, v_inst_177_, v_mvarId_178_, v_mvarIdPending_215_, v_snd_214_);
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___lam__1(lean_object* v_toApplicative_217_, lean_object* v___x_218_, lean_object* v___x_219_, lean_object* v_mvarId_x27_220_, lean_object* v_toBind_221_, lean_object* v___f_222_, lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_mvarId_225_, lean_object* v_____x_226_){
_start:
{
lean_object* v_fst_227_; 
v_fst_227_ = lean_ctor_get(v_____x_226_, 0);
lean_inc(v_fst_227_);
if (lean_obj_tag(v_fst_227_) == 0)
{
lean_object* v_snd_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_245_; 
lean_dec(v_mvarId_225_);
lean_dec_ref(v_inst_224_);
lean_dec_ref(v_inst_223_);
lean_dec(v___f_222_);
lean_dec(v_toBind_221_);
lean_dec(v_mvarId_x27_220_);
lean_dec_ref(v___x_219_);
lean_dec_ref(v___x_218_);
v_snd_228_ = lean_ctor_get(v_____x_226_, 1);
v_isSharedCheck_245_ = !lean_is_exclusive(v_____x_226_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; 
v_unused_246_ = lean_ctor_get(v_____x_226_, 0);
lean_dec(v_unused_246_);
v___x_230_ = v_____x_226_;
v_isShared_231_ = v_isSharedCheck_245_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_snd_228_);
lean_dec(v_____x_226_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_245_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_244_; 
v_a_232_ = lean_ctor_get(v_fst_227_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v_fst_227_);
if (v_isSharedCheck_244_ == 0)
{
v___x_234_ = v_fst_227_;
v_isShared_235_ = v_isSharedCheck_244_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v_fst_227_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_244_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v_toPure_236_; lean_object* v___x_238_; 
v_toPure_236_ = lean_ctor_get(v_toApplicative_217_, 1);
lean_inc(v_toPure_236_);
lean_dec_ref(v_toApplicative_217_);
if (v_isShared_235_ == 0)
{
v___x_238_ = v___x_234_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_232_);
v___x_238_ = v_reuseFailAlloc_243_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_240_; 
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_238_);
v___x_240_ = v___x_230_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_snd_228_);
v___x_240_ = v_reuseFailAlloc_242_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_241_; 
v___x_241_ = lean_apply_2(v_toPure_236_, lean_box(0), v___x_240_);
return v___x_241_;
}
}
}
}
}
else
{
lean_object* v_a_247_; 
lean_dec_ref(v_toApplicative_217_);
v_a_247_ = lean_ctor_get(v_fst_227_, 0);
lean_inc(v_a_247_);
lean_dec_ref_known(v_fst_227_, 1);
if (lean_obj_tag(v_a_247_) == 0)
{
lean_object* v_snd_248_; lean_object* v___x_6523__overap_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec(v_mvarId_225_);
lean_dec_ref(v_inst_224_);
lean_dec_ref(v_inst_223_);
v_snd_248_ = lean_ctor_get(v_____x_226_, 1);
lean_inc(v_snd_248_);
lean_dec_ref(v_____x_226_);
v___x_6523__overap_249_ = l_Lean_getDelayedMVarAssignment_x3f___redArg(v___x_218_, v___x_219_, v_mvarId_x27_220_);
v___x_250_ = lean_apply_1(v___x_6523__overap_249_, v_snd_248_);
v___x_251_ = lean_apply_4(v_toBind_221_, lean_box(0), lean_box(0), v___x_250_, v___f_222_);
return v___x_251_;
}
else
{
lean_object* v_snd_252_; lean_object* v_val_253_; lean_object* v___x_254_; 
lean_dec(v___f_222_);
lean_dec(v_toBind_221_);
lean_dec(v_mvarId_x27_220_);
lean_dec_ref(v___x_219_);
lean_dec_ref(v___x_218_);
v_snd_252_ = lean_ctor_get(v_____x_226_, 1);
lean_inc(v_snd_252_);
lean_dec_ref(v_____x_226_);
v_val_253_ = lean_ctor_get(v_a_247_, 0);
lean_inc(v_val_253_);
lean_dec_ref_known(v_a_247_, 1);
v___x_254_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_223_, v_inst_224_, v_mvarId_225_, v_val_253_, v_snd_252_);
return v___x_254_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg(lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_mvarId_259_, lean_object* v_mvarId_x27_260_, lean_object* v_a_261_){
_start:
{
uint8_t v___x_262_; 
v___x_262_ = l_Lean_instBEqMVarId_beq(v_mvarId_259_, v_mvarId_x27_260_);
if (v___x_262_ == 0)
{
lean_object* v___f_263_; lean_object* v___f_264_; lean_object* v___f_265_; lean_object* v___f_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___f_273_; lean_object* v___f_274_; lean_object* v___f_275_; lean_object* v___f_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v_getMCtx_283_; lean_object* v_modifyMCtx_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___f_287_; lean_object* v___x_288_; lean_object* v___f_289_; lean_object* v___f_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v_toApplicative_293_; lean_object* v_toBind_294_; lean_object* v___f_295_; lean_object* v___f_296_; lean_object* v___x_1342__overap_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_inc_ref_n(v_inst_257_, 11);
v___f_263_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_263_, 0, v_inst_257_);
v___f_264_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_264_, 0, v_inst_257_);
v___f_265_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_265_, 0, v_inst_257_);
v___f_266_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_266_, 0, v_inst_257_);
v___x_267_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_267_, 0, lean_box(0));
lean_closure_set(v___x_267_, 1, lean_box(0));
lean_closure_set(v___x_267_, 2, v_inst_257_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___f_263_);
v___x_269_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_269_, 0, lean_box(0));
lean_closure_set(v___x_269_, 1, lean_box(0));
lean_closure_set(v___x_269_, 2, v_inst_257_);
v___x_270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
lean_ctor_set(v___x_270_, 2, v___f_264_);
lean_ctor_set(v___x_270_, 3, v___f_265_);
lean_ctor_set(v___x_270_, 4, v___f_266_);
v___x_271_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_271_, 0, lean_box(0));
lean_closure_set(v___x_271_, 1, lean_box(0));
lean_closure_set(v___x_271_, 2, v_inst_257_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
lean_inc_ref_n(v___x_272_, 7);
v___f_273_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_273_, 0, v___x_272_);
v___f_274_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_274_, 0, v___x_272_);
v___f_275_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_275_, 0, v___x_272_);
v___f_276_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_276_, 0, v___x_272_);
v___x_277_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_277_, 0, lean_box(0));
lean_closure_set(v___x_277_, 1, lean_box(0));
lean_closure_set(v___x_277_, 2, v___x_272_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___f_273_);
v___x_279_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_279_, 0, lean_box(0));
lean_closure_set(v___x_279_, 1, lean_box(0));
lean_closure_set(v___x_279_, 2, v___x_272_);
v___x_280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
lean_ctor_set(v___x_280_, 2, v___f_274_);
lean_ctor_set(v___x_280_, 3, v___f_275_);
lean_ctor_set(v___x_280_, 4, v___f_276_);
v___x_281_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_281_, 0, lean_box(0));
lean_closure_set(v___x_281_, 1, lean_box(0));
lean_closure_set(v___x_281_, 2, v___x_272_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v_getMCtx_283_ = lean_ctor_get(v_inst_258_, 0);
v_modifyMCtx_284_ = lean_ctor_get(v_inst_258_, 1);
v___x_285_ = lean_alloc_closure((void*)(l_ExceptT_lift), 5, 3);
lean_closure_set(v___x_285_, 0, lean_box(0));
lean_closure_set(v___x_285_, 1, lean_box(0));
lean_closure_set(v___x_285_, 2, v___x_272_);
v___x_286_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_286_, 0, lean_box(0));
lean_closure_set(v___x_286_, 1, lean_box(0));
lean_closure_set(v___x_286_, 2, v_inst_257_);
lean_inc(v_modifyMCtx_284_);
v___f_287_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_287_, 0, v_modifyMCtx_284_);
lean_closure_set(v___f_287_, 1, v___x_286_);
lean_inc(v_getMCtx_283_);
v___x_288_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 5);
lean_closure_set(v___x_288_, 0, lean_box(0));
lean_closure_set(v___x_288_, 1, lean_box(0));
lean_closure_set(v___x_288_, 2, v_inst_257_);
lean_closure_set(v___x_288_, 3, lean_box(0));
lean_closure_set(v___x_288_, 4, v_getMCtx_283_);
v___f_289_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_289_, 0, v___f_287_);
lean_closure_set(v___f_289_, 1, v___x_285_);
v___f_290_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__0));
v___x_291_ = lean_alloc_closure((void*)(l_StateT_map), 8, 7);
lean_closure_set(v___x_291_, 0, lean_box(0));
lean_closure_set(v___x_291_, 1, lean_box(0));
lean_closure_set(v___x_291_, 2, v_inst_257_);
lean_closure_set(v___x_291_, 3, lean_box(0));
lean_closure_set(v___x_291_, 4, lean_box(0));
lean_closure_set(v___x_291_, 5, v___f_290_);
lean_closure_set(v___x_291_, 6, v___x_288_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___f_289_);
v_toApplicative_293_ = lean_ctor_get(v_inst_257_, 0);
lean_inc_ref_n(v_toApplicative_293_, 2);
v_toBind_294_ = lean_ctor_get(v_inst_257_, 1);
lean_inc_n(v_toBind_294_, 2);
lean_inc(v_mvarId_259_);
lean_inc_ref(v_inst_258_);
v___f_295_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___lam__0), 5, 4);
lean_closure_set(v___f_295_, 0, v_toApplicative_293_);
lean_closure_set(v___f_295_, 1, v_inst_257_);
lean_closure_set(v___f_295_, 2, v_inst_258_);
lean_closure_set(v___f_295_, 3, v_mvarId_259_);
lean_inc(v_mvarId_x27_260_);
lean_inc_ref(v___x_292_);
lean_inc_ref(v___x_282_);
v___f_296_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___lam__1), 10, 9);
lean_closure_set(v___f_296_, 0, v_toApplicative_293_);
lean_closure_set(v___f_296_, 1, v___x_282_);
lean_closure_set(v___f_296_, 2, v___x_292_);
lean_closure_set(v___f_296_, 3, v_mvarId_x27_260_);
lean_closure_set(v___f_296_, 4, v_toBind_294_);
lean_closure_set(v___f_296_, 5, v___f_295_);
lean_closure_set(v___f_296_, 6, v_inst_257_);
lean_closure_set(v___f_296_, 7, v_inst_258_);
lean_closure_set(v___f_296_, 8, v_mvarId_259_);
v___x_1342__overap_297_ = l_Lean_getExprMVarAssignment_x3f___redArg(v___x_282_, v___x_292_, v_mvarId_x27_260_);
v___x_298_ = lean_apply_1(v___x_1342__overap_297_, v_a_261_);
v___x_299_ = lean_apply_4(v_toBind_294_, lean_box(0), lean_box(0), v___x_298_, v___f_296_);
return v___x_299_;
}
else
{
lean_object* v_toApplicative_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_310_; 
lean_dec(v_mvarId_x27_260_);
lean_dec(v_mvarId_259_);
lean_dec_ref(v_inst_258_);
v_toApplicative_300_ = lean_ctor_get(v_inst_257_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v_inst_257_);
if (v_isSharedCheck_310_ == 0)
{
lean_object* v_unused_311_; 
v_unused_311_ = lean_ctor_get(v_inst_257_, 1);
lean_dec(v_unused_311_);
v___x_302_ = v_inst_257_;
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_toApplicative_300_);
lean_dec(v_inst_257_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v_toPure_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v_toPure_304_ = lean_ctor_get(v_toApplicative_300_, 1);
lean_inc(v_toPure_304_);
lean_dec_ref(v_toApplicative_300_);
v___x_305_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__1));
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v_a_261_);
lean_ctor_set(v___x_302_, 0, v___x_305_);
v___x_307_ = v___x_302_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_a_261_);
v___x_307_ = v_reuseFailAlloc_309_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; 
v___x_308_ = lean_apply_2(v_toPure_304_, lean_box(0), v___x_307_);
return v___x_308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__4(lean_object* v_toPure_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_mvarId_315_, lean_object* v_toBind_316_, lean_object* v_e_317_, lean_object* v_____x_318_){
_start:
{
lean_object* v_d_320_; lean_object* v_b_321_; lean_object* v___y_322_; lean_object* v_fst_326_; 
v_fst_326_ = lean_ctor_get(v_____x_318_, 0);
if (lean_obj_tag(v_fst_326_) == 0)
{
lean_object* v___x_327_; 
lean_dec_ref(v_e_317_);
lean_dec(v_toBind_316_);
lean_dec(v_mvarId_315_);
lean_dec_ref(v_inst_314_);
lean_dec_ref(v_inst_313_);
v___x_327_ = lean_apply_2(v_toPure_312_, lean_box(0), v_____x_318_);
return v___x_327_;
}
else
{
switch(lean_obj_tag(v_e_317_))
{
case 11:
{
lean_object* v_snd_328_; lean_object* v_struct_329_; lean_object* v___x_330_; 
lean_dec(v_toBind_316_);
lean_dec(v_toPure_312_);
v_snd_328_ = lean_ctor_get(v_____x_318_, 1);
lean_inc(v_snd_328_);
lean_dec_ref(v_____x_318_);
v_struct_329_ = lean_ctor_get(v_e_317_, 2);
lean_inc_ref(v_struct_329_);
lean_dec_ref_known(v_e_317_, 3);
v___x_330_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_313_, v_inst_314_, v_mvarId_315_, v_struct_329_, v_snd_328_);
return v___x_330_;
}
case 7:
{
lean_object* v_snd_331_; lean_object* v_binderType_332_; lean_object* v_body_333_; 
v_snd_331_ = lean_ctor_get(v_____x_318_, 1);
lean_inc(v_snd_331_);
lean_dec_ref(v_____x_318_);
v_binderType_332_ = lean_ctor_get(v_e_317_, 1);
lean_inc_ref(v_binderType_332_);
v_body_333_ = lean_ctor_get(v_e_317_, 2);
lean_inc_ref(v_body_333_);
lean_dec_ref_known(v_e_317_, 3);
v_d_320_ = v_binderType_332_;
v_b_321_ = v_body_333_;
v___y_322_ = v_snd_331_;
goto v___jp_319_;
}
case 6:
{
lean_object* v_snd_334_; lean_object* v_binderType_335_; lean_object* v_body_336_; 
v_snd_334_ = lean_ctor_get(v_____x_318_, 1);
lean_inc(v_snd_334_);
lean_dec_ref(v_____x_318_);
v_binderType_335_ = lean_ctor_get(v_e_317_, 1);
lean_inc_ref(v_binderType_335_);
v_body_336_ = lean_ctor_get(v_e_317_, 2);
lean_inc_ref(v_body_336_);
lean_dec_ref_known(v_e_317_, 3);
v_d_320_ = v_binderType_335_;
v_b_321_ = v_body_336_;
v___y_322_ = v_snd_334_;
goto v___jp_319_;
}
case 8:
{
lean_object* v_snd_337_; lean_object* v_type_338_; lean_object* v_value_339_; lean_object* v_body_340_; lean_object* v___f_341_; lean_object* v___f_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_snd_337_ = lean_ctor_get(v_____x_318_, 1);
lean_inc(v_snd_337_);
lean_dec_ref(v_____x_318_);
v_type_338_ = lean_ctor_get(v_e_317_, 1);
lean_inc_ref(v_type_338_);
v_value_339_ = lean_ctor_get(v_e_317_, 2);
lean_inc_ref(v_value_339_);
v_body_340_ = lean_ctor_get(v_e_317_, 3);
lean_inc_ref(v_body_340_);
lean_dec_ref_known(v_e_317_, 4);
lean_inc_n(v_mvarId_315_, 2);
lean_inc_ref_n(v_inst_314_, 2);
lean_inc_ref_n(v_inst_313_, 2);
lean_inc(v_toPure_312_);
v___f_341_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__1), 6, 5);
lean_closure_set(v___f_341_, 0, v_toPure_312_);
lean_closure_set(v___f_341_, 1, v_inst_313_);
lean_closure_set(v___f_341_, 2, v_inst_314_);
lean_closure_set(v___f_341_, 3, v_mvarId_315_);
lean_closure_set(v___f_341_, 4, v_body_340_);
lean_inc(v_toBind_316_);
v___f_342_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__2), 8, 7);
lean_closure_set(v___f_342_, 0, v_toPure_312_);
lean_closure_set(v___f_342_, 1, v_inst_313_);
lean_closure_set(v___f_342_, 2, v_inst_314_);
lean_closure_set(v___f_342_, 3, v_mvarId_315_);
lean_closure_set(v___f_342_, 4, v_value_339_);
lean_closure_set(v___f_342_, 5, v_toBind_316_);
lean_closure_set(v___f_342_, 6, v___f_341_);
v___x_343_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_313_, v_inst_314_, v_mvarId_315_, v_type_338_, v_snd_337_);
v___x_344_ = lean_apply_4(v_toBind_316_, lean_box(0), lean_box(0), v___x_343_, v___f_342_);
return v___x_344_;
}
case 10:
{
lean_object* v_snd_345_; lean_object* v_expr_346_; lean_object* v___x_347_; 
lean_dec(v_toBind_316_);
lean_dec(v_toPure_312_);
v_snd_345_ = lean_ctor_get(v_____x_318_, 1);
lean_inc(v_snd_345_);
lean_dec_ref(v_____x_318_);
v_expr_346_ = lean_ctor_get(v_e_317_, 1);
lean_inc_ref(v_expr_346_);
lean_dec_ref_known(v_e_317_, 2);
v___x_347_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_313_, v_inst_314_, v_mvarId_315_, v_expr_346_, v_snd_345_);
return v___x_347_;
}
case 5:
{
lean_object* v_snd_348_; lean_object* v_fn_349_; lean_object* v_arg_350_; lean_object* v___f_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v_snd_348_ = lean_ctor_get(v_____x_318_, 1);
lean_inc(v_snd_348_);
lean_dec_ref(v_____x_318_);
v_fn_349_ = lean_ctor_get(v_e_317_, 0);
lean_inc_ref(v_fn_349_);
v_arg_350_ = lean_ctor_get(v_e_317_, 1);
lean_inc_ref(v_arg_350_);
lean_dec_ref_known(v_e_317_, 2);
lean_inc(v_mvarId_315_);
lean_inc_ref(v_inst_314_);
lean_inc_ref(v_inst_313_);
v___f_351_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__3), 6, 5);
lean_closure_set(v___f_351_, 0, v_toPure_312_);
lean_closure_set(v___f_351_, 1, v_inst_313_);
lean_closure_set(v___f_351_, 2, v_inst_314_);
lean_closure_set(v___f_351_, 3, v_mvarId_315_);
lean_closure_set(v___f_351_, 4, v_arg_350_);
v___x_352_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_313_, v_inst_314_, v_mvarId_315_, v_fn_349_, v_snd_348_);
v___x_353_ = lean_apply_4(v_toBind_316_, lean_box(0), lean_box(0), v___x_352_, v___f_351_);
return v___x_353_;
}
case 2:
{
lean_object* v_snd_354_; lean_object* v_mvarId_355_; lean_object* v___x_356_; 
lean_dec(v_toBind_316_);
lean_dec(v_toPure_312_);
v_snd_354_ = lean_ctor_get(v_____x_318_, 1);
lean_inc(v_snd_354_);
lean_dec_ref(v_____x_318_);
v_mvarId_355_ = lean_ctor_get(v_e_317_, 0);
lean_inc(v_mvarId_355_);
lean_dec_ref_known(v_e_317_, 1);
v___x_356_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg(v_inst_313_, v_inst_314_, v_mvarId_315_, v_mvarId_355_, v_snd_354_);
return v___x_356_;
}
default: 
{
lean_object* v_snd_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_366_; 
lean_dec_ref(v_e_317_);
lean_dec(v_toBind_316_);
lean_dec(v_mvarId_315_);
lean_dec_ref(v_inst_314_);
lean_dec_ref(v_inst_313_);
v_snd_357_ = lean_ctor_get(v_____x_318_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v_____x_318_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; 
v_unused_367_ = lean_ctor_get(v_____x_318_, 0);
lean_dec(v_unused_367_);
v___x_359_ = v_____x_318_;
v_isShared_360_ = v_isSharedCheck_366_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_snd_357_);
lean_dec(v_____x_318_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_366_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_361_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__2));
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_361_);
v___x_363_ = v___x_359_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_snd_357_);
v___x_363_ = v_reuseFailAlloc_365_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_364_; 
v___x_364_ = lean_apply_2(v_toPure_312_, lean_box(0), v___x_363_);
return v___x_364_;
}
}
}
}
}
v___jp_319_:
{
lean_object* v___f_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
lean_inc(v_mvarId_315_);
lean_inc_ref(v_inst_314_);
lean_inc_ref(v_inst_313_);
v___f_323_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__0), 6, 5);
lean_closure_set(v___f_323_, 0, v_toPure_312_);
lean_closure_set(v___f_323_, 1, v_inst_313_);
lean_closure_set(v___f_323_, 2, v_inst_314_);
lean_closure_set(v___f_323_, 3, v_mvarId_315_);
lean_closure_set(v___f_323_, 4, v_b_321_);
v___x_324_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_313_, v_inst_314_, v_mvarId_315_, v_d_320_, v___y_322_);
v___x_325_ = lean_apply_4(v_toBind_316_, lean_box(0), lean_box(0), v___x_324_, v___f_323_);
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(lean_object* v_inst_368_, lean_object* v_inst_369_, lean_object* v_mvarId_370_, lean_object* v_e_371_, lean_object* v_a_372_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = l_Lean_Expr_hasExprMVar(v_e_371_);
if (v___x_373_ == 0)
{
lean_object* v_toApplicative_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_384_; 
lean_dec_ref(v_e_371_);
lean_dec(v_mvarId_370_);
lean_dec_ref(v_inst_369_);
v_toApplicative_374_ = lean_ctor_get(v_inst_368_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v_inst_368_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; 
v_unused_385_ = lean_ctor_get(v_inst_368_, 1);
lean_dec(v_unused_385_);
v___x_376_ = v_inst_368_;
v_isShared_377_ = v_isSharedCheck_384_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_toApplicative_374_);
lean_dec(v_inst_368_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_384_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v_toPure_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v_toPure_378_ = lean_ctor_get(v_toApplicative_374_, 1);
lean_inc(v_toPure_378_);
lean_dec_ref(v_toApplicative_374_);
v___x_379_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__2));
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 1, v_a_372_);
lean_ctor_set(v___x_376_, 0, v___x_379_);
v___x_381_ = v___x_376_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_a_372_);
v___x_381_ = v_reuseFailAlloc_383_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; 
v___x_382_ = lean_apply_2(v_toPure_378_, lean_box(0), v___x_381_);
return v___x_382_;
}
}
}
else
{
lean_object* v_toApplicative_386_; lean_object* v_toBind_387_; lean_object* v_toPure_388_; lean_object* v___f_389_; lean_object* v___f_390_; lean_object* v___f_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_toApplicative_386_ = lean_ctor_get(v_inst_368_, 0);
v_toBind_387_ = lean_ctor_get(v_inst_368_, 1);
lean_inc_n(v_toBind_387_, 4);
v_toPure_388_ = lean_ctor_get(v_toApplicative_386_, 1);
lean_inc_n(v_toPure_388_, 4);
lean_inc_ref(v_e_371_);
v___f_389_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__4), 7, 6);
lean_closure_set(v___f_389_, 0, v_toPure_388_);
lean_closure_set(v___f_389_, 1, v_inst_368_);
lean_closure_set(v___f_389_, 2, v_inst_369_);
lean_closure_set(v___f_389_, 3, v_mvarId_370_);
lean_closure_set(v___f_389_, 4, v_toBind_387_);
lean_closure_set(v___f_389_, 5, v_e_371_);
v___f_390_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6), 5, 4);
lean_closure_set(v___f_390_, 0, v_toPure_388_);
lean_closure_set(v___f_390_, 1, v_e_371_);
lean_closure_set(v___f_390_, 2, v_toBind_387_);
lean_closure_set(v___f_390_, 3, v___f_389_);
v___f_391_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__7), 2, 1);
lean_closure_set(v___f_391_, 0, v_toPure_388_);
lean_inc_ref(v_a_372_);
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v_a_372_);
lean_ctor_set(v___x_392_, 1, v_a_372_);
v___x_393_ = lean_apply_2(v_toPure_388_, lean_box(0), v___x_392_);
v___x_394_ = lean_apply_4(v_toBind_387_, lean_box(0), lean_box(0), v___x_393_, v___f_391_);
v___x_395_ = lean_apply_4(v_toBind_387_, lean_box(0), lean_box(0), v___x_394_, v___f_390_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__0(lean_object* v_toPure_396_, lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_mvarId_399_, lean_object* v_b_400_, lean_object* v_____x_401_){
_start:
{
lean_object* v_fst_402_; 
v_fst_402_ = lean_ctor_get(v_____x_401_, 0);
if (lean_obj_tag(v_fst_402_) == 0)
{
lean_object* v___x_403_; 
lean_dec_ref(v_b_400_);
lean_dec(v_mvarId_399_);
lean_dec_ref(v_inst_398_);
lean_dec_ref(v_inst_397_);
v___x_403_ = lean_apply_2(v_toPure_396_, lean_box(0), v_____x_401_);
return v___x_403_;
}
else
{
lean_object* v_snd_404_; lean_object* v___x_405_; 
lean_dec(v_toPure_396_);
v_snd_404_ = lean_ctor_get(v_____x_401_, 1);
lean_inc(v_snd_404_);
lean_dec_ref(v_____x_401_);
v___x_405_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_397_, v_inst_398_, v_mvarId_399_, v_b_400_, v_snd_404_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar(lean_object* v_m_406_, lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_mvarId_409_, lean_object* v_mvarId_x27_410_, lean_object* v_a_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg(v_inst_407_, v_inst_408_, v_mvarId_409_, v_mvarId_x27_410_, v_a_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit(lean_object* v_m_413_, lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_mvarId_416_, lean_object* v_e_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_414_, v_inst_415_, v_mvarId_416_, v_e_417_, v_a_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___redArg___lam__0(lean_object* v_toApplicative_420_, uint8_t v___x_421_, uint8_t v___x_422_, lean_object* v_____do__lift_423_){
_start:
{
lean_object* v_fst_424_; 
v_fst_424_ = lean_ctor_get(v_____do__lift_423_, 0);
if (lean_obj_tag(v_fst_424_) == 0)
{
lean_object* v_toPure_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_toPure_425_ = lean_ctor_get(v_toApplicative_420_, 1);
lean_inc(v_toPure_425_);
lean_dec_ref(v_toApplicative_420_);
v___x_426_ = lean_box(v___x_421_);
v___x_427_ = lean_apply_2(v_toPure_425_, lean_box(0), v___x_426_);
return v___x_427_;
}
else
{
lean_object* v_toPure_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_toPure_428_ = lean_ctor_get(v_toApplicative_420_, 1);
lean_inc(v_toPure_428_);
lean_dec_ref(v_toApplicative_420_);
v___x_429_ = lean_box(v___x_422_);
v___x_430_ = lean_apply_2(v_toPure_428_, lean_box(0), v___x_429_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___redArg___lam__0___boxed(lean_object* v_toApplicative_431_, lean_object* v___x_432_, lean_object* v___x_433_, lean_object* v_____do__lift_434_){
_start:
{
uint8_t v___x_240__boxed_435_; uint8_t v___x_241__boxed_436_; lean_object* v_res_437_; 
v___x_240__boxed_435_ = lean_unbox(v___x_432_);
v___x_241__boxed_436_ = lean_unbox(v___x_433_);
v_res_437_ = l_Lean_occursCheck___redArg___lam__0(v_toApplicative_431_, v___x_240__boxed_435_, v___x_241__boxed_436_, v_____do__lift_434_);
lean_dec_ref(v_____do__lift_434_);
return v_res_437_;
}
}
static lean_object* _init_l_Lean_occursCheck___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_438_; lean_object* v___x_439_; 
v_cellCount_438_ = lean_unsigned_to_nat(16u);
v___x_439_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_438_);
return v___x_439_;
}
}
static lean_object* _init_l_Lean_occursCheck___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_440_; lean_object* v___x_441_; 
v_cellCount_440_ = lean_unsigned_to_nat(16u);
v___x_441_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_440_);
return v___x_441_;
}
}
static lean_object* _init_l_Lean_occursCheck___redArg___closed__2(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_442_ = lean_obj_once(&l_Lean_occursCheck___redArg___closed__1, &l_Lean_occursCheck___redArg___closed__1_once, _init_l_Lean_occursCheck___redArg___closed__1);
v___x_443_ = lean_obj_once(&l_Lean_occursCheck___redArg___closed__0, &l_Lean_occursCheck___redArg___closed__0_once, _init_l_Lean_occursCheck___redArg___closed__0);
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v___x_443_);
lean_ctor_set(v___x_445_, 2, v___x_442_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___redArg(lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_mvarId_448_, lean_object* v_e_449_){
_start:
{
uint8_t v___x_450_; 
v___x_450_ = l_Lean_Expr_hasExprMVar(v_e_449_);
if (v___x_450_ == 0)
{
lean_object* v_toApplicative_451_; lean_object* v_toPure_452_; uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec_ref(v_e_449_);
lean_dec(v_mvarId_448_);
lean_dec_ref(v_inst_447_);
v_toApplicative_451_ = lean_ctor_get(v_inst_446_, 0);
lean_inc_ref(v_toApplicative_451_);
lean_dec_ref(v_inst_446_);
v_toPure_452_ = lean_ctor_get(v_toApplicative_451_, 1);
lean_inc(v_toPure_452_);
lean_dec_ref(v_toApplicative_451_);
v___x_453_ = 1;
v___x_454_ = lean_box(v___x_453_);
v___x_455_ = lean_apply_2(v_toPure_452_, lean_box(0), v___x_454_);
return v___x_455_;
}
else
{
lean_object* v_toApplicative_456_; lean_object* v_toBind_457_; uint8_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___f_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_toApplicative_456_ = lean_ctor_get(v_inst_446_, 0);
v_toBind_457_ = lean_ctor_get(v_inst_446_, 1);
lean_inc(v_toBind_457_);
v___x_458_ = 0;
v___x_459_ = lean_box(v___x_458_);
v___x_460_ = lean_box(v___x_450_);
lean_inc_ref(v_toApplicative_456_);
v___f_461_ = lean_alloc_closure((void*)(l_Lean_occursCheck___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_461_, 0, v_toApplicative_456_);
lean_closure_set(v___f_461_, 1, v___x_459_);
lean_closure_set(v___f_461_, 2, v___x_460_);
v___x_462_ = lean_obj_once(&l_Lean_occursCheck___redArg___closed__2, &l_Lean_occursCheck___redArg___closed__2_once, _init_l_Lean_occursCheck___redArg___closed__2);
v___x_463_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_446_, v_inst_447_, v_mvarId_448_, v_e_449_, v___x_462_);
v___x_464_ = lean_apply_4(v_toBind_457_, lean_box(0), lean_box(0), v___x_463_, v___f_461_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck(lean_object* v_m_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_mvarId_468_, lean_object* v_e_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_occursCheck___redArg(v_inst_466_, v_inst_467_, v_mvarId_468_, v_e_469_);
return v___x_470_;
}
}
lean_object* runtime_initialize_Lean_MetavarContext(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_OccursCheck(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_MetavarContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_OccursCheck(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_MetavarContext(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_OccursCheck(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_MetavarContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_OccursCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_OccursCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_OccursCheck(builtin);
}
#ifdef __cplusplus
}
#endif
