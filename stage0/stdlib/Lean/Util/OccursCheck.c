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
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
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
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_ExceptT_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_lift___redArg___lam__0(lean_object*);
lean_object* l_Lean_getDelayedMVarAssignment_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getExprMVarAssignment_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__5(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__0 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___closed__0 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___closed__1 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6(lean_object* v_toPure_29_, lean_object* v___x_30_, lean_object* v___x_31_, lean_object* v_e_32_, lean_object* v_toBind_33_, lean_object* v___f_34_, lean_object* v_____x_35_){
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
lean_dec_ref(v___x_31_);
lean_dec_ref(v___x_30_);
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
v___x_49_ = lean_apply_2(v_toPure_29_, lean_box(0), v___x_48_);
return v___x_49_;
}
}
}
}
}
else
{
lean_object* v_snd_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_75_; 
v_snd_55_ = lean_ctor_get(v_____x_35_, 1);
v_isSharedCheck_75_ = !lean_is_exclusive(v_____x_35_);
if (v_isSharedCheck_75_ == 0)
{
lean_object* v_unused_76_; 
v_unused_76_ = lean_ctor_get(v_____x_35_, 0);
lean_dec(v_unused_76_);
v___x_57_ = v_____x_35_;
v_isShared_58_ = v_isSharedCheck_75_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_snd_55_);
lean_dec(v_____x_35_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_75_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v_a_59_; uint8_t v___x_60_; 
v_a_59_ = lean_ctor_get(v_fst_36_, 0);
lean_inc(v_a_59_);
lean_dec_ref_known(v_fst_36_, 1);
lean_inc_ref(v_e_32_);
lean_inc_ref(v___x_31_);
lean_inc_ref(v___x_30_);
v___x_60_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_30_, v___x_31_, v_a_59_, v_e_32_);
lean_dec(v_a_59_);
if (v___x_60_ == 0)
{
lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
lean_inc(v_toPure_29_);
v___f_61_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__5), 2, 1);
lean_closure_set(v___f_61_, 0, v_toPure_29_);
v___x_62_ = lean_box(0);
v___x_63_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_30_, v___x_31_, v_snd_55_, v_e_32_, v___x_62_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 1, v___x_63_);
lean_ctor_set(v___x_57_, 0, v___x_62_);
v___x_65_ = v___x_57_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v___x_63_);
v___x_65_ = v_reuseFailAlloc_69_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = lean_apply_2(v_toPure_29_, lean_box(0), v___x_65_);
lean_inc(v_toBind_33_);
v___x_67_ = lean_apply_4(v_toBind_33_, lean_box(0), lean_box(0), v___x_66_, v___f_61_);
v___x_68_ = lean_apply_4(v_toBind_33_, lean_box(0), lean_box(0), v___x_67_, v___f_34_);
return v___x_68_;
}
}
else
{
lean_object* v___x_70_; lean_object* v___x_72_; 
lean_dec(v___f_34_);
lean_dec(v_toBind_33_);
lean_dec_ref(v_e_32_);
lean_dec_ref(v___x_31_);
lean_dec_ref(v___x_30_);
v___x_70_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__0));
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_70_);
v___x_72_ = v___x_57_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_70_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_snd_55_);
v___x_72_ = v_reuseFailAlloc_74_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; 
v___x_73_ = lean_apply_2(v_toPure_29_, lean_box(0), v___x_72_);
return v___x_73_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__1(lean_object* v_toPure_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_mvarId_80_, lean_object* v_body_81_, lean_object* v_____x_82_){
_start:
{
lean_object* v_fst_83_; 
v_fst_83_ = lean_ctor_get(v_____x_82_, 0);
if (lean_obj_tag(v_fst_83_) == 0)
{
lean_object* v___x_84_; 
lean_dec_ref(v_body_81_);
lean_dec(v_mvarId_80_);
lean_dec_ref(v_inst_79_);
lean_dec_ref(v_inst_78_);
v___x_84_ = lean_apply_2(v_toPure_77_, lean_box(0), v_____x_82_);
return v___x_84_;
}
else
{
lean_object* v_snd_85_; lean_object* v___x_86_; 
lean_dec(v_toPure_77_);
v_snd_85_ = lean_ctor_get(v_____x_82_, 1);
lean_inc(v_snd_85_);
lean_dec_ref(v_____x_82_);
v___x_86_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_78_, v_inst_79_, v_mvarId_80_, v_body_81_, v_snd_85_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__2(lean_object* v_toPure_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_mvarId_90_, lean_object* v_value_91_, lean_object* v_toBind_92_, lean_object* v___f_93_, lean_object* v_____x_94_){
_start:
{
lean_object* v_fst_95_; 
v_fst_95_ = lean_ctor_get(v_____x_94_, 0);
if (lean_obj_tag(v_fst_95_) == 0)
{
lean_object* v___x_96_; 
lean_dec(v___f_93_);
lean_dec(v_toBind_92_);
lean_dec_ref(v_value_91_);
lean_dec(v_mvarId_90_);
lean_dec_ref(v_inst_89_);
lean_dec_ref(v_inst_88_);
v___x_96_ = lean_apply_2(v_toPure_87_, lean_box(0), v_____x_94_);
return v___x_96_;
}
else
{
lean_object* v_snd_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
lean_dec(v_toPure_87_);
v_snd_97_ = lean_ctor_get(v_____x_94_, 1);
lean_inc(v_snd_97_);
lean_dec_ref(v_____x_94_);
v___x_98_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_88_, v_inst_89_, v_mvarId_90_, v_value_91_, v_snd_97_);
v___x_99_ = lean_apply_4(v_toBind_92_, lean_box(0), lean_box(0), v___x_98_, v___f_93_);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__3(lean_object* v_toPure_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_mvarId_103_, lean_object* v_arg_104_, lean_object* v_____x_105_){
_start:
{
lean_object* v_fst_106_; 
v_fst_106_ = lean_ctor_get(v_____x_105_, 0);
if (lean_obj_tag(v_fst_106_) == 0)
{
lean_object* v___x_107_; 
lean_dec_ref(v_arg_104_);
lean_dec(v_mvarId_103_);
lean_dec_ref(v_inst_102_);
lean_dec_ref(v_inst_101_);
v___x_107_ = lean_apply_2(v_toPure_100_, lean_box(0), v_____x_105_);
return v___x_107_;
}
else
{
lean_object* v_snd_108_; lean_object* v___x_109_; 
lean_dec(v_toPure_100_);
v_snd_108_ = lean_ctor_get(v_____x_105_, 1);
lean_inc(v_snd_108_);
lean_dec_ref(v_____x_105_);
v___x_109_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_101_, v_inst_102_, v_mvarId_103_, v_arg_104_, v_snd_108_);
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___lam__0(lean_object* v_toApplicative_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_mvarId_114_, lean_object* v_____x_115_){
_start:
{
lean_object* v_fst_116_; 
v_fst_116_ = lean_ctor_get(v_____x_115_, 0);
lean_inc(v_fst_116_);
if (lean_obj_tag(v_fst_116_) == 0)
{
lean_object* v_snd_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_134_; 
lean_dec(v_mvarId_114_);
lean_dec_ref(v_inst_113_);
lean_dec_ref(v_inst_112_);
v_snd_117_ = lean_ctor_get(v_____x_115_, 1);
v_isSharedCheck_134_ = !lean_is_exclusive(v_____x_115_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; 
v_unused_135_ = lean_ctor_get(v_____x_115_, 0);
lean_dec(v_unused_135_);
v___x_119_ = v_____x_115_;
v_isShared_120_ = v_isSharedCheck_134_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_snd_117_);
lean_dec(v_____x_115_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_134_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_133_; 
v_a_121_ = lean_ctor_get(v_fst_116_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v_fst_116_);
if (v_isSharedCheck_133_ == 0)
{
v___x_123_ = v_fst_116_;
v_isShared_124_ = v_isSharedCheck_133_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v_fst_116_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_133_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v_toPure_125_; lean_object* v___x_127_; 
v_toPure_125_ = lean_ctor_get(v_toApplicative_111_, 1);
lean_inc(v_toPure_125_);
lean_dec_ref(v_toApplicative_111_);
if (v_isShared_124_ == 0)
{
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_a_121_);
v___x_127_ = v_reuseFailAlloc_132_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; 
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v___x_127_);
v___x_129_ = v___x_119_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_snd_117_);
v___x_129_ = v_reuseFailAlloc_131_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_130_; 
v___x_130_ = lean_apply_2(v_toPure_125_, lean_box(0), v___x_129_);
return v___x_130_;
}
}
}
}
}
else
{
lean_object* v_a_136_; 
v_a_136_ = lean_ctor_get(v_fst_116_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v_fst_116_, 1);
if (lean_obj_tag(v_a_136_) == 0)
{
lean_object* v_snd_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_147_; 
lean_dec(v_mvarId_114_);
lean_dec_ref(v_inst_113_);
lean_dec_ref(v_inst_112_);
v_snd_137_ = lean_ctor_get(v_____x_115_, 1);
v_isSharedCheck_147_ = !lean_is_exclusive(v_____x_115_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; 
v_unused_148_ = lean_ctor_get(v_____x_115_, 0);
lean_dec(v_unused_148_);
v___x_139_ = v_____x_115_;
v_isShared_140_ = v_isSharedCheck_147_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_snd_137_);
lean_dec(v_____x_115_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_147_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v_toPure_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
v_toPure_141_ = lean_ctor_get(v_toApplicative_111_, 1);
lean_inc(v_toPure_141_);
lean_dec_ref(v_toApplicative_111_);
v___x_142_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__0));
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v___x_142_);
v___x_144_ = v___x_139_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_snd_137_);
v___x_144_ = v_reuseFailAlloc_146_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_145_; 
v___x_145_ = lean_apply_2(v_toPure_141_, lean_box(0), v___x_144_);
return v___x_145_;
}
}
}
else
{
lean_object* v_val_149_; lean_object* v_snd_150_; lean_object* v_mvarIdPending_151_; lean_object* v___x_152_; 
lean_dec_ref(v_toApplicative_111_);
v_val_149_ = lean_ctor_get(v_a_136_, 0);
lean_inc(v_val_149_);
lean_dec_ref_known(v_a_136_, 1);
v_snd_150_ = lean_ctor_get(v_____x_115_, 1);
lean_inc(v_snd_150_);
lean_dec_ref(v_____x_115_);
v_mvarIdPending_151_ = lean_ctor_get(v_val_149_, 1);
lean_inc(v_mvarIdPending_151_);
lean_dec(v_val_149_);
v___x_152_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg(v_inst_112_, v_inst_113_, v_mvarId_114_, v_mvarIdPending_151_, v_snd_150_);
return v___x_152_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___lam__1(lean_object* v_toApplicative_153_, lean_object* v___x_154_, lean_object* v___x_155_, lean_object* v_mvarId_x27_156_, lean_object* v_toBind_157_, lean_object* v___f_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_mvarId_161_, lean_object* v_____x_162_){
_start:
{
lean_object* v_fst_163_; 
v_fst_163_ = lean_ctor_get(v_____x_162_, 0);
lean_inc(v_fst_163_);
if (lean_obj_tag(v_fst_163_) == 0)
{
lean_object* v_snd_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_181_; 
lean_dec(v_mvarId_161_);
lean_dec_ref(v_inst_160_);
lean_dec_ref(v_inst_159_);
lean_dec(v___f_158_);
lean_dec(v_toBind_157_);
lean_dec(v_mvarId_x27_156_);
lean_dec_ref(v___x_155_);
lean_dec_ref(v___x_154_);
v_snd_164_ = lean_ctor_get(v_____x_162_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v_____x_162_);
if (v_isSharedCheck_181_ == 0)
{
lean_object* v_unused_182_; 
v_unused_182_ = lean_ctor_get(v_____x_162_, 0);
lean_dec(v_unused_182_);
v___x_166_ = v_____x_162_;
v_isShared_167_ = v_isSharedCheck_181_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_snd_164_);
lean_dec(v_____x_162_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_181_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_180_; 
v_a_168_ = lean_ctor_get(v_fst_163_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v_fst_163_);
if (v_isSharedCheck_180_ == 0)
{
v___x_170_ = v_fst_163_;
v_isShared_171_ = v_isSharedCheck_180_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v_fst_163_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_180_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v_toPure_172_; lean_object* v___x_174_; 
v_toPure_172_ = lean_ctor_get(v_toApplicative_153_, 1);
lean_inc(v_toPure_172_);
lean_dec_ref(v_toApplicative_153_);
if (v_isShared_171_ == 0)
{
v___x_174_ = v___x_170_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_168_);
v___x_174_ = v_reuseFailAlloc_179_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_176_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_174_);
v___x_176_ = v___x_166_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_snd_164_);
v___x_176_ = v_reuseFailAlloc_178_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_177_; 
v___x_177_ = lean_apply_2(v_toPure_172_, lean_box(0), v___x_176_);
return v___x_177_;
}
}
}
}
}
else
{
lean_object* v_a_183_; 
lean_dec_ref(v_toApplicative_153_);
v_a_183_ = lean_ctor_get(v_fst_163_, 0);
lean_inc(v_a_183_);
lean_dec_ref_known(v_fst_163_, 1);
if (lean_obj_tag(v_a_183_) == 0)
{
lean_object* v_snd_184_; lean_object* v___x_4611__overap_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
lean_dec(v_mvarId_161_);
lean_dec_ref(v_inst_160_);
lean_dec_ref(v_inst_159_);
v_snd_184_ = lean_ctor_get(v_____x_162_, 1);
lean_inc(v_snd_184_);
lean_dec_ref(v_____x_162_);
v___x_4611__overap_185_ = l_Lean_getDelayedMVarAssignment_x3f___redArg(v___x_154_, v___x_155_, v_mvarId_x27_156_);
v___x_186_ = lean_apply_1(v___x_4611__overap_185_, v_snd_184_);
v___x_187_ = lean_apply_4(v_toBind_157_, lean_box(0), lean_box(0), v___x_186_, v___f_158_);
return v___x_187_;
}
else
{
lean_object* v_snd_188_; lean_object* v_val_189_; lean_object* v___x_190_; 
lean_dec(v___f_158_);
lean_dec(v_toBind_157_);
lean_dec(v_mvarId_x27_156_);
lean_dec_ref(v___x_155_);
lean_dec_ref(v___x_154_);
v_snd_188_ = lean_ctor_get(v_____x_162_, 1);
lean_inc(v_snd_188_);
lean_dec_ref(v_____x_162_);
v_val_189_ = lean_ctor_get(v_a_183_, 0);
lean_inc(v_val_189_);
lean_dec_ref_known(v_a_183_, 1);
v___x_190_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_159_, v_inst_160_, v_mvarId_161_, v_val_189_, v_snd_188_);
return v___x_190_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg(lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_mvarId_195_, lean_object* v_mvarId_x27_196_, lean_object* v_a_197_){
_start:
{
lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___f_208_; lean_object* v___f_209_; lean_object* v___f_210_; lean_object* v___f_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v_getMCtx_218_; lean_object* v_modifyMCtx_219_; uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___f_223_; lean_object* v___x_224_; lean_object* v___f_225_; lean_object* v___f_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
lean_inc_ref_n(v_inst_193_, 10);
v___f_198_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_198_, 0, v_inst_193_);
v___f_199_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_199_, 0, v_inst_193_);
v___f_200_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_200_, 0, v_inst_193_);
v___f_201_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_201_, 0, v_inst_193_);
v___x_202_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_202_, 0, lean_box(0));
lean_closure_set(v___x_202_, 1, lean_box(0));
lean_closure_set(v___x_202_, 2, v_inst_193_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v___f_198_);
v___x_204_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_204_, 0, lean_box(0));
lean_closure_set(v___x_204_, 1, lean_box(0));
lean_closure_set(v___x_204_, 2, v_inst_193_);
v___x_205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_205_, 0, v___x_203_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
lean_ctor_set(v___x_205_, 2, v___f_199_);
lean_ctor_set(v___x_205_, 3, v___f_200_);
lean_ctor_set(v___x_205_, 4, v___f_201_);
v___x_206_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_206_, 0, lean_box(0));
lean_closure_set(v___x_206_, 1, lean_box(0));
lean_closure_set(v___x_206_, 2, v_inst_193_);
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
lean_inc_ref_n(v___x_207_, 7);
v___f_208_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_208_, 0, v___x_207_);
v___f_209_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_209_, 0, v___x_207_);
v___f_210_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_210_, 0, v___x_207_);
v___f_211_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_211_, 0, v___x_207_);
v___x_212_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_212_, 0, lean_box(0));
lean_closure_set(v___x_212_, 1, lean_box(0));
lean_closure_set(v___x_212_, 2, v___x_207_);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v___f_208_);
v___x_214_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_214_, 0, lean_box(0));
lean_closure_set(v___x_214_, 1, lean_box(0));
lean_closure_set(v___x_214_, 2, v___x_207_);
v___x_215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_215_, 0, v___x_213_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
lean_ctor_set(v___x_215_, 2, v___f_209_);
lean_ctor_set(v___x_215_, 3, v___f_210_);
lean_ctor_set(v___x_215_, 4, v___f_211_);
v___x_216_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_216_, 0, lean_box(0));
lean_closure_set(v___x_216_, 1, lean_box(0));
lean_closure_set(v___x_216_, 2, v___x_207_);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v_getMCtx_218_ = lean_ctor_get(v_inst_194_, 0);
v_modifyMCtx_219_ = lean_ctor_get(v_inst_194_, 1);
v___x_220_ = l_Lean_instBEqMVarId_beq(v_mvarId_195_, v_mvarId_x27_196_);
v___x_221_ = lean_alloc_closure((void*)(l_ExceptT_lift), 5, 3);
lean_closure_set(v___x_221_, 0, lean_box(0));
lean_closure_set(v___x_221_, 1, lean_box(0));
lean_closure_set(v___x_221_, 2, v___x_207_);
v___x_222_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_222_, 0, lean_box(0));
lean_closure_set(v___x_222_, 1, lean_box(0));
lean_closure_set(v___x_222_, 2, v_inst_193_);
lean_inc(v_modifyMCtx_219_);
v___f_223_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_223_, 0, v_modifyMCtx_219_);
lean_closure_set(v___f_223_, 1, v___x_222_);
lean_inc(v_getMCtx_218_);
v___x_224_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 5);
lean_closure_set(v___x_224_, 0, lean_box(0));
lean_closure_set(v___x_224_, 1, lean_box(0));
lean_closure_set(v___x_224_, 2, v_inst_193_);
lean_closure_set(v___x_224_, 3, lean_box(0));
lean_closure_set(v___x_224_, 4, v_getMCtx_218_);
v___f_225_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_225_, 0, v___f_223_);
lean_closure_set(v___f_225_, 1, v___x_221_);
v___f_226_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__0));
v___x_227_ = lean_alloc_closure((void*)(l_StateT_map), 8, 7);
lean_closure_set(v___x_227_, 0, lean_box(0));
lean_closure_set(v___x_227_, 1, lean_box(0));
lean_closure_set(v___x_227_, 2, v_inst_193_);
lean_closure_set(v___x_227_, 3, lean_box(0));
lean_closure_set(v___x_227_, 4, lean_box(0));
lean_closure_set(v___x_227_, 5, v___f_226_);
lean_closure_set(v___x_227_, 6, v___x_224_);
v___x_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___f_225_);
if (v___x_220_ == 0)
{
lean_object* v_toApplicative_229_; lean_object* v_toBind_230_; lean_object* v___f_231_; lean_object* v___f_232_; lean_object* v___x_866__overap_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_toApplicative_229_ = lean_ctor_get(v_inst_193_, 0);
lean_inc_ref_n(v_toApplicative_229_, 2);
v_toBind_230_ = lean_ctor_get(v_inst_193_, 1);
lean_inc_n(v_toBind_230_, 2);
lean_inc(v_mvarId_195_);
lean_inc_ref(v_inst_194_);
lean_inc_ref(v_inst_193_);
v___f_231_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___lam__0), 5, 4);
lean_closure_set(v___f_231_, 0, v_toApplicative_229_);
lean_closure_set(v___f_231_, 1, v_inst_193_);
lean_closure_set(v___f_231_, 2, v_inst_194_);
lean_closure_set(v___f_231_, 3, v_mvarId_195_);
lean_inc(v_mvarId_x27_196_);
lean_inc_ref(v___x_228_);
lean_inc_ref(v___x_217_);
v___f_232_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___lam__1), 10, 9);
lean_closure_set(v___f_232_, 0, v_toApplicative_229_);
lean_closure_set(v___f_232_, 1, v___x_217_);
lean_closure_set(v___f_232_, 2, v___x_228_);
lean_closure_set(v___f_232_, 3, v_mvarId_x27_196_);
lean_closure_set(v___f_232_, 4, v_toBind_230_);
lean_closure_set(v___f_232_, 5, v___f_231_);
lean_closure_set(v___f_232_, 6, v_inst_193_);
lean_closure_set(v___f_232_, 7, v_inst_194_);
lean_closure_set(v___f_232_, 8, v_mvarId_195_);
v___x_866__overap_233_ = l_Lean_getExprMVarAssignment_x3f___redArg(v___x_217_, v___x_228_, v_mvarId_x27_196_);
v___x_234_ = lean_apply_1(v___x_866__overap_233_, v_a_197_);
v___x_235_ = lean_apply_4(v_toBind_230_, lean_box(0), lean_box(0), v___x_234_, v___f_232_);
return v___x_235_;
}
else
{
lean_object* v_toApplicative_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_246_; 
lean_dec_ref_known(v___x_228_, 2);
lean_dec_ref_known(v___x_217_, 2);
lean_dec(v_mvarId_x27_196_);
lean_dec(v_mvarId_195_);
lean_dec_ref(v_inst_194_);
v_toApplicative_236_ = lean_ctor_get(v_inst_193_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v_inst_193_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; 
v_unused_247_ = lean_ctor_get(v_inst_193_, 1);
lean_dec(v_unused_247_);
v___x_238_ = v_inst_193_;
v_isShared_239_ = v_isSharedCheck_246_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_toApplicative_236_);
lean_dec(v_inst_193_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_246_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v_toPure_240_; lean_object* v___x_241_; lean_object* v___x_243_; 
v_toPure_240_ = lean_ctor_get(v_toApplicative_236_, 1);
lean_inc(v_toPure_240_);
lean_dec_ref(v_toApplicative_236_);
v___x_241_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__1));
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v_a_197_);
lean_ctor_set(v___x_238_, 0, v___x_241_);
v___x_243_ = v___x_238_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_a_197_);
v___x_243_ = v_reuseFailAlloc_245_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; 
v___x_244_ = lean_apply_2(v_toPure_240_, lean_box(0), v___x_243_);
return v___x_244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__4(lean_object* v_toPure_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_mvarId_251_, lean_object* v_toBind_252_, lean_object* v_e_253_, lean_object* v_____x_254_){
_start:
{
lean_object* v_d_256_; lean_object* v_b_257_; lean_object* v___y_258_; lean_object* v_fst_262_; 
v_fst_262_ = lean_ctor_get(v_____x_254_, 0);
if (lean_obj_tag(v_fst_262_) == 0)
{
lean_object* v___x_263_; 
lean_dec_ref(v_e_253_);
lean_dec(v_toBind_252_);
lean_dec(v_mvarId_251_);
lean_dec_ref(v_inst_250_);
lean_dec_ref(v_inst_249_);
v___x_263_ = lean_apply_2(v_toPure_248_, lean_box(0), v_____x_254_);
return v___x_263_;
}
else
{
switch(lean_obj_tag(v_e_253_))
{
case 11:
{
lean_object* v_snd_264_; lean_object* v_struct_265_; lean_object* v___x_266_; 
lean_dec(v_toBind_252_);
lean_dec(v_toPure_248_);
v_snd_264_ = lean_ctor_get(v_____x_254_, 1);
lean_inc(v_snd_264_);
lean_dec_ref(v_____x_254_);
v_struct_265_ = lean_ctor_get(v_e_253_, 2);
lean_inc_ref(v_struct_265_);
lean_dec_ref_known(v_e_253_, 3);
v___x_266_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_249_, v_inst_250_, v_mvarId_251_, v_struct_265_, v_snd_264_);
return v___x_266_;
}
case 7:
{
lean_object* v_snd_267_; lean_object* v_binderType_268_; lean_object* v_body_269_; 
v_snd_267_ = lean_ctor_get(v_____x_254_, 1);
lean_inc(v_snd_267_);
lean_dec_ref(v_____x_254_);
v_binderType_268_ = lean_ctor_get(v_e_253_, 1);
lean_inc_ref(v_binderType_268_);
v_body_269_ = lean_ctor_get(v_e_253_, 2);
lean_inc_ref(v_body_269_);
lean_dec_ref_known(v_e_253_, 3);
v_d_256_ = v_binderType_268_;
v_b_257_ = v_body_269_;
v___y_258_ = v_snd_267_;
goto v___jp_255_;
}
case 6:
{
lean_object* v_snd_270_; lean_object* v_binderType_271_; lean_object* v_body_272_; 
v_snd_270_ = lean_ctor_get(v_____x_254_, 1);
lean_inc(v_snd_270_);
lean_dec_ref(v_____x_254_);
v_binderType_271_ = lean_ctor_get(v_e_253_, 1);
lean_inc_ref(v_binderType_271_);
v_body_272_ = lean_ctor_get(v_e_253_, 2);
lean_inc_ref(v_body_272_);
lean_dec_ref_known(v_e_253_, 3);
v_d_256_ = v_binderType_271_;
v_b_257_ = v_body_272_;
v___y_258_ = v_snd_270_;
goto v___jp_255_;
}
case 8:
{
lean_object* v_snd_273_; lean_object* v_type_274_; lean_object* v_value_275_; lean_object* v_body_276_; lean_object* v___f_277_; lean_object* v___f_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v_snd_273_ = lean_ctor_get(v_____x_254_, 1);
lean_inc(v_snd_273_);
lean_dec_ref(v_____x_254_);
v_type_274_ = lean_ctor_get(v_e_253_, 1);
lean_inc_ref(v_type_274_);
v_value_275_ = lean_ctor_get(v_e_253_, 2);
lean_inc_ref(v_value_275_);
v_body_276_ = lean_ctor_get(v_e_253_, 3);
lean_inc_ref(v_body_276_);
lean_dec_ref_known(v_e_253_, 4);
lean_inc_n(v_mvarId_251_, 2);
lean_inc_ref_n(v_inst_250_, 2);
lean_inc_ref_n(v_inst_249_, 2);
lean_inc(v_toPure_248_);
v___f_277_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__1), 6, 5);
lean_closure_set(v___f_277_, 0, v_toPure_248_);
lean_closure_set(v___f_277_, 1, v_inst_249_);
lean_closure_set(v___f_277_, 2, v_inst_250_);
lean_closure_set(v___f_277_, 3, v_mvarId_251_);
lean_closure_set(v___f_277_, 4, v_body_276_);
lean_inc(v_toBind_252_);
v___f_278_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__2), 8, 7);
lean_closure_set(v___f_278_, 0, v_toPure_248_);
lean_closure_set(v___f_278_, 1, v_inst_249_);
lean_closure_set(v___f_278_, 2, v_inst_250_);
lean_closure_set(v___f_278_, 3, v_mvarId_251_);
lean_closure_set(v___f_278_, 4, v_value_275_);
lean_closure_set(v___f_278_, 5, v_toBind_252_);
lean_closure_set(v___f_278_, 6, v___f_277_);
v___x_279_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_249_, v_inst_250_, v_mvarId_251_, v_type_274_, v_snd_273_);
v___x_280_ = lean_apply_4(v_toBind_252_, lean_box(0), lean_box(0), v___x_279_, v___f_278_);
return v___x_280_;
}
case 10:
{
lean_object* v_snd_281_; lean_object* v_expr_282_; lean_object* v___x_283_; 
lean_dec(v_toBind_252_);
lean_dec(v_toPure_248_);
v_snd_281_ = lean_ctor_get(v_____x_254_, 1);
lean_inc(v_snd_281_);
lean_dec_ref(v_____x_254_);
v_expr_282_ = lean_ctor_get(v_e_253_, 1);
lean_inc_ref(v_expr_282_);
lean_dec_ref_known(v_e_253_, 2);
v___x_283_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_249_, v_inst_250_, v_mvarId_251_, v_expr_282_, v_snd_281_);
return v___x_283_;
}
case 5:
{
lean_object* v_snd_284_; lean_object* v_fn_285_; lean_object* v_arg_286_; lean_object* v___f_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_snd_284_ = lean_ctor_get(v_____x_254_, 1);
lean_inc(v_snd_284_);
lean_dec_ref(v_____x_254_);
v_fn_285_ = lean_ctor_get(v_e_253_, 0);
lean_inc_ref(v_fn_285_);
v_arg_286_ = lean_ctor_get(v_e_253_, 1);
lean_inc_ref(v_arg_286_);
lean_dec_ref_known(v_e_253_, 2);
lean_inc(v_mvarId_251_);
lean_inc_ref(v_inst_250_);
lean_inc_ref(v_inst_249_);
v___f_287_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__3), 6, 5);
lean_closure_set(v___f_287_, 0, v_toPure_248_);
lean_closure_set(v___f_287_, 1, v_inst_249_);
lean_closure_set(v___f_287_, 2, v_inst_250_);
lean_closure_set(v___f_287_, 3, v_mvarId_251_);
lean_closure_set(v___f_287_, 4, v_arg_286_);
v___x_288_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_249_, v_inst_250_, v_mvarId_251_, v_fn_285_, v_snd_284_);
v___x_289_ = lean_apply_4(v_toBind_252_, lean_box(0), lean_box(0), v___x_288_, v___f_287_);
return v___x_289_;
}
case 2:
{
lean_object* v_snd_290_; lean_object* v_mvarId_291_; lean_object* v___x_292_; 
lean_dec(v_toBind_252_);
lean_dec(v_toPure_248_);
v_snd_290_ = lean_ctor_get(v_____x_254_, 1);
lean_inc(v_snd_290_);
lean_dec_ref(v_____x_254_);
v_mvarId_291_ = lean_ctor_get(v_e_253_, 0);
lean_inc(v_mvarId_291_);
lean_dec_ref_known(v_e_253_, 1);
v___x_292_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg(v_inst_249_, v_inst_250_, v_mvarId_251_, v_mvarId_291_, v_snd_290_);
return v___x_292_;
}
default: 
{
lean_object* v_snd_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_302_; 
lean_dec_ref(v_e_253_);
lean_dec(v_toBind_252_);
lean_dec(v_mvarId_251_);
lean_dec_ref(v_inst_250_);
lean_dec_ref(v_inst_249_);
v_snd_293_ = lean_ctor_get(v_____x_254_, 1);
v_isSharedCheck_302_ = !lean_is_exclusive(v_____x_254_);
if (v_isSharedCheck_302_ == 0)
{
lean_object* v_unused_303_; 
v_unused_303_ = lean_ctor_get(v_____x_254_, 0);
lean_dec(v_unused_303_);
v___x_295_ = v_____x_254_;
v_isShared_296_ = v_isSharedCheck_302_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_snd_293_);
lean_dec(v_____x_254_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_302_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__0));
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_297_);
v___x_299_ = v___x_295_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v_snd_293_);
v___x_299_ = v_reuseFailAlloc_301_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_300_; 
v___x_300_ = lean_apply_2(v_toPure_248_, lean_box(0), v___x_299_);
return v___x_300_;
}
}
}
}
}
v___jp_255_:
{
lean_object* v___f_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
lean_inc(v_mvarId_251_);
lean_inc_ref(v_inst_250_);
lean_inc_ref(v_inst_249_);
v___f_259_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__0), 6, 5);
lean_closure_set(v___f_259_, 0, v_toPure_248_);
lean_closure_set(v___f_259_, 1, v_inst_249_);
lean_closure_set(v___f_259_, 2, v_inst_250_);
lean_closure_set(v___f_259_, 3, v_mvarId_251_);
lean_closure_set(v___f_259_, 4, v_b_257_);
v___x_260_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_249_, v_inst_250_, v_mvarId_251_, v_d_256_, v___y_258_);
v___x_261_ = lean_apply_4(v_toBind_252_, lean_box(0), lean_box(0), v___x_260_, v___f_259_);
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_mvarId_308_, lean_object* v_e_309_, lean_object* v_a_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = l_Lean_Expr_hasExprMVar(v_e_309_);
if (v___x_311_ == 0)
{
lean_object* v_toApplicative_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_322_; 
lean_dec_ref(v_e_309_);
lean_dec(v_mvarId_308_);
lean_dec_ref(v_inst_307_);
v_toApplicative_312_ = lean_ctor_get(v_inst_306_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v_inst_306_);
if (v_isSharedCheck_322_ == 0)
{
lean_object* v_unused_323_; 
v_unused_323_ = lean_ctor_get(v_inst_306_, 1);
lean_dec(v_unused_323_);
v___x_314_ = v_inst_306_;
v_isShared_315_ = v_isSharedCheck_322_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_toApplicative_312_);
lean_dec(v_inst_306_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_322_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_toPure_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v_toPure_316_ = lean_ctor_get(v_toApplicative_312_, 1);
lean_inc(v_toPure_316_);
lean_dec_ref(v_toApplicative_312_);
v___x_317_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__0));
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v_a_310_);
lean_ctor_set(v___x_314_, 0, v___x_317_);
v___x_319_ = v___x_314_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_a_310_);
v___x_319_ = v_reuseFailAlloc_321_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; 
v___x_320_ = lean_apply_2(v_toPure_316_, lean_box(0), v___x_319_);
return v___x_320_;
}
}
}
else
{
lean_object* v_toApplicative_324_; lean_object* v_toBind_325_; lean_object* v_toPure_326_; lean_object* v___f_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___f_330_; lean_object* v___f_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v_toApplicative_324_ = lean_ctor_get(v_inst_306_, 0);
v_toBind_325_ = lean_ctor_get(v_inst_306_, 1);
lean_inc_n(v_toBind_325_, 4);
v_toPure_326_ = lean_ctor_get(v_toApplicative_324_, 1);
lean_inc_n(v_toPure_326_, 4);
lean_inc_ref(v_e_309_);
v___f_327_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__4), 7, 6);
lean_closure_set(v___f_327_, 0, v_toPure_326_);
lean_closure_set(v___f_327_, 1, v_inst_306_);
lean_closure_set(v___f_327_, 2, v_inst_307_);
lean_closure_set(v___f_327_, 3, v_mvarId_308_);
lean_closure_set(v___f_327_, 4, v_toBind_325_);
lean_closure_set(v___f_327_, 5, v_e_309_);
v___x_328_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___closed__0));
v___x_329_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___closed__1));
v___f_330_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6), 7, 6);
lean_closure_set(v___f_330_, 0, v_toPure_326_);
lean_closure_set(v___f_330_, 1, v___x_328_);
lean_closure_set(v___f_330_, 2, v___x_329_);
lean_closure_set(v___f_330_, 3, v_e_309_);
lean_closure_set(v___f_330_, 4, v_toBind_325_);
lean_closure_set(v___f_330_, 5, v___f_327_);
v___f_331_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__7), 2, 1);
lean_closure_set(v___f_331_, 0, v_toPure_326_);
lean_inc_ref(v_a_310_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_a_310_);
lean_ctor_set(v___x_332_, 1, v_a_310_);
v___x_333_ = lean_apply_2(v_toPure_326_, lean_box(0), v___x_332_);
v___x_334_ = lean_apply_4(v_toBind_325_, lean_box(0), lean_box(0), v___x_333_, v___f_331_);
v___x_335_ = lean_apply_4(v_toBind_325_, lean_box(0), lean_box(0), v___x_334_, v___f_330_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__0(lean_object* v_toPure_336_, lean_object* v_inst_337_, lean_object* v_inst_338_, lean_object* v_mvarId_339_, lean_object* v_b_340_, lean_object* v_____x_341_){
_start:
{
lean_object* v_fst_342_; 
v_fst_342_ = lean_ctor_get(v_____x_341_, 0);
if (lean_obj_tag(v_fst_342_) == 0)
{
lean_object* v___x_343_; 
lean_dec_ref(v_b_340_);
lean_dec(v_mvarId_339_);
lean_dec_ref(v_inst_338_);
lean_dec_ref(v_inst_337_);
v___x_343_ = lean_apply_2(v_toPure_336_, lean_box(0), v_____x_341_);
return v___x_343_;
}
else
{
lean_object* v_snd_344_; lean_object* v___x_345_; 
lean_dec(v_toPure_336_);
v_snd_344_ = lean_ctor_get(v_____x_341_, 1);
lean_inc(v_snd_344_);
lean_dec_ref(v_____x_341_);
v___x_345_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_337_, v_inst_338_, v_mvarId_339_, v_b_340_, v_snd_344_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar(lean_object* v_m_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_mvarId_349_, lean_object* v_mvarId_x27_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg(v_inst_347_, v_inst_348_, v_mvarId_349_, v_mvarId_x27_350_, v_a_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit(lean_object* v_m_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_mvarId_356_, lean_object* v_e_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_354_, v_inst_355_, v_mvarId_356_, v_e_357_, v_a_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___redArg___lam__0(lean_object* v_toPure_360_, uint8_t v___y_361_, uint8_t v___x_362_, lean_object* v_____do__lift_363_){
_start:
{
lean_object* v_fst_364_; 
v_fst_364_ = lean_ctor_get(v_____do__lift_363_, 0);
if (lean_obj_tag(v_fst_364_) == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_box(v___y_361_);
v___x_366_ = lean_apply_2(v_toPure_360_, lean_box(0), v___x_365_);
return v___x_366_;
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_box(v___x_362_);
v___x_368_ = lean_apply_2(v_toPure_360_, lean_box(0), v___x_367_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___redArg___lam__0___boxed(lean_object* v_toPure_369_, lean_object* v___y_370_, lean_object* v___x_371_, lean_object* v_____do__lift_372_){
_start:
{
uint8_t v___y_87__boxed_373_; uint8_t v___x_88__boxed_374_; lean_object* v_res_375_; 
v___y_87__boxed_373_ = lean_unbox(v___y_370_);
v___x_88__boxed_374_ = lean_unbox(v___x_371_);
v_res_375_ = l_Lean_occursCheck___redArg___lam__0(v_toPure_369_, v___y_87__boxed_373_, v___x_88__boxed_374_, v_____do__lift_372_);
lean_dec_ref(v_____do__lift_372_);
return v_res_375_;
}
}
static lean_object* _init_l_Lean_occursCheck___redArg___closed__0(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = lean_box(0);
v___x_377_ = lean_unsigned_to_nat(16u);
v___x_378_ = lean_mk_array(v___x_377_, v___x_376_);
return v___x_378_;
}
}
static lean_object* _init_l_Lean_occursCheck___redArg___closed__1(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = lean_obj_once(&l_Lean_occursCheck___redArg___closed__0, &l_Lean_occursCheck___redArg___closed__0_once, _init_l_Lean_occursCheck___redArg___closed__0);
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___x_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___redArg(lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_mvarId_384_, lean_object* v_e_385_){
_start:
{
uint8_t v___y_387_; uint8_t v___x_400_; 
v___x_400_ = l_Lean_Expr_hasExprMVar(v_e_385_);
if (v___x_400_ == 0)
{
uint8_t v___x_401_; 
v___x_401_ = 1;
v___y_387_ = v___x_401_;
goto v___jp_386_;
}
else
{
uint8_t v___x_402_; 
v___x_402_ = 0;
v___y_387_ = v___x_402_;
goto v___jp_386_;
}
v___jp_386_:
{
lean_object* v_toApplicative_388_; lean_object* v_toBind_389_; lean_object* v_toPure_390_; uint8_t v___x_391_; 
v_toApplicative_388_ = lean_ctor_get(v_inst_382_, 0);
v_toBind_389_ = lean_ctor_get(v_inst_382_, 1);
lean_inc(v_toBind_389_);
v_toPure_390_ = lean_ctor_get(v_toApplicative_388_, 1);
v___x_391_ = 1;
if (v___y_387_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___f_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_392_ = lean_box(v___y_387_);
v___x_393_ = lean_box(v___x_391_);
lean_inc(v_toPure_390_);
v___f_394_ = lean_alloc_closure((void*)(l_Lean_occursCheck___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_394_, 0, v_toPure_390_);
lean_closure_set(v___f_394_, 1, v___x_392_);
lean_closure_set(v___f_394_, 2, v___x_393_);
v___x_395_ = lean_obj_once(&l_Lean_occursCheck___redArg___closed__1, &l_Lean_occursCheck___redArg___closed__1_once, _init_l_Lean_occursCheck___redArg___closed__1);
v___x_396_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_382_, v_inst_383_, v_mvarId_384_, v_e_385_, v___x_395_);
v___x_397_ = lean_apply_4(v_toBind_389_, lean_box(0), lean_box(0), v___x_396_, v___f_394_);
return v___x_397_;
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; 
lean_inc(v_toPure_390_);
lean_dec(v_toBind_389_);
lean_dec_ref(v_e_385_);
lean_dec(v_mvarId_384_);
lean_dec_ref(v_inst_383_);
lean_dec_ref(v_inst_382_);
v___x_398_ = lean_box(v___x_391_);
v___x_399_ = lean_apply_2(v_toPure_390_, lean_box(0), v___x_398_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck(lean_object* v_m_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_mvarId_406_, lean_object* v_e_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_occursCheck___redArg(v_inst_404_, v_inst_405_, v_mvarId_406_, v_e_407_);
return v___x_408_;
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
