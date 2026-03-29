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
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_snd_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_77_; 
v_snd_55_ = lean_ctor_get(v_____x_35_, 1);
v_isSharedCheck_77_ = !lean_is_exclusive(v_____x_35_);
if (v_isSharedCheck_77_ == 0)
{
lean_object* v_unused_78_; 
v_unused_78_ = lean_ctor_get(v_____x_35_, 0);
lean_dec(v_unused_78_);
v___x_57_ = v_____x_35_;
v_isShared_58_ = v_isSharedCheck_77_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_snd_55_);
lean_dec(v_____x_35_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_77_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v_a_59_; lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_a_59_ = lean_ctor_get(v_fst_36_, 0);
lean_inc(v_a_59_);
lean_dec_ref(v_fst_36_);
v___x_60_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__0));
v___x_61_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__1));
lean_inc_ref(v_e_32_);
v___x_62_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_60_, v___x_61_, v_a_59_, v_e_32_);
lean_dec(v_a_59_);
if (v___x_62_ == 0)
{
lean_object* v___f_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_67_; 
lean_inc(v_toPure_31_);
v___f_63_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__5), 2, 1);
lean_closure_set(v___f_63_, 0, v_toPure_31_);
v___x_64_ = lean_box(0);
v___x_65_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_60_, v___x_61_, v_snd_55_, v_e_32_, v___x_64_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 1, v___x_65_);
lean_ctor_set(v___x_57_, 0, v___x_64_);
v___x_67_ = v___x_57_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_64_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v___x_65_);
v___x_67_ = v_reuseFailAlloc_71_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_apply_2(v_toPure_31_, lean_box(0), v___x_67_);
lean_inc(v_toBind_33_);
v___x_69_ = lean_apply_4(v_toBind_33_, lean_box(0), lean_box(0), v___x_68_, v___f_63_);
v___x_70_ = lean_apply_4(v_toBind_33_, lean_box(0), lean_box(0), v___x_69_, v___f_34_);
return v___x_70_;
}
}
else
{
lean_object* v___x_72_; lean_object* v___x_74_; 
lean_dec(v___f_34_);
lean_dec(v_toBind_33_);
lean_dec_ref(v_e_32_);
v___x_72_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__2));
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_72_);
v___x_74_ = v___x_57_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v___x_72_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_snd_55_);
v___x_74_ = v_reuseFailAlloc_76_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
lean_object* v___x_75_; 
v___x_75_ = lean_apply_2(v_toPure_31_, lean_box(0), v___x_74_);
return v___x_75_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__1(lean_object* v_toPure_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_mvarId_82_, lean_object* v_body_83_, lean_object* v_____x_84_){
_start:
{
lean_object* v_fst_85_; 
v_fst_85_ = lean_ctor_get(v_____x_84_, 0);
if (lean_obj_tag(v_fst_85_) == 0)
{
lean_object* v___x_86_; 
lean_dec_ref(v_body_83_);
lean_dec(v_mvarId_82_);
lean_dec_ref(v_inst_81_);
lean_dec_ref(v_inst_80_);
v___x_86_ = lean_apply_2(v_toPure_79_, lean_box(0), v_____x_84_);
return v___x_86_;
}
else
{
lean_object* v_snd_87_; lean_object* v___x_88_; 
lean_dec(v_toPure_79_);
v_snd_87_ = lean_ctor_get(v_____x_84_, 1);
lean_inc(v_snd_87_);
lean_dec_ref(v_____x_84_);
v___x_88_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_80_, v_inst_81_, v_mvarId_82_, v_body_83_, v_snd_87_);
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__2(lean_object* v_toPure_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_mvarId_92_, lean_object* v_value_93_, lean_object* v_toBind_94_, lean_object* v___f_95_, lean_object* v_____x_96_){
_start:
{
lean_object* v_fst_97_; 
v_fst_97_ = lean_ctor_get(v_____x_96_, 0);
if (lean_obj_tag(v_fst_97_) == 0)
{
lean_object* v___x_98_; 
lean_dec(v___f_95_);
lean_dec(v_toBind_94_);
lean_dec_ref(v_value_93_);
lean_dec(v_mvarId_92_);
lean_dec_ref(v_inst_91_);
lean_dec_ref(v_inst_90_);
v___x_98_ = lean_apply_2(v_toPure_89_, lean_box(0), v_____x_96_);
return v___x_98_;
}
else
{
lean_object* v_snd_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v_toPure_89_);
v_snd_99_ = lean_ctor_get(v_____x_96_, 1);
lean_inc(v_snd_99_);
lean_dec_ref(v_____x_96_);
v___x_100_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_90_, v_inst_91_, v_mvarId_92_, v_value_93_, v_snd_99_);
v___x_101_ = lean_apply_4(v_toBind_94_, lean_box(0), lean_box(0), v___x_100_, v___f_95_);
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__3(lean_object* v_toPure_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_mvarId_105_, lean_object* v_arg_106_, lean_object* v_____x_107_){
_start:
{
lean_object* v_fst_108_; 
v_fst_108_ = lean_ctor_get(v_____x_107_, 0);
if (lean_obj_tag(v_fst_108_) == 0)
{
lean_object* v___x_109_; 
lean_dec_ref(v_arg_106_);
lean_dec(v_mvarId_105_);
lean_dec_ref(v_inst_104_);
lean_dec_ref(v_inst_103_);
v___x_109_ = lean_apply_2(v_toPure_102_, lean_box(0), v_____x_107_);
return v___x_109_;
}
else
{
lean_object* v_snd_110_; lean_object* v___x_111_; 
lean_dec(v_toPure_102_);
v_snd_110_ = lean_ctor_get(v_____x_107_, 1);
lean_inc(v_snd_110_);
lean_dec_ref(v_____x_107_);
v___x_111_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_103_, v_inst_104_, v_mvarId_105_, v_arg_106_, v_snd_110_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___lam__0(lean_object* v_toApplicative_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_mvarId_116_, lean_object* v_____x_117_){
_start:
{
lean_object* v_fst_118_; 
v_fst_118_ = lean_ctor_get(v_____x_117_, 0);
lean_inc(v_fst_118_);
if (lean_obj_tag(v_fst_118_) == 0)
{
lean_object* v_snd_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_136_; 
lean_dec(v_mvarId_116_);
lean_dec_ref(v_inst_115_);
lean_dec_ref(v_inst_114_);
v_snd_119_ = lean_ctor_get(v_____x_117_, 1);
v_isSharedCheck_136_ = !lean_is_exclusive(v_____x_117_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v_____x_117_, 0);
lean_dec(v_unused_137_);
v___x_121_ = v_____x_117_;
v_isShared_122_ = v_isSharedCheck_136_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_snd_119_);
lean_dec(v_____x_117_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_136_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_135_; 
v_a_123_ = lean_ctor_get(v_fst_118_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v_fst_118_);
if (v_isSharedCheck_135_ == 0)
{
v___x_125_ = v_fst_118_;
v_isShared_126_ = v_isSharedCheck_135_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v_fst_118_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_135_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v_toPure_127_; lean_object* v___x_129_; 
v_toPure_127_ = lean_ctor_get(v_toApplicative_113_, 1);
lean_inc(v_toPure_127_);
lean_dec_ref(v_toApplicative_113_);
if (v_isShared_126_ == 0)
{
v___x_129_ = v___x_125_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_a_123_);
v___x_129_ = v_reuseFailAlloc_134_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_131_; 
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v___x_129_);
v___x_131_ = v___x_121_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_snd_119_);
v___x_131_ = v_reuseFailAlloc_133_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; 
v___x_132_ = lean_apply_2(v_toPure_127_, lean_box(0), v___x_131_);
return v___x_132_;
}
}
}
}
}
else
{
lean_object* v_a_138_; 
v_a_138_ = lean_ctor_get(v_fst_118_, 0);
lean_inc(v_a_138_);
lean_dec_ref(v_fst_118_);
if (lean_obj_tag(v_a_138_) == 0)
{
lean_object* v_snd_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_149_; 
lean_dec(v_mvarId_116_);
lean_dec_ref(v_inst_115_);
lean_dec_ref(v_inst_114_);
v_snd_139_ = lean_ctor_get(v_____x_117_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_____x_117_);
if (v_isSharedCheck_149_ == 0)
{
lean_object* v_unused_150_; 
v_unused_150_ = lean_ctor_get(v_____x_117_, 0);
lean_dec(v_unused_150_);
v___x_141_ = v_____x_117_;
v_isShared_142_ = v_isSharedCheck_149_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_snd_139_);
lean_dec(v_____x_117_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_149_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v_toPure_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v_toPure_143_ = lean_ctor_get(v_toApplicative_113_, 1);
lean_inc(v_toPure_143_);
lean_dec_ref(v_toApplicative_113_);
v___x_144_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__2));
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_144_);
v___x_146_ = v___x_141_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_snd_139_);
v___x_146_ = v_reuseFailAlloc_148_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; 
v___x_147_ = lean_apply_2(v_toPure_143_, lean_box(0), v___x_146_);
return v___x_147_;
}
}
}
else
{
lean_object* v_val_151_; lean_object* v_snd_152_; lean_object* v_mvarIdPending_153_; lean_object* v___x_154_; 
lean_dec_ref(v_toApplicative_113_);
v_val_151_ = lean_ctor_get(v_a_138_, 0);
lean_inc(v_val_151_);
lean_dec_ref(v_a_138_);
v_snd_152_ = lean_ctor_get(v_____x_117_, 1);
lean_inc(v_snd_152_);
lean_dec_ref(v_____x_117_);
v_mvarIdPending_153_ = lean_ctor_get(v_val_151_, 1);
lean_inc(v_mvarIdPending_153_);
lean_dec(v_val_151_);
v___x_154_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg(v_inst_114_, v_inst_115_, v_mvarId_116_, v_mvarIdPending_153_, v_snd_152_);
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___lam__1(lean_object* v_toApplicative_155_, lean_object* v___x_156_, lean_object* v___x_157_, lean_object* v_mvarId_x27_158_, lean_object* v_toBind_159_, lean_object* v___f_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_mvarId_163_, lean_object* v_____x_164_){
_start:
{
lean_object* v_fst_165_; 
v_fst_165_ = lean_ctor_get(v_____x_164_, 0);
lean_inc(v_fst_165_);
if (lean_obj_tag(v_fst_165_) == 0)
{
lean_object* v_snd_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_183_; 
lean_dec(v_mvarId_163_);
lean_dec_ref(v_inst_162_);
lean_dec_ref(v_inst_161_);
lean_dec(v___f_160_);
lean_dec(v_toBind_159_);
lean_dec(v_mvarId_x27_158_);
lean_dec_ref(v___x_157_);
lean_dec_ref(v___x_156_);
v_snd_166_ = lean_ctor_get(v_____x_164_, 1);
v_isSharedCheck_183_ = !lean_is_exclusive(v_____x_164_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v_____x_164_, 0);
lean_dec(v_unused_184_);
v___x_168_ = v_____x_164_;
v_isShared_169_ = v_isSharedCheck_183_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_snd_166_);
lean_dec(v_____x_164_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_183_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_182_; 
v_a_170_ = lean_ctor_get(v_fst_165_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v_fst_165_);
if (v_isSharedCheck_182_ == 0)
{
v___x_172_ = v_fst_165_;
v_isShared_173_ = v_isSharedCheck_182_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v_fst_165_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_182_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v_toPure_174_; lean_object* v___x_176_; 
v_toPure_174_ = lean_ctor_get(v_toApplicative_155_, 1);
lean_inc(v_toPure_174_);
lean_dec_ref(v_toApplicative_155_);
if (v_isShared_173_ == 0)
{
v___x_176_ = v___x_172_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_170_);
v___x_176_ = v_reuseFailAlloc_181_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_178_; 
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_176_);
v___x_178_ = v___x_168_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_snd_166_);
v___x_178_ = v_reuseFailAlloc_180_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; 
v___x_179_ = lean_apply_2(v_toPure_174_, lean_box(0), v___x_178_);
return v___x_179_;
}
}
}
}
}
else
{
lean_object* v_a_185_; 
lean_dec_ref(v_toApplicative_155_);
v_a_185_ = lean_ctor_get(v_fst_165_, 0);
lean_inc(v_a_185_);
lean_dec_ref(v_fst_165_);
if (lean_obj_tag(v_a_185_) == 0)
{
lean_object* v_snd_186_; lean_object* v___x_5693__overap_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec(v_mvarId_163_);
lean_dec_ref(v_inst_162_);
lean_dec_ref(v_inst_161_);
v_snd_186_ = lean_ctor_get(v_____x_164_, 1);
lean_inc(v_snd_186_);
lean_dec_ref(v_____x_164_);
v___x_5693__overap_187_ = l_Lean_getDelayedMVarAssignment_x3f___redArg(v___x_156_, v___x_157_, v_mvarId_x27_158_);
v___x_188_ = lean_apply_1(v___x_5693__overap_187_, v_snd_186_);
v___x_189_ = lean_apply_4(v_toBind_159_, lean_box(0), lean_box(0), v___x_188_, v___f_160_);
return v___x_189_;
}
else
{
lean_object* v_snd_190_; lean_object* v_val_191_; lean_object* v___x_192_; 
lean_dec(v___f_160_);
lean_dec(v_toBind_159_);
lean_dec(v_mvarId_x27_158_);
lean_dec_ref(v___x_157_);
lean_dec_ref(v___x_156_);
v_snd_190_ = lean_ctor_get(v_____x_164_, 1);
lean_inc(v_snd_190_);
lean_dec_ref(v_____x_164_);
v_val_191_ = lean_ctor_get(v_a_185_, 0);
lean_inc(v_val_191_);
lean_dec_ref(v_a_185_);
v___x_192_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_161_, v_inst_162_, v_mvarId_163_, v_val_191_, v_snd_190_);
return v___x_192_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg(lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_mvarId_197_, lean_object* v_mvarId_x27_198_, lean_object* v_a_199_){
_start:
{
uint8_t v___x_200_; 
v___x_200_ = l_Lean_instBEqMVarId_beq(v_mvarId_197_, v_mvarId_x27_198_);
if (v___x_200_ == 0)
{
lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___f_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___f_211_; lean_object* v___f_212_; lean_object* v___f_213_; lean_object* v___f_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v_getMCtx_221_; lean_object* v_modifyMCtx_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___f_225_; lean_object* v___x_226_; lean_object* v___f_227_; lean_object* v___f_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v_toApplicative_231_; lean_object* v_toBind_232_; lean_object* v___f_233_; lean_object* v___f_234_; lean_object* v___x_1342__overap_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
lean_inc_ref_n(v_inst_195_, 11);
v___f_201_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_201_, 0, v_inst_195_);
v___f_202_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_202_, 0, v_inst_195_);
v___f_203_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_203_, 0, v_inst_195_);
v___f_204_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_204_, 0, v_inst_195_);
v___x_205_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_205_, 0, lean_box(0));
lean_closure_set(v___x_205_, 1, lean_box(0));
lean_closure_set(v___x_205_, 2, v_inst_195_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___f_201_);
v___x_207_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_207_, 0, lean_box(0));
lean_closure_set(v___x_207_, 1, lean_box(0));
lean_closure_set(v___x_207_, 2, v_inst_195_);
v___x_208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_208_, 0, v___x_206_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
lean_ctor_set(v___x_208_, 2, v___f_202_);
lean_ctor_set(v___x_208_, 3, v___f_203_);
lean_ctor_set(v___x_208_, 4, v___f_204_);
v___x_209_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_209_, 0, lean_box(0));
lean_closure_set(v___x_209_, 1, lean_box(0));
lean_closure_set(v___x_209_, 2, v_inst_195_);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
lean_inc_ref_n(v___x_210_, 7);
v___f_211_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_211_, 0, v___x_210_);
v___f_212_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_212_, 0, v___x_210_);
v___f_213_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_213_, 0, v___x_210_);
v___f_214_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_214_, 0, v___x_210_);
v___x_215_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_215_, 0, lean_box(0));
lean_closure_set(v___x_215_, 1, lean_box(0));
lean_closure_set(v___x_215_, 2, v___x_210_);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___f_211_);
v___x_217_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_217_, 0, lean_box(0));
lean_closure_set(v___x_217_, 1, lean_box(0));
lean_closure_set(v___x_217_, 2, v___x_210_);
v___x_218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_218_, 0, v___x_216_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
lean_ctor_set(v___x_218_, 2, v___f_212_);
lean_ctor_set(v___x_218_, 3, v___f_213_);
lean_ctor_set(v___x_218_, 4, v___f_214_);
v___x_219_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_219_, 0, lean_box(0));
lean_closure_set(v___x_219_, 1, lean_box(0));
lean_closure_set(v___x_219_, 2, v___x_210_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_218_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v_getMCtx_221_ = lean_ctor_get(v_inst_196_, 0);
v_modifyMCtx_222_ = lean_ctor_get(v_inst_196_, 1);
v___x_223_ = lean_alloc_closure((void*)(l_ExceptT_lift), 5, 3);
lean_closure_set(v___x_223_, 0, lean_box(0));
lean_closure_set(v___x_223_, 1, lean_box(0));
lean_closure_set(v___x_223_, 2, v___x_210_);
v___x_224_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_224_, 0, lean_box(0));
lean_closure_set(v___x_224_, 1, lean_box(0));
lean_closure_set(v___x_224_, 2, v_inst_195_);
lean_inc(v_modifyMCtx_222_);
v___f_225_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_225_, 0, v_modifyMCtx_222_);
lean_closure_set(v___f_225_, 1, v___x_224_);
lean_inc(v_getMCtx_221_);
v___x_226_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 5);
lean_closure_set(v___x_226_, 0, lean_box(0));
lean_closure_set(v___x_226_, 1, lean_box(0));
lean_closure_set(v___x_226_, 2, v_inst_195_);
lean_closure_set(v___x_226_, 3, lean_box(0));
lean_closure_set(v___x_226_, 4, v_getMCtx_221_);
v___f_227_ = lean_alloc_closure((void*)(l_Lean_instMonadMCtxOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_227_, 0, v___f_225_);
lean_closure_set(v___f_227_, 1, v___x_223_);
v___f_228_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__0));
v___x_229_ = lean_alloc_closure((void*)(l_StateT_map), 8, 7);
lean_closure_set(v___x_229_, 0, lean_box(0));
lean_closure_set(v___x_229_, 1, lean_box(0));
lean_closure_set(v___x_229_, 2, v_inst_195_);
lean_closure_set(v___x_229_, 3, lean_box(0));
lean_closure_set(v___x_229_, 4, lean_box(0));
lean_closure_set(v___x_229_, 5, v___f_228_);
lean_closure_set(v___x_229_, 6, v___x_226_);
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___f_227_);
v_toApplicative_231_ = lean_ctor_get(v_inst_195_, 0);
lean_inc_ref_n(v_toApplicative_231_, 2);
v_toBind_232_ = lean_ctor_get(v_inst_195_, 1);
lean_inc_n(v_toBind_232_, 2);
lean_inc(v_mvarId_197_);
lean_inc_ref(v_inst_196_);
v___f_233_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___lam__0), 5, 4);
lean_closure_set(v___f_233_, 0, v_toApplicative_231_);
lean_closure_set(v___f_233_, 1, v_inst_195_);
lean_closure_set(v___f_233_, 2, v_inst_196_);
lean_closure_set(v___f_233_, 3, v_mvarId_197_);
lean_inc(v_mvarId_x27_198_);
lean_inc_ref(v___x_230_);
lean_inc_ref(v___x_220_);
v___f_234_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___lam__1), 10, 9);
lean_closure_set(v___f_234_, 0, v_toApplicative_231_);
lean_closure_set(v___f_234_, 1, v___x_220_);
lean_closure_set(v___f_234_, 2, v___x_230_);
lean_closure_set(v___f_234_, 3, v_mvarId_x27_198_);
lean_closure_set(v___f_234_, 4, v_toBind_232_);
lean_closure_set(v___f_234_, 5, v___f_233_);
lean_closure_set(v___f_234_, 6, v_inst_195_);
lean_closure_set(v___f_234_, 7, v_inst_196_);
lean_closure_set(v___f_234_, 8, v_mvarId_197_);
v___x_1342__overap_235_ = l_Lean_getExprMVarAssignment_x3f___redArg(v___x_220_, v___x_230_, v_mvarId_x27_198_);
v___x_236_ = lean_apply_1(v___x_1342__overap_235_, v_a_199_);
v___x_237_ = lean_apply_4(v_toBind_232_, lean_box(0), lean_box(0), v___x_236_, v___f_234_);
return v___x_237_;
}
else
{
lean_object* v_toApplicative_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_248_; 
lean_dec(v_mvarId_x27_198_);
lean_dec(v_mvarId_197_);
lean_dec_ref(v_inst_196_);
v_toApplicative_238_ = lean_ctor_get(v_inst_195_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v_inst_195_);
if (v_isSharedCheck_248_ == 0)
{
lean_object* v_unused_249_; 
v_unused_249_ = lean_ctor_get(v_inst_195_, 1);
lean_dec(v_unused_249_);
v___x_240_ = v_inst_195_;
v_isShared_241_ = v_isSharedCheck_248_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_toApplicative_238_);
lean_dec(v_inst_195_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_248_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_toPure_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
v_toPure_242_ = lean_ctor_get(v_toApplicative_238_, 1);
lean_inc(v_toPure_242_);
lean_dec_ref(v_toApplicative_238_);
v___x_243_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg___closed__1));
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v_a_199_);
lean_ctor_set(v___x_240_, 0, v___x_243_);
v___x_245_ = v___x_240_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_a_199_);
v___x_245_ = v_reuseFailAlloc_247_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; 
v___x_246_ = lean_apply_2(v_toPure_242_, lean_box(0), v___x_245_);
return v___x_246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__4(lean_object* v_toPure_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_mvarId_253_, lean_object* v_toBind_254_, lean_object* v_e_255_, lean_object* v_____x_256_){
_start:
{
lean_object* v_d_258_; lean_object* v_b_259_; lean_object* v___y_260_; lean_object* v_fst_264_; 
v_fst_264_ = lean_ctor_get(v_____x_256_, 0);
if (lean_obj_tag(v_fst_264_) == 0)
{
lean_object* v___x_265_; 
lean_dec_ref(v_e_255_);
lean_dec(v_toBind_254_);
lean_dec(v_mvarId_253_);
lean_dec_ref(v_inst_252_);
lean_dec_ref(v_inst_251_);
v___x_265_ = lean_apply_2(v_toPure_250_, lean_box(0), v_____x_256_);
return v___x_265_;
}
else
{
switch(lean_obj_tag(v_e_255_))
{
case 11:
{
lean_object* v_snd_266_; lean_object* v_struct_267_; lean_object* v___x_268_; 
lean_dec(v_toBind_254_);
lean_dec(v_toPure_250_);
v_snd_266_ = lean_ctor_get(v_____x_256_, 1);
lean_inc(v_snd_266_);
lean_dec_ref(v_____x_256_);
v_struct_267_ = lean_ctor_get(v_e_255_, 2);
lean_inc_ref(v_struct_267_);
lean_dec_ref(v_e_255_);
v___x_268_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_251_, v_inst_252_, v_mvarId_253_, v_struct_267_, v_snd_266_);
return v___x_268_;
}
case 7:
{
lean_object* v_snd_269_; lean_object* v_binderType_270_; lean_object* v_body_271_; 
v_snd_269_ = lean_ctor_get(v_____x_256_, 1);
lean_inc(v_snd_269_);
lean_dec_ref(v_____x_256_);
v_binderType_270_ = lean_ctor_get(v_e_255_, 1);
lean_inc_ref(v_binderType_270_);
v_body_271_ = lean_ctor_get(v_e_255_, 2);
lean_inc_ref(v_body_271_);
lean_dec_ref(v_e_255_);
v_d_258_ = v_binderType_270_;
v_b_259_ = v_body_271_;
v___y_260_ = v_snd_269_;
goto v___jp_257_;
}
case 6:
{
lean_object* v_snd_272_; lean_object* v_binderType_273_; lean_object* v_body_274_; 
v_snd_272_ = lean_ctor_get(v_____x_256_, 1);
lean_inc(v_snd_272_);
lean_dec_ref(v_____x_256_);
v_binderType_273_ = lean_ctor_get(v_e_255_, 1);
lean_inc_ref(v_binderType_273_);
v_body_274_ = lean_ctor_get(v_e_255_, 2);
lean_inc_ref(v_body_274_);
lean_dec_ref(v_e_255_);
v_d_258_ = v_binderType_273_;
v_b_259_ = v_body_274_;
v___y_260_ = v_snd_272_;
goto v___jp_257_;
}
case 8:
{
lean_object* v_snd_275_; lean_object* v_type_276_; lean_object* v_value_277_; lean_object* v_body_278_; lean_object* v___f_279_; lean_object* v___f_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_snd_275_ = lean_ctor_get(v_____x_256_, 1);
lean_inc(v_snd_275_);
lean_dec_ref(v_____x_256_);
v_type_276_ = lean_ctor_get(v_e_255_, 1);
lean_inc_ref(v_type_276_);
v_value_277_ = lean_ctor_get(v_e_255_, 2);
lean_inc_ref(v_value_277_);
v_body_278_ = lean_ctor_get(v_e_255_, 3);
lean_inc_ref(v_body_278_);
lean_dec_ref(v_e_255_);
lean_inc_n(v_mvarId_253_, 2);
lean_inc_ref_n(v_inst_252_, 2);
lean_inc_ref_n(v_inst_251_, 2);
lean_inc(v_toPure_250_);
v___f_279_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__1), 6, 5);
lean_closure_set(v___f_279_, 0, v_toPure_250_);
lean_closure_set(v___f_279_, 1, v_inst_251_);
lean_closure_set(v___f_279_, 2, v_inst_252_);
lean_closure_set(v___f_279_, 3, v_mvarId_253_);
lean_closure_set(v___f_279_, 4, v_body_278_);
lean_inc(v_toBind_254_);
v___f_280_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__2), 8, 7);
lean_closure_set(v___f_280_, 0, v_toPure_250_);
lean_closure_set(v___f_280_, 1, v_inst_251_);
lean_closure_set(v___f_280_, 2, v_inst_252_);
lean_closure_set(v___f_280_, 3, v_mvarId_253_);
lean_closure_set(v___f_280_, 4, v_value_277_);
lean_closure_set(v___f_280_, 5, v_toBind_254_);
lean_closure_set(v___f_280_, 6, v___f_279_);
v___x_281_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_251_, v_inst_252_, v_mvarId_253_, v_type_276_, v_snd_275_);
v___x_282_ = lean_apply_4(v_toBind_254_, lean_box(0), lean_box(0), v___x_281_, v___f_280_);
return v___x_282_;
}
case 10:
{
lean_object* v_snd_283_; lean_object* v_expr_284_; lean_object* v___x_285_; 
lean_dec(v_toBind_254_);
lean_dec(v_toPure_250_);
v_snd_283_ = lean_ctor_get(v_____x_256_, 1);
lean_inc(v_snd_283_);
lean_dec_ref(v_____x_256_);
v_expr_284_ = lean_ctor_get(v_e_255_, 1);
lean_inc_ref(v_expr_284_);
lean_dec_ref(v_e_255_);
v___x_285_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_251_, v_inst_252_, v_mvarId_253_, v_expr_284_, v_snd_283_);
return v___x_285_;
}
case 5:
{
lean_object* v_snd_286_; lean_object* v_fn_287_; lean_object* v_arg_288_; lean_object* v___f_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v_snd_286_ = lean_ctor_get(v_____x_256_, 1);
lean_inc(v_snd_286_);
lean_dec_ref(v_____x_256_);
v_fn_287_ = lean_ctor_get(v_e_255_, 0);
lean_inc_ref(v_fn_287_);
v_arg_288_ = lean_ctor_get(v_e_255_, 1);
lean_inc_ref(v_arg_288_);
lean_dec_ref(v_e_255_);
lean_inc(v_mvarId_253_);
lean_inc_ref(v_inst_252_);
lean_inc_ref(v_inst_251_);
v___f_289_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__3), 6, 5);
lean_closure_set(v___f_289_, 0, v_toPure_250_);
lean_closure_set(v___f_289_, 1, v_inst_251_);
lean_closure_set(v___f_289_, 2, v_inst_252_);
lean_closure_set(v___f_289_, 3, v_mvarId_253_);
lean_closure_set(v___f_289_, 4, v_arg_288_);
v___x_290_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_251_, v_inst_252_, v_mvarId_253_, v_fn_287_, v_snd_286_);
v___x_291_ = lean_apply_4(v_toBind_254_, lean_box(0), lean_box(0), v___x_290_, v___f_289_);
return v___x_291_;
}
case 2:
{
lean_object* v_snd_292_; lean_object* v_mvarId_293_; lean_object* v___x_294_; 
lean_dec(v_toBind_254_);
lean_dec(v_toPure_250_);
v_snd_292_ = lean_ctor_get(v_____x_256_, 1);
lean_inc(v_snd_292_);
lean_dec_ref(v_____x_256_);
v_mvarId_293_ = lean_ctor_get(v_e_255_, 0);
lean_inc(v_mvarId_293_);
lean_dec_ref(v_e_255_);
v___x_294_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg(v_inst_251_, v_inst_252_, v_mvarId_253_, v_mvarId_293_, v_snd_292_);
return v___x_294_;
}
default: 
{
lean_object* v_snd_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_304_; 
lean_dec_ref(v_e_255_);
lean_dec(v_toBind_254_);
lean_dec(v_mvarId_253_);
lean_dec_ref(v_inst_252_);
lean_dec_ref(v_inst_251_);
v_snd_295_ = lean_ctor_get(v_____x_256_, 1);
v_isSharedCheck_304_ = !lean_is_exclusive(v_____x_256_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; 
v_unused_305_ = lean_ctor_get(v_____x_256_, 0);
lean_dec(v_unused_305_);
v___x_297_ = v_____x_256_;
v_isShared_298_ = v_isSharedCheck_304_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_snd_295_);
lean_dec(v_____x_256_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_304_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_299_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__2));
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_299_);
v___x_301_ = v___x_297_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_snd_295_);
v___x_301_ = v_reuseFailAlloc_303_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; 
v___x_302_ = lean_apply_2(v_toPure_250_, lean_box(0), v___x_301_);
return v___x_302_;
}
}
}
}
}
v___jp_257_:
{
lean_object* v___f_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
lean_inc(v_mvarId_253_);
lean_inc_ref(v_inst_252_);
lean_inc_ref(v_inst_251_);
v___f_261_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__0), 6, 5);
lean_closure_set(v___f_261_, 0, v_toPure_250_);
lean_closure_set(v___f_261_, 1, v_inst_251_);
lean_closure_set(v___f_261_, 2, v_inst_252_);
lean_closure_set(v___f_261_, 3, v_mvarId_253_);
lean_closure_set(v___f_261_, 4, v_b_259_);
v___x_262_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_251_, v_inst_252_, v_mvarId_253_, v_d_258_, v___y_260_);
v___x_263_ = lean_apply_4(v_toBind_254_, lean_box(0), lean_box(0), v___x_262_, v___f_261_);
return v___x_263_;
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
v___x_317_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6___closed__2));
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
lean_object* v_toApplicative_324_; lean_object* v_toBind_325_; lean_object* v_toPure_326_; lean_object* v___f_327_; lean_object* v___f_328_; lean_object* v___f_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
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
v___f_328_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__6), 5, 4);
lean_closure_set(v___f_328_, 0, v_toPure_326_);
lean_closure_set(v___f_328_, 1, v_e_309_);
lean_closure_set(v___f_328_, 2, v_toBind_325_);
lean_closure_set(v___f_328_, 3, v___f_327_);
v___f_329_ = lean_alloc_closure((void*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__7), 2, 1);
lean_closure_set(v___f_329_, 0, v_toPure_326_);
lean_inc_ref(v_a_310_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v_a_310_);
lean_ctor_set(v___x_330_, 1, v_a_310_);
v___x_331_ = lean_apply_2(v_toPure_326_, lean_box(0), v___x_330_);
v___x_332_ = lean_apply_4(v_toBind_325_, lean_box(0), lean_box(0), v___x_331_, v___f_329_);
v___x_333_ = lean_apply_4(v_toBind_325_, lean_box(0), lean_box(0), v___x_332_, v___f_328_);
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg___lam__0(lean_object* v_toPure_334_, lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_mvarId_337_, lean_object* v_b_338_, lean_object* v_____x_339_){
_start:
{
lean_object* v_fst_340_; 
v_fst_340_ = lean_ctor_get(v_____x_339_, 0);
if (lean_obj_tag(v_fst_340_) == 0)
{
lean_object* v___x_341_; 
lean_dec_ref(v_b_338_);
lean_dec(v_mvarId_337_);
lean_dec_ref(v_inst_336_);
lean_dec_ref(v_inst_335_);
v___x_341_ = lean_apply_2(v_toPure_334_, lean_box(0), v_____x_339_);
return v___x_341_;
}
else
{
lean_object* v_snd_342_; lean_object* v___x_343_; 
lean_dec(v_toPure_334_);
v_snd_342_ = lean_ctor_get(v_____x_339_, 1);
lean_inc(v_snd_342_);
lean_dec_ref(v_____x_339_);
v___x_343_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_335_, v_inst_336_, v_mvarId_337_, v_b_338_, v_snd_342_);
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar(lean_object* v_m_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_mvarId_347_, lean_object* v_mvarId_x27_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___redArg(v_inst_345_, v_inst_346_, v_mvarId_347_, v_mvarId_x27_348_, v_a_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit(lean_object* v_m_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_mvarId_354_, lean_object* v_e_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_352_, v_inst_353_, v_mvarId_354_, v_e_355_, v_a_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___redArg___lam__0(lean_object* v_toApplicative_358_, uint8_t v___x_359_, uint8_t v___x_360_, lean_object* v_____do__lift_361_){
_start:
{
lean_object* v_fst_362_; 
v_fst_362_ = lean_ctor_get(v_____do__lift_361_, 0);
if (lean_obj_tag(v_fst_362_) == 0)
{
lean_object* v_toPure_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v_toPure_363_ = lean_ctor_get(v_toApplicative_358_, 1);
lean_inc(v_toPure_363_);
lean_dec_ref(v_toApplicative_358_);
v___x_364_ = lean_box(v___x_359_);
v___x_365_ = lean_apply_2(v_toPure_363_, lean_box(0), v___x_364_);
return v___x_365_;
}
else
{
lean_object* v_toPure_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_toPure_366_ = lean_ctor_get(v_toApplicative_358_, 1);
lean_inc(v_toPure_366_);
lean_dec_ref(v_toApplicative_358_);
v___x_367_ = lean_box(v___x_360_);
v___x_368_ = lean_apply_2(v_toPure_366_, lean_box(0), v___x_367_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___redArg___lam__0___boxed(lean_object* v_toApplicative_369_, lean_object* v___x_370_, lean_object* v___x_371_, lean_object* v_____do__lift_372_){
_start:
{
uint8_t v___x_245__boxed_373_; uint8_t v___x_246__boxed_374_; lean_object* v_res_375_; 
v___x_245__boxed_373_ = lean_unbox(v___x_370_);
v___x_246__boxed_374_ = lean_unbox(v___x_371_);
v_res_375_ = l_Lean_occursCheck___redArg___lam__0(v_toApplicative_369_, v___x_245__boxed_373_, v___x_246__boxed_374_, v_____do__lift_372_);
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
uint8_t v___x_386_; 
v___x_386_ = l_Lean_Expr_hasExprMVar(v_e_385_);
if (v___x_386_ == 0)
{
lean_object* v_toApplicative_387_; lean_object* v_toPure_388_; uint8_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec_ref(v_e_385_);
lean_dec(v_mvarId_384_);
lean_dec_ref(v_inst_383_);
v_toApplicative_387_ = lean_ctor_get(v_inst_382_, 0);
lean_inc_ref(v_toApplicative_387_);
lean_dec_ref(v_inst_382_);
v_toPure_388_ = lean_ctor_get(v_toApplicative_387_, 1);
lean_inc(v_toPure_388_);
lean_dec_ref(v_toApplicative_387_);
v___x_389_ = 1;
v___x_390_ = lean_box(v___x_389_);
v___x_391_ = lean_apply_2(v_toPure_388_, lean_box(0), v___x_390_);
return v___x_391_;
}
else
{
lean_object* v_toApplicative_392_; lean_object* v_toBind_393_; uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___f_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_toApplicative_392_ = lean_ctor_get(v_inst_382_, 0);
v_toBind_393_ = lean_ctor_get(v_inst_382_, 1);
lean_inc(v_toBind_393_);
v___x_394_ = 0;
v___x_395_ = lean_box(v___x_394_);
v___x_396_ = lean_box(v___x_386_);
lean_inc_ref(v_toApplicative_392_);
v___f_397_ = lean_alloc_closure((void*)(l_Lean_occursCheck___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_397_, 0, v_toApplicative_392_);
lean_closure_set(v___f_397_, 1, v___x_395_);
lean_closure_set(v___f_397_, 2, v___x_396_);
v___x_398_ = lean_obj_once(&l_Lean_occursCheck___redArg___closed__1, &l_Lean_occursCheck___redArg___closed__1_once, _init_l_Lean_occursCheck___redArg___closed__1);
v___x_399_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___redArg(v_inst_382_, v_inst_383_, v_mvarId_384_, v_e_385_, v___x_398_);
v___x_400_ = lean_apply_4(v_toBind_393_, lean_box(0), lean_box(0), v___x_399_, v___f_397_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck(lean_object* v_m_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_mvarId_404_, lean_object* v_e_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_occursCheck___redArg(v_inst_402_, v_inst_403_, v_mvarId_404_, v_e_405_);
return v___x_406_;
}
}
lean_object* runtime_initialize_Lean_MetavarContext(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_OccursCheck(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
