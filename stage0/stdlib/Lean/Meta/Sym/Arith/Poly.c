// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Poly
// Imports: public import Init.Grind.Ring.CommSolver import Init.Data.Nat.Gcd import Init.Data.Nat.Lemmas import Init.Data.Nat.Internal.Linear import Init.WFTactics
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulMonC(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulMon(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_combineC(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_combine(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Mon_degree(lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConstC(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_sharesVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_sharesVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_lcm(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_divides(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_divides___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_div(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_coprime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_coprime___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_Poly_spol_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_Poly_spol___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Poly_spol___closed__0;
static lean_once_cell_t l_Lean_Grind_CommRing_Poly_spol___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Poly_spol___closed__1;
static lean_once_cell_t l_Lean_Grind_CommRing_Poly_spol___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Poly_spol___closed__2;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spol(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_degree(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_degree___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_numTerms(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_numTerms___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_divides(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divides___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lc___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lm___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_isZero(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_isZero___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_getConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_getConst___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_checkCoeffs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_checkCoeffs___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_checkNoUnitMon(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_checkNoUnitMon___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_size___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_size___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_length___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_toExpr_go(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Mon_toExpr___closed__0;
static lean_once_cell_t l_Lean_Grind_CommRing_Mon_toExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Mon_toExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toExpr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_sharesVar(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
else
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_4_; 
v___x_4_ = 0;
return v___x_4_;
}
else
{
lean_object* v_p_5_; lean_object* v_p_6_; lean_object* v_m_7_; lean_object* v_m_8_; lean_object* v_x_9_; lean_object* v_x_10_; uint8_t v___x_11_; 
v_p_5_ = lean_ctor_get(v_x_1_, 0);
v_p_6_ = lean_ctor_get(v_x_2_, 0);
v_m_7_ = lean_ctor_get(v_x_1_, 1);
v_m_8_ = lean_ctor_get(v_x_2_, 1);
v_x_9_ = lean_ctor_get(v_p_5_, 0);
v_x_10_ = lean_ctor_get(v_p_6_, 0);
v___x_11_ = lean_nat_dec_lt(v_x_9_, v_x_10_);
if (v___x_11_ == 0)
{
uint8_t v___x_12_; 
v___x_12_ = lean_nat_dec_eq(v_x_9_, v_x_10_);
if (v___x_12_ == 0)
{
v_x_2_ = v_m_8_;
goto _start;
}
else
{
return v___x_12_;
}
}
else
{
v_x_1_ = v_m_7_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_sharesVar___boxed(lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_Lean_Grind_CommRing_Mon_sharesVar(v_x_15_, v_x_16_);
lean_dec(v_x_16_);
lean_dec(v_x_15_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__3_splitter___redArg(lean_object* v_x_19_, lean_object* v_x_20_, lean_object* v_h__1_21_, lean_object* v_h__2_22_, lean_object* v_h__3_23_){
_start:
{
if (lean_obj_tag(v_x_19_) == 0)
{
lean_object* v___x_24_; 
lean_dec(v_h__3_23_);
lean_dec(v_h__2_22_);
v___x_24_ = lean_apply_1(v_h__1_21_, v_x_20_);
return v___x_24_;
}
else
{
lean_dec(v_h__1_21_);
if (lean_obj_tag(v_x_20_) == 0)
{
lean_object* v___x_25_; 
lean_dec(v_h__3_23_);
v___x_25_ = lean_apply_2(v_h__2_22_, v_x_19_, lean_box(0));
return v___x_25_;
}
else
{
lean_object* v_p_26_; lean_object* v_m_27_; lean_object* v_p_28_; lean_object* v_m_29_; lean_object* v___x_30_; 
lean_dec(v_h__2_22_);
v_p_26_ = lean_ctor_get(v_x_19_, 0);
lean_inc_ref(v_p_26_);
v_m_27_ = lean_ctor_get(v_x_19_, 1);
lean_inc(v_m_27_);
lean_dec_ref_known(v_x_19_, 2);
v_p_28_ = lean_ctor_get(v_x_20_, 0);
lean_inc_ref(v_p_28_);
v_m_29_ = lean_ctor_get(v_x_20_, 1);
lean_inc(v_m_29_);
lean_dec_ref_known(v_x_20_, 2);
v___x_30_ = lean_apply_4(v_h__3_23_, v_p_26_, v_m_27_, v_p_28_, v_m_29_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__3_splitter(lean_object* v_motive_31_, lean_object* v_x_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_, lean_object* v_h__3_36_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
lean_object* v___x_37_; 
lean_dec(v_h__3_36_);
lean_dec(v_h__2_35_);
v___x_37_ = lean_apply_1(v_h__1_34_, v_x_33_);
return v___x_37_;
}
else
{
lean_dec(v_h__1_34_);
if (lean_obj_tag(v_x_33_) == 0)
{
lean_object* v___x_38_; 
lean_dec(v_h__3_36_);
v___x_38_ = lean_apply_2(v_h__2_35_, v_x_32_, lean_box(0));
return v___x_38_;
}
else
{
lean_object* v_p_39_; lean_object* v_m_40_; lean_object* v_p_41_; lean_object* v_m_42_; lean_object* v___x_43_; 
lean_dec(v_h__2_35_);
v_p_39_ = lean_ctor_get(v_x_32_, 0);
lean_inc_ref(v_p_39_);
v_m_40_ = lean_ctor_get(v_x_32_, 1);
lean_inc(v_m_40_);
lean_dec_ref_known(v_x_32_, 2);
v_p_41_ = lean_ctor_get(v_x_33_, 0);
lean_inc_ref(v_p_41_);
v_m_42_ = lean_ctor_get(v_x_33_, 1);
lean_inc(v_m_42_);
lean_dec_ref_known(v_x_33_, 2);
v___x_43_ = lean_apply_4(v_h__3_36_, v_p_39_, v_m_40_, v_p_41_, v_m_42_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg(uint8_t v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_, lean_object* v_h__3_47_){
_start:
{
switch(v_x_44_)
{
case 0:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_h__3_47_);
lean_dec(v_h__1_45_);
v___x_48_ = lean_box(0);
v___x_49_ = lean_apply_1(v_h__2_46_, v___x_48_);
return v___x_49_;
}
case 1:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
lean_dec(v_h__3_47_);
lean_dec(v_h__2_46_);
v___x_50_ = lean_box(0);
v___x_51_ = lean_apply_1(v_h__1_45_, v___x_50_);
return v___x_51_;
}
default: 
{
lean_object* v___x_52_; lean_object* v___x_53_; 
lean_dec(v_h__2_46_);
lean_dec(v_h__1_45_);
v___x_52_ = lean_box(0);
v___x_53_ = lean_apply_1(v_h__3_47_, v___x_52_);
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg___boxed(lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_, lean_object* v_h__3_57_){
_start:
{
uint8_t v_x_33__boxed_58_; lean_object* v_res_59_; 
v_x_33__boxed_58_ = lean_unbox(v_x_54_);
v_res_59_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg(v_x_33__boxed_58_, v_h__1_55_, v_h__2_56_, v_h__3_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter(lean_object* v_motive_60_, uint8_t v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_, lean_object* v_h__3_64_){
_start:
{
switch(v_x_61_)
{
case 0:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec(v_h__3_64_);
lean_dec(v_h__1_62_);
v___x_65_ = lean_box(0);
v___x_66_ = lean_apply_1(v_h__2_63_, v___x_65_);
return v___x_66_;
}
case 1:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v_h__3_64_);
lean_dec(v_h__2_63_);
v___x_67_ = lean_box(0);
v___x_68_ = lean_apply_1(v_h__1_62_, v___x_67_);
return v___x_68_;
}
default: 
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_h__2_63_);
lean_dec(v_h__1_62_);
v___x_69_ = lean_box(0);
v___x_70_ = lean_apply_1(v_h__3_64_, v___x_69_);
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___boxed(lean_object* v_motive_71_, lean_object* v_x_72_, lean_object* v_h__1_73_, lean_object* v_h__2_74_, lean_object* v_h__3_75_){
_start:
{
uint8_t v_x_48__boxed_76_; lean_object* v_res_77_; 
v_x_48__boxed_76_ = lean_unbox(v_x_72_);
v_res_77_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter(v_motive_71_, v_x_48__boxed_76_, v_h__1_73_, v_h__2_74_, v_h__3_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_lcm(lean_object* v_x_78_, lean_object* v_x_79_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
return v_x_79_;
}
else
{
if (lean_obj_tag(v_x_79_) == 0)
{
return v_x_78_;
}
else
{
lean_object* v_p_80_; lean_object* v_m_81_; lean_object* v_p_82_; lean_object* v_m_83_; lean_object* v_x_84_; lean_object* v_k_85_; lean_object* v___y_87_; lean_object* v_x_91_; lean_object* v_k_92_; uint8_t v___x_93_; 
v_p_80_ = lean_ctor_get(v_x_78_, 0);
v_m_81_ = lean_ctor_get(v_x_78_, 1);
v_p_82_ = lean_ctor_get(v_x_79_, 0);
v_m_83_ = lean_ctor_get(v_x_79_, 1);
v_x_84_ = lean_ctor_get(v_p_80_, 0);
v_k_85_ = lean_ctor_get(v_p_80_, 1);
v_x_91_ = lean_ctor_get(v_p_82_, 0);
v_k_92_ = lean_ctor_get(v_p_82_, 1);
v___x_93_ = lean_nat_dec_lt(v_x_84_, v_x_91_);
if (v___x_93_ == 0)
{
lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_103_; 
lean_inc(v_m_83_);
lean_inc_ref(v_p_82_);
v_isSharedCheck_103_ = !lean_is_exclusive(v_x_79_);
if (v_isSharedCheck_103_ == 0)
{
lean_object* v_unused_104_; lean_object* v_unused_105_; 
v_unused_104_ = lean_ctor_get(v_x_79_, 1);
lean_dec(v_unused_104_);
v_unused_105_ = lean_ctor_get(v_x_79_, 0);
lean_dec(v_unused_105_);
v___x_95_ = v_x_79_;
v_isShared_96_ = v_isSharedCheck_103_;
goto v_resetjp_94_;
}
else
{
lean_dec(v_x_79_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_103_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
uint8_t v___x_97_; 
v___x_97_ = lean_nat_dec_eq(v_x_84_, v_x_91_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_98_ = l_Lean_Grind_CommRing_Mon_lcm(v_x_78_, v_m_83_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 1, v___x_98_);
v___x_100_ = v___x_95_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_p_82_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v___x_98_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
else
{
uint8_t v___x_102_; 
lean_inc(v_k_92_);
lean_inc(v_k_85_);
lean_inc(v_x_84_);
lean_inc(v_m_81_);
lean_del_object(v___x_95_);
lean_dec_ref(v_p_82_);
lean_dec_ref_known(v_x_78_, 2);
v___x_102_ = lean_nat_dec_le(v_k_85_, v_k_92_);
if (v___x_102_ == 0)
{
lean_dec(v_k_92_);
v___y_87_ = v_k_85_;
goto v___jp_86_;
}
else
{
lean_dec(v_k_85_);
v___y_87_ = v_k_92_;
goto v___jp_86_;
}
}
}
}
else
{
lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_113_; 
lean_inc(v_m_81_);
lean_inc_ref(v_p_80_);
v_isSharedCheck_113_ = !lean_is_exclusive(v_x_78_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; lean_object* v_unused_115_; 
v_unused_114_ = lean_ctor_get(v_x_78_, 1);
lean_dec(v_unused_114_);
v_unused_115_ = lean_ctor_get(v_x_78_, 0);
lean_dec(v_unused_115_);
v___x_107_ = v_x_78_;
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
else
{
lean_dec(v_x_78_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_109_ = l_Lean_Grind_CommRing_Mon_lcm(v_m_81_, v_x_79_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v___x_109_);
v___x_111_ = v___x_107_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_p_80_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
v___jp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_88_, 0, v_x_84_);
lean_ctor_set(v___x_88_, 1, v___y_87_);
v___x_89_ = l_Lean_Grind_CommRing_Mon_lcm(v_m_81_, v_m_83_);
v___x_90_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
return v___x_90_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_divides(lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
if (lean_obj_tag(v_x_116_) == 0)
{
uint8_t v___x_118_; 
v___x_118_ = 1;
return v___x_118_;
}
else
{
if (lean_obj_tag(v_x_117_) == 0)
{
uint8_t v___x_119_; 
v___x_119_ = 0;
return v___x_119_;
}
else
{
lean_object* v_p_120_; lean_object* v_p_121_; lean_object* v_m_122_; lean_object* v_m_123_; lean_object* v_x_124_; lean_object* v_k_125_; lean_object* v_x_126_; lean_object* v_k_127_; uint8_t v___x_128_; 
v_p_120_ = lean_ctor_get(v_x_116_, 0);
v_p_121_ = lean_ctor_get(v_x_117_, 0);
v_m_122_ = lean_ctor_get(v_x_116_, 1);
v_m_123_ = lean_ctor_get(v_x_117_, 1);
v_x_124_ = lean_ctor_get(v_p_120_, 0);
v_k_125_ = lean_ctor_get(v_p_120_, 1);
v_x_126_ = lean_ctor_get(v_p_121_, 0);
v_k_127_ = lean_ctor_get(v_p_121_, 1);
v___x_128_ = lean_nat_dec_lt(v_x_124_, v_x_126_);
if (v___x_128_ == 0)
{
uint8_t v___x_129_; 
v___x_129_ = lean_nat_dec_eq(v_x_124_, v_x_126_);
if (v___x_129_ == 0)
{
v_x_117_ = v_m_123_;
goto _start;
}
else
{
uint8_t v___x_131_; 
v___x_131_ = lean_nat_dec_le(v_k_125_, v_k_127_);
if (v___x_131_ == 0)
{
return v___x_131_;
}
else
{
v_x_116_ = v_m_122_;
v_x_117_ = v_m_123_;
goto _start;
}
}
}
else
{
uint8_t v___x_133_; 
v___x_133_ = 0;
return v___x_133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_divides___boxed(lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l_Lean_Grind_CommRing_Mon_divides(v_x_134_, v_x_135_);
lean_dec(v_x_135_);
lean_dec(v_x_134_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_div(lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
if (lean_obj_tag(v_x_139_) == 0)
{
return v_x_138_;
}
else
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_dec_ref_known(v_x_139_, 2);
return v_x_138_;
}
else
{
lean_object* v_p_140_; lean_object* v_p_141_; lean_object* v_m_142_; lean_object* v_m_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_173_; 
v_p_140_ = lean_ctor_get(v_x_138_, 0);
lean_inc_ref(v_p_140_);
v_p_141_ = lean_ctor_get(v_x_139_, 0);
lean_inc_ref(v_p_141_);
v_m_142_ = lean_ctor_get(v_x_139_, 1);
v_m_143_ = lean_ctor_get(v_x_138_, 1);
v_isSharedCheck_173_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_173_ == 0)
{
lean_object* v_unused_174_; 
v_unused_174_ = lean_ctor_get(v_x_138_, 0);
lean_dec(v_unused_174_);
v___x_145_ = v_x_138_;
v_isShared_146_ = v_isSharedCheck_173_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_m_143_);
lean_dec(v_x_138_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_173_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v_x_147_; lean_object* v_k_148_; lean_object* v_x_149_; lean_object* v_k_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_172_; 
v_x_147_ = lean_ctor_get(v_p_140_, 0);
v_k_148_ = lean_ctor_get(v_p_140_, 1);
v_x_149_ = lean_ctor_get(v_p_141_, 0);
v_k_150_ = lean_ctor_get(v_p_141_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_p_141_);
if (v_isSharedCheck_172_ == 0)
{
v___x_152_ = v_p_141_;
v_isShared_153_ = v_isSharedCheck_172_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_k_150_);
lean_inc(v_x_149_);
lean_dec(v_p_141_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_172_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
uint8_t v___x_154_; 
v___x_154_ = lean_nat_dec_lt(v_x_147_, v_x_149_);
if (v___x_154_ == 0)
{
uint8_t v___x_155_; 
lean_inc(v_k_148_);
lean_inc(v_x_147_);
lean_inc(v_m_142_);
lean_dec_ref(v_p_140_);
lean_dec_ref_known(v_x_139_, 2);
v___x_155_ = lean_nat_dec_eq(v_x_147_, v_x_149_);
lean_dec(v_x_149_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; 
lean_del_object(v___x_152_);
lean_dec(v_k_150_);
lean_dec(v_k_148_);
lean_dec(v_x_147_);
lean_del_object(v___x_145_);
lean_dec(v_m_143_);
lean_dec(v_m_142_);
v___x_156_ = lean_box(0);
return v___x_156_;
}
else
{
lean_object* v_k_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v_k_157_ = lean_nat_sub(v_k_148_, v_k_150_);
lean_dec(v_k_150_);
lean_dec(v_k_148_);
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_nat_dec_eq(v_k_157_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_161_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v_k_157_);
lean_ctor_set(v___x_152_, 0, v_x_147_);
v___x_161_ = v___x_152_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_x_147_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_k_157_);
v___x_161_ = v_reuseFailAlloc_166_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = l_Lean_Grind_CommRing_Mon_div(v_m_143_, v_m_142_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v___x_162_);
lean_ctor_set(v___x_145_, 0, v___x_161_);
v___x_164_ = v___x_145_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
else
{
lean_dec(v_k_157_);
lean_del_object(v___x_152_);
lean_dec(v_x_147_);
lean_del_object(v___x_145_);
v_x_138_ = v_m_143_;
v_x_139_ = v_m_142_;
goto _start;
}
}
}
else
{
lean_object* v___x_168_; lean_object* v___x_170_; 
lean_del_object(v___x_152_);
lean_dec(v_k_150_);
lean_dec(v_x_149_);
v___x_168_ = l_Lean_Grind_CommRing_Mon_div(v_m_143_, v_x_139_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v___x_168_);
v___x_170_ = v___x_145_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_p_140_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_coprime(lean_object* v_x_175_, lean_object* v_x_176_){
_start:
{
if (lean_obj_tag(v_x_175_) == 0)
{
uint8_t v___x_177_; 
v___x_177_ = 1;
return v___x_177_;
}
else
{
if (lean_obj_tag(v_x_176_) == 0)
{
uint8_t v___x_178_; 
v___x_178_ = 1;
return v___x_178_;
}
else
{
lean_object* v_p_179_; lean_object* v_p_180_; lean_object* v_m_181_; lean_object* v_m_182_; lean_object* v_x_183_; lean_object* v_x_184_; uint8_t v___x_185_; 
v_p_179_ = lean_ctor_get(v_x_175_, 0);
v_p_180_ = lean_ctor_get(v_x_176_, 0);
v_m_181_ = lean_ctor_get(v_x_175_, 1);
v_m_182_ = lean_ctor_get(v_x_176_, 1);
v_x_183_ = lean_ctor_get(v_p_179_, 0);
v_x_184_ = lean_ctor_get(v_p_180_, 0);
v___x_185_ = lean_nat_dec_lt(v_x_183_, v_x_184_);
if (v___x_185_ == 0)
{
uint8_t v___x_186_; 
v___x_186_ = lean_nat_dec_eq(v_x_183_, v_x_184_);
if (v___x_186_ == 0)
{
v_x_176_ = v_m_182_;
goto _start;
}
else
{
return v___x_185_;
}
}
else
{
v_x_175_ = v_m_181_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_coprime___boxed(lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Lean_Grind_CommRing_Mon_coprime(v_x_189_, v_x_190_);
lean_dec(v_x_190_);
lean_dec(v_x_189_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_x27(lean_object* v_p_193_, lean_object* v_k_194_, lean_object* v_char_x3f_195_){
_start:
{
if (lean_obj_tag(v_char_x3f_195_) == 1)
{
lean_object* v_val_196_; lean_object* v___x_197_; 
v_val_196_ = lean_ctor_get(v_char_x3f_195_, 0);
lean_inc(v_val_196_);
lean_dec_ref_known(v_char_x3f_195_, 1);
v___x_197_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_194_, v_p_193_, v_val_196_);
return v___x_197_;
}
else
{
lean_object* v___x_198_; 
lean_dec(v_char_x3f_195_);
v___x_198_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_194_, v_p_193_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_x27___boxed(lean_object* v_p_199_, lean_object* v_k_200_, lean_object* v_char_x3f_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Grind_CommRing_Poly_mulConst_x27(v_p_199_, v_k_200_, v_char_x3f_201_);
lean_dec(v_k_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_x27(lean_object* v_p_203_, lean_object* v_k_204_, lean_object* v_m_205_, lean_object* v_char_x3f_206_){
_start:
{
if (lean_obj_tag(v_char_x3f_206_) == 1)
{
lean_object* v_val_207_; lean_object* v___x_208_; 
v_val_207_ = lean_ctor_get(v_char_x3f_206_, 0);
lean_inc(v_val_207_);
lean_dec_ref_known(v_char_x3f_206_, 1);
v___x_208_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_204_, v_m_205_, v_p_203_, v_val_207_);
return v___x_208_;
}
else
{
lean_object* v___x_209_; 
lean_dec(v_char_x3f_206_);
v___x_209_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_204_, v_m_205_, v_p_203_);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_x27___boxed(lean_object* v_p_210_, lean_object* v_k_211_, lean_object* v_m_212_, lean_object* v_char_x3f_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Grind_CommRing_Poly_mulMon_x27(v_p_210_, v_k_211_, v_m_212_, v_char_x3f_213_);
lean_dec(v_k_211_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine_x27(lean_object* v_p_u2081_215_, lean_object* v_p_u2082_216_, lean_object* v_char_x3f_217_){
_start:
{
if (lean_obj_tag(v_char_x3f_217_) == 1)
{
lean_object* v_val_218_; lean_object* v___x_219_; 
v_val_218_ = lean_ctor_get(v_char_x3f_217_, 0);
lean_inc(v_val_218_);
lean_dec_ref_known(v_char_x3f_217_, 1);
v___x_219_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_u2081_215_, v_p_u2082_216_, v_val_218_);
return v___x_219_;
}
else
{
lean_object* v___x_220_; 
lean_dec(v_char_x3f_217_);
v___x_220_ = l_Lean_Grind_CommRing_Poly_combine(v_p_u2081_215_, v_p_u2082_216_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_Poly_spol_spec__0(lean_object* v_a_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_nat_to_int(v_a_221_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spol___closed__0(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = lean_nat_to_int(v___x_223_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spol___closed__1(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spol___closed__2(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_227_ = lean_box(0);
v___x_228_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_229_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__1, &l_Lean_Grind_CommRing_Poly_spol___closed__1_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__1);
v___x_230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___x_228_);
lean_ctor_set(v___x_230_, 2, v___x_227_);
lean_ctor_set(v___x_230_, 3, v___x_228_);
lean_ctor_set(v___x_230_, 4, v___x_227_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spol(lean_object* v_p_u2081_231_, lean_object* v_p_u2082_232_, lean_object* v_char_x3f_233_){
_start:
{
if (lean_obj_tag(v_p_u2081_231_) == 1)
{
if (lean_obj_tag(v_p_u2082_232_) == 1)
{
lean_object* v_k_236_; lean_object* v_v_237_; lean_object* v_p_238_; lean_object* v_k_239_; lean_object* v_v_240_; lean_object* v_p_241_; lean_object* v_m_242_; lean_object* v_m_u2081_243_; lean_object* v_m_u2082_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v_g_247_; lean_object* v___x_248_; lean_object* v_c_u2081_249_; lean_object* v___x_250_; lean_object* v_c_u2082_251_; lean_object* v_p_u2081_252_; lean_object* v_p_u2082_253_; lean_object* v_spol_254_; lean_object* v___x_255_; 
v_k_236_ = lean_ctor_get(v_p_u2081_231_, 0);
lean_inc(v_k_236_);
v_v_237_ = lean_ctor_get(v_p_u2081_231_, 1);
lean_inc_n(v_v_237_, 2);
v_p_238_ = lean_ctor_get(v_p_u2081_231_, 2);
lean_inc_ref(v_p_238_);
lean_dec_ref_known(v_p_u2081_231_, 3);
v_k_239_ = lean_ctor_get(v_p_u2082_232_, 0);
lean_inc(v_k_239_);
v_v_240_ = lean_ctor_get(v_p_u2082_232_, 1);
lean_inc_n(v_v_240_, 2);
v_p_241_ = lean_ctor_get(v_p_u2082_232_, 2);
lean_inc_ref(v_p_241_);
lean_dec_ref_known(v_p_u2082_232_, 3);
v_m_242_ = l_Lean_Grind_CommRing_Mon_lcm(v_v_237_, v_v_240_);
lean_inc(v_m_242_);
v_m_u2081_243_ = l_Lean_Grind_CommRing_Mon_div(v_m_242_, v_v_237_);
v_m_u2082_244_ = l_Lean_Grind_CommRing_Mon_div(v_m_242_, v_v_240_);
v___x_245_ = lean_nat_abs(v_k_236_);
v___x_246_ = lean_nat_abs(v_k_239_);
v_g_247_ = lean_nat_gcd(v___x_245_, v___x_246_);
lean_dec(v___x_246_);
lean_dec(v___x_245_);
v___x_248_ = lean_nat_to_int(v_g_247_);
v_c_u2081_249_ = lean_int_ediv(v_k_239_, v___x_248_);
lean_dec(v_k_239_);
v___x_250_ = lean_int_neg(v_k_236_);
lean_dec(v_k_236_);
v_c_u2082_251_ = lean_int_ediv(v___x_250_, v___x_248_);
lean_dec(v___x_248_);
lean_dec(v___x_250_);
lean_inc_n(v_char_x3f_233_, 2);
lean_inc(v_m_u2081_243_);
v_p_u2081_252_ = l_Lean_Grind_CommRing_Poly_mulMon_x27(v_p_238_, v_c_u2081_249_, v_m_u2081_243_, v_char_x3f_233_);
lean_inc(v_m_u2082_244_);
v_p_u2082_253_ = l_Lean_Grind_CommRing_Poly_mulMon_x27(v_p_241_, v_c_u2082_251_, v_m_u2082_244_, v_char_x3f_233_);
v_spol_254_ = l_Lean_Grind_CommRing_Poly_combine_x27(v_p_u2081_252_, v_p_u2082_253_, v_char_x3f_233_);
v___x_255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_255_, 0, v_spol_254_);
lean_ctor_set(v___x_255_, 1, v_c_u2081_249_);
lean_ctor_set(v___x_255_, 2, v_m_u2081_243_);
lean_ctor_set(v___x_255_, 3, v_c_u2082_251_);
lean_ctor_set(v___x_255_, 4, v_m_u2082_244_);
return v___x_255_;
}
else
{
lean_dec_ref_known(v_p_u2081_231_, 3);
lean_dec(v_char_x3f_233_);
lean_dec_ref(v_p_u2082_232_);
goto v___jp_234_;
}
}
else
{
lean_dec(v_char_x3f_233_);
lean_dec_ref(v_p_u2082_232_);
lean_dec_ref(v_p_u2081_231_);
goto v___jp_234_;
}
v___jp_234_:
{
lean_object* v___x_235_; 
v___x_235_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__2, &l_Lean_Grind_CommRing_Poly_spol___closed__2_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__2);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_degree(lean_object* v_x_256_){
_start:
{
if (lean_obj_tag(v_x_256_) == 0)
{
lean_object* v___x_257_; 
v___x_257_ = lean_unsigned_to_nat(0u);
return v___x_257_;
}
else
{
lean_object* v_v_258_; lean_object* v___x_259_; 
v_v_258_ = lean_ctor_get(v_x_256_, 1);
v___x_259_ = l_Lean_Grind_CommRing_Mon_degree(v_v_258_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_degree___boxed(lean_object* v_x_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_Grind_CommRing_Poly_degree(v_x_260_);
lean_dec_ref(v_x_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go(lean_object* v_p_262_, lean_object* v_acc_263_){
_start:
{
if (lean_obj_tag(v_p_262_) == 0)
{
return v_acc_263_;
}
else
{
lean_object* v_p_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_p_264_ = lean_ctor_get(v_p_262_, 2);
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_add(v_acc_263_, v___x_265_);
lean_dec(v_acc_263_);
v_p_262_ = v_p_264_;
v_acc_263_ = v___x_266_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go___boxed(lean_object* v_p_268_, lean_object* v_acc_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go(v_p_268_, v_acc_269_);
lean_dec_ref(v_p_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_numTerms(lean_object* v_p_271_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go(v_p_271_, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_numTerms___boxed(lean_object* v_p_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_Grind_CommRing_Poly_numTerms(v_p_274_);
lean_dec_ref(v_p_274_);
return v_res_275_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_divides(lean_object* v_p_276_, lean_object* v_m_277_){
_start:
{
if (lean_obj_tag(v_p_276_) == 0)
{
uint8_t v___x_278_; 
v___x_278_ = 1;
return v___x_278_;
}
else
{
lean_object* v_v_279_; uint8_t v___x_280_; 
v_v_279_ = lean_ctor_get(v_p_276_, 1);
v___x_280_ = l_Lean_Grind_CommRing_Mon_divides(v_v_279_, v_m_277_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divides___boxed(lean_object* v_p_281_, lean_object* v_m_282_){
_start:
{
uint8_t v_res_283_; lean_object* v_r_284_; 
v_res_283_ = l_Lean_Grind_CommRing_Poly_divides(v_p_281_, v_m_282_);
lean_dec(v_m_282_);
lean_dec_ref(v_p_281_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lc(lean_object* v_x_285_){
_start:
{
lean_object* v_k_286_; 
v_k_286_ = lean_ctor_get(v_x_285_, 0);
lean_inc(v_k_286_);
return v_k_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lc___boxed(lean_object* v_x_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Grind_CommRing_Poly_lc(v_x_287_);
lean_dec_ref(v_x_287_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lm(lean_object* v_x_289_){
_start:
{
if (lean_obj_tag(v_x_289_) == 0)
{
lean_object* v___x_290_; 
v___x_290_ = lean_box(0);
return v___x_290_;
}
else
{
lean_object* v_v_291_; 
v_v_291_ = lean_ctor_get(v_x_289_, 1);
lean_inc(v_v_291_);
return v_v_291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lm___boxed(lean_object* v_x_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_Grind_CommRing_Poly_lm(v_x_292_);
lean_dec_ref(v_x_292_);
return v_res_293_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_isZero(lean_object* v_x_294_){
_start:
{
if (lean_obj_tag(v_x_294_) == 0)
{
lean_object* v_k_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_k_295_ = lean_ctor_get(v_x_294_, 0);
v___x_296_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_297_ = lean_int_dec_eq(v_k_295_, v___x_296_);
return v___x_297_;
}
else
{
uint8_t v___x_298_; 
v___x_298_ = 0;
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_isZero___boxed(lean_object* v_x_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_Lean_Grind_CommRing_Poly_isZero(v_x_299_);
lean_dec_ref(v_x_299_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_getConst(lean_object* v_x_302_){
_start:
{
if (lean_obj_tag(v_x_302_) == 0)
{
lean_object* v_k_303_; 
v_k_303_ = lean_ctor_get(v_x_302_, 0);
lean_inc(v_k_303_);
return v_k_303_;
}
else
{
lean_object* v_p_304_; 
v_p_304_ = lean_ctor_get(v_x_302_, 2);
v_x_302_ = v_p_304_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_getConst___boxed(lean_object* v_x_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Grind_CommRing_Poly_getConst(v_x_306_);
lean_dec_ref(v_x_306_);
return v_res_307_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_checkCoeffs(lean_object* v_x_308_){
_start:
{
if (lean_obj_tag(v_x_308_) == 0)
{
uint8_t v___x_309_; 
v___x_309_ = 1;
return v___x_309_;
}
else
{
lean_object* v_k_310_; lean_object* v_p_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v_k_310_ = lean_ctor_get(v_x_308_, 0);
v_p_311_ = lean_ctor_get(v_x_308_, 2);
v___x_312_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_313_ = lean_int_dec_eq(v_k_310_, v___x_312_);
if (v___x_313_ == 0)
{
v_x_308_ = v_p_311_;
goto _start;
}
else
{
uint8_t v___x_315_; 
v___x_315_ = 0;
return v___x_315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_checkCoeffs___boxed(lean_object* v_x_316_){
_start:
{
uint8_t v_res_317_; lean_object* v_r_318_; 
v_res_317_ = l_Lean_Grind_CommRing_Poly_checkCoeffs(v_x_316_);
lean_dec_ref(v_x_316_);
v_r_318_ = lean_box(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_checkNoUnitMon(lean_object* v_x_319_){
_start:
{
if (lean_obj_tag(v_x_319_) == 0)
{
uint8_t v___x_320_; 
v___x_320_ = 1;
return v___x_320_;
}
else
{
lean_object* v_v_321_; 
v_v_321_ = lean_ctor_get(v_x_319_, 1);
if (lean_obj_tag(v_v_321_) == 0)
{
uint8_t v___x_322_; 
v___x_322_ = 0;
return v___x_322_;
}
else
{
lean_object* v_p_323_; 
v_p_323_ = lean_ctor_get(v_x_319_, 2);
v_x_319_ = v_p_323_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_checkNoUnitMon___boxed(lean_object* v_x_325_){
_start:
{
uint8_t v_res_326_; lean_object* v_r_327_; 
v_res_326_ = l_Lean_Grind_CommRing_Poly_checkNoUnitMon(v_x_325_);
lean_dec_ref(v_x_325_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_size(lean_object* v_x_328_){
_start:
{
if (lean_obj_tag(v_x_328_) == 0)
{
lean_object* v___x_329_; 
v___x_329_ = lean_unsigned_to_nat(0u);
return v___x_329_;
}
else
{
lean_object* v_m_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_m_330_ = lean_ctor_get(v_x_328_, 1);
v___x_331_ = l_Lean_Grind_CommRing_Mon_size(v_m_330_);
v___x_332_ = lean_unsigned_to_nat(1u);
v___x_333_ = lean_nat_add(v___x_331_, v___x_332_);
lean_dec(v___x_331_);
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_size___boxed(lean_object* v_x_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Grind_CommRing_Mon_size(v_x_334_);
lean_dec(v_x_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_size(lean_object* v_x_336_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
lean_object* v___x_337_; 
v___x_337_ = lean_unsigned_to_nat(1u);
return v___x_337_;
}
else
{
lean_object* v_v_338_; lean_object* v_p_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_v_338_ = lean_ctor_get(v_x_336_, 1);
v_p_339_ = lean_ctor_get(v_x_336_, 2);
v___x_340_ = l_Lean_Grind_CommRing_Mon_size(v_v_338_);
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = lean_nat_add(v___x_340_, v___x_341_);
lean_dec(v___x_340_);
v___x_343_ = l_Lean_Grind_CommRing_Poly_size(v_p_339_);
v___x_344_ = lean_nat_add(v___x_342_, v___x_343_);
lean_dec(v___x_343_);
lean_dec(v___x_342_);
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_size___boxed(lean_object* v_x_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Grind_CommRing_Poly_size(v_x_345_);
lean_dec_ref(v_x_345_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_length(lean_object* v_x_347_){
_start:
{
if (lean_obj_tag(v_x_347_) == 0)
{
lean_object* v___x_348_; 
v___x_348_ = lean_unsigned_to_nat(0u);
return v___x_348_;
}
else
{
lean_object* v_p_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_p_349_ = lean_ctor_get(v_x_347_, 2);
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = l_Lean_Grind_CommRing_Poly_length(v_p_349_);
v___x_352_ = lean_nat_add(v___x_350_, v___x_351_);
lean_dec(v___x_351_);
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_length___boxed(lean_object* v_x_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Grind_CommRing_Poly_length(v_x_353_);
lean_dec_ref(v_x_353_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_toExpr(lean_object* v_pw_355_){
_start:
{
lean_object* v_x_356_; lean_object* v_k_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_368_; 
v_x_356_ = lean_ctor_get(v_pw_355_, 0);
v_k_357_ = lean_ctor_get(v_pw_355_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v_pw_355_);
if (v_isSharedCheck_368_ == 0)
{
v___x_359_ = v_pw_355_;
v_isShared_360_ = v_isSharedCheck_368_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_k_357_);
lean_inc(v_x_356_);
lean_dec(v_pw_355_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_368_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = lean_unsigned_to_nat(1u);
v___x_362_ = lean_nat_dec_eq(v_k_357_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_363_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_363_, 0, v_x_356_);
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 8);
lean_ctor_set(v___x_359_, 0, v___x_363_);
v___x_365_ = v___x_359_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_k_357_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
else
{
lean_object* v___x_367_; 
lean_del_object(v___x_359_);
lean_dec(v_k_357_);
v___x_367_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_367_, 0, v_x_356_);
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_toExpr_go(lean_object* v_m_369_, lean_object* v_acc_370_){
_start:
{
if (lean_obj_tag(v_m_369_) == 0)
{
return v_acc_370_;
}
else
{
lean_object* v_p_371_; lean_object* v_m_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_381_; 
v_p_371_ = lean_ctor_get(v_m_369_, 0);
v_m_372_ = lean_ctor_get(v_m_369_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v_m_369_);
if (v_isSharedCheck_381_ == 0)
{
v___x_374_ = v_m_369_;
v_isShared_375_ = v_isSharedCheck_381_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_m_372_);
lean_inc(v_p_371_);
lean_dec(v_m_369_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_381_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_376_ = l_Lean_Grind_CommRing_Power_toExpr(v_p_371_);
if (v_isShared_375_ == 0)
{
lean_ctor_set_tag(v___x_374_, 7);
lean_ctor_set(v___x_374_, 1, v___x_376_);
lean_ctor_set(v___x_374_, 0, v_acc_370_);
v___x_378_ = v___x_374_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_acc_370_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v___x_376_);
v___x_378_ = v_reuseFailAlloc_380_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
v_m_369_ = v_m_372_;
v_acc_370_ = v___x_378_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_unsigned_to_nat(1u);
v___x_383_ = lean_nat_to_int(v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__1(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_toExpr___closed__0, &l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_toExpr(lean_object* v_m_386_){
_start:
{
if (lean_obj_tag(v_m_386_) == 0)
{
lean_object* v___x_387_; 
v___x_387_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_toExpr___closed__1, &l_Lean_Grind_CommRing_Mon_toExpr___closed__1_once, _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__1);
return v___x_387_;
}
else
{
lean_object* v_p_388_; lean_object* v_m_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v_p_388_ = lean_ctor_get(v_m_386_, 0);
lean_inc_ref(v_p_388_);
v_m_389_ = lean_ctor_get(v_m_386_, 1);
lean_inc(v_m_389_);
lean_dec_ref_known(v_m_386_, 2);
v___x_390_ = l_Lean_Grind_CommRing_Power_toExpr(v_p_388_);
v___x_391_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_toExpr_go(v_m_389_, v___x_390_);
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(lean_object* v_k_392_, lean_object* v_m_393_){
_start:
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_toExpr___closed__0, &l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0);
v___x_395_ = lean_int_dec_eq(v_k_392_, v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v_k_392_);
v___x_397_ = l_Lean_Grind_CommRing_Mon_toExpr(v_m_393_);
v___x_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; 
lean_dec(v_k_392_);
v___x_399_ = l_Lean_Grind_CommRing_Mon_toExpr(v_m_393_);
return v___x_399_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_go(lean_object* v_p_400_, lean_object* v_acc_401_){
_start:
{
if (lean_obj_tag(v_p_400_) == 0)
{
lean_object* v_k_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_412_; 
v_k_402_ = lean_ctor_get(v_p_400_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v_p_400_);
if (v_isSharedCheck_412_ == 0)
{
v___x_404_ = v_p_400_;
v_isShared_405_ = v_isSharedCheck_412_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_k_402_);
lean_dec(v_p_400_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_412_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_407_ = lean_int_dec_eq(v_k_402_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_409_; 
if (v_isShared_405_ == 0)
{
v___x_409_ = v___x_404_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_k_402_);
v___x_409_ = v_reuseFailAlloc_411_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_410_; 
v___x_410_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_410_, 0, v_acc_401_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
return v___x_410_;
}
}
else
{
lean_del_object(v___x_404_);
lean_dec(v_k_402_);
return v_acc_401_;
}
}
}
else
{
lean_object* v_k_413_; lean_object* v_v_414_; lean_object* v_p_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_k_413_ = lean_ctor_get(v_p_400_, 0);
lean_inc(v_k_413_);
v_v_414_ = lean_ctor_get(v_p_400_, 1);
lean_inc(v_v_414_);
v_p_415_ = lean_ctor_get(v_p_400_, 2);
lean_inc_ref(v_p_415_);
lean_dec_ref_known(v_p_400_, 3);
v___x_416_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(v_k_413_, v_v_414_);
v___x_417_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_417_, 0, v_acc_401_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v_p_400_ = v_p_415_;
v_acc_401_ = v___x_417_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toExpr(lean_object* v_p_419_){
_start:
{
if (lean_obj_tag(v_p_419_) == 0)
{
lean_object* v_k_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
v_k_420_ = lean_ctor_get(v_p_419_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v_p_419_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v_p_419_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_k_420_);
lean_dec(v_p_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_k_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
else
{
lean_object* v_k_428_; lean_object* v_v_429_; lean_object* v_p_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_k_428_ = lean_ctor_get(v_p_419_, 0);
lean_inc(v_k_428_);
v_v_429_ = lean_ctor_get(v_p_419_, 1);
lean_inc(v_v_429_);
v_p_430_ = lean_ctor_get(v_p_419_, 2);
lean_inc_ref(v_p_430_);
lean_dec_ref_known(v_p_419_, 3);
v___x_431_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(v_k_428_, v_v_429_);
v___x_432_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_go(v_p_430_, v___x_431_);
return v___x_432_;
}
}
}
lean_object* runtime_initialize_Init_Grind_Ring_CommSolver(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Gcd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Ring_CommSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ring_CommSolver(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Gcd(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_CommSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_Poly(builtin);
}
#ifdef __cplusplus
}
#endif
