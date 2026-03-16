// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Poly
// Imports: public import Init.Grind.Ring.CommSolver import Init.Data.Nat.Gcd import Init.Data.Nat.Lemmas import Init.Data.Nat.Linear import Init.WFTactics
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
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulMonC(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulMon(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConstC(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_combineC(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_combine(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Mon_degreeOf(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Mon_degree(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_sharesVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_sharesVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_simp_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_simp_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simp_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_degree(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_degree___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divConst___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_size___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_size___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_length___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_toExpr_go(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Mon_toExpr___closed__0;
static lean_once_cell_t l_Lean_Grind_CommRing_Mon_toExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Mon_toExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_toExpr_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_maxDegreeOf_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_maxDegreeOf_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__3_splitter___redArg(lean_object* v_x_19_, lean_object* v_x_20_, lean_object* v_h__1_21_, lean_object* v_h__2_22_, lean_object* v_h__3_23_){
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
lean_dec_ref(v_x_19_);
v_p_28_ = lean_ctor_get(v_x_20_, 0);
lean_inc_ref(v_p_28_);
v_m_29_ = lean_ctor_get(v_x_20_, 1);
lean_inc(v_m_29_);
lean_dec_ref(v_x_20_);
v___x_30_ = lean_apply_4(v_h__3_23_, v_p_26_, v_m_27_, v_p_28_, v_m_29_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__3_splitter(lean_object* v_motive_31_, lean_object* v_x_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_, lean_object* v_h__3_36_){
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
lean_dec_ref(v_x_32_);
v_p_41_ = lean_ctor_get(v_x_33_, 0);
lean_inc_ref(v_p_41_);
v_m_42_ = lean_ctor_get(v_x_33_, 1);
lean_inc(v_m_42_);
lean_dec_ref(v_x_33_);
v___x_43_ = lean_apply_4(v_h__3_36_, v_p_39_, v_m_40_, v_p_41_, v_m_42_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg(uint8_t v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_, lean_object* v_h__3_47_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg___boxed(lean_object* v_x_54_, lean_object* v_h__1_55_, lean_object* v_h__2_56_, lean_object* v_h__3_57_){
_start:
{
uint8_t v_x_30__boxed_58_; lean_object* v_res_59_; 
v_x_30__boxed_58_ = lean_unbox(v_x_54_);
v_res_59_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg(v_x_30__boxed_58_, v_h__1_55_, v_h__2_56_, v_h__3_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter(lean_object* v_motive_60_, uint8_t v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_, lean_object* v_h__3_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg(v_x_61_, v_h__1_62_, v_h__2_63_, v_h__3_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___boxed(lean_object* v_motive_66_, lean_object* v_x_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_, lean_object* v_h__3_70_){
_start:
{
uint8_t v_x_45__boxed_71_; lean_object* v_res_72_; 
v_x_45__boxed_71_ = lean_unbox(v_x_67_);
v_res_72_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter(v_motive_66_, v_x_45__boxed_71_, v_h__1_68_, v_h__2_69_, v_h__3_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_lcm(lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_x_73_) == 0)
{
return v_x_74_;
}
else
{
if (lean_obj_tag(v_x_74_) == 0)
{
return v_x_73_;
}
else
{
lean_object* v_p_75_; lean_object* v_m_76_; lean_object* v_p_77_; lean_object* v_m_78_; lean_object* v_x_79_; lean_object* v_k_80_; lean_object* v___y_82_; lean_object* v_x_86_; lean_object* v_k_87_; uint8_t v___x_88_; 
v_p_75_ = lean_ctor_get(v_x_73_, 0);
v_m_76_ = lean_ctor_get(v_x_73_, 1);
v_p_77_ = lean_ctor_get(v_x_74_, 0);
v_m_78_ = lean_ctor_get(v_x_74_, 1);
v_x_79_ = lean_ctor_get(v_p_75_, 0);
v_k_80_ = lean_ctor_get(v_p_75_, 1);
v_x_86_ = lean_ctor_get(v_p_77_, 0);
v_k_87_ = lean_ctor_get(v_p_77_, 1);
v___x_88_ = lean_nat_dec_lt(v_x_79_, v_x_86_);
if (v___x_88_ == 0)
{
lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_98_; 
lean_inc(v_m_78_);
lean_inc_ref(v_p_77_);
v_isSharedCheck_98_ = !lean_is_exclusive(v_x_74_);
if (v_isSharedCheck_98_ == 0)
{
lean_object* v_unused_99_; lean_object* v_unused_100_; 
v_unused_99_ = lean_ctor_get(v_x_74_, 1);
lean_dec(v_unused_99_);
v_unused_100_ = lean_ctor_get(v_x_74_, 0);
lean_dec(v_unused_100_);
v___x_90_ = v_x_74_;
v_isShared_91_ = v_isSharedCheck_98_;
goto v_resetjp_89_;
}
else
{
lean_dec(v_x_74_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_98_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
uint8_t v___x_92_; 
v___x_92_ = lean_nat_dec_eq(v_x_79_, v_x_86_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_93_ = l_Lean_Grind_CommRing_Mon_lcm(v_x_73_, v_m_78_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v___x_93_);
v___x_95_ = v___x_90_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_p_77_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
else
{
uint8_t v___x_97_; 
lean_inc(v_k_87_);
lean_inc(v_k_80_);
lean_inc(v_x_79_);
lean_inc(v_m_76_);
lean_del_object(v___x_90_);
lean_dec_ref(v_p_77_);
lean_dec_ref(v_x_73_);
v___x_97_ = lean_nat_dec_le(v_k_80_, v_k_87_);
if (v___x_97_ == 0)
{
lean_dec(v_k_87_);
v___y_82_ = v_k_80_;
goto v___jp_81_;
}
else
{
lean_dec(v_k_80_);
v___y_82_ = v_k_87_;
goto v___jp_81_;
}
}
}
}
else
{
lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_108_; 
lean_inc(v_m_76_);
lean_inc_ref(v_p_75_);
v_isSharedCheck_108_ = !lean_is_exclusive(v_x_73_);
if (v_isSharedCheck_108_ == 0)
{
lean_object* v_unused_109_; lean_object* v_unused_110_; 
v_unused_109_ = lean_ctor_get(v_x_73_, 1);
lean_dec(v_unused_109_);
v_unused_110_ = lean_ctor_get(v_x_73_, 0);
lean_dec(v_unused_110_);
v___x_102_ = v_x_73_;
v_isShared_103_ = v_isSharedCheck_108_;
goto v_resetjp_101_;
}
else
{
lean_dec(v_x_73_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_108_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_104_ = l_Lean_Grind_CommRing_Mon_lcm(v_m_76_, v_x_74_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___x_104_);
v___x_106_ = v___x_102_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_p_75_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
v___jp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v_x_79_);
lean_ctor_set(v___x_83_, 1, v___y_82_);
v___x_84_ = l_Lean_Grind_CommRing_Mon_lcm(v_m_76_, v_m_78_);
v___x_85_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
return v___x_85_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_divides(lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
if (lean_obj_tag(v_x_111_) == 0)
{
uint8_t v___x_113_; 
v___x_113_ = 1;
return v___x_113_;
}
else
{
if (lean_obj_tag(v_x_112_) == 0)
{
uint8_t v___x_114_; 
v___x_114_ = 0;
return v___x_114_;
}
else
{
lean_object* v_p_115_; lean_object* v_p_116_; lean_object* v_m_117_; lean_object* v_m_118_; lean_object* v_x_119_; lean_object* v_k_120_; lean_object* v_x_121_; lean_object* v_k_122_; uint8_t v___x_123_; 
v_p_115_ = lean_ctor_get(v_x_111_, 0);
v_p_116_ = lean_ctor_get(v_x_112_, 0);
v_m_117_ = lean_ctor_get(v_x_111_, 1);
v_m_118_ = lean_ctor_get(v_x_112_, 1);
v_x_119_ = lean_ctor_get(v_p_115_, 0);
v_k_120_ = lean_ctor_get(v_p_115_, 1);
v_x_121_ = lean_ctor_get(v_p_116_, 0);
v_k_122_ = lean_ctor_get(v_p_116_, 1);
v___x_123_ = lean_nat_dec_lt(v_x_119_, v_x_121_);
if (v___x_123_ == 0)
{
uint8_t v___x_124_; 
v___x_124_ = lean_nat_dec_eq(v_x_119_, v_x_121_);
if (v___x_124_ == 0)
{
v_x_112_ = v_m_118_;
goto _start;
}
else
{
uint8_t v___x_126_; 
v___x_126_ = lean_nat_dec_le(v_k_120_, v_k_122_);
if (v___x_126_ == 0)
{
return v___x_126_;
}
else
{
v_x_111_ = v_m_117_;
v_x_112_ = v_m_118_;
goto _start;
}
}
}
else
{
uint8_t v___x_128_; 
v___x_128_ = 0;
return v___x_128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_divides___boxed(lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Lean_Grind_CommRing_Mon_divides(v_x_129_, v_x_130_);
lean_dec(v_x_130_);
lean_dec(v_x_129_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_div(lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
if (lean_obj_tag(v_x_134_) == 0)
{
return v_x_133_;
}
else
{
if (lean_obj_tag(v_x_133_) == 0)
{
lean_dec_ref(v_x_134_);
return v_x_133_;
}
else
{
lean_object* v_p_135_; lean_object* v_p_136_; lean_object* v_m_137_; lean_object* v_m_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_168_; 
v_p_135_ = lean_ctor_get(v_x_133_, 0);
lean_inc_ref(v_p_135_);
v_p_136_ = lean_ctor_get(v_x_134_, 0);
lean_inc_ref(v_p_136_);
v_m_137_ = lean_ctor_get(v_x_134_, 1);
v_m_138_ = lean_ctor_get(v_x_133_, 1);
v_isSharedCheck_168_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_168_ == 0)
{
lean_object* v_unused_169_; 
v_unused_169_ = lean_ctor_get(v_x_133_, 0);
lean_dec(v_unused_169_);
v___x_140_ = v_x_133_;
v_isShared_141_ = v_isSharedCheck_168_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_m_138_);
lean_dec(v_x_133_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_168_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v_x_142_; lean_object* v_k_143_; lean_object* v_x_144_; lean_object* v_k_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_167_; 
v_x_142_ = lean_ctor_get(v_p_135_, 0);
v_k_143_ = lean_ctor_get(v_p_135_, 1);
v_x_144_ = lean_ctor_get(v_p_136_, 0);
v_k_145_ = lean_ctor_get(v_p_136_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v_p_136_);
if (v_isSharedCheck_167_ == 0)
{
v___x_147_ = v_p_136_;
v_isShared_148_ = v_isSharedCheck_167_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_k_145_);
lean_inc(v_x_144_);
lean_dec(v_p_136_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_167_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
uint8_t v___x_149_; 
v___x_149_ = lean_nat_dec_lt(v_x_142_, v_x_144_);
if (v___x_149_ == 0)
{
uint8_t v___x_150_; 
lean_inc(v_k_143_);
lean_inc(v_x_142_);
lean_inc(v_m_137_);
lean_dec_ref(v_p_135_);
lean_dec_ref(v_x_134_);
v___x_150_ = lean_nat_dec_eq(v_x_142_, v_x_144_);
lean_dec(v_x_144_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
lean_del_object(v___x_147_);
lean_dec(v_k_145_);
lean_dec(v_k_143_);
lean_dec(v_x_142_);
lean_del_object(v___x_140_);
lean_dec(v_m_138_);
lean_dec(v_m_137_);
v___x_151_ = lean_box(0);
return v___x_151_;
}
else
{
lean_object* v_k_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v_k_152_ = lean_nat_sub(v_k_143_, v_k_145_);
lean_dec(v_k_145_);
lean_dec(v_k_143_);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = lean_nat_dec_eq(v_k_152_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_156_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 1, v_k_152_);
lean_ctor_set(v___x_147_, 0, v_x_142_);
v___x_156_ = v___x_147_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_x_142_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_k_152_);
v___x_156_ = v_reuseFailAlloc_161_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_157_ = l_Lean_Grind_CommRing_Mon_div(v_m_138_, v_m_137_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v___x_157_);
lean_ctor_set(v___x_140_, 0, v___x_156_);
v___x_159_ = v___x_140_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
else
{
lean_dec(v_k_152_);
lean_del_object(v___x_147_);
lean_dec(v_x_142_);
lean_del_object(v___x_140_);
v_x_133_ = v_m_138_;
v_x_134_ = v_m_137_;
goto _start;
}
}
}
else
{
lean_object* v___x_163_; lean_object* v___x_165_; 
lean_del_object(v___x_147_);
lean_dec(v_k_145_);
lean_dec(v_x_144_);
v___x_163_ = l_Lean_Grind_CommRing_Mon_div(v_m_138_, v_x_134_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v___x_163_);
v___x_165_ = v___x_140_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_p_135_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v___x_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Mon_coprime(lean_object* v_x_170_, lean_object* v_x_171_){
_start:
{
if (lean_obj_tag(v_x_170_) == 0)
{
uint8_t v___x_172_; 
v___x_172_ = 1;
return v___x_172_;
}
else
{
if (lean_obj_tag(v_x_171_) == 0)
{
uint8_t v___x_173_; 
v___x_173_ = 1;
return v___x_173_;
}
else
{
lean_object* v_p_174_; lean_object* v_p_175_; lean_object* v_m_176_; lean_object* v_m_177_; lean_object* v_x_178_; lean_object* v_x_179_; uint8_t v___x_180_; 
v_p_174_ = lean_ctor_get(v_x_170_, 0);
v_p_175_ = lean_ctor_get(v_x_171_, 0);
v_m_176_ = lean_ctor_get(v_x_170_, 1);
v_m_177_ = lean_ctor_get(v_x_171_, 1);
v_x_178_ = lean_ctor_get(v_p_174_, 0);
v_x_179_ = lean_ctor_get(v_p_175_, 0);
v___x_180_ = lean_nat_dec_lt(v_x_178_, v_x_179_);
if (v___x_180_ == 0)
{
uint8_t v___x_181_; 
v___x_181_ = lean_nat_dec_eq(v_x_178_, v_x_179_);
if (v___x_181_ == 0)
{
v_x_171_ = v_m_177_;
goto _start;
}
else
{
return v___x_180_;
}
}
else
{
v_x_170_ = v_m_176_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_coprime___boxed(lean_object* v_x_184_, lean_object* v_x_185_){
_start:
{
uint8_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = l_Lean_Grind_CommRing_Mon_coprime(v_x_184_, v_x_185_);
lean_dec(v_x_185_);
lean_dec(v_x_184_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_x27(lean_object* v_p_188_, lean_object* v_k_189_, lean_object* v_char_x3f_190_){
_start:
{
if (lean_obj_tag(v_char_x3f_190_) == 1)
{
lean_object* v_val_191_; lean_object* v___x_192_; 
v_val_191_ = lean_ctor_get(v_char_x3f_190_, 0);
lean_inc(v_val_191_);
lean_dec_ref(v_char_x3f_190_);
v___x_192_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_189_, v_p_188_, v_val_191_);
return v___x_192_;
}
else
{
lean_object* v___x_193_; 
lean_dec(v_char_x3f_190_);
v___x_193_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_189_, v_p_188_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_x27___boxed(lean_object* v_p_194_, lean_object* v_k_195_, lean_object* v_char_x3f_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Grind_CommRing_Poly_mulConst_x27(v_p_194_, v_k_195_, v_char_x3f_196_);
lean_dec(v_k_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_x27(lean_object* v_p_198_, lean_object* v_k_199_, lean_object* v_m_200_, lean_object* v_char_x3f_201_){
_start:
{
if (lean_obj_tag(v_char_x3f_201_) == 1)
{
lean_object* v_val_202_; lean_object* v___x_203_; 
v_val_202_ = lean_ctor_get(v_char_x3f_201_, 0);
lean_inc(v_val_202_);
lean_dec_ref(v_char_x3f_201_);
v___x_203_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_199_, v_m_200_, v_p_198_, v_val_202_);
return v___x_203_;
}
else
{
lean_object* v___x_204_; 
lean_dec(v_char_x3f_201_);
v___x_204_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_199_, v_m_200_, v_p_198_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_x27___boxed(lean_object* v_p_205_, lean_object* v_k_206_, lean_object* v_m_207_, lean_object* v_char_x3f_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Grind_CommRing_Poly_mulMon_x27(v_p_205_, v_k_206_, v_m_207_, v_char_x3f_208_);
lean_dec(v_k_206_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine_x27(lean_object* v_p_u2081_210_, lean_object* v_p_u2082_211_, lean_object* v_char_x3f_212_){
_start:
{
if (lean_obj_tag(v_char_x3f_212_) == 1)
{
lean_object* v_val_213_; lean_object* v___x_214_; 
v_val_213_ = lean_ctor_get(v_char_x3f_212_, 0);
lean_inc(v_val_213_);
lean_dec_ref(v_char_x3f_212_);
v___x_214_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_u2081_210_, v_p_u2082_211_, v_val_213_);
return v___x_214_;
}
else
{
lean_object* v___x_215_; 
lean_dec(v_char_x3f_212_);
v___x_215_ = l_Lean_Grind_CommRing_Poly_combine(v_p_u2081_210_, v_p_u2082_211_);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_Poly_spol_spec__0(lean_object* v_a_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_nat_to_int(v_a_216_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spol___closed__0(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_nat_to_int(v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spol___closed__1(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spol___closed__2(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_222_ = lean_box(0);
v___x_223_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_224_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__1, &l_Lean_Grind_CommRing_Poly_spol___closed__1_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__1);
v___x_225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v___x_223_);
lean_ctor_set(v___x_225_, 2, v___x_222_);
lean_ctor_set(v___x_225_, 3, v___x_223_);
lean_ctor_set(v___x_225_, 4, v___x_222_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spol(lean_object* v_p_u2081_226_, lean_object* v_p_u2082_227_, lean_object* v_char_x3f_228_){
_start:
{
if (lean_obj_tag(v_p_u2081_226_) == 1)
{
if (lean_obj_tag(v_p_u2082_227_) == 1)
{
lean_object* v_k_231_; lean_object* v_v_232_; lean_object* v_p_233_; lean_object* v_k_234_; lean_object* v_v_235_; lean_object* v_p_236_; lean_object* v_m_237_; lean_object* v_m_u2081_238_; lean_object* v_m_u2082_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v_g_242_; lean_object* v___x_243_; lean_object* v_c_u2081_244_; lean_object* v___x_245_; lean_object* v_c_u2082_246_; lean_object* v_p_u2081_247_; lean_object* v_p_u2082_248_; lean_object* v_spol_249_; lean_object* v___x_250_; 
v_k_231_ = lean_ctor_get(v_p_u2081_226_, 0);
lean_inc(v_k_231_);
v_v_232_ = lean_ctor_get(v_p_u2081_226_, 1);
lean_inc(v_v_232_);
v_p_233_ = lean_ctor_get(v_p_u2081_226_, 2);
lean_inc_ref(v_p_233_);
lean_dec_ref(v_p_u2081_226_);
v_k_234_ = lean_ctor_get(v_p_u2082_227_, 0);
lean_inc(v_k_234_);
v_v_235_ = lean_ctor_get(v_p_u2082_227_, 1);
lean_inc(v_v_235_);
v_p_236_ = lean_ctor_get(v_p_u2082_227_, 2);
lean_inc_ref(v_p_236_);
lean_dec_ref(v_p_u2082_227_);
lean_inc(v_v_235_);
lean_inc(v_v_232_);
v_m_237_ = l_Lean_Grind_CommRing_Mon_lcm(v_v_232_, v_v_235_);
lean_inc(v_m_237_);
v_m_u2081_238_ = l_Lean_Grind_CommRing_Mon_div(v_m_237_, v_v_232_);
v_m_u2082_239_ = l_Lean_Grind_CommRing_Mon_div(v_m_237_, v_v_235_);
v___x_240_ = lean_nat_abs(v_k_231_);
v___x_241_ = lean_nat_abs(v_k_234_);
v_g_242_ = lean_nat_gcd(v___x_240_, v___x_241_);
lean_dec(v___x_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_nat_to_int(v_g_242_);
v_c_u2081_244_ = lean_int_ediv(v_k_234_, v___x_243_);
lean_dec(v_k_234_);
v___x_245_ = lean_int_neg(v_k_231_);
lean_dec(v_k_231_);
v_c_u2082_246_ = lean_int_ediv(v___x_245_, v___x_243_);
lean_dec(v___x_243_);
lean_dec(v___x_245_);
lean_inc(v_char_x3f_228_);
lean_inc(v_m_u2081_238_);
v_p_u2081_247_ = l_Lean_Grind_CommRing_Poly_mulMon_x27(v_p_233_, v_c_u2081_244_, v_m_u2081_238_, v_char_x3f_228_);
lean_inc(v_char_x3f_228_);
lean_inc(v_m_u2082_239_);
v_p_u2082_248_ = l_Lean_Grind_CommRing_Poly_mulMon_x27(v_p_236_, v_c_u2082_246_, v_m_u2082_239_, v_char_x3f_228_);
v_spol_249_ = l_Lean_Grind_CommRing_Poly_combine_x27(v_p_u2081_247_, v_p_u2082_248_, v_char_x3f_228_);
v___x_250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_250_, 0, v_spol_249_);
lean_ctor_set(v___x_250_, 1, v_c_u2081_244_);
lean_ctor_set(v___x_250_, 2, v_m_u2081_238_);
lean_ctor_set(v___x_250_, 3, v_c_u2082_246_);
lean_ctor_set(v___x_250_, 4, v_m_u2082_239_);
return v___x_250_;
}
else
{
lean_dec_ref(v_p_u2081_226_);
lean_dec(v_char_x3f_228_);
lean_dec_ref(v_p_u2082_227_);
goto v___jp_229_;
}
}
else
{
lean_dec(v_char_x3f_228_);
lean_dec_ref(v_p_u2082_227_);
lean_dec_ref(v_p_u2081_226_);
goto v___jp_229_;
}
v___jp_229_:
{
lean_object* v___x_230_; 
v___x_230_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__2, &l_Lean_Grind_CommRing_Poly_spol___closed__2_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__2);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_simp_x3f_go_x3f(lean_object* v_char_x3f_251_, lean_object* v_k_u2082_x27_252_, lean_object* v_m_u2082_253_, lean_object* v_p_u2082_254_, lean_object* v_p_u2081_255_){
_start:
{
if (lean_obj_tag(v_p_u2081_255_) == 0)
{
lean_object* v___x_256_; 
lean_dec_ref(v_p_u2081_255_);
lean_dec_ref(v_p_u2082_254_);
lean_dec(v_m_u2082_253_);
lean_dec(v_char_x3f_251_);
v___x_256_ = lean_box(0);
return v___x_256_;
}
else
{
lean_object* v_k_257_; lean_object* v_v_258_; lean_object* v_p_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_330_; 
v_k_257_ = lean_ctor_get(v_p_u2081_255_, 0);
v_v_258_ = lean_ctor_get(v_p_u2081_255_, 1);
v_p_259_ = lean_ctor_get(v_p_u2081_255_, 2);
v_isSharedCheck_330_ = !lean_is_exclusive(v_p_u2081_255_);
if (v_isSharedCheck_330_ == 0)
{
v___x_261_ = v_p_u2081_255_;
v_isShared_262_ = v_isSharedCheck_330_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_p_259_);
lean_inc(v_v_258_);
lean_inc(v_k_257_);
lean_dec(v_p_u2081_255_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_330_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
uint8_t v___x_263_; 
v___x_263_ = l_Lean_Grind_CommRing_Mon_divides(v_m_u2082_253_, v_v_258_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
lean_inc(v_char_x3f_251_);
v___x_264_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_simp_x3f_go_x3f(v_char_x3f_251_, v_k_u2082_x27_252_, v_m_u2082_253_, v_p_u2082_254_, v_p_259_);
if (lean_obj_tag(v___x_264_) == 1)
{
if (lean_obj_tag(v_char_x3f_251_) == 1)
{
lean_object* v_val_265_; lean_object* v_val_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_292_; 
v_val_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_val_265_);
v_val_266_ = lean_ctor_get(v_char_x3f_251_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v_char_x3f_251_);
if (v_isSharedCheck_292_ == 0)
{
v___x_268_ = v_char_x3f_251_;
v_isShared_269_ = v_isSharedCheck_292_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_val_266_);
lean_dec(v_char_x3f_251_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_292_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v_p_270_; lean_object* v_k_u2081_271_; lean_object* v_k_u2082_272_; lean_object* v_m_u2082_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_291_; 
v_p_270_ = lean_ctor_get(v_val_265_, 0);
v_k_u2081_271_ = lean_ctor_get(v_val_265_, 1);
v_k_u2082_272_ = lean_ctor_get(v_val_265_, 2);
v_m_u2082_273_ = lean_ctor_get(v_val_265_, 3);
v_isSharedCheck_291_ = !lean_is_exclusive(v_val_265_);
if (v_isSharedCheck_291_ == 0)
{
v___x_275_ = v_val_265_;
v_isShared_276_ = v_isSharedCheck_291_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_m_u2082_273_);
lean_inc(v_k_u2082_272_);
lean_inc(v_k_u2081_271_);
lean_inc(v_p_270_);
lean_dec(v_val_265_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_291_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_k_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_277_ = lean_int_mul(v_k_257_, v_k_u2081_271_);
lean_dec(v_k_257_);
v___x_278_ = lean_nat_to_int(v_val_266_);
v_k_279_ = lean_int_emod(v___x_277_, v___x_278_);
lean_dec(v___x_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_281_ = lean_int_dec_eq(v_k_279_, v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_283_; 
lean_dec_ref(v___x_264_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 2, v_p_270_);
lean_ctor_set(v___x_261_, 0, v_k_279_);
v___x_283_ = v___x_261_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_k_279_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_v_258_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v_p_270_);
v___x_283_ = v_reuseFailAlloc_290_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_285_; 
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_283_);
v___x_285_ = v___x_275_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_k_u2081_271_);
lean_ctor_set(v_reuseFailAlloc_289_, 2, v_k_u2082_272_);
lean_ctor_set(v_reuseFailAlloc_289_, 3, v_m_u2082_273_);
v___x_285_ = v_reuseFailAlloc_289_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_287_; 
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_285_);
v___x_287_ = v___x_268_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
else
{
lean_dec(v_k_279_);
lean_del_object(v___x_275_);
lean_dec(v_m_u2082_273_);
lean_dec(v_k_u2082_272_);
lean_dec(v_k_u2081_271_);
lean_dec_ref(v_p_270_);
lean_del_object(v___x_268_);
lean_del_object(v___x_261_);
lean_dec(v_v_258_);
return v___x_264_;
}
}
}
}
else
{
lean_object* v_val_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_315_; 
lean_dec(v_char_x3f_251_);
v_val_293_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_315_ == 0)
{
v___x_295_ = v___x_264_;
v_isShared_296_ = v_isSharedCheck_315_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_val_293_);
lean_dec(v___x_264_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_315_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v_p_297_; lean_object* v_k_u2081_298_; lean_object* v_k_u2082_299_; lean_object* v_m_u2082_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_314_; 
v_p_297_ = lean_ctor_get(v_val_293_, 0);
v_k_u2081_298_ = lean_ctor_get(v_val_293_, 1);
v_k_u2082_299_ = lean_ctor_get(v_val_293_, 2);
v_m_u2082_300_ = lean_ctor_get(v_val_293_, 3);
v_isSharedCheck_314_ = !lean_is_exclusive(v_val_293_);
if (v_isSharedCheck_314_ == 0)
{
v___x_302_ = v_val_293_;
v_isShared_303_ = v_isSharedCheck_314_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_m_u2082_300_);
lean_inc(v_k_u2082_299_);
lean_inc(v_k_u2081_298_);
lean_inc(v_p_297_);
lean_dec(v_val_293_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_314_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_304_ = lean_int_mul(v_k_257_, v_k_u2081_298_);
lean_dec(v_k_257_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 2, v_p_297_);
lean_ctor_set(v___x_261_, 0, v___x_304_);
v___x_306_ = v___x_261_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_v_258_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_p_297_);
v___x_306_ = v_reuseFailAlloc_313_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_308_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_306_);
v___x_308_ = v___x_302_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_k_u2081_298_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v_k_u2082_299_);
lean_ctor_set(v_reuseFailAlloc_312_, 3, v_m_u2082_300_);
v___x_308_ = v_reuseFailAlloc_312_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_310_; 
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_308_);
v___x_310_ = v___x_295_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_316_; 
lean_dec(v___x_264_);
lean_del_object(v___x_261_);
lean_dec(v_v_258_);
lean_dec(v_k_257_);
lean_dec(v_char_x3f_251_);
v___x_316_ = lean_box(0);
return v___x_316_;
}
}
else
{
lean_object* v_m_u2082_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v_g_320_; lean_object* v___x_321_; lean_object* v_k_u2081_322_; lean_object* v___x_323_; lean_object* v_k_u2082_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v_p_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_del_object(v___x_261_);
v_m_u2082_317_ = l_Lean_Grind_CommRing_Mon_div(v_v_258_, v_m_u2082_253_);
v___x_318_ = lean_nat_abs(v_k_257_);
v___x_319_ = lean_nat_abs(v_k_u2082_x27_252_);
v_g_320_ = lean_nat_gcd(v___x_318_, v___x_319_);
lean_dec(v___x_319_);
lean_dec(v___x_318_);
v___x_321_ = lean_nat_to_int(v_g_320_);
v_k_u2081_322_ = lean_int_ediv(v_k_u2082_x27_252_, v___x_321_);
v___x_323_ = lean_int_neg(v_k_257_);
lean_dec(v_k_257_);
v_k_u2082_324_ = lean_int_ediv(v___x_323_, v___x_321_);
lean_dec(v___x_321_);
lean_dec(v___x_323_);
lean_inc(v_char_x3f_251_);
lean_inc(v_m_u2082_317_);
v___x_325_ = l_Lean_Grind_CommRing_Poly_mulMon_x27(v_p_u2082_254_, v_k_u2082_324_, v_m_u2082_317_, v_char_x3f_251_);
lean_inc(v_char_x3f_251_);
v___x_326_ = l_Lean_Grind_CommRing_Poly_mulConst_x27(v_p_259_, v_k_u2081_322_, v_char_x3f_251_);
v_p_327_ = l_Lean_Grind_CommRing_Poly_combine_x27(v___x_325_, v___x_326_, v_char_x3f_251_);
v___x_328_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_328_, 0, v_p_327_);
lean_ctor_set(v___x_328_, 1, v_k_u2081_322_);
lean_ctor_set(v___x_328_, 2, v_k_u2082_324_);
lean_ctor_set(v___x_328_, 3, v_m_u2082_317_);
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_simp_x3f_go_x3f___boxed(lean_object* v_char_x3f_331_, lean_object* v_k_u2082_x27_332_, lean_object* v_m_u2082_333_, lean_object* v_p_u2082_334_, lean_object* v_p_u2081_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_simp_x3f_go_x3f(v_char_x3f_331_, v_k_u2082_x27_332_, v_m_u2082_333_, v_p_u2082_334_, v_p_u2081_335_);
lean_dec(v_k_u2082_x27_332_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simp_x3f(lean_object* v_p_u2081_337_, lean_object* v_p_u2082_338_, lean_object* v_char_x3f_339_){
_start:
{
if (lean_obj_tag(v_p_u2082_338_) == 1)
{
lean_object* v_k_340_; lean_object* v_v_341_; lean_object* v_p_342_; lean_object* v___x_343_; 
v_k_340_ = lean_ctor_get(v_p_u2082_338_, 0);
lean_inc(v_k_340_);
v_v_341_ = lean_ctor_get(v_p_u2082_338_, 1);
lean_inc(v_v_341_);
v_p_342_ = lean_ctor_get(v_p_u2082_338_, 2);
lean_inc_ref(v_p_342_);
lean_dec_ref(v_p_u2082_338_);
v___x_343_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_simp_x3f_go_x3f(v_char_x3f_339_, v_k_340_, v_v_341_, v_p_342_, v_p_u2081_337_);
lean_dec(v_k_340_);
return v___x_343_;
}
else
{
lean_object* v___x_344_; 
lean_dec(v_char_x3f_339_);
lean_dec_ref(v_p_u2082_338_);
lean_dec_ref(v_p_u2081_337_);
v___x_344_ = lean_box(0);
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_degree(lean_object* v_x_345_){
_start:
{
if (lean_obj_tag(v_x_345_) == 0)
{
lean_object* v___x_346_; 
v___x_346_ = lean_unsigned_to_nat(0u);
return v___x_346_;
}
else
{
lean_object* v_v_347_; lean_object* v___x_348_; 
v_v_347_ = lean_ctor_get(v_x_345_, 1);
v___x_348_ = l_Lean_Grind_CommRing_Mon_degree(v_v_347_);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_degree___boxed(lean_object* v_x_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Grind_CommRing_Poly_degree(v_x_349_);
lean_dec_ref(v_x_349_);
return v_res_350_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_divides(lean_object* v_p_351_, lean_object* v_m_352_){
_start:
{
if (lean_obj_tag(v_p_351_) == 0)
{
uint8_t v___x_353_; 
v___x_353_ = 1;
return v___x_353_;
}
else
{
lean_object* v_v_354_; uint8_t v___x_355_; 
v_v_354_ = lean_ctor_get(v_p_351_, 1);
v___x_355_ = l_Lean_Grind_CommRing_Mon_divides(v_v_354_, v_m_352_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divides___boxed(lean_object* v_p_356_, lean_object* v_m_357_){
_start:
{
uint8_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = l_Lean_Grind_CommRing_Poly_divides(v_p_356_, v_m_357_);
lean_dec(v_m_357_);
lean_dec_ref(v_p_356_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lc(lean_object* v_x_360_){
_start:
{
lean_object* v_k_361_; 
v_k_361_ = lean_ctor_get(v_x_360_, 0);
lean_inc(v_k_361_);
return v_k_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lc___boxed(lean_object* v_x_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Grind_CommRing_Poly_lc(v_x_362_);
lean_dec_ref(v_x_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lm(lean_object* v_x_364_){
_start:
{
if (lean_obj_tag(v_x_364_) == 0)
{
lean_object* v___x_365_; 
v___x_365_ = lean_box(0);
return v___x_365_;
}
else
{
lean_object* v_v_366_; 
v_v_366_ = lean_ctor_get(v_x_364_, 1);
lean_inc(v_v_366_);
return v_v_366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lm___boxed(lean_object* v_x_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Grind_CommRing_Poly_lm(v_x_367_);
lean_dec_ref(v_x_367_);
return v_res_368_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_isZero(lean_object* v_x_369_){
_start:
{
if (lean_obj_tag(v_x_369_) == 0)
{
lean_object* v_k_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v_k_370_ = lean_ctor_get(v_x_369_, 0);
v___x_371_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_372_ = lean_int_dec_eq(v_k_370_, v___x_371_);
return v___x_372_;
}
else
{
uint8_t v___x_373_; 
v___x_373_ = 0;
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_isZero___boxed(lean_object* v_x_374_){
_start:
{
uint8_t v_res_375_; lean_object* v_r_376_; 
v_res_375_ = l_Lean_Grind_CommRing_Poly_isZero(v_x_374_);
lean_dec_ref(v_x_374_);
v_r_376_ = lean_box(v_res_375_);
return v_r_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_getConst(lean_object* v_x_377_){
_start:
{
if (lean_obj_tag(v_x_377_) == 0)
{
lean_object* v_k_378_; 
v_k_378_ = lean_ctor_get(v_x_377_, 0);
lean_inc(v_k_378_);
return v_k_378_;
}
else
{
lean_object* v_p_379_; 
v_p_379_ = lean_ctor_get(v_x_377_, 2);
v_x_377_ = v_p_379_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_getConst___boxed(lean_object* v_x_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Grind_CommRing_Poly_getConst(v_x_381_);
lean_dec_ref(v_x_381_);
return v_res_382_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_checkCoeffs(lean_object* v_x_383_){
_start:
{
if (lean_obj_tag(v_x_383_) == 0)
{
uint8_t v___x_384_; 
v___x_384_ = 1;
return v___x_384_;
}
else
{
lean_object* v_k_385_; lean_object* v_p_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v_k_385_ = lean_ctor_get(v_x_383_, 0);
v_p_386_ = lean_ctor_get(v_x_383_, 2);
v___x_387_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_388_ = lean_int_dec_eq(v_k_385_, v___x_387_);
if (v___x_388_ == 0)
{
v_x_383_ = v_p_386_;
goto _start;
}
else
{
uint8_t v___x_390_; 
v___x_390_ = 0;
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_checkCoeffs___boxed(lean_object* v_x_391_){
_start:
{
uint8_t v_res_392_; lean_object* v_r_393_; 
v_res_392_ = l_Lean_Grind_CommRing_Poly_checkCoeffs(v_x_391_);
lean_dec_ref(v_x_391_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_checkNoUnitMon(lean_object* v_x_394_){
_start:
{
if (lean_obj_tag(v_x_394_) == 0)
{
uint8_t v___x_395_; 
v___x_395_ = 1;
return v___x_395_;
}
else
{
lean_object* v_v_396_; 
v_v_396_ = lean_ctor_get(v_x_394_, 1);
if (lean_obj_tag(v_v_396_) == 0)
{
uint8_t v___x_397_; 
v___x_397_ = 0;
return v___x_397_;
}
else
{
lean_object* v_p_398_; 
v_p_398_ = lean_ctor_get(v_x_394_, 2);
v_x_394_ = v_p_398_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_checkNoUnitMon___boxed(lean_object* v_x_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l_Lean_Grind_CommRing_Poly_checkNoUnitMon(v_x_400_);
lean_dec_ref(v_x_400_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go(lean_object* v_p_403_, lean_object* v_acc_404_){
_start:
{
lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_405_ = lean_unsigned_to_nat(1u);
v___x_406_ = lean_nat_dec_eq(v_acc_404_, v___x_405_);
if (v___x_406_ == 0)
{
if (lean_obj_tag(v_p_403_) == 0)
{
lean_object* v_k_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_k_407_ = lean_ctor_get(v_p_403_, 0);
v___x_408_ = lean_nat_abs(v_k_407_);
v___x_409_ = lean_nat_gcd(v_acc_404_, v___x_408_);
lean_dec(v___x_408_);
lean_dec(v_acc_404_);
return v___x_409_;
}
else
{
lean_object* v_k_410_; lean_object* v_p_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_k_410_ = lean_ctor_get(v_p_403_, 0);
v_p_411_ = lean_ctor_get(v_p_403_, 2);
v___x_412_ = lean_nat_abs(v_k_410_);
v___x_413_ = lean_nat_gcd(v_acc_404_, v___x_412_);
lean_dec(v___x_412_);
lean_dec(v_acc_404_);
v_p_403_ = v_p_411_;
v_acc_404_ = v___x_413_;
goto _start;
}
}
else
{
return v_acc_404_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go___boxed(lean_object* v_p_415_, lean_object* v_acc_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go(v_p_415_, v_acc_416_);
lean_dec_ref(v_p_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs(lean_object* v_x_418_){
_start:
{
if (lean_obj_tag(v_x_418_) == 0)
{
lean_object* v_k_419_; lean_object* v___x_420_; 
v_k_419_ = lean_ctor_get(v_x_418_, 0);
v___x_420_ = lean_nat_abs(v_k_419_);
return v___x_420_;
}
else
{
lean_object* v_k_421_; lean_object* v_p_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_k_421_ = lean_ctor_get(v_x_418_, 0);
v_p_422_ = lean_ctor_get(v_x_418_, 2);
v___x_423_ = lean_nat_abs(v_k_421_);
v___x_424_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go(v_p_422_, v___x_423_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs___boxed(lean_object* v_x_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs(v_x_425_);
lean_dec_ref(v_x_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divConst(lean_object* v_p_427_, lean_object* v_a_428_){
_start:
{
if (lean_obj_tag(v_p_427_) == 0)
{
lean_object* v_k_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_437_; 
v_k_429_ = lean_ctor_get(v_p_427_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v_p_427_);
if (v_isSharedCheck_437_ == 0)
{
v___x_431_ = v_p_427_;
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_k_429_);
lean_dec(v_p_427_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_433_ = lean_int_ediv(v_k_429_, v_a_428_);
lean_dec(v_k_429_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_433_);
v___x_435_ = v___x_431_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
else
{
lean_object* v_k_438_; lean_object* v_v_439_; lean_object* v_p_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_449_; 
v_k_438_ = lean_ctor_get(v_p_427_, 0);
v_v_439_ = lean_ctor_get(v_p_427_, 1);
v_p_440_ = lean_ctor_get(v_p_427_, 2);
v_isSharedCheck_449_ = !lean_is_exclusive(v_p_427_);
if (v_isSharedCheck_449_ == 0)
{
v___x_442_ = v_p_427_;
v_isShared_443_ = v_isSharedCheck_449_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_p_440_);
lean_inc(v_v_439_);
lean_inc(v_k_438_);
lean_dec(v_p_427_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_449_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_444_ = lean_int_ediv(v_k_438_, v_a_428_);
lean_dec(v_k_438_);
v___x_445_ = l_Lean_Grind_CommRing_Poly_divConst(v_p_440_, v_a_428_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 2, v___x_445_);
lean_ctor_set(v___x_442_, 0, v___x_444_);
v___x_447_ = v___x_442_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_v_439_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divConst___boxed(lean_object* v_p_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_Grind_CommRing_Poly_divConst(v_p_450_, v_a_451_);
lean_dec(v_a_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_size(lean_object* v_x_453_){
_start:
{
if (lean_obj_tag(v_x_453_) == 0)
{
lean_object* v___x_454_; 
v___x_454_ = lean_unsigned_to_nat(0u);
return v___x_454_;
}
else
{
lean_object* v_m_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_m_455_ = lean_ctor_get(v_x_453_, 1);
v___x_456_ = l_Lean_Grind_CommRing_Mon_size(v_m_455_);
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_add(v___x_456_, v___x_457_);
lean_dec(v___x_456_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_size___boxed(lean_object* v_x_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_Grind_CommRing_Mon_size(v_x_459_);
lean_dec(v_x_459_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_size(lean_object* v_x_461_){
_start:
{
if (lean_obj_tag(v_x_461_) == 0)
{
lean_object* v___x_462_; 
v___x_462_ = lean_unsigned_to_nat(1u);
return v___x_462_;
}
else
{
lean_object* v_v_463_; lean_object* v_p_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_v_463_ = lean_ctor_get(v_x_461_, 1);
v_p_464_ = lean_ctor_get(v_x_461_, 2);
v___x_465_ = l_Lean_Grind_CommRing_Mon_size(v_v_463_);
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = lean_nat_add(v___x_465_, v___x_466_);
lean_dec(v___x_465_);
v___x_468_ = l_Lean_Grind_CommRing_Poly_size(v_p_464_);
v___x_469_ = lean_nat_add(v___x_467_, v___x_468_);
lean_dec(v___x_468_);
lean_dec(v___x_467_);
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_size___boxed(lean_object* v_x_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_Grind_CommRing_Poly_size(v_x_470_);
lean_dec_ref(v_x_470_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_length(lean_object* v_x_472_){
_start:
{
if (lean_obj_tag(v_x_472_) == 0)
{
lean_object* v___x_473_; 
v___x_473_ = lean_unsigned_to_nat(0u);
return v___x_473_;
}
else
{
lean_object* v_p_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_p_474_ = lean_ctor_get(v_x_472_, 2);
v___x_475_ = lean_unsigned_to_nat(1u);
v___x_476_ = l_Lean_Grind_CommRing_Poly_length(v_p_474_);
v___x_477_ = lean_nat_add(v___x_475_, v___x_476_);
lean_dec(v___x_476_);
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_length___boxed(lean_object* v_x_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_Grind_CommRing_Poly_length(v_x_478_);
lean_dec_ref(v_x_478_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_toExpr(lean_object* v_pw_480_){
_start:
{
lean_object* v_x_481_; lean_object* v_k_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_493_; 
v_x_481_ = lean_ctor_get(v_pw_480_, 0);
v_k_482_ = lean_ctor_get(v_pw_480_, 1);
v_isSharedCheck_493_ = !lean_is_exclusive(v_pw_480_);
if (v_isSharedCheck_493_ == 0)
{
v___x_484_ = v_pw_480_;
v_isShared_485_ = v_isSharedCheck_493_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_k_482_);
lean_inc(v_x_481_);
lean_dec(v_pw_480_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_493_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_dec_eq(v_k_482_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_488_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_488_, 0, v_x_481_);
if (v_isShared_485_ == 0)
{
lean_ctor_set_tag(v___x_484_, 8);
lean_ctor_set(v___x_484_, 0, v___x_488_);
v___x_490_ = v___x_484_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_k_482_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
else
{
lean_object* v___x_492_; 
lean_del_object(v___x_484_);
lean_dec(v_k_482_);
v___x_492_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_492_, 0, v_x_481_);
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_toExpr_go(lean_object* v_m_494_, lean_object* v_acc_495_){
_start:
{
if (lean_obj_tag(v_m_494_) == 0)
{
return v_acc_495_;
}
else
{
lean_object* v_p_496_; lean_object* v_m_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_506_; 
v_p_496_ = lean_ctor_get(v_m_494_, 0);
v_m_497_ = lean_ctor_get(v_m_494_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v_m_494_);
if (v_isSharedCheck_506_ == 0)
{
v___x_499_ = v_m_494_;
v_isShared_500_ = v_isSharedCheck_506_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_m_497_);
lean_inc(v_p_496_);
lean_dec(v_m_494_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_506_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_501_ = l_Lean_Grind_CommRing_Power_toExpr(v_p_496_);
if (v_isShared_500_ == 0)
{
lean_ctor_set_tag(v___x_499_, 7);
lean_ctor_set(v___x_499_, 1, v___x_501_);
lean_ctor_set(v___x_499_, 0, v_acc_495_);
v___x_503_ = v___x_499_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_acc_495_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v___x_501_);
v___x_503_ = v_reuseFailAlloc_505_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
v_m_494_ = v_m_497_;
v_acc_495_ = v___x_503_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_to_int(v___x_507_);
return v___x_508_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__1(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_toExpr___closed__0, &l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_toExpr(lean_object* v_m_511_){
_start:
{
if (lean_obj_tag(v_m_511_) == 0)
{
lean_object* v___x_512_; 
v___x_512_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_toExpr___closed__1, &l_Lean_Grind_CommRing_Mon_toExpr___closed__1_once, _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__1);
return v___x_512_;
}
else
{
lean_object* v_p_513_; lean_object* v_m_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_p_513_ = lean_ctor_get(v_m_511_, 0);
lean_inc_ref(v_p_513_);
v_m_514_ = lean_ctor_get(v_m_511_, 1);
lean_inc(v_m_514_);
lean_dec_ref(v_m_511_);
v___x_515_ = l_Lean_Grind_CommRing_Power_toExpr(v_p_513_);
v___x_516_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Mon_toExpr_go(v_m_514_, v___x_515_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(lean_object* v_k_517_, lean_object* v_m_518_){
_start:
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_toExpr___closed__0, &l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0);
v___x_520_ = lean_int_dec_eq(v_k_517_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v_k_517_);
v___x_522_ = l_Lean_Grind_CommRing_Mon_toExpr(v_m_518_);
v___x_523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
return v___x_523_;
}
else
{
lean_object* v___x_524_; 
lean_dec(v_k_517_);
v___x_524_ = l_Lean_Grind_CommRing_Mon_toExpr(v_m_518_);
return v___x_524_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_toExpr_go(lean_object* v_p_525_, lean_object* v_acc_526_){
_start:
{
if (lean_obj_tag(v_p_525_) == 0)
{
lean_object* v_k_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_537_; 
v_k_527_ = lean_ctor_get(v_p_525_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v_p_525_);
if (v_isSharedCheck_537_ == 0)
{
v___x_529_ = v_p_525_;
v_isShared_530_ = v_isSharedCheck_537_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_k_527_);
lean_dec(v_p_525_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_537_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_532_ = lean_int_dec_eq(v_k_527_, v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_534_; 
if (v_isShared_530_ == 0)
{
v___x_534_ = v___x_529_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_k_527_);
v___x_534_ = v_reuseFailAlloc_536_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_535_; 
v___x_535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_535_, 0, v_acc_526_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
return v___x_535_;
}
}
else
{
lean_del_object(v___x_529_);
lean_dec(v_k_527_);
return v_acc_526_;
}
}
}
else
{
lean_object* v_k_538_; lean_object* v_v_539_; lean_object* v_p_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_k_538_ = lean_ctor_get(v_p_525_, 0);
lean_inc(v_k_538_);
v_v_539_ = lean_ctor_get(v_p_525_, 1);
lean_inc(v_v_539_);
v_p_540_ = lean_ctor_get(v_p_525_, 2);
lean_inc_ref(v_p_540_);
lean_dec_ref(v_p_525_);
v___x_541_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(v_k_538_, v_v_539_);
v___x_542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_542_, 0, v_acc_526_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v_p_525_ = v_p_540_;
v_acc_526_ = v___x_542_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toExpr(lean_object* v_p_544_){
_start:
{
if (lean_obj_tag(v_p_544_) == 0)
{
lean_object* v_k_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
v_k_545_ = lean_ctor_get(v_p_544_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v_p_544_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v_p_544_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_k_545_);
lean_dec(v_p_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_k_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
else
{
lean_object* v_k_553_; lean_object* v_v_554_; lean_object* v_p_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_k_553_ = lean_ctor_get(v_p_544_, 0);
lean_inc(v_k_553_);
v_v_554_ = lean_ctor_get(v_p_544_, 1);
lean_inc(v_v_554_);
v_p_555_ = lean_ctor_get(v_p_544_, 2);
lean_inc_ref(v_p_555_);
lean_dec_ref(v_p_544_);
v___x_556_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(v_k_553_, v_v_554_);
v___x_557_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_toExpr_go(v_p_555_, v___x_556_);
return v___x_557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_maxDegreeOf_go(lean_object* v_x_558_, lean_object* v_p_559_, lean_object* v_max_560_){
_start:
{
if (lean_obj_tag(v_p_559_) == 0)
{
return v_max_560_;
}
else
{
lean_object* v_v_561_; lean_object* v_p_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_v_561_ = lean_ctor_get(v_p_559_, 1);
v_p_562_ = lean_ctor_get(v_p_559_, 2);
v___x_563_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_v_561_, v_x_558_);
v___x_564_ = lean_nat_dec_le(v_max_560_, v___x_563_);
if (v___x_564_ == 0)
{
lean_dec(v___x_563_);
v_p_559_ = v_p_562_;
goto _start;
}
else
{
lean_dec(v_max_560_);
v_p_559_ = v_p_562_;
v_max_560_ = v___x_563_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_maxDegreeOf_go___boxed(lean_object* v_x_567_, lean_object* v_p_568_, lean_object* v_max_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_maxDegreeOf_go(v_x_567_, v_p_568_, v_max_569_);
lean_dec_ref(v_p_568_);
lean_dec(v_x_567_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf(lean_object* v_p_571_, lean_object* v_x_572_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly_0__Lean_Grind_CommRing_Poly_maxDegreeOf_go(v_x_572_, v_p_571_, v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf___boxed(lean_object* v_p_575_, lean_object* v_x_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf(v_p_575_, v_x_576_);
lean_dec(v_x_576_);
lean_dec_ref(v_p_575_);
return v_res_577_;
}
}
lean_object* runtime_initialize_Init_Grind_Ring_CommSolver(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Gcd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Ring_CommSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ring_CommSolver(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Gcd(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly(uint8_t builtin) {
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
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly(builtin);
}
#ifdef __cplusplus
}
#endif
