// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Poly
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_simp_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_simp_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simp_x3f(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_toExpr_go(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Mon_toExpr___closed__0;
static lean_once_cell_t l_Lean_Grind_CommRing_Mon_toExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Mon_toExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_maxDegreeOf_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_maxDegreeOf_go___boxed(lean_object*, lean_object*, lean_object*);
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
uint8_t v_x_36__boxed_58_; lean_object* v_res_59_; 
v_x_36__boxed_58_ = lean_unbox(v_x_54_);
v_res_59_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg(v_x_36__boxed_58_, v_h__1_55_, v_h__2_56_, v_h__3_57_);
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
uint8_t v_x_51__boxed_76_; lean_object* v_res_77_; 
v_x_51__boxed_76_ = lean_unbox(v_x_72_);
v_res_77_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter(v_motive_71_, v_x_51__boxed_76_, v_h__1_73_, v_h__2_74_, v_h__3_75_);
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
lean_dec_ref(v_x_78_);
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
lean_dec_ref(v_x_139_);
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
lean_dec_ref(v_x_139_);
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
lean_dec_ref(v_char_x3f_195_);
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
lean_dec_ref(v_char_x3f_206_);
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
lean_dec_ref(v_char_x3f_217_);
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
lean_dec_ref(v_p_u2081_231_);
v_k_239_ = lean_ctor_get(v_p_u2082_232_, 0);
lean_inc(v_k_239_);
v_v_240_ = lean_ctor_get(v_p_u2082_232_, 1);
lean_inc_n(v_v_240_, 2);
v_p_241_ = lean_ctor_get(v_p_u2082_232_, 2);
lean_inc_ref(v_p_241_);
lean_dec_ref(v_p_u2082_232_);
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
lean_dec_ref(v_p_u2081_231_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_simp_x3f_go_x3f(lean_object* v_char_x3f_256_, lean_object* v_k_u2082_x27_257_, lean_object* v_m_u2082_258_, lean_object* v_p_u2082_259_, lean_object* v_p_u2081_260_){
_start:
{
if (lean_obj_tag(v_p_u2081_260_) == 0)
{
lean_object* v___x_261_; 
lean_dec_ref(v_p_u2081_260_);
lean_dec_ref(v_p_u2082_259_);
lean_dec(v_m_u2082_258_);
lean_dec(v_char_x3f_256_);
v___x_261_ = lean_box(0);
return v___x_261_;
}
else
{
lean_object* v_k_262_; lean_object* v_v_263_; lean_object* v_p_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_335_; 
v_k_262_ = lean_ctor_get(v_p_u2081_260_, 0);
v_v_263_ = lean_ctor_get(v_p_u2081_260_, 1);
v_p_264_ = lean_ctor_get(v_p_u2081_260_, 2);
v_isSharedCheck_335_ = !lean_is_exclusive(v_p_u2081_260_);
if (v_isSharedCheck_335_ == 0)
{
v___x_266_ = v_p_u2081_260_;
v_isShared_267_ = v_isSharedCheck_335_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_p_264_);
lean_inc(v_v_263_);
lean_inc(v_k_262_);
lean_dec(v_p_u2081_260_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_335_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
uint8_t v___x_268_; 
v___x_268_ = l_Lean_Grind_CommRing_Mon_divides(v_m_u2082_258_, v_v_263_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
lean_inc(v_char_x3f_256_);
v___x_269_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_simp_x3f_go_x3f(v_char_x3f_256_, v_k_u2082_x27_257_, v_m_u2082_258_, v_p_u2082_259_, v_p_264_);
if (lean_obj_tag(v___x_269_) == 1)
{
if (lean_obj_tag(v_char_x3f_256_) == 1)
{
lean_object* v_val_270_; lean_object* v_val_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_297_; 
v_val_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_val_270_);
v_val_271_ = lean_ctor_get(v_char_x3f_256_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v_char_x3f_256_);
if (v_isSharedCheck_297_ == 0)
{
v___x_273_ = v_char_x3f_256_;
v_isShared_274_ = v_isSharedCheck_297_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_val_271_);
lean_dec(v_char_x3f_256_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_297_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v_p_275_; lean_object* v_k_u2081_276_; lean_object* v_k_u2082_277_; lean_object* v_m_u2082_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_296_; 
v_p_275_ = lean_ctor_get(v_val_270_, 0);
v_k_u2081_276_ = lean_ctor_get(v_val_270_, 1);
v_k_u2082_277_ = lean_ctor_get(v_val_270_, 2);
v_m_u2082_278_ = lean_ctor_get(v_val_270_, 3);
v_isSharedCheck_296_ = !lean_is_exclusive(v_val_270_);
if (v_isSharedCheck_296_ == 0)
{
v___x_280_ = v_val_270_;
v_isShared_281_ = v_isSharedCheck_296_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_m_u2082_278_);
lean_inc(v_k_u2082_277_);
lean_inc(v_k_u2081_276_);
lean_inc(v_p_275_);
lean_dec(v_val_270_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_296_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v_k_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_282_ = lean_int_mul(v_k_262_, v_k_u2081_276_);
lean_dec(v_k_262_);
v___x_283_ = lean_nat_to_int(v_val_271_);
v_k_284_ = lean_int_emod(v___x_282_, v___x_283_);
lean_dec(v___x_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_286_ = lean_int_dec_eq(v_k_284_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_288_; 
lean_dec_ref(v___x_269_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 2, v_p_275_);
lean_ctor_set(v___x_266_, 0, v_k_284_);
v___x_288_ = v___x_266_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_k_284_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_v_263_);
lean_ctor_set(v_reuseFailAlloc_295_, 2, v_p_275_);
v___x_288_ = v_reuseFailAlloc_295_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_290_; 
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_288_);
v___x_290_ = v___x_280_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_k_u2081_276_);
lean_ctor_set(v_reuseFailAlloc_294_, 2, v_k_u2082_277_);
lean_ctor_set(v_reuseFailAlloc_294_, 3, v_m_u2082_278_);
v___x_290_ = v_reuseFailAlloc_294_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_292_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_290_);
v___x_292_ = v___x_273_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
else
{
lean_dec(v_k_284_);
lean_del_object(v___x_280_);
lean_dec(v_m_u2082_278_);
lean_dec(v_k_u2082_277_);
lean_dec(v_k_u2081_276_);
lean_dec_ref(v_p_275_);
lean_del_object(v___x_273_);
lean_del_object(v___x_266_);
lean_dec(v_v_263_);
return v___x_269_;
}
}
}
}
else
{
lean_object* v_val_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_320_; 
lean_dec(v_char_x3f_256_);
v_val_298_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_320_ == 0)
{
v___x_300_ = v___x_269_;
v_isShared_301_ = v_isSharedCheck_320_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_val_298_);
lean_dec(v___x_269_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_320_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v_p_302_; lean_object* v_k_u2081_303_; lean_object* v_k_u2082_304_; lean_object* v_m_u2082_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_319_; 
v_p_302_ = lean_ctor_get(v_val_298_, 0);
v_k_u2081_303_ = lean_ctor_get(v_val_298_, 1);
v_k_u2082_304_ = lean_ctor_get(v_val_298_, 2);
v_m_u2082_305_ = lean_ctor_get(v_val_298_, 3);
v_isSharedCheck_319_ = !lean_is_exclusive(v_val_298_);
if (v_isSharedCheck_319_ == 0)
{
v___x_307_ = v_val_298_;
v_isShared_308_ = v_isSharedCheck_319_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_m_u2082_305_);
lean_inc(v_k_u2082_304_);
lean_inc(v_k_u2081_303_);
lean_inc(v_p_302_);
lean_dec(v_val_298_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_319_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_309_ = lean_int_mul(v_k_262_, v_k_u2081_303_);
lean_dec(v_k_262_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 2, v_p_302_);
lean_ctor_set(v___x_266_, 0, v___x_309_);
v___x_311_ = v___x_266_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_v_263_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_p_302_);
v___x_311_ = v_reuseFailAlloc_318_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_313_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_311_);
v___x_313_ = v___x_307_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_k_u2081_303_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v_k_u2082_304_);
lean_ctor_set(v_reuseFailAlloc_317_, 3, v_m_u2082_305_);
v___x_313_ = v_reuseFailAlloc_317_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_315_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_313_);
v___x_315_ = v___x_300_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_321_; 
lean_dec(v___x_269_);
lean_del_object(v___x_266_);
lean_dec(v_v_263_);
lean_dec(v_k_262_);
lean_dec(v_char_x3f_256_);
v___x_321_ = lean_box(0);
return v___x_321_;
}
}
else
{
lean_object* v_m_u2082_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v_g_325_; lean_object* v___x_326_; lean_object* v_k_u2081_327_; lean_object* v___x_328_; lean_object* v_k_u2082_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v_p_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
lean_del_object(v___x_266_);
v_m_u2082_322_ = l_Lean_Grind_CommRing_Mon_div(v_v_263_, v_m_u2082_258_);
v___x_323_ = lean_nat_abs(v_k_262_);
v___x_324_ = lean_nat_abs(v_k_u2082_x27_257_);
v_g_325_ = lean_nat_gcd(v___x_323_, v___x_324_);
lean_dec(v___x_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_nat_to_int(v_g_325_);
v_k_u2081_327_ = lean_int_ediv(v_k_u2082_x27_257_, v___x_326_);
v___x_328_ = lean_int_neg(v_k_262_);
lean_dec(v_k_262_);
v_k_u2082_329_ = lean_int_ediv(v___x_328_, v___x_326_);
lean_dec(v___x_326_);
lean_dec(v___x_328_);
lean_inc_n(v_char_x3f_256_, 2);
lean_inc(v_m_u2082_322_);
v___x_330_ = l_Lean_Grind_CommRing_Poly_mulMon_x27(v_p_u2082_259_, v_k_u2082_329_, v_m_u2082_322_, v_char_x3f_256_);
v___x_331_ = l_Lean_Grind_CommRing_Poly_mulConst_x27(v_p_264_, v_k_u2081_327_, v_char_x3f_256_);
v_p_332_ = l_Lean_Grind_CommRing_Poly_combine_x27(v___x_330_, v___x_331_, v_char_x3f_256_);
v___x_333_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_333_, 0, v_p_332_);
lean_ctor_set(v___x_333_, 1, v_k_u2081_327_);
lean_ctor_set(v___x_333_, 2, v_k_u2082_329_);
lean_ctor_set(v___x_333_, 3, v_m_u2082_322_);
v___x_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_simp_x3f_go_x3f___boxed(lean_object* v_char_x3f_336_, lean_object* v_k_u2082_x27_337_, lean_object* v_m_u2082_338_, lean_object* v_p_u2082_339_, lean_object* v_p_u2081_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_simp_x3f_go_x3f(v_char_x3f_336_, v_k_u2082_x27_337_, v_m_u2082_338_, v_p_u2082_339_, v_p_u2081_340_);
lean_dec(v_k_u2082_x27_337_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_simp_x3f(lean_object* v_p_u2081_342_, lean_object* v_p_u2082_343_, lean_object* v_char_x3f_344_){
_start:
{
if (lean_obj_tag(v_p_u2082_343_) == 1)
{
lean_object* v_k_345_; lean_object* v_v_346_; lean_object* v_p_347_; lean_object* v___x_348_; 
v_k_345_ = lean_ctor_get(v_p_u2082_343_, 0);
lean_inc(v_k_345_);
v_v_346_ = lean_ctor_get(v_p_u2082_343_, 1);
lean_inc(v_v_346_);
v_p_347_ = lean_ctor_get(v_p_u2082_343_, 2);
lean_inc_ref(v_p_347_);
lean_dec_ref(v_p_u2082_343_);
v___x_348_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_simp_x3f_go_x3f(v_char_x3f_344_, v_k_345_, v_v_346_, v_p_347_, v_p_u2081_342_);
lean_dec(v_k_345_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; 
lean_dec(v_char_x3f_344_);
lean_dec_ref(v_p_u2082_343_);
lean_dec_ref(v_p_u2081_342_);
v___x_349_ = lean_box(0);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_degree(lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
lean_object* v___x_351_; 
v___x_351_ = lean_unsigned_to_nat(0u);
return v___x_351_;
}
else
{
lean_object* v_v_352_; lean_object* v___x_353_; 
v_v_352_ = lean_ctor_get(v_x_350_, 1);
v___x_353_ = l_Lean_Grind_CommRing_Mon_degree(v_v_352_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_degree___boxed(lean_object* v_x_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Grind_CommRing_Poly_degree(v_x_354_);
lean_dec_ref(v_x_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go(lean_object* v_p_356_, lean_object* v_acc_357_){
_start:
{
if (lean_obj_tag(v_p_356_) == 0)
{
return v_acc_357_;
}
else
{
lean_object* v_p_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_p_358_ = lean_ctor_get(v_p_356_, 2);
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = lean_nat_add(v_acc_357_, v___x_359_);
lean_dec(v_acc_357_);
v_p_356_ = v_p_358_;
v_acc_357_ = v___x_360_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go___boxed(lean_object* v_p_362_, lean_object* v_acc_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go(v_p_362_, v_acc_363_);
lean_dec_ref(v_p_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_numTerms(lean_object* v_p_365_){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go(v_p_365_, v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_numTerms___boxed(lean_object* v_p_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Grind_CommRing_Poly_numTerms(v_p_368_);
lean_dec_ref(v_p_368_);
return v_res_369_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_divides(lean_object* v_p_370_, lean_object* v_m_371_){
_start:
{
if (lean_obj_tag(v_p_370_) == 0)
{
uint8_t v___x_372_; 
v___x_372_ = 1;
return v___x_372_;
}
else
{
lean_object* v_v_373_; uint8_t v___x_374_; 
v_v_373_ = lean_ctor_get(v_p_370_, 1);
v___x_374_ = l_Lean_Grind_CommRing_Mon_divides(v_v_373_, v_m_371_);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divides___boxed(lean_object* v_p_375_, lean_object* v_m_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l_Lean_Grind_CommRing_Poly_divides(v_p_375_, v_m_376_);
lean_dec(v_m_376_);
lean_dec_ref(v_p_375_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lc(lean_object* v_x_379_){
_start:
{
lean_object* v_k_380_; 
v_k_380_ = lean_ctor_get(v_x_379_, 0);
lean_inc(v_k_380_);
return v_k_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lc___boxed(lean_object* v_x_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Grind_CommRing_Poly_lc(v_x_381_);
lean_dec_ref(v_x_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lm(lean_object* v_x_383_){
_start:
{
if (lean_obj_tag(v_x_383_) == 0)
{
lean_object* v___x_384_; 
v___x_384_ = lean_box(0);
return v___x_384_;
}
else
{
lean_object* v_v_385_; 
v_v_385_ = lean_ctor_get(v_x_383_, 1);
lean_inc(v_v_385_);
return v_v_385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lm___boxed(lean_object* v_x_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Grind_CommRing_Poly_lm(v_x_386_);
lean_dec_ref(v_x_386_);
return v_res_387_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_isZero(lean_object* v_x_388_){
_start:
{
if (lean_obj_tag(v_x_388_) == 0)
{
lean_object* v_k_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v_k_389_ = lean_ctor_get(v_x_388_, 0);
v___x_390_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_391_ = lean_int_dec_eq(v_k_389_, v___x_390_);
return v___x_391_;
}
else
{
uint8_t v___x_392_; 
v___x_392_ = 0;
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_isZero___boxed(lean_object* v_x_393_){
_start:
{
uint8_t v_res_394_; lean_object* v_r_395_; 
v_res_394_ = l_Lean_Grind_CommRing_Poly_isZero(v_x_393_);
lean_dec_ref(v_x_393_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_getConst(lean_object* v_x_396_){
_start:
{
if (lean_obj_tag(v_x_396_) == 0)
{
lean_object* v_k_397_; 
v_k_397_ = lean_ctor_get(v_x_396_, 0);
lean_inc(v_k_397_);
return v_k_397_;
}
else
{
lean_object* v_p_398_; 
v_p_398_ = lean_ctor_get(v_x_396_, 2);
v_x_396_ = v_p_398_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_getConst___boxed(lean_object* v_x_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Grind_CommRing_Poly_getConst(v_x_400_);
lean_dec_ref(v_x_400_);
return v_res_401_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_checkCoeffs(lean_object* v_x_402_){
_start:
{
if (lean_obj_tag(v_x_402_) == 0)
{
uint8_t v___x_403_; 
v___x_403_ = 1;
return v___x_403_;
}
else
{
lean_object* v_k_404_; lean_object* v_p_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v_k_404_ = lean_ctor_get(v_x_402_, 0);
v_p_405_ = lean_ctor_get(v_x_402_, 2);
v___x_406_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_407_ = lean_int_dec_eq(v_k_404_, v___x_406_);
if (v___x_407_ == 0)
{
v_x_402_ = v_p_405_;
goto _start;
}
else
{
uint8_t v___x_409_; 
v___x_409_ = 0;
return v___x_409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_checkCoeffs___boxed(lean_object* v_x_410_){
_start:
{
uint8_t v_res_411_; lean_object* v_r_412_; 
v_res_411_ = l_Lean_Grind_CommRing_Poly_checkCoeffs(v_x_410_);
lean_dec_ref(v_x_410_);
v_r_412_ = lean_box(v_res_411_);
return v_r_412_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_Poly_checkNoUnitMon(lean_object* v_x_413_){
_start:
{
if (lean_obj_tag(v_x_413_) == 0)
{
uint8_t v___x_414_; 
v___x_414_ = 1;
return v___x_414_;
}
else
{
lean_object* v_v_415_; 
v_v_415_ = lean_ctor_get(v_x_413_, 1);
if (lean_obj_tag(v_v_415_) == 0)
{
uint8_t v___x_416_; 
v___x_416_ = 0;
return v___x_416_;
}
else
{
lean_object* v_p_417_; 
v_p_417_ = lean_ctor_get(v_x_413_, 2);
v_x_413_ = v_p_417_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_checkNoUnitMon___boxed(lean_object* v_x_419_){
_start:
{
uint8_t v_res_420_; lean_object* v_r_421_; 
v_res_420_ = l_Lean_Grind_CommRing_Poly_checkNoUnitMon(v_x_419_);
lean_dec_ref(v_x_419_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go(lean_object* v_p_422_, lean_object* v_acc_423_){
_start:
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = lean_unsigned_to_nat(1u);
v___x_425_ = lean_nat_dec_eq(v_acc_423_, v___x_424_);
if (v___x_425_ == 0)
{
if (lean_obj_tag(v_p_422_) == 0)
{
lean_object* v_k_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v_k_426_ = lean_ctor_get(v_p_422_, 0);
v___x_427_ = lean_nat_abs(v_k_426_);
v___x_428_ = lean_nat_gcd(v_acc_423_, v___x_427_);
lean_dec(v___x_427_);
lean_dec(v_acc_423_);
return v___x_428_;
}
else
{
lean_object* v_k_429_; lean_object* v_p_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_k_429_ = lean_ctor_get(v_p_422_, 0);
v_p_430_ = lean_ctor_get(v_p_422_, 2);
v___x_431_ = lean_nat_abs(v_k_429_);
v___x_432_ = lean_nat_gcd(v_acc_423_, v___x_431_);
lean_dec(v___x_431_);
lean_dec(v_acc_423_);
v_p_422_ = v_p_430_;
v_acc_423_ = v___x_432_;
goto _start;
}
}
else
{
return v_acc_423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go___boxed(lean_object* v_p_434_, lean_object* v_acc_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go(v_p_434_, v_acc_435_);
lean_dec_ref(v_p_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs(lean_object* v_x_437_){
_start:
{
if (lean_obj_tag(v_x_437_) == 0)
{
lean_object* v_k_438_; lean_object* v___x_439_; 
v_k_438_ = lean_ctor_get(v_x_437_, 0);
v___x_439_ = lean_nat_abs(v_k_438_);
return v___x_439_;
}
else
{
lean_object* v_k_440_; lean_object* v_p_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_k_440_ = lean_ctor_get(v_x_437_, 0);
v_p_441_ = lean_ctor_get(v_x_437_, 2);
v___x_442_ = lean_nat_abs(v_k_440_);
v___x_443_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go(v_p_441_, v___x_442_);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs___boxed(lean_object* v_x_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs(v_x_444_);
lean_dec_ref(v_x_444_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divConst(lean_object* v_p_446_, lean_object* v_a_447_){
_start:
{
if (lean_obj_tag(v_p_446_) == 0)
{
lean_object* v_k_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_456_; 
v_k_448_ = lean_ctor_get(v_p_446_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v_p_446_);
if (v_isSharedCheck_456_ == 0)
{
v___x_450_ = v_p_446_;
v_isShared_451_ = v_isSharedCheck_456_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_k_448_);
lean_dec(v_p_446_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_456_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_452_ = lean_int_ediv(v_k_448_, v_a_447_);
lean_dec(v_k_448_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_452_);
v___x_454_ = v___x_450_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
else
{
lean_object* v_k_457_; lean_object* v_v_458_; lean_object* v_p_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_468_; 
v_k_457_ = lean_ctor_get(v_p_446_, 0);
v_v_458_ = lean_ctor_get(v_p_446_, 1);
v_p_459_ = lean_ctor_get(v_p_446_, 2);
v_isSharedCheck_468_ = !lean_is_exclusive(v_p_446_);
if (v_isSharedCheck_468_ == 0)
{
v___x_461_ = v_p_446_;
v_isShared_462_ = v_isSharedCheck_468_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_p_459_);
lean_inc(v_v_458_);
lean_inc(v_k_457_);
lean_dec(v_p_446_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_468_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_463_ = lean_int_ediv(v_k_457_, v_a_447_);
lean_dec(v_k_457_);
v___x_464_ = l_Lean_Grind_CommRing_Poly_divConst(v_p_459_, v_a_447_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 2, v___x_464_);
lean_ctor_set(v___x_461_, 0, v___x_463_);
v___x_466_ = v___x_461_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_v_458_);
lean_ctor_set(v_reuseFailAlloc_467_, 2, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divConst___boxed(lean_object* v_p_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_Grind_CommRing_Poly_divConst(v_p_469_, v_a_470_);
lean_dec(v_a_470_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_size(lean_object* v_x_472_){
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
lean_object* v_m_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_m_474_ = lean_ctor_get(v_x_472_, 1);
v___x_475_ = l_Lean_Grind_CommRing_Mon_size(v_m_474_);
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_add(v___x_475_, v___x_476_);
lean_dec(v___x_475_);
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_size___boxed(lean_object* v_x_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_Grind_CommRing_Mon_size(v_x_478_);
lean_dec(v_x_478_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_size(lean_object* v_x_480_){
_start:
{
if (lean_obj_tag(v_x_480_) == 0)
{
lean_object* v___x_481_; 
v___x_481_ = lean_unsigned_to_nat(1u);
return v___x_481_;
}
else
{
lean_object* v_v_482_; lean_object* v_p_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_v_482_ = lean_ctor_get(v_x_480_, 1);
v_p_483_ = lean_ctor_get(v_x_480_, 2);
v___x_484_ = l_Lean_Grind_CommRing_Mon_size(v_v_482_);
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = lean_nat_add(v___x_484_, v___x_485_);
lean_dec(v___x_484_);
v___x_487_ = l_Lean_Grind_CommRing_Poly_size(v_p_483_);
v___x_488_ = lean_nat_add(v___x_486_, v___x_487_);
lean_dec(v___x_487_);
lean_dec(v___x_486_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_size___boxed(lean_object* v_x_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Grind_CommRing_Poly_size(v_x_489_);
lean_dec_ref(v_x_489_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_length(lean_object* v_x_491_){
_start:
{
if (lean_obj_tag(v_x_491_) == 0)
{
lean_object* v___x_492_; 
v___x_492_ = lean_unsigned_to_nat(0u);
return v___x_492_;
}
else
{
lean_object* v_p_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_p_493_ = lean_ctor_get(v_x_491_, 2);
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = l_Lean_Grind_CommRing_Poly_length(v_p_493_);
v___x_496_ = lean_nat_add(v___x_494_, v___x_495_);
lean_dec(v___x_495_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_length___boxed(lean_object* v_x_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Grind_CommRing_Poly_length(v_x_497_);
lean_dec_ref(v_x_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_toExpr(lean_object* v_pw_499_){
_start:
{
lean_object* v_x_500_; lean_object* v_k_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_512_; 
v_x_500_ = lean_ctor_get(v_pw_499_, 0);
v_k_501_ = lean_ctor_get(v_pw_499_, 1);
v_isSharedCheck_512_ = !lean_is_exclusive(v_pw_499_);
if (v_isSharedCheck_512_ == 0)
{
v___x_503_ = v_pw_499_;
v_isShared_504_ = v_isSharedCheck_512_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_k_501_);
lean_inc(v_x_500_);
lean_dec(v_pw_499_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_512_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_unsigned_to_nat(1u);
v___x_506_ = lean_nat_dec_eq(v_k_501_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_507_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_507_, 0, v_x_500_);
if (v_isShared_504_ == 0)
{
lean_ctor_set_tag(v___x_503_, 8);
lean_ctor_set(v___x_503_, 0, v___x_507_);
v___x_509_ = v___x_503_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_k_501_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
else
{
lean_object* v___x_511_; 
lean_del_object(v___x_503_);
lean_dec(v_k_501_);
v___x_511_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_511_, 0, v_x_500_);
return v___x_511_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_toExpr_go(lean_object* v_m_513_, lean_object* v_acc_514_){
_start:
{
if (lean_obj_tag(v_m_513_) == 0)
{
return v_acc_514_;
}
else
{
lean_object* v_p_515_; lean_object* v_m_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_525_; 
v_p_515_ = lean_ctor_get(v_m_513_, 0);
v_m_516_ = lean_ctor_get(v_m_513_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v_m_513_);
if (v_isSharedCheck_525_ == 0)
{
v___x_518_ = v_m_513_;
v_isShared_519_ = v_isSharedCheck_525_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_m_516_);
lean_inc(v_p_515_);
lean_dec(v_m_513_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_525_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_520_ = l_Lean_Grind_CommRing_Power_toExpr(v_p_515_);
if (v_isShared_519_ == 0)
{
lean_ctor_set_tag(v___x_518_, 7);
lean_ctor_set(v___x_518_, 1, v___x_520_);
lean_ctor_set(v___x_518_, 0, v_acc_514_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_acc_514_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_520_);
v___x_522_ = v_reuseFailAlloc_524_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
v_m_513_ = v_m_516_;
v_acc_514_ = v___x_522_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_unsigned_to_nat(1u);
v___x_527_ = lean_nat_to_int(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__1(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_toExpr___closed__0, &l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_toExpr(lean_object* v_m_530_){
_start:
{
if (lean_obj_tag(v_m_530_) == 0)
{
lean_object* v___x_531_; 
v___x_531_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_toExpr___closed__1, &l_Lean_Grind_CommRing_Mon_toExpr___closed__1_once, _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__1);
return v___x_531_;
}
else
{
lean_object* v_p_532_; lean_object* v_m_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_p_532_ = lean_ctor_get(v_m_530_, 0);
lean_inc_ref(v_p_532_);
v_m_533_ = lean_ctor_get(v_m_530_, 1);
lean_inc(v_m_533_);
lean_dec_ref(v_m_530_);
v___x_534_ = l_Lean_Grind_CommRing_Power_toExpr(v_p_532_);
v___x_535_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_toExpr_go(v_m_533_, v___x_534_);
return v___x_535_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(lean_object* v_k_536_, lean_object* v_m_537_){
_start:
{
lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_538_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_toExpr___closed__0, &l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0);
v___x_539_ = lean_int_dec_eq(v_k_536_, v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v_k_536_);
v___x_541_ = l_Lean_Grind_CommRing_Mon_toExpr(v_m_537_);
v___x_542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
return v___x_542_;
}
else
{
lean_object* v___x_543_; 
lean_dec(v_k_536_);
v___x_543_ = l_Lean_Grind_CommRing_Mon_toExpr(v_m_537_);
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_go(lean_object* v_p_544_, lean_object* v_acc_545_){
_start:
{
if (lean_obj_tag(v_p_544_) == 0)
{
lean_object* v_k_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_556_; 
v_k_546_ = lean_ctor_get(v_p_544_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v_p_544_);
if (v_isSharedCheck_556_ == 0)
{
v___x_548_ = v_p_544_;
v_isShared_549_ = v_isSharedCheck_556_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_k_546_);
lean_dec(v_p_544_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_556_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_550_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_551_ = lean_int_dec_eq(v_k_546_, v___x_550_);
if (v___x_551_ == 0)
{
lean_object* v___x_553_; 
if (v_isShared_549_ == 0)
{
v___x_553_ = v___x_548_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_k_546_);
v___x_553_ = v_reuseFailAlloc_555_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_554_; 
v___x_554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_554_, 0, v_acc_545_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
return v___x_554_;
}
}
else
{
lean_del_object(v___x_548_);
lean_dec(v_k_546_);
return v_acc_545_;
}
}
}
else
{
lean_object* v_k_557_; lean_object* v_v_558_; lean_object* v_p_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_k_557_ = lean_ctor_get(v_p_544_, 0);
lean_inc(v_k_557_);
v_v_558_ = lean_ctor_get(v_p_544_, 1);
lean_inc(v_v_558_);
v_p_559_ = lean_ctor_get(v_p_544_, 2);
lean_inc_ref(v_p_559_);
lean_dec_ref(v_p_544_);
v___x_560_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(v_k_557_, v_v_558_);
v___x_561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_561_, 0, v_acc_545_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v_p_544_ = v_p_559_;
v_acc_545_ = v___x_561_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toExpr(lean_object* v_p_563_){
_start:
{
if (lean_obj_tag(v_p_563_) == 0)
{
lean_object* v_k_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
v_k_564_ = lean_ctor_get(v_p_563_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v_p_563_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v_p_563_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_k_564_);
lean_dec(v_p_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_k_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
else
{
lean_object* v_k_572_; lean_object* v_v_573_; lean_object* v_p_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_k_572_ = lean_ctor_get(v_p_563_, 0);
lean_inc(v_k_572_);
v_v_573_ = lean_ctor_get(v_p_563_, 1);
lean_inc(v_v_573_);
v_p_574_ = lean_ctor_get(v_p_563_, 2);
lean_inc_ref(v_p_574_);
lean_dec_ref(v_p_563_);
v___x_575_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(v_k_572_, v_v_573_);
v___x_576_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_go(v_p_574_, v___x_575_);
return v___x_576_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_maxDegreeOf_go(lean_object* v_x_577_, lean_object* v_p_578_, lean_object* v_max_579_){
_start:
{
if (lean_obj_tag(v_p_578_) == 0)
{
return v_max_579_;
}
else
{
lean_object* v_v_580_; lean_object* v_p_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v_v_580_ = lean_ctor_get(v_p_578_, 1);
v_p_581_ = lean_ctor_get(v_p_578_, 2);
v___x_582_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_v_580_, v_x_577_);
v___x_583_ = lean_nat_dec_le(v_max_579_, v___x_582_);
if (v___x_583_ == 0)
{
lean_dec(v___x_582_);
v_p_578_ = v_p_581_;
goto _start;
}
else
{
lean_dec(v_max_579_);
v_p_578_ = v_p_581_;
v_max_579_ = v___x_582_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_maxDegreeOf_go___boxed(lean_object* v_x_586_, lean_object* v_p_587_, lean_object* v_max_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_maxDegreeOf_go(v_x_586_, v_p_587_, v_max_588_);
lean_dec_ref(v_p_587_);
lean_dec(v_x_586_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf(lean_object* v_p_590_, lean_object* v_x_591_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_maxDegreeOf_go(v_x_591_, v_p_590_, v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf___boxed(lean_object* v_p_594_, lean_object* v_x_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf(v_p_594_, v_x_595_);
lean_dec(v_x_595_);
lean_dec_ref(v_p_594_);
return v_res_596_;
}
}
lean_object* runtime_initialize_Init_Grind_Ring_CommSolver(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Gcd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin) {
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
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin) {
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
res = initialize_Init_Data_Nat_Linear(builtin);
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
