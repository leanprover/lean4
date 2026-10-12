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
uint8_t l_Lean_Grind_CommRing_Mon_sharesVar(lean_object* v_x_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_Lean_Grind_CommRing_Mon_sharesVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_15_;
v_res_15_ = l_Lean_Grind_CommRing_Mon_sharesVar(v_x_1_, v_x_2_);
stack->m_num = v_res_15_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_sharesVar___boxed(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l_Lean_Grind_CommRing_Mon_sharesVar(v_x_16_, v_x_17_);
lean_dec(v_x_17_);
lean_dec(v_x_16_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__3_splitter___redArg(lean_object* v_x_20_, lean_object* v_x_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_, lean_object* v_h__3_24_){
_start:
{
if (lean_obj_tag(v_x_20_) == 0)
{
lean_object* v___x_25_; 
lean_dec(v_h__3_24_);
lean_dec(v_h__2_23_);
v___x_25_ = lean_apply_1(v_h__1_22_, v_x_21_);
return v___x_25_;
}
else
{
lean_dec(v_h__1_22_);
if (lean_obj_tag(v_x_21_) == 0)
{
lean_object* v___x_26_; 
lean_dec(v_h__3_24_);
v___x_26_ = lean_apply_2(v_h__2_23_, v_x_20_, lean_box(0));
return v___x_26_;
}
else
{
lean_object* v_p_27_; lean_object* v_m_28_; lean_object* v_p_29_; lean_object* v_m_30_; lean_object* v___x_31_; 
lean_dec(v_h__2_23_);
v_p_27_ = lean_ctor_get(v_x_20_, 0);
lean_inc_ref(v_p_27_);
v_m_28_ = lean_ctor_get(v_x_20_, 1);
lean_inc(v_m_28_);
lean_dec_ref_known(v_x_20_, 2);
v_p_29_ = lean_ctor_get(v_x_21_, 0);
lean_inc_ref(v_p_29_);
v_m_30_ = lean_ctor_get(v_x_21_, 1);
lean_inc(v_m_30_);
lean_dec_ref_known(v_x_21_, 2);
v___x_31_ = lean_apply_4(v_h__3_24_, v_p_27_, v_m_28_, v_p_29_, v_m_30_);
return v___x_31_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__3_splitter(lean_object* v_motive_32_, lean_object* v_x_33_, lean_object* v_x_34_, lean_object* v_h__1_35_, lean_object* v_h__2_36_, lean_object* v_h__3_37_){
_start:
{
if (lean_obj_tag(v_x_33_) == 0)
{
lean_object* v___x_38_; 
lean_dec(v_h__3_37_);
lean_dec(v_h__2_36_);
v___x_38_ = lean_apply_1(v_h__1_35_, v_x_34_);
return v___x_38_;
}
else
{
lean_dec(v_h__1_35_);
if (lean_obj_tag(v_x_34_) == 0)
{
lean_object* v___x_39_; 
lean_dec(v_h__3_37_);
v___x_39_ = lean_apply_2(v_h__2_36_, v_x_33_, lean_box(0));
return v___x_39_;
}
else
{
lean_object* v_p_40_; lean_object* v_m_41_; lean_object* v_p_42_; lean_object* v_m_43_; lean_object* v___x_44_; 
lean_dec(v_h__2_36_);
v_p_40_ = lean_ctor_get(v_x_33_, 0);
lean_inc_ref(v_p_40_);
v_m_41_ = lean_ctor_get(v_x_33_, 1);
lean_inc(v_m_41_);
lean_dec_ref_known(v_x_33_, 2);
v_p_42_ = lean_ctor_get(v_x_34_, 0);
lean_inc_ref(v_p_42_);
v_m_43_ = lean_ctor_get(v_x_34_, 1);
lean_inc(v_m_43_);
lean_dec_ref_known(v_x_34_, 2);
v___x_44_ = lean_apply_4(v_h__3_37_, v_p_40_, v_m_41_, v_p_42_, v_m_43_);
return v___x_44_;
}
}
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg(uint8_t v_x_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_, lean_object* v_h__3_48_){
_start:
{
switch(v_x_45_)
{
case 0:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_h__3_48_);
lean_dec(v_h__1_46_);
v___x_49_ = lean_box(0);
v___x_50_ = lean_apply_1(v_h__2_47_, v___x_49_);
return v___x_50_;
}
case 1:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
lean_dec(v_h__3_48_);
lean_dec(v_h__2_47_);
v___x_51_ = lean_box(0);
v___x_52_ = lean_apply_1(v_h__1_46_, v___x_51_);
return v___x_52_;
}
default: 
{
lean_object* v___x_53_; lean_object* v___x_54_; 
lean_dec(v_h__2_47_);
lean_dec(v_h__1_46_);
v___x_53_ = lean_box(0);
v___x_54_ = lean_apply_1(v_h__3_48_, v___x_53_);
return v___x_54_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_45_ = stack[0].m_num;
lean_object* v_h__1_46_ = stack[1].m_obj;
lean_object* v_h__2_47_ = stack[2].m_obj;
lean_object* v_h__3_48_ = stack[3].m_obj;
lean_object* v_res_55_;
v_res_55_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg(v_x_45_, v_h__1_46_, v_h__2_47_, v_h__3_48_);
stack->m_obj
 = v_res_55_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg___boxed(lean_object* v_x_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_, lean_object* v_h__3_59_){
_start:
{
uint8_t v_x_33__boxed_60_; lean_object* v_res_61_; 
v_x_33__boxed_60_ = lean_unbox(v_x_56_);
v_res_61_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg(v_x_33__boxed_60_, v_h__1_57_, v_h__2_58_, v_h__3_59_);
return v_res_61_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter(lean_object* v_motive_62_, uint8_t v_x_63_, lean_object* v_h__1_64_, lean_object* v_h__2_65_, lean_object* v_h__3_66_){
_start:
{
switch(v_x_63_)
{
case 0:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v_h__3_66_);
lean_dec(v_h__1_64_);
v___x_67_ = lean_box(0);
v___x_68_ = lean_apply_1(v_h__2_65_, v___x_67_);
return v___x_68_;
}
case 1:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_h__3_66_);
lean_dec(v_h__2_65_);
v___x_69_ = lean_box(0);
v___x_70_ = lean_apply_1(v_h__1_64_, v___x_69_);
return v___x_70_;
}
default: 
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec(v_h__2_65_);
lean_dec(v_h__1_64_);
v___x_71_ = lean_box(0);
v___x_72_ = lean_apply_1(v_h__3_66_, v___x_71_);
return v___x_72_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_63_ = stack[1].m_num;
lean_object* v_h__1_64_ = stack[2].m_obj;
lean_object* v_h__2_65_ = stack[3].m_obj;
lean_object* v_h__3_66_ = stack[4].m_obj;
lean_object* v_res_73_;
v_res_73_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter(lean_box(0), v_x_63_, v_h__1_64_, v_h__2_65_, v_h__3_66_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___boxed(lean_object* v_motive_74_, lean_object* v_x_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_, lean_object* v_h__3_78_){
_start:
{
uint8_t v_x_56__boxed_79_; lean_object* v_res_80_; 
v_x_56__boxed_79_ = lean_unbox(v_x_75_);
v_res_80_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter(v_motive_74_, v_x_56__boxed_79_, v_h__1_76_, v_h__2_77_, v_h__3_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_lcm(lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
if (lean_obj_tag(v_x_81_) == 0)
{
return v_x_82_;
}
else
{
if (lean_obj_tag(v_x_82_) == 0)
{
return v_x_81_;
}
else
{
lean_object* v_p_83_; lean_object* v_m_84_; lean_object* v_p_85_; lean_object* v_m_86_; lean_object* v_x_87_; lean_object* v_k_88_; lean_object* v___y_90_; lean_object* v_x_94_; lean_object* v_k_95_; uint8_t v___x_96_; 
v_p_83_ = lean_ctor_get(v_x_81_, 0);
v_m_84_ = lean_ctor_get(v_x_81_, 1);
v_p_85_ = lean_ctor_get(v_x_82_, 0);
v_m_86_ = lean_ctor_get(v_x_82_, 1);
v_x_87_ = lean_ctor_get(v_p_83_, 0);
v_k_88_ = lean_ctor_get(v_p_83_, 1);
v_x_94_ = lean_ctor_get(v_p_85_, 0);
v_k_95_ = lean_ctor_get(v_p_85_, 1);
v___x_96_ = lean_nat_dec_lt(v_x_87_, v_x_94_);
if (v___x_96_ == 0)
{
lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_106_; 
lean_inc(v_m_86_);
lean_inc_ref(v_p_85_);
v_isSharedCheck_106_ = !lean_is_exclusive(v_x_82_);
if (v_isSharedCheck_106_ == 0)
{
lean_object* v_unused_107_; lean_object* v_unused_108_; 
v_unused_107_ = lean_ctor_get(v_x_82_, 1);
lean_dec(v_unused_107_);
v_unused_108_ = lean_ctor_get(v_x_82_, 0);
lean_dec(v_unused_108_);
v___x_98_ = v_x_82_;
v_isShared_99_ = v_isSharedCheck_106_;
goto v_resetjp_97_;
}
else
{
lean_dec(v_x_82_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_106_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
uint8_t v___x_100_; 
v___x_100_ = lean_nat_dec_eq(v_x_87_, v_x_94_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_101_ = l_Lean_Grind_CommRing_Mon_lcm(v_x_81_, v_m_86_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v___x_101_);
v___x_103_ = v___x_98_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_p_85_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
else
{
uint8_t v___x_105_; 
lean_inc(v_k_95_);
lean_inc(v_k_88_);
lean_inc(v_x_87_);
lean_inc(v_m_84_);
lean_del_object(v___x_98_);
lean_dec_ref(v_p_85_);
lean_dec_ref_known(v_x_81_, 2);
v___x_105_ = lean_nat_dec_le(v_k_88_, v_k_95_);
if (v___x_105_ == 0)
{
lean_dec(v_k_95_);
v___y_90_ = v_k_88_;
goto v___jp_89_;
}
else
{
lean_dec(v_k_88_);
v___y_90_ = v_k_95_;
goto v___jp_89_;
}
}
}
}
else
{
lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_116_; 
lean_inc(v_m_84_);
lean_inc_ref(v_p_83_);
v_isSharedCheck_116_ = !lean_is_exclusive(v_x_81_);
if (v_isSharedCheck_116_ == 0)
{
lean_object* v_unused_117_; lean_object* v_unused_118_; 
v_unused_117_ = lean_ctor_get(v_x_81_, 1);
lean_dec(v_unused_117_);
v_unused_118_ = lean_ctor_get(v_x_81_, 0);
lean_dec(v_unused_118_);
v___x_110_ = v_x_81_;
v_isShared_111_ = v_isSharedCheck_116_;
goto v_resetjp_109_;
}
else
{
lean_dec(v_x_81_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_116_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_112_ = l_Lean_Grind_CommRing_Mon_lcm(v_m_84_, v_x_82_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 1, v___x_112_);
v___x_114_ = v___x_110_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_p_83_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
v___jp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v_x_87_);
lean_ctor_set(v___x_91_, 1, v___y_90_);
v___x_92_ = l_Lean_Grind_CommRing_Mon_lcm(v_m_84_, v_m_86_);
v___x_93_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
return v___x_93_;
}
}
}
}
}
uint8_t l_Lean_Grind_CommRing_Mon_divides(lean_object* v_x_119_, lean_object* v_x_120_){
_start:
{
if (lean_obj_tag(v_x_119_) == 0)
{
uint8_t v___x_121_; 
v___x_121_ = 1;
return v___x_121_;
}
else
{
if (lean_obj_tag(v_x_120_) == 0)
{
uint8_t v___x_122_; 
v___x_122_ = 0;
return v___x_122_;
}
else
{
lean_object* v_p_123_; lean_object* v_p_124_; lean_object* v_m_125_; lean_object* v_m_126_; lean_object* v_x_127_; lean_object* v_k_128_; lean_object* v_x_129_; lean_object* v_k_130_; uint8_t v___x_131_; 
v_p_123_ = lean_ctor_get(v_x_119_, 0);
v_p_124_ = lean_ctor_get(v_x_120_, 0);
v_m_125_ = lean_ctor_get(v_x_119_, 1);
v_m_126_ = lean_ctor_get(v_x_120_, 1);
v_x_127_ = lean_ctor_get(v_p_123_, 0);
v_k_128_ = lean_ctor_get(v_p_123_, 1);
v_x_129_ = lean_ctor_get(v_p_124_, 0);
v_k_130_ = lean_ctor_get(v_p_124_, 1);
v___x_131_ = lean_nat_dec_lt(v_x_127_, v_x_129_);
if (v___x_131_ == 0)
{
uint8_t v___x_132_; 
v___x_132_ = lean_nat_dec_eq(v_x_127_, v_x_129_);
if (v___x_132_ == 0)
{
v_x_120_ = v_m_126_;
goto _start;
}
else
{
uint8_t v___x_134_; 
v___x_134_ = lean_nat_dec_le(v_k_128_, v_k_130_);
if (v___x_134_ == 0)
{
return v___x_134_;
}
else
{
v_x_119_ = v_m_125_;
v_x_120_ = v_m_126_;
goto _start;
}
}
}
else
{
uint8_t v___x_136_; 
v___x_136_ = 0;
return v___x_136_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Mon_divides_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_119_ = stack[0].m_obj;
lean_object* v_x_120_ = stack[1].m_obj;
uint8_t v_res_137_;
v_res_137_ = l_Lean_Grind_CommRing_Mon_divides(v_x_119_, v_x_120_);
stack->m_num = v_res_137_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_divides___boxed(lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Lean_Grind_CommRing_Mon_divides(v_x_138_, v_x_139_);
lean_dec(v_x_139_);
lean_dec(v_x_138_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_div(lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
if (lean_obj_tag(v_x_143_) == 0)
{
return v_x_142_;
}
else
{
if (lean_obj_tag(v_x_142_) == 0)
{
lean_dec_ref_known(v_x_143_, 2);
return v_x_142_;
}
else
{
lean_object* v_p_144_; lean_object* v_p_145_; lean_object* v_m_146_; lean_object* v_m_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_177_; 
v_p_144_ = lean_ctor_get(v_x_142_, 0);
lean_inc_ref(v_p_144_);
v_p_145_ = lean_ctor_get(v_x_143_, 0);
lean_inc_ref(v_p_145_);
v_m_146_ = lean_ctor_get(v_x_143_, 1);
v_m_147_ = lean_ctor_get(v_x_142_, 1);
v_isSharedCheck_177_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_177_ == 0)
{
lean_object* v_unused_178_; 
v_unused_178_ = lean_ctor_get(v_x_142_, 0);
lean_dec(v_unused_178_);
v___x_149_ = v_x_142_;
v_isShared_150_ = v_isSharedCheck_177_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_m_147_);
lean_dec(v_x_142_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_177_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v_x_151_; lean_object* v_k_152_; lean_object* v_x_153_; lean_object* v_k_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_176_; 
v_x_151_ = lean_ctor_get(v_p_144_, 0);
v_k_152_ = lean_ctor_get(v_p_144_, 1);
v_x_153_ = lean_ctor_get(v_p_145_, 0);
v_k_154_ = lean_ctor_get(v_p_145_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v_p_145_);
if (v_isSharedCheck_176_ == 0)
{
v___x_156_ = v_p_145_;
v_isShared_157_ = v_isSharedCheck_176_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_k_154_);
lean_inc(v_x_153_);
lean_dec(v_p_145_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_176_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
uint8_t v___x_158_; 
v___x_158_ = lean_nat_dec_lt(v_x_151_, v_x_153_);
if (v___x_158_ == 0)
{
uint8_t v___x_159_; 
lean_inc(v_k_152_);
lean_inc(v_x_151_);
lean_inc(v_m_146_);
lean_dec_ref(v_p_144_);
lean_dec_ref_known(v_x_143_, 2);
v___x_159_ = lean_nat_dec_eq(v_x_151_, v_x_153_);
lean_dec(v_x_153_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; 
lean_del_object(v___x_156_);
lean_dec(v_k_154_);
lean_dec(v_k_152_);
lean_dec(v_x_151_);
lean_del_object(v___x_149_);
lean_dec(v_m_147_);
lean_dec(v_m_146_);
v___x_160_ = lean_box(0);
return v___x_160_;
}
else
{
lean_object* v_k_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_k_161_ = lean_nat_sub(v_k_152_, v_k_154_);
lean_dec(v_k_154_);
lean_dec(v_k_152_);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_nat_dec_eq(v_k_161_, v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_165_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v_k_161_);
lean_ctor_set(v___x_156_, 0, v_x_151_);
v___x_165_ = v___x_156_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_x_151_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_k_161_);
v___x_165_ = v_reuseFailAlloc_170_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_166_ = l_Lean_Grind_CommRing_Mon_div(v_m_147_, v_m_146_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 1, v___x_166_);
lean_ctor_set(v___x_149_, 0, v___x_165_);
v___x_168_ = v___x_149_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
else
{
lean_dec(v_k_161_);
lean_del_object(v___x_156_);
lean_dec(v_x_151_);
lean_del_object(v___x_149_);
v_x_142_ = v_m_147_;
v_x_143_ = v_m_146_;
goto _start;
}
}
}
else
{
lean_object* v___x_172_; lean_object* v___x_174_; 
lean_del_object(v___x_156_);
lean_dec(v_k_154_);
lean_dec(v_x_153_);
v___x_172_ = l_Lean_Grind_CommRing_Mon_div(v_m_147_, v_x_143_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 1, v___x_172_);
v___x_174_ = v___x_149_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_p_144_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
}
}
}
uint8_t l_Lean_Grind_CommRing_Mon_coprime(lean_object* v_x_179_, lean_object* v_x_180_){
_start:
{
if (lean_obj_tag(v_x_179_) == 0)
{
uint8_t v___x_181_; 
v___x_181_ = 1;
return v___x_181_;
}
else
{
if (lean_obj_tag(v_x_180_) == 0)
{
uint8_t v___x_182_; 
v___x_182_ = 1;
return v___x_182_;
}
else
{
lean_object* v_p_183_; lean_object* v_p_184_; lean_object* v_m_185_; lean_object* v_m_186_; lean_object* v_x_187_; lean_object* v_x_188_; uint8_t v___x_189_; 
v_p_183_ = lean_ctor_get(v_x_179_, 0);
v_p_184_ = lean_ctor_get(v_x_180_, 0);
v_m_185_ = lean_ctor_get(v_x_179_, 1);
v_m_186_ = lean_ctor_get(v_x_180_, 1);
v_x_187_ = lean_ctor_get(v_p_183_, 0);
v_x_188_ = lean_ctor_get(v_p_184_, 0);
v___x_189_ = lean_nat_dec_lt(v_x_187_, v_x_188_);
if (v___x_189_ == 0)
{
uint8_t v___x_190_; 
v___x_190_ = lean_nat_dec_eq(v_x_187_, v_x_188_);
if (v___x_190_ == 0)
{
v_x_180_ = v_m_186_;
goto _start;
}
else
{
return v___x_189_;
}
}
else
{
v_x_179_ = v_m_185_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Mon_coprime_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_179_ = stack[0].m_obj;
lean_object* v_x_180_ = stack[1].m_obj;
uint8_t v_res_193_;
v_res_193_ = l_Lean_Grind_CommRing_Mon_coprime(v_x_179_, v_x_180_);
stack->m_num = v_res_193_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_coprime___boxed(lean_object* v_x_194_, lean_object* v_x_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_Lean_Grind_CommRing_Mon_coprime(v_x_194_, v_x_195_);
lean_dec(v_x_195_);
lean_dec(v_x_194_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_x27(lean_object* v_p_198_, lean_object* v_k_199_, lean_object* v_char_x3f_200_){
_start:
{
if (lean_obj_tag(v_char_x3f_200_) == 1)
{
lean_object* v_val_201_; lean_object* v___x_202_; 
v_val_201_ = lean_ctor_get(v_char_x3f_200_, 0);
lean_inc(v_val_201_);
lean_dec_ref_known(v_char_x3f_200_, 1);
v___x_202_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_199_, v_p_198_, v_val_201_);
return v___x_202_;
}
else
{
lean_object* v___x_203_; 
lean_dec(v_char_x3f_200_);
v___x_203_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_199_, v_p_198_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulConst_x27___boxed(lean_object* v_p_204_, lean_object* v_k_205_, lean_object* v_char_x3f_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Grind_CommRing_Poly_mulConst_x27(v_p_204_, v_k_205_, v_char_x3f_206_);
lean_dec(v_k_205_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_x27(lean_object* v_p_208_, lean_object* v_k_209_, lean_object* v_m_210_, lean_object* v_char_x3f_211_){
_start:
{
if (lean_obj_tag(v_char_x3f_211_) == 1)
{
lean_object* v_val_212_; lean_object* v___x_213_; 
v_val_212_ = lean_ctor_get(v_char_x3f_211_, 0);
lean_inc(v_val_212_);
lean_dec_ref_known(v_char_x3f_211_, 1);
v___x_213_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_209_, v_m_210_, v_p_208_, v_val_212_);
return v___x_213_;
}
else
{
lean_object* v___x_214_; 
lean_dec(v_char_x3f_211_);
v___x_214_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_209_, v_m_210_, v_p_208_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_mulMon_x27___boxed(lean_object* v_p_215_, lean_object* v_k_216_, lean_object* v_m_217_, lean_object* v_char_x3f_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Grind_CommRing_Poly_mulMon_x27(v_p_215_, v_k_216_, v_m_217_, v_char_x3f_218_);
lean_dec(v_k_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_combine_x27(lean_object* v_p_u2081_220_, lean_object* v_p_u2082_221_, lean_object* v_char_x3f_222_){
_start:
{
if (lean_obj_tag(v_char_x3f_222_) == 1)
{
lean_object* v_val_223_; lean_object* v___x_224_; 
v_val_223_ = lean_ctor_get(v_char_x3f_222_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v_char_x3f_222_, 1);
v___x_224_ = l_Lean_Grind_CommRing_Poly_combineC(v_p_u2081_220_, v_p_u2082_221_, v_val_223_);
return v___x_224_;
}
else
{
lean_object* v___x_225_; 
lean_dec(v_char_x3f_222_);
v___x_225_ = l_Lean_Grind_CommRing_Poly_combine(v_p_u2081_220_, v_p_u2082_221_);
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_Poly_spol_spec__0(lean_object* v_a_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = lean_nat_to_int(v_a_226_);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spol___closed__0(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_nat_to_int(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spol___closed__1(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Poly_spol___closed__2(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_232_ = lean_box(0);
v___x_233_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_234_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__1, &l_Lean_Grind_CommRing_Poly_spol___closed__1_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__1);
v___x_235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___x_233_);
lean_ctor_set(v___x_235_, 2, v___x_232_);
lean_ctor_set(v___x_235_, 3, v___x_233_);
lean_ctor_set(v___x_235_, 4, v___x_232_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_spol(lean_object* v_p_u2081_236_, lean_object* v_p_u2082_237_, lean_object* v_char_x3f_238_){
_start:
{
if (lean_obj_tag(v_p_u2081_236_) == 1)
{
if (lean_obj_tag(v_p_u2082_237_) == 1)
{
lean_object* v_k_241_; lean_object* v_v_242_; lean_object* v_p_243_; lean_object* v_k_244_; lean_object* v_v_245_; lean_object* v_p_246_; lean_object* v_m_247_; lean_object* v_m_u2081_248_; lean_object* v_m_u2082_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v_g_252_; lean_object* v___x_253_; lean_object* v_c_u2081_254_; lean_object* v___x_255_; lean_object* v_c_u2082_256_; lean_object* v_p_u2081_257_; lean_object* v_p_u2082_258_; lean_object* v_spol_259_; lean_object* v___x_260_; 
v_k_241_ = lean_ctor_get(v_p_u2081_236_, 0);
lean_inc(v_k_241_);
v_v_242_ = lean_ctor_get(v_p_u2081_236_, 1);
lean_inc_n(v_v_242_, 2);
v_p_243_ = lean_ctor_get(v_p_u2081_236_, 2);
lean_inc_ref(v_p_243_);
lean_dec_ref_known(v_p_u2081_236_, 3);
v_k_244_ = lean_ctor_get(v_p_u2082_237_, 0);
lean_inc(v_k_244_);
v_v_245_ = lean_ctor_get(v_p_u2082_237_, 1);
lean_inc_n(v_v_245_, 2);
v_p_246_ = lean_ctor_get(v_p_u2082_237_, 2);
lean_inc_ref(v_p_246_);
lean_dec_ref_known(v_p_u2082_237_, 3);
v_m_247_ = l_Lean_Grind_CommRing_Mon_lcm(v_v_242_, v_v_245_);
lean_inc(v_m_247_);
v_m_u2081_248_ = l_Lean_Grind_CommRing_Mon_div(v_m_247_, v_v_242_);
v_m_u2082_249_ = l_Lean_Grind_CommRing_Mon_div(v_m_247_, v_v_245_);
v___x_250_ = lean_nat_abs(v_k_241_);
v___x_251_ = lean_nat_abs(v_k_244_);
v_g_252_ = lean_nat_gcd(v___x_250_, v___x_251_);
lean_dec(v___x_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_nat_to_int(v_g_252_);
v_c_u2081_254_ = lean_int_ediv(v_k_244_, v___x_253_);
lean_dec(v_k_244_);
v___x_255_ = lean_int_neg(v_k_241_);
lean_dec(v_k_241_);
v_c_u2082_256_ = lean_int_ediv(v___x_255_, v___x_253_);
lean_dec(v___x_253_);
lean_dec(v___x_255_);
lean_inc_n(v_char_x3f_238_, 2);
lean_inc(v_m_u2081_248_);
v_p_u2081_257_ = l_Lean_Grind_CommRing_Poly_mulMon_x27(v_p_243_, v_c_u2081_254_, v_m_u2081_248_, v_char_x3f_238_);
lean_inc(v_m_u2082_249_);
v_p_u2082_258_ = l_Lean_Grind_CommRing_Poly_mulMon_x27(v_p_246_, v_c_u2082_256_, v_m_u2082_249_, v_char_x3f_238_);
v_spol_259_ = l_Lean_Grind_CommRing_Poly_combine_x27(v_p_u2081_257_, v_p_u2082_258_, v_char_x3f_238_);
v___x_260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_260_, 0, v_spol_259_);
lean_ctor_set(v___x_260_, 1, v_c_u2081_254_);
lean_ctor_set(v___x_260_, 2, v_m_u2081_248_);
lean_ctor_set(v___x_260_, 3, v_c_u2082_256_);
lean_ctor_set(v___x_260_, 4, v_m_u2082_249_);
return v___x_260_;
}
else
{
lean_dec_ref_known(v_p_u2081_236_, 3);
lean_dec(v_char_x3f_238_);
lean_dec_ref(v_p_u2082_237_);
goto v___jp_239_;
}
}
else
{
lean_dec(v_char_x3f_238_);
lean_dec_ref(v_p_u2082_237_);
lean_dec_ref(v_p_u2081_236_);
goto v___jp_239_;
}
v___jp_239_:
{
lean_object* v___x_240_; 
v___x_240_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__2, &l_Lean_Grind_CommRing_Poly_spol___closed__2_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__2);
return v___x_240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_degree(lean_object* v_x_261_){
_start:
{
if (lean_obj_tag(v_x_261_) == 0)
{
lean_object* v___x_262_; 
v___x_262_ = lean_unsigned_to_nat(0u);
return v___x_262_;
}
else
{
lean_object* v_v_263_; lean_object* v___x_264_; 
v_v_263_ = lean_ctor_get(v_x_261_, 1);
v___x_264_ = l_Lean_Grind_CommRing_Mon_degree(v_v_263_);
return v___x_264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_degree___boxed(lean_object* v_x_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Grind_CommRing_Poly_degree(v_x_265_);
lean_dec_ref(v_x_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go(lean_object* v_p_267_, lean_object* v_acc_268_){
_start:
{
if (lean_obj_tag(v_p_267_) == 0)
{
return v_acc_268_;
}
else
{
lean_object* v_p_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_p_269_ = lean_ctor_get(v_p_267_, 2);
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = lean_nat_add(v_acc_268_, v___x_270_);
lean_dec(v_acc_268_);
v_p_267_ = v_p_269_;
v_acc_268_ = v___x_271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go___boxed(lean_object* v_p_273_, lean_object* v_acc_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go(v_p_273_, v_acc_274_);
lean_dec_ref(v_p_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_numTerms(lean_object* v_p_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go(v_p_276_, v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_numTerms___boxed(lean_object* v_p_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Grind_CommRing_Poly_numTerms(v_p_279_);
lean_dec_ref(v_p_279_);
return v_res_280_;
}
}
uint8_t l_Lean_Grind_CommRing_Poly_divides(lean_object* v_p_281_, lean_object* v_m_282_){
_start:
{
if (lean_obj_tag(v_p_281_) == 0)
{
uint8_t v___x_283_; 
v___x_283_ = 1;
return v___x_283_;
}
else
{
lean_object* v_v_284_; uint8_t v___x_285_; 
v_v_284_ = lean_ctor_get(v_p_281_, 1);
v___x_285_ = l_Lean_Grind_CommRing_Mon_divides(v_v_284_, v_m_282_);
return v___x_285_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Poly_divides_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_281_ = stack[0].m_obj;
lean_object* v_m_282_ = stack[1].m_obj;
uint8_t v_res_286_;
v_res_286_ = l_Lean_Grind_CommRing_Poly_divides(v_p_281_, v_m_282_);
stack->m_num = v_res_286_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_divides___boxed(lean_object* v_p_287_, lean_object* v_m_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Lean_Grind_CommRing_Poly_divides(v_p_287_, v_m_288_);
lean_dec(v_m_288_);
lean_dec_ref(v_p_287_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lc(lean_object* v_x_291_){
_start:
{
lean_object* v_k_292_; 
v_k_292_ = lean_ctor_get(v_x_291_, 0);
lean_inc(v_k_292_);
return v_k_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lc___boxed(lean_object* v_x_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Grind_CommRing_Poly_lc(v_x_293_);
lean_dec_ref(v_x_293_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lm(lean_object* v_x_295_){
_start:
{
if (lean_obj_tag(v_x_295_) == 0)
{
lean_object* v___x_296_; 
v___x_296_ = lean_box(0);
return v___x_296_;
}
else
{
lean_object* v_v_297_; 
v_v_297_ = lean_ctor_get(v_x_295_, 1);
lean_inc(v_v_297_);
return v_v_297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_lm___boxed(lean_object* v_x_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Grind_CommRing_Poly_lm(v_x_298_);
lean_dec_ref(v_x_298_);
return v_res_299_;
}
}
uint8_t l_Lean_Grind_CommRing_Poly_isZero(lean_object* v_x_300_){
_start:
{
if (lean_obj_tag(v_x_300_) == 0)
{
lean_object* v_k_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v_k_301_ = lean_ctor_get(v_x_300_, 0);
v___x_302_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_303_ = lean_int_dec_eq(v_k_301_, v___x_302_);
return v___x_303_;
}
else
{
uint8_t v___x_304_; 
v___x_304_ = 0;
return v___x_304_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Poly_isZero_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_300_ = stack[0].m_obj;
uint8_t v_res_305_;
v_res_305_ = l_Lean_Grind_CommRing_Poly_isZero(v_x_300_);
stack->m_num = v_res_305_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_isZero___boxed(lean_object* v_x_306_){
_start:
{
uint8_t v_res_307_; lean_object* v_r_308_; 
v_res_307_ = l_Lean_Grind_CommRing_Poly_isZero(v_x_306_);
lean_dec_ref(v_x_306_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_getConst(lean_object* v_x_309_){
_start:
{
if (lean_obj_tag(v_x_309_) == 0)
{
lean_object* v_k_310_; 
v_k_310_ = lean_ctor_get(v_x_309_, 0);
lean_inc(v_k_310_);
return v_k_310_;
}
else
{
lean_object* v_p_311_; 
v_p_311_ = lean_ctor_get(v_x_309_, 2);
v_x_309_ = v_p_311_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_getConst___boxed(lean_object* v_x_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Grind_CommRing_Poly_getConst(v_x_313_);
lean_dec_ref(v_x_313_);
return v_res_314_;
}
}
uint8_t l_Lean_Grind_CommRing_Poly_checkCoeffs(lean_object* v_x_315_){
_start:
{
if (lean_obj_tag(v_x_315_) == 0)
{
uint8_t v___x_316_; 
v___x_316_ = 1;
return v___x_316_;
}
else
{
lean_object* v_k_317_; lean_object* v_p_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v_k_317_ = lean_ctor_get(v_x_315_, 0);
v_p_318_ = lean_ctor_get(v_x_315_, 2);
v___x_319_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_320_ = lean_int_dec_eq(v_k_317_, v___x_319_);
if (v___x_320_ == 0)
{
v_x_315_ = v_p_318_;
goto _start;
}
else
{
uint8_t v___x_322_; 
v___x_322_ = 0;
return v___x_322_;
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Poly_checkCoeffs_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_315_ = stack[0].m_obj;
uint8_t v_res_323_;
v_res_323_ = l_Lean_Grind_CommRing_Poly_checkCoeffs(v_x_315_);
stack->m_num = v_res_323_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_checkCoeffs___boxed(lean_object* v_x_324_){
_start:
{
uint8_t v_res_325_; lean_object* v_r_326_; 
v_res_325_ = l_Lean_Grind_CommRing_Poly_checkCoeffs(v_x_324_);
lean_dec_ref(v_x_324_);
v_r_326_ = lean_box(v_res_325_);
return v_r_326_;
}
}
uint8_t l_Lean_Grind_CommRing_Poly_checkNoUnitMon(lean_object* v_x_327_){
_start:
{
if (lean_obj_tag(v_x_327_) == 0)
{
uint8_t v___x_328_; 
v___x_328_ = 1;
return v___x_328_;
}
else
{
lean_object* v_v_329_; 
v_v_329_ = lean_ctor_get(v_x_327_, 1);
if (lean_obj_tag(v_v_329_) == 0)
{
uint8_t v___x_330_; 
v___x_330_ = 0;
return v___x_330_;
}
else
{
lean_object* v_p_331_; 
v_p_331_ = lean_ctor_get(v_x_327_, 2);
v_x_327_ = v_p_331_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_CommRing_Poly_checkNoUnitMon_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_327_ = stack[0].m_obj;
uint8_t v_res_333_;
v_res_333_ = l_Lean_Grind_CommRing_Poly_checkNoUnitMon(v_x_327_);
stack->m_num = v_res_333_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_checkNoUnitMon___boxed(lean_object* v_x_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Lean_Grind_CommRing_Poly_checkNoUnitMon(v_x_334_);
lean_dec_ref(v_x_334_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_size(lean_object* v_x_337_){
_start:
{
if (lean_obj_tag(v_x_337_) == 0)
{
lean_object* v___x_338_; 
v___x_338_ = lean_unsigned_to_nat(0u);
return v___x_338_;
}
else
{
lean_object* v_m_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_m_339_ = lean_ctor_get(v_x_337_, 1);
v___x_340_ = l_Lean_Grind_CommRing_Mon_size(v_m_339_);
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = lean_nat_add(v___x_340_, v___x_341_);
lean_dec(v___x_340_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_size___boxed(lean_object* v_x_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Grind_CommRing_Mon_size(v_x_343_);
lean_dec(v_x_343_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_size(lean_object* v_x_345_){
_start:
{
if (lean_obj_tag(v_x_345_) == 0)
{
lean_object* v___x_346_; 
v___x_346_ = lean_unsigned_to_nat(1u);
return v___x_346_;
}
else
{
lean_object* v_v_347_; lean_object* v_p_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v_v_347_ = lean_ctor_get(v_x_345_, 1);
v_p_348_ = lean_ctor_get(v_x_345_, 2);
v___x_349_ = l_Lean_Grind_CommRing_Mon_size(v_v_347_);
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_nat_add(v___x_349_, v___x_350_);
lean_dec(v___x_349_);
v___x_352_ = l_Lean_Grind_CommRing_Poly_size(v_p_348_);
v___x_353_ = lean_nat_add(v___x_351_, v___x_352_);
lean_dec(v___x_352_);
lean_dec(v___x_351_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_size___boxed(lean_object* v_x_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Grind_CommRing_Poly_size(v_x_354_);
lean_dec_ref(v_x_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_length(lean_object* v_x_356_){
_start:
{
if (lean_obj_tag(v_x_356_) == 0)
{
lean_object* v___x_357_; 
v___x_357_ = lean_unsigned_to_nat(0u);
return v___x_357_;
}
else
{
lean_object* v_p_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_p_358_ = lean_ctor_get(v_x_356_, 2);
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = l_Lean_Grind_CommRing_Poly_length(v_p_358_);
v___x_361_ = lean_nat_add(v___x_359_, v___x_360_);
lean_dec(v___x_360_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_length___boxed(lean_object* v_x_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Grind_CommRing_Poly_length(v_x_362_);
lean_dec_ref(v_x_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_toExpr(lean_object* v_pw_364_){
_start:
{
lean_object* v_x_365_; lean_object* v_k_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_377_; 
v_x_365_ = lean_ctor_get(v_pw_364_, 0);
v_k_366_ = lean_ctor_get(v_pw_364_, 1);
v_isSharedCheck_377_ = !lean_is_exclusive(v_pw_364_);
if (v_isSharedCheck_377_ == 0)
{
v___x_368_ = v_pw_364_;
v_isShared_369_ = v_isSharedCheck_377_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_k_366_);
lean_inc(v_x_365_);
lean_dec(v_pw_364_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_377_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = lean_nat_dec_eq(v_k_366_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_372_, 0, v_x_365_);
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 8);
lean_ctor_set(v___x_368_, 0, v___x_372_);
v___x_374_ = v___x_368_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_k_366_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
else
{
lean_object* v___x_376_; 
lean_del_object(v___x_368_);
lean_dec(v_k_366_);
v___x_376_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_376_, 0, v_x_365_);
return v___x_376_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_toExpr_go(lean_object* v_m_378_, lean_object* v_acc_379_){
_start:
{
if (lean_obj_tag(v_m_378_) == 0)
{
return v_acc_379_;
}
else
{
lean_object* v_p_380_; lean_object* v_m_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_390_; 
v_p_380_ = lean_ctor_get(v_m_378_, 0);
v_m_381_ = lean_ctor_get(v_m_378_, 1);
v_isSharedCheck_390_ = !lean_is_exclusive(v_m_378_);
if (v_isSharedCheck_390_ == 0)
{
v___x_383_ = v_m_378_;
v_isShared_384_ = v_isSharedCheck_390_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_m_381_);
lean_inc(v_p_380_);
lean_dec(v_m_378_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_390_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_385_ = l_Lean_Grind_CommRing_Power_toExpr(v_p_380_);
if (v_isShared_384_ == 0)
{
lean_ctor_set_tag(v___x_383_, 7);
lean_ctor_set(v___x_383_, 1, v___x_385_);
lean_ctor_set(v___x_383_, 0, v_acc_379_);
v___x_387_ = v___x_383_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_acc_379_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_385_);
v___x_387_ = v_reuseFailAlloc_389_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
v_m_378_ = v_m_381_;
v_acc_379_ = v___x_387_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_unsigned_to_nat(1u);
v___x_392_ = lean_nat_to_int(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__1(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_toExpr___closed__0, &l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0);
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_toExpr(lean_object* v_m_395_){
_start:
{
if (lean_obj_tag(v_m_395_) == 0)
{
lean_object* v___x_396_; 
v___x_396_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_toExpr___closed__1, &l_Lean_Grind_CommRing_Mon_toExpr___closed__1_once, _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__1);
return v___x_396_;
}
else
{
lean_object* v_p_397_; lean_object* v_m_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_p_397_ = lean_ctor_get(v_m_395_, 0);
lean_inc_ref(v_p_397_);
v_m_398_ = lean_ctor_get(v_m_395_, 1);
lean_inc(v_m_398_);
lean_dec_ref_known(v_m_395_, 2);
v___x_399_ = l_Lean_Grind_CommRing_Power_toExpr(v_p_397_);
v___x_400_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_toExpr_go(v_m_398_, v___x_399_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(lean_object* v_k_401_, lean_object* v_m_402_){
_start:
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = lean_obj_once(&l_Lean_Grind_CommRing_Mon_toExpr___closed__0, &l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once, _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0);
v___x_404_ = lean_int_dec_eq(v_k_401_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v_k_401_);
v___x_406_ = l_Lean_Grind_CommRing_Mon_toExpr(v_m_402_);
v___x_407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
return v___x_407_;
}
else
{
lean_object* v___x_408_; 
lean_dec(v_k_401_);
v___x_408_ = l_Lean_Grind_CommRing_Mon_toExpr(v_m_402_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_go(lean_object* v_p_409_, lean_object* v_acc_410_){
_start:
{
if (lean_obj_tag(v_p_409_) == 0)
{
lean_object* v_k_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_421_; 
v_k_411_ = lean_ctor_get(v_p_409_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v_p_409_);
if (v_isSharedCheck_421_ == 0)
{
v___x_413_ = v_p_409_;
v_isShared_414_ = v_isSharedCheck_421_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_k_411_);
lean_dec(v_p_409_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_421_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_415_ = lean_obj_once(&l_Lean_Grind_CommRing_Poly_spol___closed__0, &l_Lean_Grind_CommRing_Poly_spol___closed__0_once, _init_l_Lean_Grind_CommRing_Poly_spol___closed__0);
v___x_416_ = lean_int_dec_eq(v_k_411_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_418_; 
if (v_isShared_414_ == 0)
{
v___x_418_ = v___x_413_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_k_411_);
v___x_418_ = v_reuseFailAlloc_420_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; 
v___x_419_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_419_, 0, v_acc_410_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
return v___x_419_;
}
}
else
{
lean_del_object(v___x_413_);
lean_dec(v_k_411_);
return v_acc_410_;
}
}
}
else
{
lean_object* v_k_422_; lean_object* v_v_423_; lean_object* v_p_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_k_422_ = lean_ctor_get(v_p_409_, 0);
lean_inc(v_k_422_);
v_v_423_ = lean_ctor_get(v_p_409_, 1);
lean_inc(v_v_423_);
v_p_424_ = lean_ctor_get(v_p_409_, 2);
lean_inc_ref(v_p_424_);
lean_dec_ref_known(v_p_409_, 3);
v___x_425_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(v_k_422_, v_v_423_);
v___x_426_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_426_, 0, v_acc_410_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v_p_409_ = v_p_424_;
v_acc_410_ = v___x_426_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_toExpr(lean_object* v_p_428_){
_start:
{
if (lean_obj_tag(v_p_428_) == 0)
{
lean_object* v_k_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
v_k_429_ = lean_ctor_get(v_p_428_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v_p_428_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v_p_428_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_k_429_);
lean_dec(v_p_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_k_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
else
{
lean_object* v_k_437_; lean_object* v_v_438_; lean_object* v_p_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_k_437_ = lean_ctor_get(v_p_428_, 0);
lean_inc(v_k_437_);
v_v_438_ = lean_ctor_get(v_p_428_, 1);
lean_inc(v_v_438_);
v_p_439_ = lean_ctor_get(v_p_428_, 2);
lean_inc_ref(v_p_439_);
lean_dec_ref_known(v_p_428_, 3);
v___x_440_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(v_k_437_, v_v_438_);
v___x_441_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_go(v_p_439_, v___x_440_);
return v___x_441_;
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
