// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Kronecker
// Imports: public import Lean.Meta.Sym.Arith.Types
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Mon_degree(lean_object*);
lean_object* lean_nat_log2(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_kronSatBits;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_satMul___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_satMul___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_satMul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_satMul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_satPow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_satPow___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprDegB(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprDegB___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprLin(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprLin___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Arith_exprLinS___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_exprLinS___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprLinS(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprLinS___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprDegS(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprDegS___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_exprExpandsSum_isSum(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_exprExpandsSum_isSum___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_Arith_exprExpandsSum(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprExpandsSum___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprMajorant(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprMajorant___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_polyMaxDeg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_polyMaxDeg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_polyNorm1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_polyNorm1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_monCode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_monCode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_polyMaxCode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_polyMaxCode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprMaxCode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprMaxCode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_kronExponent_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_kronExponent_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprLinCode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprLinCode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_kronLinExponent_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_kronLinExponent_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_invLookup(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_invLookup___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Arith_exprMajQ___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_Arith_exprMajQ___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_exprMajQ___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprMajQ(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprMajQ___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_deg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_deg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_kronQArgs_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_kronQArgs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprDegQL(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprDegQL___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQLinExponent_x3f_maxVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQLinExponent_x3f_maxVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_kronQLinExponent_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_kronQLinExponent_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Sym_Arith_kronSatBits(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(4194304u);
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_satMul___closed__0(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_2_ = lean_unsigned_to_nat(4194304u);
v___x_3_ = lean_unsigned_to_nat(2u);
v___x_4_ = lean_nat_pow(v___x_3_, v___x_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_satMul(lean_object* v_a_5_, lean_object* v_b_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_7_ = lean_nat_log2(v_a_5_);
v___x_8_ = lean_nat_log2(v_b_6_);
v___x_9_ = lean_nat_add(v___x_7_, v___x_8_);
lean_dec(v___x_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_unsigned_to_nat(4194304u);
v___x_11_ = lean_nat_dec_lt(v___x_9_, v___x_10_);
lean_dec(v___x_9_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_satMul___closed__0, &l_Lean_Meta_Sym_Arith_satMul___closed__0_once, _init_l_Lean_Meta_Sym_Arith_satMul___closed__0);
return v___x_12_;
}
else
{
lean_object* v___x_13_; 
v___x_13_ = lean_nat_mul(v_a_5_, v_b_6_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_satMul___boxed(lean_object* v_a_14_, lean_object* v_b_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Meta_Sym_Arith_satMul(v_a_14_, v_b_15_);
lean_dec(v_b_15_);
lean_dec(v_a_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_satPow(lean_object* v_a_17_, lean_object* v_k_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_19_ = lean_unsigned_to_nat(4194304u);
v___x_20_ = lean_nat_log2(v_a_17_);
v___x_21_ = lean_nat_dec_le(v___x_19_, v___x_20_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_22_ = lean_unsigned_to_nat(1u);
v___x_23_ = lean_nat_dec_le(v_a_17_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_24_ = lean_nat_mul(v_k_18_, v___x_20_);
lean_dec(v___x_20_);
v___x_25_ = lean_nat_dec_lt(v___x_24_, v___x_19_);
lean_dec(v___x_24_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; 
v___x_26_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_satMul___closed__0, &l_Lean_Meta_Sym_Arith_satMul___closed__0_once, _init_l_Lean_Meta_Sym_Arith_satMul___closed__0);
return v___x_26_;
}
else
{
lean_object* v___x_27_; 
v___x_27_ = lean_nat_pow(v_a_17_, v_k_18_);
return v___x_27_;
}
}
else
{
lean_object* v___x_28_; 
lean_dec(v___x_20_);
v___x_28_ = lean_nat_pow(v_a_17_, v_k_18_);
return v___x_28_;
}
}
else
{
lean_dec(v___x_20_);
lean_inc(v_a_17_);
return v_a_17_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_satPow___boxed(lean_object* v_a_29_, lean_object* v_k_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Meta_Sym_Arith_satPow(v_a_29_, v_k_30_);
lean_dec(v_k_30_);
lean_dec(v_a_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprDegB(lean_object* v_x_32_){
_start:
{
lean_object* v_a_34_; lean_object* v_b_35_; 
switch(lean_obj_tag(v_x_32_))
{
case 3:
{
lean_object* v___x_39_; 
v___x_39_ = lean_unsigned_to_nat(1u);
return v___x_39_;
}
case 4:
{
lean_object* v_a_40_; 
v_a_40_ = lean_ctor_get(v_x_32_, 0);
v_x_32_ = v_a_40_;
goto _start;
}
case 5:
{
lean_object* v_a_42_; lean_object* v_b_43_; 
v_a_42_ = lean_ctor_get(v_x_32_, 0);
v_b_43_ = lean_ctor_get(v_x_32_, 1);
v_a_34_ = v_a_42_;
v_b_35_ = v_b_43_;
goto v___jp_33_;
}
case 6:
{
lean_object* v_a_44_; lean_object* v_b_45_; 
v_a_44_ = lean_ctor_get(v_x_32_, 0);
v_b_45_ = lean_ctor_get(v_x_32_, 1);
v_a_34_ = v_a_44_;
v_b_35_ = v_b_45_;
goto v___jp_33_;
}
case 7:
{
lean_object* v_a_46_; lean_object* v_b_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_a_46_ = lean_ctor_get(v_x_32_, 0);
v_b_47_ = lean_ctor_get(v_x_32_, 1);
v___x_48_ = l_Lean_Meta_Sym_Arith_exprDegB(v_a_46_);
v___x_49_ = l_Lean_Meta_Sym_Arith_exprDegB(v_b_47_);
v___x_50_ = lean_nat_add(v___x_48_, v___x_49_);
lean_dec(v___x_49_);
lean_dec(v___x_48_);
return v___x_50_;
}
case 8:
{
lean_object* v_a_51_; lean_object* v_k_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v_a_51_ = lean_ctor_get(v_x_32_, 0);
v_k_52_ = lean_ctor_get(v_x_32_, 1);
v___x_53_ = l_Lean_Meta_Sym_Arith_exprDegB(v_a_51_);
v___x_54_ = lean_nat_mul(v___x_53_, v_k_52_);
lean_dec(v___x_53_);
return v___x_54_;
}
default: 
{
lean_object* v___x_55_; 
v___x_55_ = lean_unsigned_to_nat(0u);
return v___x_55_;
}
}
v___jp_33_:
{
lean_object* v___x_36_; lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_36_ = l_Lean_Meta_Sym_Arith_exprDegB(v_a_34_);
v___x_37_ = l_Lean_Meta_Sym_Arith_exprDegB(v_b_35_);
v___x_38_ = lean_nat_dec_le(v___x_36_, v___x_37_);
if (v___x_38_ == 0)
{
lean_dec(v___x_37_);
return v___x_36_;
}
else
{
lean_dec(v___x_36_);
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprDegB___boxed(lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Meta_Sym_Arith_exprDegB(v_x_56_);
lean_dec_ref(v_x_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprLin(lean_object* v_x_58_){
_start:
{
lean_object* v_a_60_; lean_object* v_b_61_; 
switch(lean_obj_tag(v_x_58_))
{
case 3:
{
lean_object* v___x_65_; 
v___x_65_ = lean_unsigned_to_nat(1u);
return v___x_65_;
}
case 4:
{
lean_object* v_a_66_; 
v_a_66_ = lean_ctor_get(v_x_58_, 0);
v_x_58_ = v_a_66_;
goto _start;
}
case 5:
{
lean_object* v_a_68_; lean_object* v_b_69_; 
v_a_68_ = lean_ctor_get(v_x_58_, 0);
v_b_69_ = lean_ctor_get(v_x_58_, 1);
v_a_60_ = v_a_68_;
v_b_61_ = v_b_69_;
goto v___jp_59_;
}
case 6:
{
lean_object* v_a_70_; lean_object* v_b_71_; 
v_a_70_ = lean_ctor_get(v_x_58_, 0);
v_b_71_ = lean_ctor_get(v_x_58_, 1);
v_a_60_ = v_a_70_;
v_b_61_ = v_b_71_;
goto v___jp_59_;
}
case 7:
{
lean_object* v_a_72_; lean_object* v_b_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_a_72_ = lean_ctor_get(v_x_58_, 0);
v_b_73_ = lean_ctor_get(v_x_58_, 1);
v___x_74_ = l_Lean_Meta_Sym_Arith_exprLin(v_a_72_);
v___x_75_ = l_Lean_Meta_Sym_Arith_exprLin(v_b_73_);
v___x_76_ = lean_nat_add(v___x_74_, v___x_75_);
lean_dec(v___x_75_);
lean_dec(v___x_74_);
return v___x_76_;
}
case 8:
{
lean_object* v_a_77_; lean_object* v_k_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_a_77_ = lean_ctor_get(v_x_58_, 0);
v_k_78_ = lean_ctor_get(v_x_58_, 1);
v___x_79_ = l_Lean_Meta_Sym_Arith_exprLin(v_a_77_);
v___x_80_ = lean_nat_mul(v___x_79_, v_k_78_);
lean_dec(v___x_79_);
return v___x_80_;
}
default: 
{
lean_object* v___x_81_; 
v___x_81_ = lean_unsigned_to_nat(0u);
return v___x_81_;
}
}
v___jp_59_:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = l_Lean_Meta_Sym_Arith_exprLin(v_a_60_);
v___x_63_ = l_Lean_Meta_Sym_Arith_exprLin(v_b_61_);
v___x_64_ = lean_nat_lor(v___x_62_, v___x_63_);
lean_dec(v___x_63_);
lean_dec(v___x_62_);
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprLin___boxed(lean_object* v_x_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Meta_Sym_Arith_exprLin(v_x_82_);
lean_dec_ref(v_x_82_);
return v_res_83_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_exprLinS___closed__0(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = lean_nat_to_int(v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprLinS(lean_object* v_x_86_){
_start:
{
switch(lean_obj_tag(v_x_86_))
{
case 0:
{
lean_object* v_k_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_k_87_ = lean_ctor_get(v_x_86_, 0);
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_89_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_exprLinS___closed__0, &l_Lean_Meta_Sym_Arith_exprLinS___closed__0_once, _init_l_Lean_Meta_Sym_Arith_exprLinS___closed__0);
v___x_90_ = lean_int_dec_le(v___x_89_, v_k_87_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; 
v___x_91_ = lean_unsigned_to_nat(2u);
return v___x_91_;
}
else
{
return v___x_88_;
}
}
case 1:
{
lean_object* v___x_92_; 
v___x_92_ = lean_unsigned_to_nat(0u);
return v___x_92_;
}
case 3:
{
lean_object* v___x_93_; 
v___x_93_ = lean_unsigned_to_nat(1u);
return v___x_93_;
}
case 5:
{
lean_object* v_a_94_; lean_object* v_b_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v_a_94_ = lean_ctor_get(v_x_86_, 0);
v_b_95_ = lean_ctor_get(v_x_86_, 1);
v___x_96_ = l_Lean_Meta_Sym_Arith_exprLinS(v_a_94_);
v___x_97_ = l_Lean_Meta_Sym_Arith_exprLinS(v_b_95_);
v___x_98_ = lean_nat_lor(v___x_96_, v___x_97_);
lean_dec(v___x_97_);
lean_dec(v___x_96_);
return v___x_98_;
}
case 7:
{
lean_object* v_a_99_; lean_object* v_b_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_a_99_ = lean_ctor_get(v_x_86_, 0);
v_b_100_ = lean_ctor_get(v_x_86_, 1);
v___x_101_ = l_Lean_Meta_Sym_Arith_exprLinS(v_a_99_);
v___x_102_ = l_Lean_Meta_Sym_Arith_exprLinS(v_b_100_);
v___x_103_ = lean_nat_add(v___x_101_, v___x_102_);
lean_dec(v___x_102_);
lean_dec(v___x_101_);
return v___x_103_;
}
case 8:
{
lean_object* v_a_104_; lean_object* v_k_105_; lean_object* v_d_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_a_104_ = lean_ctor_get(v_x_86_, 0);
v_k_105_ = lean_ctor_get(v_x_86_, 1);
v_d_106_ = l_Lean_Meta_Sym_Arith_exprLinS(v_a_104_);
v___x_107_ = lean_unsigned_to_nat(2u);
v___x_108_ = lean_nat_dec_le(v___x_107_, v_d_106_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
v___x_109_ = lean_nat_mul(v_d_106_, v_k_105_);
lean_dec(v_d_106_);
return v___x_109_;
}
else
{
lean_dec(v_d_106_);
return v___x_107_;
}
}
default: 
{
lean_object* v___x_110_; 
v___x_110_ = lean_unsigned_to_nat(2u);
return v___x_110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprLinS___boxed(lean_object* v_x_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_Meta_Sym_Arith_exprLinS(v_x_111_);
lean_dec_ref(v_x_111_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprDegS(lean_object* v_B_113_, lean_object* v_x_114_){
_start:
{
switch(lean_obj_tag(v_x_114_))
{
case 0:
{
lean_object* v_k_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v_k_115_ = lean_ctor_get(v_x_114_, 0);
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_exprLinS___closed__0, &l_Lean_Meta_Sym_Arith_exprLinS___closed__0_once, _init_l_Lean_Meta_Sym_Arith_exprLinS___closed__0);
v___x_118_ = lean_int_dec_le(v___x_117_, v_k_115_);
if (v___x_118_ == 0)
{
lean_inc(v_B_113_);
return v_B_113_;
}
else
{
return v___x_116_;
}
}
case 1:
{
lean_object* v___x_119_; 
v___x_119_ = lean_unsigned_to_nat(0u);
return v___x_119_;
}
case 3:
{
lean_object* v___x_120_; 
v___x_120_ = lean_unsigned_to_nat(1u);
return v___x_120_;
}
case 5:
{
lean_object* v_a_121_; lean_object* v_b_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v_a_121_ = lean_ctor_get(v_x_114_, 0);
v_b_122_ = lean_ctor_get(v_x_114_, 1);
v___x_123_ = l_Lean_Meta_Sym_Arith_exprDegS(v_B_113_, v_a_121_);
v___x_124_ = l_Lean_Meta_Sym_Arith_exprDegS(v_B_113_, v_b_122_);
v___x_125_ = lean_nat_dec_le(v___x_123_, v___x_124_);
if (v___x_125_ == 0)
{
lean_dec(v___x_124_);
return v___x_123_;
}
else
{
lean_dec(v___x_123_);
return v___x_124_;
}
}
case 7:
{
lean_object* v_a_126_; lean_object* v_b_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_a_126_ = lean_ctor_get(v_x_114_, 0);
v_b_127_ = lean_ctor_get(v_x_114_, 1);
v___x_128_ = l_Lean_Meta_Sym_Arith_exprDegS(v_B_113_, v_a_126_);
v___x_129_ = l_Lean_Meta_Sym_Arith_exprDegS(v_B_113_, v_b_127_);
v___x_130_ = lean_nat_add(v___x_128_, v___x_129_);
lean_dec(v___x_129_);
lean_dec(v___x_128_);
return v___x_130_;
}
case 8:
{
lean_object* v_a_131_; lean_object* v_k_132_; lean_object* v_d_133_; uint8_t v___x_134_; 
v_a_131_ = lean_ctor_get(v_x_114_, 0);
v_k_132_ = lean_ctor_get(v_x_114_, 1);
v_d_133_ = l_Lean_Meta_Sym_Arith_exprDegS(v_B_113_, v_a_131_);
v___x_134_ = lean_nat_dec_le(v_B_113_, v_d_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; 
v___x_135_ = lean_nat_mul(v_d_133_, v_k_132_);
lean_dec(v_d_133_);
return v___x_135_;
}
else
{
lean_dec(v_d_133_);
lean_inc(v_B_113_);
return v_B_113_;
}
}
default: 
{
lean_inc(v_B_113_);
return v_B_113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprDegS___boxed(lean_object* v_B_136_, lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Meta_Sym_Arith_exprDegS(v_B_136_, v_x_137_);
lean_dec_ref(v_x_137_);
lean_dec(v_B_136_);
return v_res_138_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_exprExpandsSum_isSum(lean_object* v_e_139_){
_start:
{
if (lean_obj_tag(v_e_139_) == 5)
{
goto v___jp_140_;
}
else
{
if (lean_obj_tag(v_e_139_) == 6)
{
goto v___jp_140_;
}
else
{
uint8_t v___x_144_; 
v___x_144_ = 0;
return v___x_144_;
}
}
v___jp_140_:
{
lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_141_ = lean_unsigned_to_nat(1u);
v___x_142_ = l_Lean_Meta_Sym_Arith_exprDegB(v_e_139_);
v___x_143_ = lean_nat_dec_le(v___x_141_, v___x_142_);
lean_dec(v___x_142_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_exprExpandsSum_isSum___boxed(lean_object* v_e_145_){
_start:
{
uint8_t v_res_146_; lean_object* v_r_147_; 
v_res_146_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_exprExpandsSum_isSum(v_e_145_);
lean_dec_ref(v_e_145_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_Arith_exprExpandsSum(lean_object* v_x_148_){
_start:
{
lean_object* v_a_150_; lean_object* v_b_151_; 
switch(lean_obj_tag(v_x_148_))
{
case 7:
{
lean_object* v_a_154_; lean_object* v_b_155_; uint8_t v___x_164_; 
v_a_154_ = lean_ctor_get(v_x_148_, 0);
v_b_155_ = lean_ctor_get(v_x_148_, 1);
v___x_164_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_exprExpandsSum_isSum(v_a_154_);
if (v___x_164_ == 0)
{
goto v___jp_159_;
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = l_Lean_Meta_Sym_Arith_exprDegB(v_b_155_);
v___x_167_ = lean_nat_dec_le(v___x_165_, v___x_166_);
lean_dec(v___x_166_);
if (v___x_167_ == 0)
{
goto v___jp_159_;
}
else
{
return v___x_167_;
}
}
v___jp_156_:
{
uint8_t v___x_157_; 
v___x_157_ = l_Lean_Meta_Sym_Arith_exprExpandsSum(v_a_154_);
if (v___x_157_ == 0)
{
v_x_148_ = v_b_155_;
goto _start;
}
else
{
return v___x_157_;
}
}
v___jp_159_:
{
uint8_t v___x_160_; 
v___x_160_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_exprExpandsSum_isSum(v_b_155_);
if (v___x_160_ == 0)
{
goto v___jp_156_;
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = l_Lean_Meta_Sym_Arith_exprDegB(v_a_154_);
v___x_163_ = lean_nat_dec_le(v___x_161_, v___x_162_);
lean_dec(v___x_162_);
if (v___x_163_ == 0)
{
goto v___jp_156_;
}
else
{
return v___x_163_;
}
}
}
}
case 8:
{
lean_object* v_a_168_; lean_object* v_k_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v_a_168_ = lean_ctor_get(v_x_148_, 0);
v_k_169_ = lean_ctor_get(v_x_148_, 1);
v___x_170_ = lean_unsigned_to_nat(2u);
v___x_171_ = lean_nat_dec_le(v___x_170_, v_k_169_);
if (v___x_171_ == 0)
{
v_x_148_ = v_a_168_;
goto _start;
}
else
{
uint8_t v___x_173_; 
v___x_173_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_exprExpandsSum_isSum(v_a_168_);
if (v___x_173_ == 0)
{
v_x_148_ = v_a_168_;
goto _start;
}
else
{
return v___x_173_;
}
}
}
case 5:
{
lean_object* v_a_175_; lean_object* v_b_176_; 
v_a_175_ = lean_ctor_get(v_x_148_, 0);
v_b_176_ = lean_ctor_get(v_x_148_, 1);
v_a_150_ = v_a_175_;
v_b_151_ = v_b_176_;
goto v___jp_149_;
}
case 6:
{
lean_object* v_a_177_; lean_object* v_b_178_; 
v_a_177_ = lean_ctor_get(v_x_148_, 0);
v_b_178_ = lean_ctor_get(v_x_148_, 1);
v_a_150_ = v_a_177_;
v_b_151_ = v_b_178_;
goto v___jp_149_;
}
case 4:
{
lean_object* v_a_179_; 
v_a_179_ = lean_ctor_get(v_x_148_, 0);
v_x_148_ = v_a_179_;
goto _start;
}
default: 
{
uint8_t v___x_181_; 
v___x_181_ = 0;
return v___x_181_;
}
}
v___jp_149_:
{
uint8_t v___x_152_; 
v___x_152_ = l_Lean_Meta_Sym_Arith_exprExpandsSum(v_a_150_);
if (v___x_152_ == 0)
{
v_x_148_ = v_b_151_;
goto _start;
}
else
{
return v___x_152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprExpandsSum___boxed(lean_object* v_x_182_){
_start:
{
uint8_t v_res_183_; lean_object* v_r_184_; 
v_res_183_ = l_Lean_Meta_Sym_Arith_exprExpandsSum(v_x_182_);
lean_dec_ref(v_x_182_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprMajorant(lean_object* v_x_185_){
_start:
{
lean_object* v_a_187_; lean_object* v_b_188_; 
switch(lean_obj_tag(v_x_185_))
{
case 1:
{
lean_object* v_k_192_; 
v_k_192_ = lean_ctor_get(v_x_185_, 0);
lean_inc(v_k_192_);
return v_k_192_;
}
case 3:
{
lean_object* v___x_193_; 
v___x_193_ = lean_unsigned_to_nat(1u);
return v___x_193_;
}
case 4:
{
lean_object* v_a_194_; 
v_a_194_ = lean_ctor_get(v_x_185_, 0);
v_x_185_ = v_a_194_;
goto _start;
}
case 5:
{
lean_object* v_a_196_; lean_object* v_b_197_; 
v_a_196_ = lean_ctor_get(v_x_185_, 0);
v_b_197_ = lean_ctor_get(v_x_185_, 1);
v_a_187_ = v_a_196_;
v_b_188_ = v_b_197_;
goto v___jp_186_;
}
case 6:
{
lean_object* v_a_198_; lean_object* v_b_199_; 
v_a_198_ = lean_ctor_get(v_x_185_, 0);
v_b_199_ = lean_ctor_get(v_x_185_, 1);
v_a_187_ = v_a_198_;
v_b_188_ = v_b_199_;
goto v___jp_186_;
}
case 7:
{
lean_object* v_a_200_; lean_object* v_b_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_a_200_ = lean_ctor_get(v_x_185_, 0);
v_b_201_ = lean_ctor_get(v_x_185_, 1);
v___x_202_ = l_Lean_Meta_Sym_Arith_exprMajorant(v_a_200_);
v___x_203_ = l_Lean_Meta_Sym_Arith_exprMajorant(v_b_201_);
v___x_204_ = l_Lean_Meta_Sym_Arith_satMul(v___x_202_, v___x_203_);
lean_dec(v___x_203_);
lean_dec(v___x_202_);
return v___x_204_;
}
case 8:
{
lean_object* v_a_205_; lean_object* v_k_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_a_205_ = lean_ctor_get(v_x_185_, 0);
v_k_206_ = lean_ctor_get(v_x_185_, 1);
v___x_207_ = l_Lean_Meta_Sym_Arith_exprMajorant(v_a_205_);
v___x_208_ = l_Lean_Meta_Sym_Arith_satPow(v___x_207_, v_k_206_);
lean_dec(v___x_207_);
return v___x_208_;
}
default: 
{
lean_object* v_k_209_; lean_object* v___x_210_; 
v_k_209_ = lean_ctor_get(v_x_185_, 0);
v___x_210_ = lean_nat_abs(v_k_209_);
return v___x_210_;
}
}
v___jp_186_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = l_Lean_Meta_Sym_Arith_exprMajorant(v_a_187_);
v___x_190_ = l_Lean_Meta_Sym_Arith_exprMajorant(v_b_188_);
v___x_191_ = lean_nat_add(v___x_189_, v___x_190_);
lean_dec(v___x_190_);
lean_dec(v___x_189_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprMajorant___boxed(lean_object* v_x_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Meta_Sym_Arith_exprMajorant(v_x_211_);
lean_dec_ref(v_x_211_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_polyMaxDeg(lean_object* v_x_213_){
_start:
{
if (lean_obj_tag(v_x_213_) == 0)
{
lean_object* v___x_214_; 
v___x_214_ = lean_unsigned_to_nat(0u);
return v___x_214_;
}
else
{
lean_object* v_v_215_; lean_object* v_p_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v_v_215_ = lean_ctor_get(v_x_213_, 1);
v_p_216_ = lean_ctor_get(v_x_213_, 2);
v___x_217_ = l_Lean_Grind_CommRing_Mon_degree(v_v_215_);
v___x_218_ = l_Lean_Meta_Sym_Arith_polyMaxDeg(v_p_216_);
v___x_219_ = lean_nat_dec_le(v___x_217_, v___x_218_);
if (v___x_219_ == 0)
{
lean_dec(v___x_218_);
return v___x_217_;
}
else
{
lean_dec(v___x_217_);
return v___x_218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_polyMaxDeg___boxed(lean_object* v_x_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Meta_Sym_Arith_polyMaxDeg(v_x_220_);
lean_dec_ref(v_x_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_polyNorm1(lean_object* v_x_222_){
_start:
{
if (lean_obj_tag(v_x_222_) == 0)
{
lean_object* v_k_223_; lean_object* v___x_224_; 
v_k_223_ = lean_ctor_get(v_x_222_, 0);
v___x_224_ = lean_nat_abs(v_k_223_);
return v___x_224_;
}
else
{
lean_object* v_k_225_; lean_object* v_p_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_k_225_ = lean_ctor_get(v_x_222_, 0);
v_p_226_ = lean_ctor_get(v_x_222_, 2);
v___x_227_ = lean_nat_abs(v_k_225_);
v___x_228_ = l_Lean_Meta_Sym_Arith_polyNorm1(v_p_226_);
v___x_229_ = lean_nat_add(v___x_227_, v___x_228_);
lean_dec(v___x_228_);
lean_dec(v___x_227_);
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_polyNorm1___boxed(lean_object* v_x_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Meta_Sym_Arith_polyNorm1(v_x_230_);
lean_dec_ref(v_x_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_monCode(lean_object* v_B_232_, lean_object* v_x_233_){
_start:
{
if (lean_obj_tag(v_x_233_) == 0)
{
lean_object* v___x_234_; 
v___x_234_ = lean_unsigned_to_nat(0u);
return v___x_234_;
}
else
{
lean_object* v_p_235_; lean_object* v_m_236_; lean_object* v_x_237_; lean_object* v_k_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_p_235_ = lean_ctor_get(v_x_233_, 0);
v_m_236_ = lean_ctor_get(v_x_233_, 1);
v_x_237_ = lean_ctor_get(v_p_235_, 0);
v_k_238_ = lean_ctor_get(v_p_235_, 1);
v___x_239_ = lean_nat_pow(v_B_232_, v_x_237_);
v___x_240_ = lean_nat_mul(v_k_238_, v___x_239_);
lean_dec(v___x_239_);
v___x_241_ = l_Lean_Meta_Sym_Arith_monCode(v_B_232_, v_m_236_);
v___x_242_ = lean_nat_add(v___x_240_, v___x_241_);
lean_dec(v___x_241_);
lean_dec(v___x_240_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_monCode___boxed(lean_object* v_B_243_, lean_object* v_x_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Meta_Sym_Arith_monCode(v_B_243_, v_x_244_);
lean_dec(v_x_244_);
lean_dec(v_B_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_polyMaxCode(lean_object* v_B_246_, lean_object* v_x_247_){
_start:
{
if (lean_obj_tag(v_x_247_) == 0)
{
lean_object* v___x_248_; 
v___x_248_ = lean_unsigned_to_nat(0u);
return v___x_248_;
}
else
{
lean_object* v_v_249_; lean_object* v_p_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v_v_249_ = lean_ctor_get(v_x_247_, 1);
v_p_250_ = lean_ctor_get(v_x_247_, 2);
v___x_251_ = l_Lean_Meta_Sym_Arith_monCode(v_B_246_, v_v_249_);
v___x_252_ = l_Lean_Meta_Sym_Arith_polyMaxCode(v_B_246_, v_p_250_);
v___x_253_ = lean_nat_dec_le(v___x_251_, v___x_252_);
if (v___x_253_ == 0)
{
lean_dec(v___x_252_);
return v___x_251_;
}
else
{
lean_dec(v___x_251_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_polyMaxCode___boxed(lean_object* v_B_254_, lean_object* v_x_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Meta_Sym_Arith_polyMaxCode(v_B_254_, v_x_255_);
lean_dec_ref(v_x_255_);
lean_dec(v_B_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprMaxCode(lean_object* v_B_257_, lean_object* v_x_258_){
_start:
{
lean_object* v_a_260_; lean_object* v_b_261_; 
switch(lean_obj_tag(v_x_258_))
{
case 3:
{
lean_object* v_i_265_; lean_object* v___x_266_; 
v_i_265_ = lean_ctor_get(v_x_258_, 0);
v___x_266_ = l_Lean_Meta_Sym_Arith_satPow(v_B_257_, v_i_265_);
return v___x_266_;
}
case 4:
{
lean_object* v_a_267_; 
v_a_267_ = lean_ctor_get(v_x_258_, 0);
v_x_258_ = v_a_267_;
goto _start;
}
case 5:
{
lean_object* v_a_269_; lean_object* v_b_270_; 
v_a_269_ = lean_ctor_get(v_x_258_, 0);
v_b_270_ = lean_ctor_get(v_x_258_, 1);
v_a_260_ = v_a_269_;
v_b_261_ = v_b_270_;
goto v___jp_259_;
}
case 6:
{
lean_object* v_a_271_; lean_object* v_b_272_; 
v_a_271_ = lean_ctor_get(v_x_258_, 0);
v_b_272_ = lean_ctor_get(v_x_258_, 1);
v_a_260_ = v_a_271_;
v_b_261_ = v_b_272_;
goto v___jp_259_;
}
case 7:
{
lean_object* v_a_273_; lean_object* v_b_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_a_273_ = lean_ctor_get(v_x_258_, 0);
v_b_274_ = lean_ctor_get(v_x_258_, 1);
v___x_275_ = l_Lean_Meta_Sym_Arith_exprMaxCode(v_B_257_, v_a_273_);
v___x_276_ = l_Lean_Meta_Sym_Arith_exprMaxCode(v_B_257_, v_b_274_);
v___x_277_ = lean_nat_add(v___x_275_, v___x_276_);
lean_dec(v___x_276_);
lean_dec(v___x_275_);
return v___x_277_;
}
case 8:
{
lean_object* v_a_278_; lean_object* v_k_279_; lean_object* v_c_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v_a_278_ = lean_ctor_get(v_x_258_, 0);
v_k_279_ = lean_ctor_get(v_x_258_, 1);
v_c_280_ = l_Lean_Meta_Sym_Arith_exprMaxCode(v_B_257_, v_a_278_);
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = lean_nat_dec_eq(v_k_279_, v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Meta_Sym_Arith_satMul(v_c_280_, v_k_279_);
lean_dec(v_c_280_);
return v___x_283_;
}
else
{
return v_c_280_;
}
}
default: 
{
lean_object* v___x_284_; 
v___x_284_ = lean_unsigned_to_nat(0u);
return v___x_284_;
}
}
v___jp_259_:
{
lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_262_ = l_Lean_Meta_Sym_Arith_exprMaxCode(v_B_257_, v_a_260_);
v___x_263_ = l_Lean_Meta_Sym_Arith_exprMaxCode(v_B_257_, v_b_261_);
v___x_264_ = lean_nat_dec_le(v___x_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_dec(v___x_263_);
return v___x_262_;
}
else
{
lean_dec(v___x_262_);
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprMaxCode___boxed(lean_object* v_B_285_, lean_object* v_x_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Meta_Sym_Arith_exprMaxCode(v_B_285_, v_x_286_);
lean_dec_ref(v_x_286_);
lean_dec(v_B_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_kronExponent_x3f(lean_object* v_norm_288_, lean_object* v_maxCode_289_, lean_object* v_maxBits_290_){
_start:
{
uint8_t v___x_291_; 
v___x_291_ = lean_nat_dec_lt(v_maxBits_290_, v_maxCode_289_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v_K_296_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_292_ = lean_unsigned_to_nat(2u);
v___x_293_ = lean_nat_mul(v___x_292_, v_norm_288_);
v___x_294_ = lean_nat_log2(v___x_293_);
lean_dec(v___x_293_);
v___x_295_ = lean_unsigned_to_nat(1u);
v_K_296_ = lean_nat_add(v___x_294_, v___x_295_);
lean_dec(v___x_294_);
v___x_297_ = lean_nat_add(v_maxCode_289_, v___x_295_);
v___x_298_ = lean_nat_mul(v_K_296_, v___x_297_);
lean_dec(v___x_297_);
v___x_299_ = lean_nat_dec_lt(v_maxBits_290_, v___x_298_);
lean_dec(v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
v___x_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_300_, 0, v_K_296_);
return v___x_300_;
}
else
{
lean_object* v___x_301_; 
lean_dec(v_K_296_);
v___x_301_ = lean_box(0);
return v___x_301_;
}
}
else
{
lean_object* v___x_302_; 
v___x_302_ = lean_box(0);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_kronExponent_x3f___boxed(lean_object* v_norm_303_, lean_object* v_maxCode_304_, lean_object* v_maxBits_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Meta_Sym_Arith_kronExponent_x3f(v_norm_303_, v_maxCode_304_, v_maxBits_305_);
lean_dec(v_maxBits_305_);
lean_dec(v_maxCode_304_);
lean_dec(v_norm_303_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprLinCode(lean_object* v_x_307_){
_start:
{
lean_object* v_a_309_; lean_object* v_b_310_; 
switch(lean_obj_tag(v_x_307_))
{
case 3:
{
lean_object* v_i_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v_i_314_ = lean_ctor_get(v_x_307_, 0);
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_add(v_i_314_, v___x_315_);
return v___x_316_;
}
case 4:
{
lean_object* v_a_317_; 
v_a_317_ = lean_ctor_get(v_x_307_, 0);
v_x_307_ = v_a_317_;
goto _start;
}
case 5:
{
lean_object* v_a_319_; lean_object* v_b_320_; 
v_a_319_ = lean_ctor_get(v_x_307_, 0);
v_b_320_ = lean_ctor_get(v_x_307_, 1);
v_a_309_ = v_a_319_;
v_b_310_ = v_b_320_;
goto v___jp_308_;
}
case 6:
{
lean_object* v_a_321_; lean_object* v_b_322_; 
v_a_321_ = lean_ctor_get(v_x_307_, 0);
v_b_322_ = lean_ctor_get(v_x_307_, 1);
v_a_309_ = v_a_321_;
v_b_310_ = v_b_322_;
goto v___jp_308_;
}
case 7:
{
lean_object* v_a_323_; lean_object* v_b_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_a_323_ = lean_ctor_get(v_x_307_, 0);
v_b_324_ = lean_ctor_get(v_x_307_, 1);
v___x_325_ = l_Lean_Meta_Sym_Arith_exprLinCode(v_a_323_);
v___x_326_ = l_Lean_Meta_Sym_Arith_exprLinCode(v_b_324_);
v___x_327_ = lean_nat_add(v___x_325_, v___x_326_);
lean_dec(v___x_326_);
lean_dec(v___x_325_);
return v___x_327_;
}
case 8:
{
lean_object* v_a_328_; lean_object* v_k_329_; lean_object* v_c_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v_a_328_ = lean_ctor_get(v_x_307_, 0);
v_k_329_ = lean_ctor_get(v_x_307_, 1);
v_c_330_ = l_Lean_Meta_Sym_Arith_exprLinCode(v_a_328_);
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = lean_nat_dec_eq(v_k_329_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_Meta_Sym_Arith_satMul(v_c_330_, v_k_329_);
lean_dec(v_c_330_);
return v___x_333_;
}
else
{
return v_c_330_;
}
}
default: 
{
lean_object* v___x_334_; 
v___x_334_ = lean_unsigned_to_nat(0u);
return v___x_334_;
}
}
v___jp_308_:
{
lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_311_ = l_Lean_Meta_Sym_Arith_exprLinCode(v_a_309_);
v___x_312_ = l_Lean_Meta_Sym_Arith_exprLinCode(v_b_310_);
v___x_313_ = lean_nat_dec_le(v___x_311_, v___x_312_);
if (v___x_313_ == 0)
{
lean_dec(v___x_312_);
return v___x_311_;
}
else
{
lean_dec(v___x_311_);
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprLinCode___boxed(lean_object* v_x_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Meta_Sym_Arith_exprLinCode(v_x_335_);
lean_dec_ref(v_x_335_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_kronLinExponent_x3f(lean_object* v_l_337_, lean_object* v_r_338_, lean_object* v_maxBits_339_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_340_ = l_Lean_Meta_Sym_Arith_exprLin(v_l_337_);
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = lean_nat_dec_le(v___x_340_, v___x_341_);
lean_dec(v___x_340_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
v___x_343_ = lean_box(0);
return v___x_343_;
}
else
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = l_Lean_Meta_Sym_Arith_exprLin(v_r_338_);
v___x_345_ = lean_nat_dec_le(v___x_344_, v___x_341_);
lean_dec(v___x_344_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; 
v___x_346_ = lean_box(0);
return v___x_346_;
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_347_ = l_Lean_Meta_Sym_Arith_exprMajorant(v_l_337_);
v___x_348_ = l_Lean_Meta_Sym_Arith_exprMajorant(v_r_338_);
v___x_349_ = lean_nat_add(v___x_347_, v___x_348_);
lean_dec(v___x_348_);
lean_dec(v___x_347_);
v___x_350_ = l_Lean_Meta_Sym_Arith_exprLinCode(v_l_337_);
v___x_351_ = l_Lean_Meta_Sym_Arith_exprLinCode(v_r_338_);
v___x_352_ = lean_nat_dec_le(v___x_350_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; 
lean_dec(v___x_351_);
v___x_353_ = l_Lean_Meta_Sym_Arith_kronExponent_x3f(v___x_349_, v___x_350_, v_maxBits_339_);
lean_dec(v___x_350_);
lean_dec(v___x_349_);
return v___x_353_;
}
else
{
lean_object* v___x_354_; 
lean_dec(v___x_350_);
v___x_354_ = l_Lean_Meta_Sym_Arith_kronExponent_x3f(v___x_349_, v___x_351_, v_maxBits_339_);
lean_dec(v___x_351_);
lean_dec(v___x_349_);
return v___x_354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_kronLinExponent_x3f___boxed(lean_object* v_l_355_, lean_object* v_r_356_, lean_object* v_maxBits_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Meta_Sym_Arith_kronLinExponent_x3f(v_l_355_, v_r_356_, v_maxBits_357_);
lean_dec(v_maxBits_357_);
lean_dec_ref(v_r_356_);
lean_dec_ref(v_l_355_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_invLookup(lean_object* v_invs_359_, lean_object* v_x_360_){
_start:
{
if (lean_obj_tag(v_invs_359_) == 0)
{
lean_object* v___x_361_; 
v___x_361_ = lean_box(0);
return v___x_361_;
}
else
{
lean_object* v_head_362_; lean_object* v_tail_363_; lean_object* v_fst_364_; lean_object* v_snd_365_; uint8_t v___x_366_; 
v_head_362_ = lean_ctor_get(v_invs_359_, 0);
v_tail_363_ = lean_ctor_get(v_invs_359_, 1);
v_fst_364_ = lean_ctor_get(v_head_362_, 0);
v_snd_365_ = lean_ctor_get(v_head_362_, 1);
v___x_366_ = lean_nat_dec_lt(v_x_360_, v_fst_364_);
if (v___x_366_ == 0)
{
uint8_t v___x_367_; 
v___x_367_ = lean_nat_dec_eq(v_fst_364_, v_x_360_);
if (v___x_367_ == 0)
{
v_invs_359_ = v_tail_363_;
goto _start;
}
else
{
lean_object* v___x_369_; 
lean_inc(v_snd_365_);
v___x_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_369_, 0, v_snd_365_);
return v___x_369_;
}
}
else
{
lean_object* v___x_370_; 
v___x_370_ = lean_box(0);
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_invLookup___boxed(lean_object* v_invs_371_, lean_object* v_x_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Meta_Sym_Arith_invLookup(v_invs_371_, v_x_372_);
lean_dec(v_x_372_);
lean_dec(v_invs_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprMajQ(lean_object* v_invs_376_, lean_object* v_x_377_){
_start:
{
lean_object* v_k_379_; lean_object* v_a_384_; lean_object* v_b_385_; 
switch(lean_obj_tag(v_x_377_))
{
case 1:
{
lean_object* v_k_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v_k_403_ = lean_ctor_get(v_x_377_, 0);
v___x_404_ = lean_unsigned_to_nat(1u);
lean_inc(v_k_403_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v_k_403_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
return v___x_405_;
}
case 3:
{
lean_object* v_i_406_; lean_object* v___x_407_; 
v_i_406_ = lean_ctor_get(v_x_377_, 0);
v___x_407_ = l_Lean_Meta_Sym_Arith_invLookup(v_invs_376_, v_i_406_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v___x_408_; 
v___x_408_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_exprMajQ___closed__0));
return v___x_408_;
}
else
{
lean_object* v_val_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_val_409_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_val_409_);
lean_dec_ref_known(v___x_407_, 1);
v___x_410_ = lean_unsigned_to_nat(1u);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_val_409_);
return v___x_411_;
}
}
case 4:
{
lean_object* v_a_412_; 
v_a_412_ = lean_ctor_get(v_x_377_, 0);
v_x_377_ = v_a_412_;
goto _start;
}
case 5:
{
lean_object* v_a_414_; lean_object* v_b_415_; 
v_a_414_ = lean_ctor_get(v_x_377_, 0);
v_b_415_ = lean_ctor_get(v_x_377_, 1);
v_a_384_ = v_a_414_;
v_b_385_ = v_b_415_;
goto v___jp_383_;
}
case 6:
{
lean_object* v_a_416_; lean_object* v_b_417_; 
v_a_416_ = lean_ctor_get(v_x_377_, 0);
v_b_417_ = lean_ctor_get(v_x_377_, 1);
v_a_384_ = v_a_416_;
v_b_385_ = v_b_417_;
goto v___jp_383_;
}
case 7:
{
lean_object* v_a_418_; lean_object* v_b_419_; lean_object* v___x_420_; lean_object* v_fst_421_; lean_object* v_snd_422_; lean_object* v___x_423_; lean_object* v_fst_424_; lean_object* v_snd_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_434_; 
v_a_418_ = lean_ctor_get(v_x_377_, 0);
v_b_419_ = lean_ctor_get(v_x_377_, 1);
v___x_420_ = l_Lean_Meta_Sym_Arith_exprMajQ(v_invs_376_, v_a_418_);
v_fst_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_fst_421_);
v_snd_422_ = lean_ctor_get(v___x_420_, 1);
lean_inc(v_snd_422_);
lean_dec_ref(v___x_420_);
v___x_423_ = l_Lean_Meta_Sym_Arith_exprMajQ(v_invs_376_, v_b_419_);
v_fst_424_ = lean_ctor_get(v___x_423_, 0);
v_snd_425_ = lean_ctor_get(v___x_423_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_434_ == 0)
{
v___x_427_ = v___x_423_;
v_isShared_428_ = v_isSharedCheck_434_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_snd_425_);
lean_inc(v_fst_424_);
lean_dec(v___x_423_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_434_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_429_ = l_Lean_Meta_Sym_Arith_satMul(v_fst_421_, v_fst_424_);
lean_dec(v_fst_424_);
lean_dec(v_fst_421_);
v___x_430_ = l_Lean_Meta_Sym_Arith_satMul(v_snd_422_, v_snd_425_);
lean_dec(v_snd_425_);
lean_dec(v_snd_422_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 1, v___x_430_);
lean_ctor_set(v___x_427_, 0, v___x_429_);
v___x_432_ = v___x_427_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
case 8:
{
lean_object* v_a_435_; lean_object* v_k_436_; lean_object* v___x_437_; lean_object* v_fst_438_; lean_object* v_snd_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_448_; 
v_a_435_ = lean_ctor_get(v_x_377_, 0);
v_k_436_ = lean_ctor_get(v_x_377_, 1);
v___x_437_ = l_Lean_Meta_Sym_Arith_exprMajQ(v_invs_376_, v_a_435_);
v_fst_438_ = lean_ctor_get(v___x_437_, 0);
v_snd_439_ = lean_ctor_get(v___x_437_, 1);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_448_ == 0)
{
v___x_441_ = v___x_437_;
v_isShared_442_ = v_isSharedCheck_448_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_snd_439_);
lean_inc(v_fst_438_);
lean_dec(v___x_437_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_448_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_443_ = l_Lean_Meta_Sym_Arith_satPow(v_fst_438_, v_k_436_);
lean_dec(v_fst_438_);
v___x_444_ = l_Lean_Meta_Sym_Arith_satPow(v_snd_439_, v_k_436_);
lean_dec(v_snd_439_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v___x_444_);
lean_ctor_set(v___x_441_, 0, v___x_443_);
v___x_446_ = v___x_441_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
default: 
{
lean_object* v_k_449_; 
v_k_449_ = lean_ctor_get(v_x_377_, 0);
v_k_379_ = v_k_449_;
goto v___jp_378_;
}
}
v___jp_378_:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = lean_nat_abs(v_k_379_);
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
return v___x_382_;
}
v___jp_383_:
{
lean_object* v___x_386_; lean_object* v_fst_387_; lean_object* v_snd_388_; lean_object* v___x_389_; lean_object* v_fst_390_; lean_object* v_snd_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_402_; 
v___x_386_ = l_Lean_Meta_Sym_Arith_exprMajQ(v_invs_376_, v_a_384_);
v_fst_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_fst_387_);
v_snd_388_ = lean_ctor_get(v___x_386_, 1);
lean_inc(v_snd_388_);
lean_dec_ref(v___x_386_);
v___x_389_ = l_Lean_Meta_Sym_Arith_exprMajQ(v_invs_376_, v_b_385_);
v_fst_390_ = lean_ctor_get(v___x_389_, 0);
v_snd_391_ = lean_ctor_get(v___x_389_, 1);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_402_ == 0)
{
v___x_393_ = v___x_389_;
v_isShared_394_ = v_isSharedCheck_402_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_snd_391_);
lean_inc(v_fst_390_);
lean_dec(v___x_389_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_402_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_395_ = l_Lean_Meta_Sym_Arith_satMul(v_fst_387_, v_snd_391_);
lean_dec(v_fst_387_);
v___x_396_ = l_Lean_Meta_Sym_Arith_satMul(v_fst_390_, v_snd_388_);
lean_dec(v_fst_390_);
v___x_397_ = lean_nat_add(v___x_395_, v___x_396_);
lean_dec(v___x_396_);
lean_dec(v___x_395_);
v___x_398_ = l_Lean_Meta_Sym_Arith_satMul(v_snd_388_, v_snd_391_);
lean_dec(v_snd_391_);
lean_dec(v_snd_388_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 1, v___x_398_);
lean_ctor_set(v___x_393_, 0, v___x_397_);
v___x_400_ = v___x_393_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprMajQ___boxed(lean_object* v_invs_450_, lean_object* v_x_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_Meta_Sym_Arith_exprMajQ(v_invs_450_, v_x_451_);
lean_dec_ref(v_x_451_);
lean_dec(v_invs_450_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_go(lean_object* v_invs_453_, lean_object* v_B_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_a_457_; lean_object* v_b_458_; 
switch(lean_obj_tag(v_a_455_))
{
case 3:
{
lean_object* v_i_462_; lean_object* v___x_463_; 
v_i_462_ = lean_ctor_get(v_a_455_, 0);
v___x_463_ = l_Lean_Meta_Sym_Arith_invLookup(v_invs_453_, v_i_462_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_Meta_Sym_Arith_satPow(v_B_454_, v_i_462_);
return v___x_464_;
}
else
{
lean_object* v___x_465_; 
lean_dec_ref_known(v___x_463_, 1);
v___x_465_ = lean_unsigned_to_nat(0u);
return v___x_465_;
}
}
case 4:
{
lean_object* v_a_466_; 
v_a_466_ = lean_ctor_get(v_a_455_, 0);
v_a_455_ = v_a_466_;
goto _start;
}
case 5:
{
lean_object* v_a_468_; lean_object* v_b_469_; 
v_a_468_ = lean_ctor_get(v_a_455_, 0);
v_b_469_ = lean_ctor_get(v_a_455_, 1);
v_a_457_ = v_a_468_;
v_b_458_ = v_b_469_;
goto v___jp_456_;
}
case 6:
{
lean_object* v_a_470_; lean_object* v_b_471_; 
v_a_470_ = lean_ctor_get(v_a_455_, 0);
v_b_471_ = lean_ctor_get(v_a_455_, 1);
v_a_457_ = v_a_470_;
v_b_458_ = v_b_471_;
goto v___jp_456_;
}
case 7:
{
lean_object* v_a_472_; lean_object* v_b_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_a_472_ = lean_ctor_get(v_a_455_, 0);
v_b_473_ = lean_ctor_get(v_a_455_, 1);
v___x_474_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_go(v_invs_453_, v_B_454_, v_a_472_);
v___x_475_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_go(v_invs_453_, v_B_454_, v_b_473_);
v___x_476_ = lean_nat_add(v___x_474_, v___x_475_);
lean_dec(v___x_475_);
lean_dec(v___x_474_);
return v___x_476_;
}
case 8:
{
lean_object* v_a_477_; lean_object* v_k_478_; lean_object* v_c_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v_a_477_ = lean_ctor_get(v_a_455_, 0);
v_k_478_ = lean_ctor_get(v_a_455_, 1);
v_c_479_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_go(v_invs_453_, v_B_454_, v_a_477_);
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = lean_nat_dec_eq(v_k_478_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_Meta_Sym_Arith_satMul(v_c_479_, v_k_478_);
lean_dec(v_c_479_);
return v___x_482_;
}
else
{
return v_c_479_;
}
}
default: 
{
lean_object* v___x_483_; 
v___x_483_ = lean_unsigned_to_nat(0u);
return v___x_483_;
}
}
v___jp_456_:
{
lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_459_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_go(v_invs_453_, v_B_454_, v_a_457_);
v___x_460_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_go(v_invs_453_, v_B_454_, v_b_458_);
v___x_461_ = lean_nat_dec_le(v___x_459_, v___x_460_);
if (v___x_461_ == 0)
{
lean_dec(v___x_460_);
return v___x_459_;
}
else
{
lean_dec(v___x_459_);
return v___x_460_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_go___boxed(lean_object* v_invs_484_, lean_object* v_B_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_go(v_invs_484_, v_B_485_, v_a_486_);
lean_dec_ref(v_a_486_);
lean_dec(v_B_485_);
lean_dec(v_invs_484_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_deg(lean_object* v_invs_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_a_491_; lean_object* v_b_492_; 
switch(lean_obj_tag(v_a_489_))
{
case 3:
{
lean_object* v_i_496_; lean_object* v___x_497_; 
v_i_496_ = lean_ctor_get(v_a_489_, 0);
v___x_497_ = l_Lean_Meta_Sym_Arith_invLookup(v_invs_488_, v_i_496_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v___x_498_; 
v___x_498_ = lean_unsigned_to_nat(1u);
return v___x_498_;
}
else
{
lean_object* v___x_499_; 
lean_dec_ref_known(v___x_497_, 1);
v___x_499_ = lean_unsigned_to_nat(0u);
return v___x_499_;
}
}
case 4:
{
lean_object* v_a_500_; 
v_a_500_ = lean_ctor_get(v_a_489_, 0);
v_a_489_ = v_a_500_;
goto _start;
}
case 5:
{
lean_object* v_a_502_; lean_object* v_b_503_; 
v_a_502_ = lean_ctor_get(v_a_489_, 0);
v_b_503_ = lean_ctor_get(v_a_489_, 1);
v_a_491_ = v_a_502_;
v_b_492_ = v_b_503_;
goto v___jp_490_;
}
case 6:
{
lean_object* v_a_504_; lean_object* v_b_505_; 
v_a_504_ = lean_ctor_get(v_a_489_, 0);
v_b_505_ = lean_ctor_get(v_a_489_, 1);
v_a_491_ = v_a_504_;
v_b_492_ = v_b_505_;
goto v___jp_490_;
}
case 7:
{
lean_object* v_a_506_; lean_object* v_b_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_a_506_ = lean_ctor_get(v_a_489_, 0);
v_b_507_ = lean_ctor_get(v_a_489_, 1);
v___x_508_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_deg(v_invs_488_, v_a_506_);
v___x_509_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_deg(v_invs_488_, v_b_507_);
v___x_510_ = lean_nat_add(v___x_508_, v___x_509_);
lean_dec(v___x_509_);
lean_dec(v___x_508_);
return v___x_510_;
}
case 8:
{
lean_object* v_a_511_; lean_object* v_k_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_a_511_ = lean_ctor_get(v_a_489_, 0);
v_k_512_ = lean_ctor_get(v_a_489_, 1);
v___x_513_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_deg(v_invs_488_, v_a_511_);
v___x_514_ = lean_nat_mul(v___x_513_, v_k_512_);
lean_dec(v___x_513_);
return v___x_514_;
}
default: 
{
lean_object* v___x_515_; 
v___x_515_ = lean_unsigned_to_nat(0u);
return v___x_515_;
}
}
v___jp_490_:
{
lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_493_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_deg(v_invs_488_, v_a_491_);
v___x_494_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_deg(v_invs_488_, v_b_492_);
v___x_495_ = lean_nat_dec_le(v___x_493_, v___x_494_);
if (v___x_495_ == 0)
{
lean_dec(v___x_494_);
return v___x_493_;
}
else
{
lean_dec(v___x_493_);
return v___x_494_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_deg___boxed(lean_object* v_invs_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_deg(v_invs_516_, v_a_517_);
lean_dec_ref(v_a_517_);
lean_dec(v_invs_516_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_kronQArgs_x3f(lean_object* v_l_519_, lean_object* v_r_520_, lean_object* v_invs_521_, lean_object* v_maxBits_522_){
_start:
{
lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_539_; lean_object* v___x_552_; lean_object* v___y_554_; lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_552_ = lean_unsigned_to_nat(2u);
v___x_558_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_deg(v_invs_521_, v_l_519_);
v___x_559_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_deg(v_invs_521_, v_r_520_);
v___x_560_ = lean_nat_dec_le(v___x_558_, v___x_559_);
if (v___x_560_ == 0)
{
lean_dec(v___x_559_);
v___y_554_ = v___x_558_;
goto v___jp_553_;
}
else
{
lean_dec(v___x_558_);
v___y_554_ = v___x_559_;
goto v___jp_553_;
}
v___jp_523_:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_Meta_Sym_Arith_kronExponent_x3f(v___y_524_, v___y_526_, v_maxBits_522_);
lean_dec(v___y_526_);
lean_dec(v___y_524_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v___x_528_; 
lean_dec(v___y_525_);
v___x_528_ = lean_box(0);
return v___x_528_;
}
else
{
lean_object* v_val_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_537_; 
v_val_529_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_537_ == 0)
{
v___x_531_ = v___x_527_;
v_isShared_532_ = v_isSharedCheck_537_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_val_529_);
lean_dec(v___x_527_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_537_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v_val_529_);
lean_ctor_set(v___x_533_, 1, v___y_525_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_533_);
v___x_535_ = v___x_531_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
v___jp_538_:
{
lean_object* v___x_540_; lean_object* v_fst_541_; lean_object* v_snd_542_; lean_object* v___x_543_; lean_object* v_fst_544_; lean_object* v_snd_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_540_ = l_Lean_Meta_Sym_Arith_exprMajQ(v_invs_521_, v_l_519_);
v_fst_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_fst_541_);
v_snd_542_ = lean_ctor_get(v___x_540_, 1);
lean_inc(v_snd_542_);
lean_dec_ref(v___x_540_);
v___x_543_ = l_Lean_Meta_Sym_Arith_exprMajQ(v_invs_521_, v_r_520_);
v_fst_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_fst_544_);
v_snd_545_ = lean_ctor_get(v___x_543_, 1);
lean_inc(v_snd_545_);
lean_dec_ref(v___x_543_);
v___x_546_ = l_Lean_Meta_Sym_Arith_satMul(v_snd_545_, v_fst_541_);
lean_dec(v_fst_541_);
lean_dec(v_snd_545_);
v___x_547_ = l_Lean_Meta_Sym_Arith_satMul(v_snd_542_, v_fst_544_);
lean_dec(v_fst_544_);
lean_dec(v_snd_542_);
v___x_548_ = lean_nat_add(v___x_546_, v___x_547_);
lean_dec(v___x_547_);
lean_dec(v___x_546_);
v___x_549_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_go(v_invs_521_, v___y_539_, v_l_519_);
v___x_550_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQArgs_x3f_go(v_invs_521_, v___y_539_, v_r_520_);
v___x_551_ = lean_nat_dec_le(v___x_549_, v___x_550_);
if (v___x_551_ == 0)
{
lean_dec(v___x_550_);
v___y_524_ = v___x_548_;
v___y_525_ = v___y_539_;
v___y_526_ = v___x_549_;
goto v___jp_523_;
}
else
{
lean_dec(v___x_549_);
v___y_524_ = v___x_548_;
v___y_525_ = v___y_539_;
v___y_526_ = v___x_550_;
goto v___jp_523_;
}
}
v___jp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_555_ = lean_unsigned_to_nat(1u);
v___x_556_ = lean_nat_add(v___y_554_, v___x_555_);
lean_dec(v___y_554_);
v___x_557_ = lean_nat_dec_le(v___x_552_, v___x_556_);
if (v___x_557_ == 0)
{
lean_dec(v___x_556_);
v___y_539_ = v___x_552_;
goto v___jp_538_;
}
else
{
v___y_539_ = v___x_556_;
goto v___jp_538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_kronQArgs_x3f___boxed(lean_object* v_l_561_, lean_object* v_r_562_, lean_object* v_invs_563_, lean_object* v_maxBits_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_Meta_Sym_Arith_kronQArgs_x3f(v_l_561_, v_r_562_, v_invs_563_, v_maxBits_564_);
lean_dec(v_maxBits_564_);
lean_dec(v_invs_563_);
lean_dec_ref(v_r_562_);
lean_dec_ref(v_l_561_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprDegQL(lean_object* v_invs_566_, lean_object* v_x_567_){
_start:
{
lean_object* v_a_569_; lean_object* v_b_570_; 
switch(lean_obj_tag(v_x_567_))
{
case 3:
{
lean_object* v_i_574_; lean_object* v___x_575_; 
v_i_574_ = lean_ctor_get(v_x_567_, 0);
v___x_575_ = l_Lean_Meta_Sym_Arith_invLookup(v_invs_566_, v_i_574_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_576_; 
v___x_576_ = lean_unsigned_to_nat(1u);
return v___x_576_;
}
else
{
lean_object* v___x_577_; 
lean_dec_ref_known(v___x_575_, 1);
v___x_577_ = lean_unsigned_to_nat(0u);
return v___x_577_;
}
}
case 4:
{
lean_object* v_a_578_; 
v_a_578_ = lean_ctor_get(v_x_567_, 0);
v_x_567_ = v_a_578_;
goto _start;
}
case 5:
{
lean_object* v_a_580_; lean_object* v_b_581_; 
v_a_580_ = lean_ctor_get(v_x_567_, 0);
v_b_581_ = lean_ctor_get(v_x_567_, 1);
v_a_569_ = v_a_580_;
v_b_570_ = v_b_581_;
goto v___jp_568_;
}
case 6:
{
lean_object* v_a_582_; lean_object* v_b_583_; 
v_a_582_ = lean_ctor_get(v_x_567_, 0);
v_b_583_ = lean_ctor_get(v_x_567_, 1);
v_a_569_ = v_a_582_;
v_b_570_ = v_b_583_;
goto v___jp_568_;
}
case 7:
{
lean_object* v_a_584_; lean_object* v_b_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_a_584_ = lean_ctor_get(v_x_567_, 0);
v_b_585_ = lean_ctor_get(v_x_567_, 1);
v___x_586_ = l_Lean_Meta_Sym_Arith_exprDegQL(v_invs_566_, v_a_584_);
v___x_587_ = l_Lean_Meta_Sym_Arith_exprDegQL(v_invs_566_, v_b_585_);
v___x_588_ = lean_nat_add(v___x_586_, v___x_587_);
lean_dec(v___x_587_);
lean_dec(v___x_586_);
return v___x_588_;
}
case 8:
{
lean_object* v_a_589_; lean_object* v_k_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_a_589_ = lean_ctor_get(v_x_567_, 0);
v_k_590_ = lean_ctor_get(v_x_567_, 1);
v___x_591_ = l_Lean_Meta_Sym_Arith_exprDegQL(v_invs_566_, v_a_589_);
v___x_592_ = lean_nat_mul(v___x_591_, v_k_590_);
lean_dec(v___x_591_);
return v___x_592_;
}
default: 
{
lean_object* v___x_593_; 
v___x_593_ = lean_unsigned_to_nat(0u);
return v___x_593_;
}
}
v___jp_568_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = l_Lean_Meta_Sym_Arith_exprDegQL(v_invs_566_, v_a_569_);
v___x_572_ = l_Lean_Meta_Sym_Arith_exprDegQL(v_invs_566_, v_b_570_);
v___x_573_ = lean_nat_lor(v___x_571_, v___x_572_);
lean_dec(v___x_572_);
lean_dec(v___x_571_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_exprDegQL___boxed(lean_object* v_invs_594_, lean_object* v_x_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Meta_Sym_Arith_exprDegQL(v_invs_594_, v_x_595_);
lean_dec_ref(v_x_595_);
lean_dec(v_invs_594_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQLinExponent_x3f_maxVar(lean_object* v_invs_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_a_600_; lean_object* v_b_601_; 
switch(lean_obj_tag(v_a_598_))
{
case 3:
{
lean_object* v_i_605_; lean_object* v___x_606_; 
v_i_605_ = lean_ctor_get(v_a_598_, 0);
v___x_606_ = l_Lean_Meta_Sym_Arith_invLookup(v_invs_597_, v_i_605_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_unsigned_to_nat(1u);
v___x_608_ = lean_nat_add(v_i_605_, v___x_607_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; 
lean_dec_ref_known(v___x_606_, 1);
v___x_609_ = lean_unsigned_to_nat(0u);
return v___x_609_;
}
}
case 4:
{
lean_object* v_a_610_; 
v_a_610_ = lean_ctor_get(v_a_598_, 0);
v_a_598_ = v_a_610_;
goto _start;
}
case 5:
{
lean_object* v_a_612_; lean_object* v_b_613_; 
v_a_612_ = lean_ctor_get(v_a_598_, 0);
v_b_613_ = lean_ctor_get(v_a_598_, 1);
v_a_600_ = v_a_612_;
v_b_601_ = v_b_613_;
goto v___jp_599_;
}
case 6:
{
lean_object* v_a_614_; lean_object* v_b_615_; 
v_a_614_ = lean_ctor_get(v_a_598_, 0);
v_b_615_ = lean_ctor_get(v_a_598_, 1);
v_a_600_ = v_a_614_;
v_b_601_ = v_b_615_;
goto v___jp_599_;
}
case 7:
{
lean_object* v_a_616_; lean_object* v_b_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_a_616_ = lean_ctor_get(v_a_598_, 0);
v_b_617_ = lean_ctor_get(v_a_598_, 1);
v___x_618_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQLinExponent_x3f_maxVar(v_invs_597_, v_a_616_);
v___x_619_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQLinExponent_x3f_maxVar(v_invs_597_, v_b_617_);
v___x_620_ = lean_nat_add(v___x_618_, v___x_619_);
lean_dec(v___x_619_);
lean_dec(v___x_618_);
return v___x_620_;
}
case 8:
{
lean_object* v_a_621_; lean_object* v_k_622_; lean_object* v_c_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v_a_621_ = lean_ctor_get(v_a_598_, 0);
v_k_622_ = lean_ctor_get(v_a_598_, 1);
v_c_623_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQLinExponent_x3f_maxVar(v_invs_597_, v_a_621_);
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = lean_nat_dec_eq(v_k_622_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_Meta_Sym_Arith_satMul(v_c_623_, v_k_622_);
lean_dec(v_c_623_);
return v___x_626_;
}
else
{
return v_c_623_;
}
}
default: 
{
lean_object* v___x_627_; 
v___x_627_ = lean_unsigned_to_nat(0u);
return v___x_627_;
}
}
v___jp_599_:
{
lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_602_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQLinExponent_x3f_maxVar(v_invs_597_, v_a_600_);
v___x_603_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQLinExponent_x3f_maxVar(v_invs_597_, v_b_601_);
v___x_604_ = lean_nat_dec_le(v___x_602_, v___x_603_);
if (v___x_604_ == 0)
{
lean_dec(v___x_603_);
return v___x_602_;
}
else
{
lean_dec(v___x_602_);
return v___x_603_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQLinExponent_x3f_maxVar___boxed(lean_object* v_invs_628_, lean_object* v_a_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQLinExponent_x3f_maxVar(v_invs_628_, v_a_629_);
lean_dec_ref(v_a_629_);
lean_dec(v_invs_628_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_kronQLinExponent_x3f(lean_object* v_l_631_, lean_object* v_r_632_, lean_object* v_invs_633_, lean_object* v_maxBits_634_){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_635_ = l_Lean_Meta_Sym_Arith_exprDegQL(v_invs_633_, v_l_631_);
v___x_636_ = lean_unsigned_to_nat(1u);
v___x_637_ = lean_nat_dec_le(v___x_635_, v___x_636_);
lean_dec(v___x_635_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
v___x_638_ = lean_box(0);
return v___x_638_;
}
else
{
lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_639_ = l_Lean_Meta_Sym_Arith_exprDegQL(v_invs_633_, v_r_632_);
v___x_640_ = lean_nat_dec_le(v___x_639_, v___x_636_);
lean_dec(v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
v___x_641_ = lean_box(0);
return v___x_641_;
}
else
{
lean_object* v___x_642_; lean_object* v_fst_643_; lean_object* v_snd_644_; lean_object* v___x_645_; lean_object* v_fst_646_; lean_object* v_snd_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_642_ = l_Lean_Meta_Sym_Arith_exprMajQ(v_invs_633_, v_l_631_);
v_fst_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_fst_643_);
v_snd_644_ = lean_ctor_get(v___x_642_, 1);
lean_inc(v_snd_644_);
lean_dec_ref(v___x_642_);
v___x_645_ = l_Lean_Meta_Sym_Arith_exprMajQ(v_invs_633_, v_r_632_);
v_fst_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_fst_646_);
v_snd_647_ = lean_ctor_get(v___x_645_, 1);
lean_inc(v_snd_647_);
lean_dec_ref(v___x_645_);
v___x_648_ = l_Lean_Meta_Sym_Arith_satMul(v_snd_647_, v_fst_643_);
lean_dec(v_fst_643_);
lean_dec(v_snd_647_);
v___x_649_ = l_Lean_Meta_Sym_Arith_satMul(v_snd_644_, v_fst_646_);
lean_dec(v_fst_646_);
lean_dec(v_snd_644_);
v___x_650_ = lean_nat_add(v___x_648_, v___x_649_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
v___x_651_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQLinExponent_x3f_maxVar(v_invs_633_, v_l_631_);
v___x_652_ = l___private_Lean_Meta_Sym_Arith_Kronecker_0__Lean_Meta_Sym_Arith_kronQLinExponent_x3f_maxVar(v_invs_633_, v_r_632_);
v___x_653_ = lean_nat_dec_le(v___x_651_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_dec(v___x_652_);
v___x_654_ = l_Lean_Meta_Sym_Arith_kronExponent_x3f(v___x_650_, v___x_651_, v_maxBits_634_);
lean_dec(v___x_651_);
lean_dec(v___x_650_);
return v___x_654_;
}
else
{
lean_object* v___x_655_; 
lean_dec(v___x_651_);
v___x_655_ = l_Lean_Meta_Sym_Arith_kronExponent_x3f(v___x_650_, v___x_652_, v_maxBits_634_);
lean_dec(v___x_652_);
lean_dec(v___x_650_);
return v___x_655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_kronQLinExponent_x3f___boxed(lean_object* v_l_656_, lean_object* v_r_657_, lean_object* v_invs_658_, lean_object* v_maxBits_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_Meta_Sym_Arith_kronQLinExponent_x3f(v_l_656_, v_r_657_, v_invs_658_, v_maxBits_659_);
lean_dec(v_maxBits_659_);
lean_dec(v_invs_658_);
lean_dec_ref(v_r_657_);
lean_dec_ref(v_l_656_);
return v_res_660_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Kronecker(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Arith_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Sym_Arith_kronSatBits = _init_l_Lean_Meta_Sym_Arith_kronSatBits();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_kronSatBits);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_Kronecker(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_Kronecker(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Arith_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Kronecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_Kronecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_Kronecker(builtin);
}
#ifdef __cplusplus
}
#endif
