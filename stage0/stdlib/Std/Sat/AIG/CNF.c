// Lean compiler output
// Module: Std.Sat.AIG.CNF
// Imports: public import Std.Sat.CNF public import Std.Sat.AIG.Lemmas import Init.ByCases import Init.Omega
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_Std_Sat_CNF_eval___redArg(lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_denote_go___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_xor(uint8_t, uint8_t);
static const lean_array_object l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0 = (const lean_object*)&l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__13_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__13_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__21_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__21_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__21_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__19_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__19_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__19_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__16_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__16_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__16_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(lean_object* v_output_3_){
_start:
{
uint8_t v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_4_ = 0;
v___x_5_ = lean_box(v___x_4_);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v_output_3_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
v___x_7_ = lean_box(0);
v___x_8_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_8_, 0, v___x_6_);
lean_ctor_set(v___x_8_, 1, v___x_7_);
v___x_9_ = ((lean_object*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0));
v___x_10_ = lean_array_push(v___x_9_, v___x_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF(lean_object* v_00_u03b1_11_, lean_object* v_output_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(v_output_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg(lean_object* v_output_14_, lean_object* v_atom_15_){
_start:
{
uint8_t v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_16_ = 0;
v___x_17_ = lean_box(v___x_16_);
lean_inc(v_output_14_);
v___x_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_18_, 0, v_output_14_);
lean_ctor_set(v___x_18_, 1, v___x_17_);
v___x_19_ = 1;
v___x_20_ = lean_box(v___x_19_);
lean_inc(v_atom_15_);
v___x_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_21_, 0, v_atom_15_);
lean_ctor_set(v___x_21_, 1, v___x_20_);
v___x_22_ = lean_box(0);
v___x_23_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_21_);
lean_ctor_set(v___x_23_, 1, v___x_22_);
v___x_24_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_18_);
lean_ctor_set(v___x_24_, 1, v___x_23_);
v___x_25_ = lean_box(v___x_19_);
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v_output_14_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
v___x_27_ = lean_box(v___x_16_);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v_atom_15_);
lean_ctor_set(v___x_28_, 1, v___x_27_);
v___x_29_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___x_22_);
v___x_30_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_26_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
v___x_31_ = ((lean_object*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0));
v___x_32_ = lean_array_push(v___x_31_, v___x_30_);
v___x_33_ = lean_array_push(v___x_32_, v___x_24_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF(lean_object* v_00_u03b1_34_, lean_object* v_output_35_, lean_object* v_atom_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg(v_output_35_, v_atom_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(lean_object* v_output_38_, lean_object* v_lhs_39_, lean_object* v_rhs_40_, uint8_t v_linv_41_, uint8_t v_rinv_42_){
_start:
{
uint8_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_43_ = 1;
v___x_44_ = lean_box(v___x_43_);
lean_inc(v_output_38_);
v___x_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_45_, 0, v_output_38_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
v___x_46_ = lean_box(v_linv_41_);
lean_inc(v_lhs_39_);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v_lhs_39_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
v___x_48_ = lean_box(v_rinv_42_);
lean_inc(v_rhs_40_);
v___x_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_49_, 0, v_rhs_40_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v___x_50_ = lean_box(0);
v___x_51_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_49_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
v___x_52_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_47_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
v___x_53_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_45_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
v___x_54_ = 0;
v___x_55_ = lean_box(v___x_54_);
v___x_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_56_, 0, v_output_38_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = lean_bool_not(v_rinv_42_);
v___x_58_ = lean_box(v___x_57_);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v_rhs_40_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
v___x_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___x_50_);
lean_inc_ref(v___x_56_);
v___x_61_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_56_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v___x_62_ = lean_bool_not(v_linv_41_);
v___x_63_ = lean_box(v___x_62_);
v___x_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_64_, 0, v_lhs_39_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
v___x_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_50_);
v___x_66_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_56_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = ((lean_object*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0));
v___x_68_ = lean_array_push(v___x_67_, v___x_66_);
v___x_69_ = lean_array_push(v___x_68_, v___x_61_);
v___x_70_ = lean_array_push(v___x_69_, v___x_53_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___boxed(lean_object* v_output_71_, lean_object* v_lhs_72_, lean_object* v_rhs_73_, lean_object* v_linv_74_, lean_object* v_rinv_75_){
_start:
{
uint8_t v_linv_boxed_76_; uint8_t v_rinv_boxed_77_; lean_object* v_res_78_; 
v_linv_boxed_76_ = lean_unbox(v_linv_74_);
v_rinv_boxed_77_ = lean_unbox(v_rinv_75_);
v_res_78_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_output_71_, v_lhs_72_, v_rhs_73_, v_linv_boxed_76_, v_rinv_boxed_77_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF(lean_object* v_00_u03b1_79_, lean_object* v_output_80_, lean_object* v_lhs_81_, lean_object* v_rhs_82_, uint8_t v_linv_83_, uint8_t v_rinv_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_output_80_, v_lhs_81_, v_rhs_82_, v_linv_83_, v_rinv_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___boxed(lean_object* v_00_u03b1_86_, lean_object* v_output_87_, lean_object* v_lhs_88_, lean_object* v_rhs_89_, lean_object* v_linv_90_, lean_object* v_rinv_91_){
_start:
{
uint8_t v_linv_boxed_92_; uint8_t v_rinv_boxed_93_; lean_object* v_res_94_; 
v_linv_boxed_92_ = lean_unbox(v_linv_90_);
v_rinv_boxed_93_ = lean_unbox(v_rinv_91_);
v_res_94_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF(v_00_u03b1_86_, v_output_87_, v_lhs_88_, v_rhs_89_, v_linv_boxed_92_, v_rinv_boxed_93_);
return v_res_94_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns(lean_object* v_aig_95_, lean_object* v_assign1_96_, lean_object* v_assign2_97_, lean_object* v_var_98_){
_start:
{
lean_object* v_decls_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v_decls_99_ = lean_ctor_get(v_aig_95_, 0);
v___x_100_ = lean_array_get_size(v_decls_99_);
v___x_101_ = lean_nat_dec_lt(v_var_98_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
lean_dec_ref(v_assign2_97_);
v___x_102_ = lean_nat_sub(v_var_98_, v___x_100_);
lean_dec(v_var_98_);
v___x_103_ = lean_apply_1(v_assign1_96_, v___x_102_);
v___x_104_ = lean_unbox(v___x_103_);
return v___x_104_;
}
else
{
lean_object* v___x_105_; uint8_t v___x_106_; 
lean_dec_ref(v_assign1_96_);
v___x_105_ = lean_apply_1(v_assign2_97_, v_var_98_);
v___x_106_ = lean_unbox(v___x_105_);
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns___boxed(lean_object* v_aig_107_, lean_object* v_assign1_108_, lean_object* v_assign2_109_, lean_object* v_var_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns(v_aig_107_, v_assign1_108_, v_assign2_109_, v_var_110_);
lean_dec_ref(v_aig_107_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign(lean_object* v_aig_113_, lean_object* v_assign_114_, lean_object* v_var_115_){
_start:
{
lean_object* v_decls_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v_decls_116_ = lean_ctor_get(v_aig_113_, 0);
v___x_117_ = lean_array_get_size(v_decls_116_);
v___x_118_ = lean_nat_add(v_var_115_, v___x_117_);
v___x_119_ = lean_apply_1(v_assign_114_, v___x_118_);
v___x_120_ = lean_unbox(v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___boxed(lean_object* v_aig_121_, lean_object* v_assign_122_, lean_object* v_var_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign(v_aig_121_, v_assign_122_, v_var_123_);
lean_dec(v_var_123_);
lean_dec_ref(v_aig_121_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign(lean_object* v_assign_126_, lean_object* v_idx_127_){
_start:
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = lean_apply_1(v_assign_126_, v_idx_127_);
v___x_129_ = lean_unbox(v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign___boxed(lean_object* v_assign_130_, lean_object* v_idx_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign(v_assign_130_, v_idx_131_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(lean_object* v_assign_134_, lean_object* v_entry_135_){
_start:
{
lean_object* v_ref_136_; lean_object* v_aig_137_; lean_object* v_gate_138_; uint8_t v_invert_139_; lean_object* v_decls_140_; uint8_t v___x_141_; uint8_t v___x_142_; 
v_ref_136_ = lean_ctor_get(v_entry_135_, 1);
v_aig_137_ = lean_ctor_get(v_entry_135_, 0);
v_gate_138_ = lean_ctor_get(v_ref_136_, 0);
v_invert_139_ = lean_ctor_get_uint8(v_ref_136_, sizeof(void*)*1);
v_decls_140_ = lean_ctor_get(v_aig_137_, 0);
v___x_141_ = l_Std_Sat_AIG_denote_go___redArg(v_gate_138_, v_decls_140_, v_assign_134_);
v___x_142_ = lean_bool_xor(v___x_141_, v_invert_139_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0___boxed(lean_object* v_assign_143_, lean_object* v_entry_144_){
_start:
{
uint8_t v_res_145_; lean_object* v_r_146_; 
v_res_145_ = l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(v_assign_143_, v_entry_144_);
lean_dec_ref(v_entry_144_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0(lean_object* v_aig_147_, lean_object* v_assign1_148_, lean_object* v_idx_149_){
_start:
{
uint8_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_150_ = 0;
v___x_151_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_151_, 0, v_idx_149_);
lean_ctor_set_uint8(v___x_151_, sizeof(void*)*1, v___x_150_);
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v_aig_147_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(v_assign1_148_, v___x_152_);
lean_dec_ref_known(v___x_152_, 2);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0___boxed(lean_object* v_aig_154_, lean_object* v_assign1_155_, lean_object* v_idx_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0(v_aig_154_, v_assign1_155_, v_idx_156_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(lean_object* v_aig_159_, lean_object* v_assign1_160_, lean_object* v_var_161_){
_start:
{
lean_object* v___f_162_; uint8_t v___x_163_; 
lean_inc_ref(v_assign1_160_);
lean_inc_ref(v_aig_159_);
v___f_162_ = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0___boxed), 3, 2);
lean_closure_set(v___f_162_, 0, v_aig_159_);
lean_closure_set(v___f_162_, 1, v_assign1_160_);
v___x_163_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns(v_aig_159_, v_assign1_160_, v___f_162_, v_var_161_);
lean_dec_ref(v_aig_159_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___boxed(lean_object* v_aig_164_, lean_object* v_assign1_165_, lean_object* v_var_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(v_aig_164_, v_assign1_165_, v_var_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(lean_object* v_aig_169_){
_start:
{
lean_object* v_decls_170_; lean_object* v___x_171_; uint8_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v_decls_170_ = lean_ctor_get(v_aig_169_, 0);
v___x_171_ = lean_array_get_size(v_decls_170_);
v___x_172_ = 0;
v___x_173_ = lean_box(v___x_172_);
v___x_174_ = lean_mk_array(v___x_171_, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___boxed(lean_object* v_aig_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(v_aig_175_);
lean_dec_ref(v_aig_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(lean_object* v_cache_177_, lean_object* v_idx_178_){
_start:
{
uint8_t v___x_179_; lean_object* v___x_180_; lean_object* v_out_181_; 
v___x_179_ = 1;
v___x_180_ = lean_box(v___x_179_);
v_out_181_ = lean_array_fset(v_cache_177_, v_idx_178_, v___x_180_);
return v_out_181_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg___boxed(lean_object* v_cache_182_, lean_object* v_idx_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_182_, v_idx_183_);
lean_dec(v_idx_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(lean_object* v_aig_185_, lean_object* v_cnf_186_, lean_object* v_cache_187_, lean_object* v_idx_188_, lean_object* v_h_189_, lean_object* v_htip_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_187_, v_idx_188_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___boxed(lean_object* v_aig_192_, lean_object* v_cnf_193_, lean_object* v_cache_194_, lean_object* v_idx_195_, lean_object* v_h_196_, lean_object* v_htip_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(v_aig_192_, v_cnf_193_, v_cache_194_, v_idx_195_, v_h_196_, v_htip_197_);
lean_dec(v_idx_195_);
lean_dec_ref(v_cnf_193_);
lean_dec_ref(v_aig_192_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(lean_object* v_cache_199_, lean_object* v_idx_200_){
_start:
{
uint8_t v___x_201_; lean_object* v___x_202_; lean_object* v_out_203_; 
v___x_201_ = 1;
v___x_202_ = lean_box(v___x_201_);
v_out_203_ = lean_array_fset(v_cache_199_, v_idx_200_, v___x_202_);
return v_out_203_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg___boxed(lean_object* v_cache_204_, lean_object* v_idx_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_204_, v_idx_205_);
lean_dec(v_idx_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(lean_object* v_aig_207_, lean_object* v_cnf_208_, lean_object* v_a_209_, lean_object* v_cache_210_, lean_object* v_idx_211_, lean_object* v_h_212_, lean_object* v_htip_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_210_, v_idx_211_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___boxed(lean_object* v_aig_215_, lean_object* v_cnf_216_, lean_object* v_a_217_, lean_object* v_cache_218_, lean_object* v_idx_219_, lean_object* v_h_220_, lean_object* v_htip_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(v_aig_215_, v_cnf_216_, v_a_217_, v_cache_218_, v_idx_219_, v_h_220_, v_htip_221_);
lean_dec(v_idx_219_);
lean_dec(v_a_217_);
lean_dec_ref(v_cnf_216_);
lean_dec_ref(v_aig_215_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(lean_object* v_cache_223_, lean_object* v_idx_224_){
_start:
{
uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v_out_227_; 
v___x_225_ = 1;
v___x_226_ = lean_box(v___x_225_);
v_out_227_ = lean_array_fset(v_cache_223_, v_idx_224_, v___x_226_);
return v_out_227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg___boxed(lean_object* v_cache_228_, lean_object* v_idx_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_cache_228_, v_idx_229_);
lean_dec(v_idx_229_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(lean_object* v_aig_231_, lean_object* v_cnf_232_, lean_object* v_lhs_233_, lean_object* v_rhs_234_, lean_object* v_cache_235_, lean_object* v_hlb_236_, lean_object* v_hrb_237_, lean_object* v_idx_238_, lean_object* v_h_239_, lean_object* v_htip_240_, lean_object* v_hl_241_, lean_object* v_hr_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_cache_235_, v_idx_238_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___boxed(lean_object* v_aig_244_, lean_object* v_cnf_245_, lean_object* v_lhs_246_, lean_object* v_rhs_247_, lean_object* v_cache_248_, lean_object* v_hlb_249_, lean_object* v_hrb_250_, lean_object* v_idx_251_, lean_object* v_h_252_, lean_object* v_htip_253_, lean_object* v_hl_254_, lean_object* v_hr_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(v_aig_244_, v_cnf_245_, v_lhs_246_, v_rhs_247_, v_cache_248_, v_hlb_249_, v_hrb_250_, v_idx_251_, v_h_252_, v_htip_253_, v_hl_254_, v_hr_255_);
lean_dec(v_idx_251_);
lean_dec(v_rhs_247_);
lean_dec(v_lhs_246_);
lean_dec_ref(v_cnf_245_);
lean_dec_ref(v_aig_244_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty(lean_object* v_aig_257_){
_start:
{
lean_object* v_decls_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_decls_258_ = lean_ctor_get(v_aig_257_, 0);
v___x_259_ = lean_array_get_size(v_decls_258_);
v___x_260_ = lean_unsigned_to_nat(2u);
v___x_261_ = lean_nat_mul(v___x_259_, v___x_260_);
v___x_262_ = lean_mk_empty_array_with_capacity(v___x_261_);
lean_dec(v___x_261_);
v___x_263_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(v_aig_257_);
v_isSharedCheck_270_ = !lean_is_exclusive(v_aig_257_);
if (v_isSharedCheck_270_ == 0)
{
lean_object* v_unused_271_; lean_object* v_unused_272_; 
v_unused_271_ = lean_ctor_get(v_aig_257_, 1);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v_aig_257_, 0);
lean_dec(v_unused_272_);
v___x_265_ = v_aig_257_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_dec(v_aig_257_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v___x_263_);
lean_ctor_set(v___x_265_, 0, v___x_262_);
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v___x_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(lean_object* v_state_273_, lean_object* v_idx_274_){
_start:
{
lean_object* v_cnf_275_; lean_object* v_cache_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_286_; 
v_cnf_275_ = lean_ctor_get(v_state_273_, 0);
v_cache_276_ = lean_ctor_get(v_state_273_, 1);
v_isSharedCheck_286_ = !lean_is_exclusive(v_state_273_);
if (v_isSharedCheck_286_ == 0)
{
v___x_278_ = v_state_273_;
v_isShared_279_ = v_isSharedCheck_286_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_cache_276_);
lean_inc(v_cnf_275_);
lean_dec(v_state_273_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_286_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v_val_280_; lean_object* v_newCnf_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v_val_280_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_276_, v_idx_274_);
v_newCnf_281_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(v_idx_274_);
v___x_282_ = l_Array_append___redArg(v_cnf_275_, v_newCnf_281_);
lean_dec_ref(v_newCnf_281_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 1, v_val_280_);
lean_ctor_set(v___x_278_, 0, v___x_282_);
v___x_284_ = v___x_278_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_val_280_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(lean_object* v_aig_287_, lean_object* v_state_288_, lean_object* v_idx_289_, lean_object* v_h_290_, lean_object* v_htip_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(v_state_288_, v_idx_289_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___boxed(lean_object* v_aig_293_, lean_object* v_state_294_, lean_object* v_idx_295_, lean_object* v_h_296_, lean_object* v_htip_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(v_aig_293_, v_state_294_, v_idx_295_, v_h_296_, v_htip_297_);
lean_dec_ref(v_aig_293_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(lean_object* v_aig_299_, lean_object* v_a_300_, lean_object* v_state_301_, lean_object* v_idx_302_){
_start:
{
lean_object* v_cnf_303_; lean_object* v_cache_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_317_; 
v_cnf_303_ = lean_ctor_get(v_state_301_, 0);
v_cache_304_ = lean_ctor_get(v_state_301_, 1);
v_isSharedCheck_317_ = !lean_is_exclusive(v_state_301_);
if (v_isSharedCheck_317_ == 0)
{
v___x_306_ = v_state_301_;
v_isShared_307_ = v_isSharedCheck_317_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_cache_304_);
lean_inc(v_cnf_303_);
lean_dec(v_state_301_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_317_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v_decls_308_; lean_object* v_val_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v_newCnf_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v_decls_308_ = lean_ctor_get(v_aig_299_, 0);
v_val_309_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_304_, v_idx_302_);
v___x_310_ = lean_array_get_size(v_decls_308_);
v___x_311_ = lean_nat_add(v_a_300_, v___x_310_);
v_newCnf_312_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg(v_idx_302_, v___x_311_);
v___x_313_ = l_Array_append___redArg(v_cnf_303_, v_newCnf_312_);
lean_dec_ref(v_newCnf_312_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v_val_309_);
lean_ctor_set(v___x_306_, 0, v___x_313_);
v___x_315_ = v___x_306_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_val_309_);
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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg___boxed(lean_object* v_aig_318_, lean_object* v_a_319_, lean_object* v_state_320_, lean_object* v_idx_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_aig_318_, v_a_319_, v_state_320_, v_idx_321_);
lean_dec(v_a_319_);
lean_dec_ref(v_aig_318_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(lean_object* v_aig_323_, lean_object* v_a_324_, lean_object* v_state_325_, lean_object* v_idx_326_, lean_object* v_h_327_, lean_object* v_htip_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_aig_323_, v_a_324_, v_state_325_, v_idx_326_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___boxed(lean_object* v_aig_330_, lean_object* v_a_331_, lean_object* v_state_332_, lean_object* v_idx_333_, lean_object* v_h_334_, lean_object* v_htip_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(v_aig_330_, v_a_331_, v_state_332_, v_idx_333_, v_h_334_, v_htip_335_);
lean_dec(v_a_331_);
lean_dec_ref(v_aig_330_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(lean_object* v_lhs_337_, lean_object* v_rhs_338_, lean_object* v_state_339_, lean_object* v_idx_340_){
_start:
{
lean_object* v_cnf_341_; lean_object* v_cache_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_362_; 
v_cnf_341_ = lean_ctor_get(v_state_339_, 0);
v_cache_342_ = lean_ctor_get(v_state_339_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_state_339_);
if (v_isSharedCheck_362_ == 0)
{
v___x_344_ = v_state_339_;
v_isShared_345_ = v_isSharedCheck_362_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_cache_342_);
lean_inc(v_cnf_341_);
lean_dec(v_state_339_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_362_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; lean_object* v_val_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; uint8_t v___x_356_; lean_object* v_newCnf_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = lean_nat_land(v___x_346_, v_lhs_337_);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_nat_dec_eq(v___x_347_, v___x_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_nat_land(v___x_346_, v_rhs_338_);
v___x_351_ = lean_nat_dec_eq(v___x_350_, v___x_348_);
lean_dec(v___x_350_);
v_val_352_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_cache_342_, v_idx_340_);
v___x_353_ = lean_nat_shiftr(v_lhs_337_, v___x_346_);
v___x_354_ = lean_nat_shiftr(v_rhs_338_, v___x_346_);
v___x_355_ = lean_bool_not(v___x_349_);
v___x_356_ = lean_bool_not(v___x_351_);
v_newCnf_357_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_idx_340_, v___x_353_, v___x_354_, v___x_355_, v___x_356_);
v___x_358_ = l_Array_append___redArg(v_cnf_341_, v_newCnf_357_);
lean_dec_ref(v_newCnf_357_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 1, v_val_352_);
lean_ctor_set(v___x_344_, 0, v___x_358_);
v___x_360_ = v___x_344_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_val_352_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg___boxed(lean_object* v_lhs_363_, lean_object* v_rhs_364_, lean_object* v_state_365_, lean_object* v_idx_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_lhs_363_, v_rhs_364_, v_state_365_, v_idx_366_);
lean_dec(v_rhs_364_);
lean_dec(v_lhs_363_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(lean_object* v_aig_368_, lean_object* v_lhs_369_, lean_object* v_rhs_370_, lean_object* v_state_371_, lean_object* v_hlb_372_, lean_object* v_hrb_373_, lean_object* v_idx_374_, lean_object* v_h_375_, lean_object* v_htip_376_, lean_object* v_hl_377_, lean_object* v_hr_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_lhs_369_, v_rhs_370_, v_state_371_, v_idx_374_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___boxed(lean_object* v_aig_380_, lean_object* v_lhs_381_, lean_object* v_rhs_382_, lean_object* v_state_383_, lean_object* v_hlb_384_, lean_object* v_hrb_385_, lean_object* v_idx_386_, lean_object* v_h_387_, lean_object* v_htip_388_, lean_object* v_hl_389_, lean_object* v_hr_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(v_aig_380_, v_lhs_381_, v_rhs_382_, v_state_383_, v_hlb_384_, v_hrb_385_, v_idx_386_, v_h_387_, v_htip_388_, v_hl_389_, v_hr_390_);
lean_dec(v_rhs_382_);
lean_dec(v_lhs_381_);
lean_dec_ref(v_aig_380_);
return v_res_391_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(lean_object* v_assign_392_, lean_object* v_state_393_){
_start:
{
lean_object* v_cnf_394_; uint8_t v___x_395_; 
v_cnf_394_ = lean_ctor_get(v_state_393_, 0);
v___x_395_ = l_Std_Sat_CNF_eval___redArg(v_assign_392_, v_cnf_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg___boxed(lean_object* v_assign_396_, lean_object* v_state_397_){
_start:
{
uint8_t v_res_398_; lean_object* v_r_399_; 
v_res_398_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(v_assign_396_, v_state_397_);
lean_dec_ref(v_state_397_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(lean_object* v_aig_400_, lean_object* v_assign_401_, lean_object* v_state_402_){
_start:
{
uint8_t v___x_403_; 
v___x_403_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(v_assign_401_, v_state_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___boxed(lean_object* v_aig_404_, lean_object* v_assign_405_, lean_object* v_state_406_){
_start:
{
uint8_t v_res_407_; lean_object* v_r_408_; 
v_res_407_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(v_aig_404_, v_assign_405_, v_state_406_);
lean_dec_ref(v_state_406_);
lean_dec_ref(v_aig_404_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(lean_object* v_aig_409_, lean_object* v_upper_410_, lean_object* v_state_411_){
_start:
{
lean_object* v_cache_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v_cache_412_ = lean_ctor_get(v_state_411_, 1);
v___x_413_ = lean_array_fget_borrowed(v_cache_412_, v_upper_410_);
v___x_414_ = lean_unbox(v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v_decls_415_; lean_object* v_decl_416_; 
v_decls_415_ = lean_ctor_get(v_aig_409_, 0);
v_decl_416_ = lean_array_fget_borrowed(v_decls_415_, v_upper_410_);
switch(lean_obj_tag(v_decl_416_))
{
case 0:
{
lean_object* v___x_417_; 
v___x_417_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(v_state_411_, v_upper_410_);
return v___x_417_;
}
case 1:
{
lean_object* v_idx_418_; lean_object* v___x_419_; 
v_idx_418_ = lean_ctor_get(v_decl_416_, 0);
v___x_419_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_aig_409_, v_idx_418_, v_state_411_, v_upper_410_);
return v___x_419_;
}
default: 
{
lean_object* v_l_420_; lean_object* v_r_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v_val_424_; lean_object* v___x_425_; lean_object* v_val_426_; lean_object* v_val_427_; 
v_l_420_ = lean_ctor_get(v_decl_416_, 0);
v_r_421_ = lean_ctor_get(v_decl_416_, 1);
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_nat_shiftr(v_l_420_, v___x_422_);
v_val_424_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_409_, v___x_423_, v_state_411_);
v___x_425_ = lean_nat_shiftr(v_r_421_, v___x_422_);
v_val_426_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_409_, v___x_425_, v_val_424_);
v_val_427_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_l_420_, v_r_421_, v_val_426_, v_upper_410_);
return v_val_427_;
}
}
}
else
{
lean_dec(v_upper_410_);
return v_state_411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg___boxed(lean_object* v_aig_428_, lean_object* v_upper_429_, lean_object* v_state_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_428_, v_upper_429_, v_state_430_);
lean_dec_ref(v_aig_428_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go(lean_object* v_aig_432_, lean_object* v_upper_433_, lean_object* v_h_434_, lean_object* v_state_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_432_, v_upper_433_, v_state_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___boxed(lean_object* v_aig_437_, lean_object* v_upper_438_, lean_object* v_h_439_, lean_object* v_state_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go(v_aig_437_, v_upper_438_, v_h_439_, v_state_440_);
lean_dec_ref(v_aig_437_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__13_splitter___redArg(lean_object* v_decl_442_, lean_object* v_h__1_443_, lean_object* v_h__2_444_, lean_object* v_h__3_445_){
_start:
{
switch(lean_obj_tag(v_decl_442_))
{
case 0:
{
lean_object* v___x_446_; 
lean_dec(v_h__3_445_);
lean_dec(v_h__2_444_);
v___x_446_ = lean_apply_1(v_h__1_443_, lean_box(0));
return v___x_446_;
}
case 1:
{
lean_object* v_idx_447_; lean_object* v___x_448_; 
lean_dec(v_h__3_445_);
lean_dec(v_h__1_443_);
v_idx_447_ = lean_ctor_get(v_decl_442_, 0);
lean_inc(v_idx_447_);
lean_dec_ref_known(v_decl_442_, 1);
v___x_448_ = lean_apply_2(v_h__2_444_, v_idx_447_, lean_box(0));
return v___x_448_;
}
default: 
{
lean_object* v_l_449_; lean_object* v_r_450_; lean_object* v___x_451_; 
lean_dec(v_h__2_444_);
lean_dec(v_h__1_443_);
v_l_449_ = lean_ctor_get(v_decl_442_, 0);
lean_inc(v_l_449_);
v_r_450_ = lean_ctor_get(v_decl_442_, 1);
lean_inc(v_r_450_);
lean_dec_ref_known(v_decl_442_, 2);
v___x_451_ = lean_apply_3(v_h__3_445_, v_l_449_, v_r_450_, lean_box(0));
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__13_splitter(lean_object* v_motive_452_, lean_object* v_decl_453_, lean_object* v_h__1_454_, lean_object* v_h__2_455_, lean_object* v_h__3_456_){
_start:
{
switch(lean_obj_tag(v_decl_453_))
{
case 0:
{
lean_object* v___x_457_; 
lean_dec(v_h__3_456_);
lean_dec(v_h__2_455_);
v___x_457_ = lean_apply_1(v_h__1_454_, lean_box(0));
return v___x_457_;
}
case 1:
{
lean_object* v_idx_458_; lean_object* v___x_459_; 
lean_dec(v_h__3_456_);
lean_dec(v_h__1_454_);
v_idx_458_ = lean_ctor_get(v_decl_453_, 0);
lean_inc(v_idx_458_);
lean_dec_ref_known(v_decl_453_, 1);
v___x_459_ = lean_apply_2(v_h__2_455_, v_idx_458_, lean_box(0));
return v___x_459_;
}
default: 
{
lean_object* v_l_460_; lean_object* v_r_461_; lean_object* v___x_462_; 
lean_dec(v_h__2_455_);
lean_dec(v_h__1_454_);
v_l_460_ = lean_ctor_get(v_decl_453_, 0);
lean_inc(v_l_460_);
v_r_461_ = lean_ctor_get(v_decl_453_, 1);
lean_inc(v_r_461_);
lean_dec_ref_known(v_decl_453_, 2);
v___x_462_ = lean_apply_3(v_h__3_456_, v_l_460_, v_r_461_, lean_box(0));
return v___x_462_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__21_splitter___redArg(lean_object* v_x_463_, lean_object* v_h__1_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = lean_apply_2(v_h__1_464_, v_x_463_, lean_box(0));
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__21_splitter(lean_object* v_aig_466_, lean_object* v_upper_467_, lean_object* v_h_468_, lean_object* v_state_469_, lean_object* v_lhs_470_, lean_object* v_rhs_471_, lean_object* v_this_472_, lean_object* v_motive_473_, lean_object* v_x_474_, lean_object* v_h__1_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = lean_apply_2(v_h__1_475_, v_x_474_, lean_box(0));
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__21_splitter___boxed(lean_object* v_aig_477_, lean_object* v_upper_478_, lean_object* v_h_479_, lean_object* v_state_480_, lean_object* v_lhs_481_, lean_object* v_rhs_482_, lean_object* v_this_483_, lean_object* v_motive_484_, lean_object* v_x_485_, lean_object* v_h__1_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__21_splitter(v_aig_477_, v_upper_478_, v_h_479_, v_state_480_, v_lhs_481_, v_rhs_482_, v_this_483_, v_motive_484_, v_x_485_, v_h__1_486_);
lean_dec(v_rhs_482_);
lean_dec(v_lhs_481_);
lean_dec_ref(v_state_480_);
lean_dec(v_upper_478_);
lean_dec_ref(v_aig_477_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__19_splitter___redArg(lean_object* v_x_488_, lean_object* v_h__1_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = lean_apply_2(v_h__1_489_, v_x_488_, lean_box(0));
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__19_splitter(lean_object* v_aig_491_, lean_object* v_upper_492_, lean_object* v_h_493_, lean_object* v_lhs_494_, lean_object* v_rhs_495_, lean_object* v_this_496_, lean_object* v_lstate_497_, lean_object* v_motive_498_, lean_object* v_x_499_, lean_object* v_h__1_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = lean_apply_2(v_h__1_500_, v_x_499_, lean_box(0));
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__19_splitter___boxed(lean_object* v_aig_502_, lean_object* v_upper_503_, lean_object* v_h_504_, lean_object* v_lhs_505_, lean_object* v_rhs_506_, lean_object* v_this_507_, lean_object* v_lstate_508_, lean_object* v_motive_509_, lean_object* v_x_510_, lean_object* v_h__1_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__19_splitter(v_aig_502_, v_upper_503_, v_h_504_, v_lhs_505_, v_rhs_506_, v_this_507_, v_lstate_508_, v_motive_509_, v_x_510_, v_h__1_511_);
lean_dec_ref(v_lstate_508_);
lean_dec(v_rhs_506_);
lean_dec(v_lhs_505_);
lean_dec(v_upper_503_);
lean_dec_ref(v_aig_502_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__16_splitter___redArg(lean_object* v_x_513_, lean_object* v_h__1_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = lean_apply_2(v_h__1_514_, v_x_513_, lean_box(0));
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__16_splitter(lean_object* v_aig_516_, lean_object* v_upper_517_, lean_object* v_h_518_, lean_object* v_rstate_519_, lean_object* v_motive_520_, lean_object* v_x_521_, lean_object* v_h__1_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = lean_apply_2(v_h__1_522_, v_x_521_, lean_box(0));
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__16_splitter___boxed(lean_object* v_aig_524_, lean_object* v_upper_525_, lean_object* v_h_526_, lean_object* v_rstate_527_, lean_object* v_motive_528_, lean_object* v_x_529_, lean_object* v_h__1_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__16_splitter(v_aig_524_, v_upper_525_, v_h_526_, v_rstate_527_, v_motive_528_, v_x_529_, v_h__1_530_);
lean_dec_ref(v_rstate_527_);
lean_dec(v_upper_525_);
lean_dec_ref(v_aig_524_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF(lean_object* v_entry_532_){
_start:
{
lean_object* v_ref_533_; lean_object* v_aig_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_558_; 
v_ref_533_ = lean_ctor_get(v_entry_532_, 1);
v_aig_534_ = lean_ctor_get(v_entry_532_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v_entry_532_);
if (v_isSharedCheck_558_ == 0)
{
v___x_536_ = v_entry_532_;
v_isShared_537_ = v_isSharedCheck_558_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_ref_533_);
lean_inc(v_aig_534_);
lean_dec(v_entry_532_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_558_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v_gate_538_; uint8_t v_invert_539_; lean_object* v___x_540_; lean_object* v_val_541_; lean_object* v_cnf_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_556_; 
v_gate_538_ = lean_ctor_get(v_ref_533_, 0);
lean_inc_n(v_gate_538_, 2);
v_invert_539_ = lean_ctor_get_uint8(v_ref_533_, sizeof(void*)*1);
lean_dec_ref(v_ref_533_);
lean_inc_ref(v_aig_534_);
v___x_540_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty(v_aig_534_);
v_val_541_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_534_, v_gate_538_, v___x_540_);
lean_dec_ref(v_aig_534_);
v_cnf_542_ = lean_ctor_get(v_val_541_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v_val_541_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v_val_541_, 1);
lean_dec(v_unused_557_);
v___x_544_ = v_val_541_;
v_isShared_545_ = v_isSharedCheck_556_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_cnf_542_);
lean_dec(v_val_541_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_556_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_546_ = lean_bool_not(v_invert_539_);
v___x_547_ = lean_box(v___x_546_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 1, v___x_547_);
lean_ctor_set(v___x_544_, 0, v_gate_538_);
v___x_549_ = v___x_544_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_gate_538_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v___x_547_);
v___x_549_ = v_reuseFailAlloc_555_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = lean_box(0);
if (v_isShared_537_ == 0)
{
lean_ctor_set_tag(v___x_536_, 1);
lean_ctor_set(v___x_536_, 1, v___x_550_);
lean_ctor_set(v___x_536_, 0, v___x_549_);
v___x_552_ = v___x_536_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v___x_550_);
v___x_552_ = v_reuseFailAlloc_554_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; 
v___x_553_ = lean_array_push(v_cnf_542_, v___x_552_);
return v___x_553_;
}
}
}
}
}
}
lean_object* runtime_initialize_Std_Sat_CNF(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_CNF(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sat_CNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_AIG_CNF(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_CNF(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_Lemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_CNF(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_CNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_AIG_CNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_AIG_CNF(builtin);
}
#ifdef __cplusplus
}
#endif
