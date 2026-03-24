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
uint8_t l_Std_Sat_CNF_eval___redArg(lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_denote_go___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___y_58_; uint8_t v___y_59_; uint8_t v___y_69_; 
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
if (v_rinv_42_ == 0)
{
v___y_69_ = v___x_43_;
goto v___jp_68_;
}
else
{
v___y_69_ = v___x_54_;
goto v___jp_68_;
}
v___jp_57_:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_60_ = lean_box(v___y_59_);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v_lhs_39_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_50_);
v___x_63_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_56_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
v___x_64_ = ((lean_object*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg___closed__0));
v___x_65_ = lean_array_push(v___x_64_, v___x_63_);
v___x_66_ = lean_array_push(v___x_65_, v___y_58_);
v___x_67_ = lean_array_push(v___x_66_, v___x_53_);
return v___x_67_;
}
v___jp_68_:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = lean_box(v___y_69_);
v___x_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_71_, 0, v_rhs_40_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___x_50_);
lean_inc_ref(v___x_56_);
v___x_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_56_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
if (v_linv_41_ == 0)
{
v___y_58_ = v___x_73_;
v___y_59_ = v___x_43_;
goto v___jp_57_;
}
else
{
v___y_58_ = v___x_73_;
v___y_59_ = v___x_54_;
goto v___jp_57_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg___boxed(lean_object* v_output_74_, lean_object* v_lhs_75_, lean_object* v_rhs_76_, lean_object* v_linv_77_, lean_object* v_rinv_78_){
_start:
{
uint8_t v_linv_boxed_79_; uint8_t v_rinv_boxed_80_; lean_object* v_res_81_; 
v_linv_boxed_79_ = lean_unbox(v_linv_77_);
v_rinv_boxed_80_ = lean_unbox(v_rinv_78_);
v_res_81_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_output_74_, v_lhs_75_, v_rhs_76_, v_linv_boxed_79_, v_rinv_boxed_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF(lean_object* v_00_u03b1_82_, lean_object* v_output_83_, lean_object* v_lhs_84_, lean_object* v_rhs_85_, uint8_t v_linv_86_, uint8_t v_rinv_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_output_83_, v_lhs_84_, v_rhs_85_, v_linv_86_, v_rinv_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___boxed(lean_object* v_00_u03b1_89_, lean_object* v_output_90_, lean_object* v_lhs_91_, lean_object* v_rhs_92_, lean_object* v_linv_93_, lean_object* v_rinv_94_){
_start:
{
uint8_t v_linv_boxed_95_; uint8_t v_rinv_boxed_96_; lean_object* v_res_97_; 
v_linv_boxed_95_ = lean_unbox(v_linv_93_);
v_rinv_boxed_96_ = lean_unbox(v_rinv_94_);
v_res_97_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF(v_00_u03b1_89_, v_output_90_, v_lhs_91_, v_rhs_92_, v_linv_boxed_95_, v_rinv_boxed_96_);
return v_res_97_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns(lean_object* v_aig_98_, lean_object* v_assign1_99_, lean_object* v_assign2_100_, lean_object* v_var_101_){
_start:
{
lean_object* v_decls_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_decls_102_ = lean_ctor_get(v_aig_98_, 0);
v___x_103_ = lean_array_get_size(v_decls_102_);
v___x_104_ = lean_nat_dec_lt(v_var_101_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
lean_dec_ref(v_assign2_100_);
v___x_105_ = lean_nat_sub(v_var_101_, v___x_103_);
lean_dec(v_var_101_);
v___x_106_ = lean_apply_1(v_assign1_99_, v___x_105_);
v___x_107_ = lean_unbox(v___x_106_);
return v___x_107_;
}
else
{
lean_object* v___x_108_; uint8_t v___x_109_; 
lean_dec_ref(v_assign1_99_);
v___x_108_ = lean_apply_1(v_assign2_100_, v_var_101_);
v___x_109_ = lean_unbox(v___x_108_);
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns___boxed(lean_object* v_aig_110_, lean_object* v_assign1_111_, lean_object* v_assign2_112_, lean_object* v_var_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns(v_aig_110_, v_assign1_111_, v_assign2_112_, v_var_113_);
lean_dec_ref(v_aig_110_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign(lean_object* v_aig_116_, lean_object* v_assign_117_, lean_object* v_var_118_){
_start:
{
lean_object* v_decls_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v_decls_119_ = lean_ctor_get(v_aig_116_, 0);
v___x_120_ = lean_array_get_size(v_decls_119_);
v___x_121_ = lean_nat_add(v_var_118_, v___x_120_);
v___x_122_ = lean_apply_1(v_assign_117_, v___x_121_);
v___x_123_ = lean_unbox(v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign___boxed(lean_object* v_aig_124_, lean_object* v_assign_125_, lean_object* v_var_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectLeftAssign(v_aig_124_, v_assign_125_, v_var_126_);
lean_dec(v_var_126_);
lean_dec_ref(v_aig_124_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign(lean_object* v_assign_129_, lean_object* v_idx_130_){
_start:
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = lean_apply_1(v_assign_129_, v_idx_130_);
v___x_132_ = lean_unbox(v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign___boxed(lean_object* v_assign_133_, lean_object* v_idx_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_projectRightAssign(v_assign_133_, v_idx_134_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(lean_object* v_assign_137_, lean_object* v_entry_138_){
_start:
{
uint8_t v___y_140_; lean_object* v_ref_143_; lean_object* v_aig_144_; lean_object* v_gate_145_; uint8_t v_invert_146_; lean_object* v_decls_147_; uint8_t v___x_148_; 
v_ref_143_ = lean_ctor_get(v_entry_138_, 1);
v_aig_144_ = lean_ctor_get(v_entry_138_, 0);
v_gate_145_ = lean_ctor_get(v_ref_143_, 0);
v_invert_146_ = lean_ctor_get_uint8(v_ref_143_, sizeof(void*)*1);
v_decls_147_ = lean_ctor_get(v_aig_144_, 0);
v___x_148_ = l_Std_Sat_AIG_denote_go___redArg(v_gate_145_, v_decls_147_, v_assign_137_);
if (v___x_148_ == 0)
{
if (v_invert_146_ == 0)
{
return v_invert_146_;
}
else
{
v___y_140_ = v___x_148_;
goto v___jp_139_;
}
}
else
{
v___y_140_ = v_invert_146_;
goto v___jp_139_;
}
v___jp_139_:
{
if (v___y_140_ == 0)
{
uint8_t v___x_141_; 
v___x_141_ = 1;
return v___x_141_;
}
else
{
uint8_t v___x_142_; 
v___x_142_ = 0;
return v___x_142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0___boxed(lean_object* v_assign_149_, lean_object* v_entry_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(v_assign_149_, v_entry_150_);
lean_dec_ref(v_entry_150_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0(lean_object* v_aig_153_, lean_object* v_assign1_154_, lean_object* v_idx_155_){
_start:
{
uint8_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_156_ = 0;
v___x_157_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_157_, 0, v_idx_155_);
lean_ctor_set_uint8(v___x_157_, sizeof(void*)*1, v___x_156_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v_aig_153_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = l_Std_Sat_AIG_denote___at___00__private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment_spec__0(v_assign1_154_, v___x_158_);
lean_dec_ref(v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0___boxed(lean_object* v_aig_160_, lean_object* v_assign1_161_, lean_object* v_idx_162_){
_start:
{
uint8_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0(v_aig_160_, v_assign1_161_, v_idx_162_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(lean_object* v_aig_165_, lean_object* v_assign1_166_, lean_object* v_var_167_){
_start:
{
lean_object* v___f_168_; uint8_t v___x_169_; 
lean_inc_ref(v_assign1_166_);
lean_inc_ref(v_aig_165_);
v___f_168_ = lean_alloc_closure((void*)(l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___lam__0___boxed), 3, 2);
lean_closure_set(v___f_168_, 0, v_aig_165_);
lean_closure_set(v___f_168_, 1, v_assign1_166_);
v___x_169_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_mixAssigns(v_aig_165_, v_assign1_166_, v___f_168_, v_var_167_);
lean_dec_ref(v_aig_165_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment___boxed(lean_object* v_aig_170_, lean_object* v_assign1_171_, lean_object* v_var_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_cnfSatAssignment(v_aig_170_, v_assign1_171_, v_var_172_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(lean_object* v_aig_175_){
_start:
{
lean_object* v_decls_176_; lean_object* v___x_177_; uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_decls_176_ = lean_ctor_get(v_aig_175_, 0);
v___x_177_ = lean_array_get_size(v_decls_176_);
v___x_178_ = 0;
v___x_179_ = lean_box(v___x_178_);
v___x_180_ = lean_mk_array(v___x_177_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___boxed(lean_object* v_aig_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(v_aig_181_);
lean_dec_ref(v_aig_181_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(lean_object* v_cache_183_, lean_object* v_idx_184_){
_start:
{
uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v_out_187_; 
v___x_185_ = 1;
v___x_186_ = lean_box(v___x_185_);
v_out_187_ = lean_array_fset(v_cache_183_, v_idx_184_, v___x_186_);
return v_out_187_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg___boxed(lean_object* v_cache_188_, lean_object* v_idx_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_188_, v_idx_189_);
lean_dec(v_idx_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(lean_object* v_aig_191_, lean_object* v_cnf_192_, lean_object* v_cache_193_, lean_object* v_idx_194_, lean_object* v_h_195_, lean_object* v_htip_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_193_, v_idx_194_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___boxed(lean_object* v_aig_198_, lean_object* v_cnf_199_, lean_object* v_cache_200_, lean_object* v_idx_201_, lean_object* v_h_202_, lean_object* v_htip_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse(v_aig_198_, v_cnf_199_, v_cache_200_, v_idx_201_, v_h_202_, v_htip_203_);
lean_dec(v_idx_201_);
lean_dec_ref(v_cnf_199_);
lean_dec_ref(v_aig_198_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(lean_object* v_cache_205_, lean_object* v_idx_206_){
_start:
{
uint8_t v___x_207_; lean_object* v___x_208_; lean_object* v_out_209_; 
v___x_207_ = 1;
v___x_208_ = lean_box(v___x_207_);
v_out_209_ = lean_array_fset(v_cache_205_, v_idx_206_, v___x_208_);
return v_out_209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg___boxed(lean_object* v_cache_210_, lean_object* v_idx_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_210_, v_idx_211_);
lean_dec(v_idx_211_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(lean_object* v_aig_213_, lean_object* v_cnf_214_, lean_object* v_a_215_, lean_object* v_cache_216_, lean_object* v_idx_217_, lean_object* v_h_218_, lean_object* v_htip_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_216_, v_idx_217_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___boxed(lean_object* v_aig_221_, lean_object* v_cnf_222_, lean_object* v_a_223_, lean_object* v_cache_224_, lean_object* v_idx_225_, lean_object* v_h_226_, lean_object* v_htip_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom(v_aig_221_, v_cnf_222_, v_a_223_, v_cache_224_, v_idx_225_, v_h_226_, v_htip_227_);
lean_dec(v_idx_225_);
lean_dec(v_a_223_);
lean_dec_ref(v_cnf_222_);
lean_dec_ref(v_aig_221_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(lean_object* v_lhs_229_, lean_object* v_rhs_230_, lean_object* v_cache_231_, lean_object* v_idx_232_){
_start:
{
uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v_out_235_; 
v___x_233_ = 1;
v___x_234_ = lean_box(v___x_233_);
v_out_235_ = lean_array_fset(v_cache_231_, v_idx_232_, v___x_234_);
return v_out_235_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg___boxed(lean_object* v_lhs_236_, lean_object* v_rhs_237_, lean_object* v_cache_238_, lean_object* v_idx_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_236_, v_rhs_237_, v_cache_238_, v_idx_239_);
lean_dec(v_idx_239_);
lean_dec(v_rhs_237_);
lean_dec(v_lhs_236_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(lean_object* v_aig_241_, lean_object* v_cnf_242_, lean_object* v_lhs_243_, lean_object* v_rhs_244_, lean_object* v_cache_245_, lean_object* v_hlb_246_, lean_object* v_hrb_247_, lean_object* v_idx_248_, lean_object* v_h_249_, lean_object* v_htip_250_, lean_object* v_hl_251_, lean_object* v_hr_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_243_, v_rhs_244_, v_cache_245_, v_idx_248_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___boxed(lean_object* v_aig_254_, lean_object* v_cnf_255_, lean_object* v_lhs_256_, lean_object* v_rhs_257_, lean_object* v_cache_258_, lean_object* v_hlb_259_, lean_object* v_hrb_260_, lean_object* v_idx_261_, lean_object* v_h_262_, lean_object* v_htip_263_, lean_object* v_hl_264_, lean_object* v_hr_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate(v_aig_254_, v_cnf_255_, v_lhs_256_, v_rhs_257_, v_cache_258_, v_hlb_259_, v_hrb_260_, v_idx_261_, v_h_262_, v_htip_263_, v_hl_264_, v_hr_265_);
lean_dec(v_idx_261_);
lean_dec(v_rhs_257_);
lean_dec(v_lhs_256_);
lean_dec_ref(v_cnf_255_);
lean_dec_ref(v_aig_254_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty(lean_object* v_aig_267_){
_start:
{
lean_object* v_decls_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
v_decls_268_ = lean_ctor_get(v_aig_267_, 0);
v___x_269_ = lean_array_get_size(v_decls_268_);
v___x_270_ = lean_unsigned_to_nat(2u);
v___x_271_ = lean_nat_mul(v___x_269_, v___x_270_);
v___x_272_ = lean_mk_empty_array_with_capacity(v___x_271_);
lean_dec(v___x_271_);
v___x_273_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init(v_aig_267_);
v_isSharedCheck_280_ = !lean_is_exclusive(v_aig_267_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; lean_object* v_unused_282_; 
v_unused_281_ = lean_ctor_get(v_aig_267_, 1);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_aig_267_, 0);
lean_dec(v_unused_282_);
v___x_275_ = v_aig_267_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_dec(v_aig_267_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v___x_273_);
lean_ctor_set(v___x_275_, 0, v___x_272_);
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(lean_object* v_state_283_, lean_object* v_idx_284_){
_start:
{
lean_object* v_cnf_285_; lean_object* v_cache_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_296_; 
v_cnf_285_ = lean_ctor_get(v_state_283_, 0);
v_cache_286_ = lean_ctor_get(v_state_283_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v_state_283_);
if (v_isSharedCheck_296_ == 0)
{
v___x_288_ = v_state_283_;
v_isShared_289_ = v_isSharedCheck_296_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_cache_286_);
lean_inc(v_cnf_285_);
lean_dec(v_state_283_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_296_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v_val_290_; lean_object* v_newCnf_291_; lean_object* v___x_292_; lean_object* v___x_294_; 
v_val_290_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addFalse___redArg(v_cache_286_, v_idx_284_);
v_newCnf_291_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_falseToCNF___redArg(v_idx_284_);
v___x_292_ = l_Array_append___redArg(v_cnf_285_, v_newCnf_291_);
lean_dec_ref(v_newCnf_291_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 1, v_val_290_);
lean_ctor_set(v___x_288_, 0, v___x_292_);
v___x_294_ = v___x_288_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_val_290_);
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
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(lean_object* v_aig_297_, lean_object* v_state_298_, lean_object* v_idx_299_, lean_object* v_h_300_, lean_object* v_htip_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(v_state_298_, v_idx_299_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___boxed(lean_object* v_aig_303_, lean_object* v_state_304_, lean_object* v_idx_305_, lean_object* v_h_306_, lean_object* v_htip_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse(v_aig_303_, v_state_304_, v_idx_305_, v_h_306_, v_htip_307_);
lean_dec_ref(v_aig_303_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(lean_object* v_aig_309_, lean_object* v_a_310_, lean_object* v_state_311_, lean_object* v_idx_312_){
_start:
{
lean_object* v_cnf_313_; lean_object* v_cache_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_327_; 
v_cnf_313_ = lean_ctor_get(v_state_311_, 0);
v_cache_314_ = lean_ctor_get(v_state_311_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v_state_311_);
if (v_isSharedCheck_327_ == 0)
{
v___x_316_ = v_state_311_;
v_isShared_317_ = v_isSharedCheck_327_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_cache_314_);
lean_inc(v_cnf_313_);
lean_dec(v_state_311_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_327_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v_decls_318_; lean_object* v_val_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v_newCnf_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
v_decls_318_ = lean_ctor_get(v_aig_309_, 0);
v_val_319_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addAtom___redArg(v_cache_314_, v_idx_312_);
v___x_320_ = lean_array_get_size(v_decls_318_);
v___x_321_ = lean_nat_add(v_a_310_, v___x_320_);
v_newCnf_322_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_atomToCNF___redArg(v_idx_312_, v___x_321_);
v___x_323_ = l_Array_append___redArg(v_cnf_313_, v_newCnf_322_);
lean_dec_ref(v_newCnf_322_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 1, v_val_319_);
lean_ctor_set(v___x_316_, 0, v___x_323_);
v___x_325_ = v___x_316_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_val_319_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg___boxed(lean_object* v_aig_328_, lean_object* v_a_329_, lean_object* v_state_330_, lean_object* v_idx_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_aig_328_, v_a_329_, v_state_330_, v_idx_331_);
lean_dec(v_a_329_);
lean_dec_ref(v_aig_328_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(lean_object* v_aig_333_, lean_object* v_a_334_, lean_object* v_state_335_, lean_object* v_idx_336_, lean_object* v_h_337_, lean_object* v_htip_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_aig_333_, v_a_334_, v_state_335_, v_idx_336_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___boxed(lean_object* v_aig_340_, lean_object* v_a_341_, lean_object* v_state_342_, lean_object* v_idx_343_, lean_object* v_h_344_, lean_object* v_htip_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom(v_aig_340_, v_a_341_, v_state_342_, v_idx_343_, v_h_344_, v_htip_345_);
lean_dec(v_a_341_);
lean_dec_ref(v_aig_340_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(lean_object* v_lhs_347_, lean_object* v_rhs_348_, lean_object* v_state_349_, lean_object* v_idx_350_){
_start:
{
lean_object* v_cnf_351_; lean_object* v_cache_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_380_; 
v_cnf_351_ = lean_ctor_get(v_state_349_, 0);
v_cache_352_ = lean_ctor_get(v_state_349_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v_state_349_);
if (v_isSharedCheck_380_ == 0)
{
v___x_354_ = v_state_349_;
v_isShared_355_ = v_isSharedCheck_380_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_cache_352_);
lean_inc(v_cnf_351_);
lean_dec(v_state_349_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_380_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___y_360_; uint8_t v___y_361_; uint8_t v___y_369_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = lean_nat_shiftr(v_lhs_347_, v___x_356_);
v___x_358_ = lean_nat_shiftr(v_rhs_348_, v___x_356_);
v___x_375_ = lean_nat_land(v___x_356_, v_lhs_347_);
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = lean_nat_dec_eq(v___x_375_, v___x_376_);
lean_dec(v___x_375_);
if (v___x_377_ == 0)
{
uint8_t v___x_378_; 
v___x_378_ = 1;
v___y_369_ = v___x_378_;
goto v___jp_368_;
}
else
{
uint8_t v___x_379_; 
v___x_379_ = 0;
v___y_369_ = v___x_379_;
goto v___jp_368_;
}
v___jp_359_:
{
lean_object* v_val_362_; lean_object* v_newCnf_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v_val_362_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_addGate___redArg(v_lhs_347_, v_rhs_348_, v_cache_352_, v_idx_350_);
v_newCnf_363_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_Decl_gateToCNF___redArg(v_idx_350_, v___x_357_, v___x_358_, v___y_360_, v___y_361_);
v___x_364_ = l_Array_append___redArg(v_cnf_351_, v_newCnf_363_);
lean_dec_ref(v_newCnf_363_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v_val_362_);
lean_ctor_set(v___x_354_, 0, v___x_364_);
v___x_366_ = v___x_354_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_val_362_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
v___jp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_370_ = lean_nat_land(v___x_356_, v_rhs_348_);
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = lean_nat_dec_eq(v___x_370_, v___x_371_);
lean_dec(v___x_370_);
if (v___x_372_ == 0)
{
uint8_t v___x_373_; 
v___x_373_ = 1;
v___y_360_ = v___y_369_;
v___y_361_ = v___x_373_;
goto v___jp_359_;
}
else
{
uint8_t v___x_374_; 
v___x_374_ = 0;
v___y_360_ = v___y_369_;
v___y_361_ = v___x_374_;
goto v___jp_359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg___boxed(lean_object* v_lhs_381_, lean_object* v_rhs_382_, lean_object* v_state_383_, lean_object* v_idx_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_lhs_381_, v_rhs_382_, v_state_383_, v_idx_384_);
lean_dec(v_rhs_382_);
lean_dec(v_lhs_381_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(lean_object* v_aig_386_, lean_object* v_lhs_387_, lean_object* v_rhs_388_, lean_object* v_state_389_, lean_object* v_hlb_390_, lean_object* v_hrb_391_, lean_object* v_idx_392_, lean_object* v_h_393_, lean_object* v_htip_394_, lean_object* v_hl_395_, lean_object* v_hr_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_lhs_387_, v_rhs_388_, v_state_389_, v_idx_392_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___boxed(lean_object* v_aig_398_, lean_object* v_lhs_399_, lean_object* v_rhs_400_, lean_object* v_state_401_, lean_object* v_hlb_402_, lean_object* v_hrb_403_, lean_object* v_idx_404_, lean_object* v_h_405_, lean_object* v_htip_406_, lean_object* v_hl_407_, lean_object* v_hr_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate(v_aig_398_, v_lhs_399_, v_rhs_400_, v_state_401_, v_hlb_402_, v_hrb_403_, v_idx_404_, v_h_405_, v_htip_406_, v_hl_407_, v_hr_408_);
lean_dec(v_rhs_400_);
lean_dec(v_lhs_399_);
lean_dec_ref(v_aig_398_);
return v_res_409_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(lean_object* v_assign_410_, lean_object* v_state_411_){
_start:
{
lean_object* v_cnf_412_; uint8_t v___x_413_; 
v_cnf_412_ = lean_ctor_get(v_state_411_, 0);
v___x_413_ = l_Std_Sat_CNF_eval___redArg(v_assign_410_, v_cnf_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg___boxed(lean_object* v_assign_414_, lean_object* v_state_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(v_assign_414_, v_state_415_);
lean_dec_ref(v_state_415_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(lean_object* v_aig_418_, lean_object* v_assign_419_, lean_object* v_state_420_){
_start:
{
uint8_t v___x_421_; 
v___x_421_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___redArg(v_assign_419_, v_state_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval___boxed(lean_object* v_aig_422_, lean_object* v_assign_423_, lean_object* v_state_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_eval(v_aig_422_, v_assign_423_, v_state_424_);
lean_dec_ref(v_state_424_);
lean_dec_ref(v_aig_422_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(lean_object* v_aig_427_, lean_object* v_upper_428_, lean_object* v_state_429_){
_start:
{
lean_object* v_cache_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v_cache_430_ = lean_ctor_get(v_state_429_, 1);
v___x_431_ = lean_array_fget_borrowed(v_cache_430_, v_upper_428_);
v___x_432_ = lean_unbox(v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v_decls_433_; lean_object* v_decl_434_; 
v_decls_433_ = lean_ctor_get(v_aig_427_, 0);
v_decl_434_ = lean_array_fget_borrowed(v_decls_433_, v_upper_428_);
switch(lean_obj_tag(v_decl_434_))
{
case 0:
{
lean_object* v___x_435_; 
v___x_435_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addFalse___redArg(v_state_429_, v_upper_428_);
return v___x_435_;
}
case 1:
{
lean_object* v_idx_436_; lean_object* v___x_437_; 
v_idx_436_ = lean_ctor_get(v_decl_434_, 0);
v___x_437_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addAtom___redArg(v_aig_427_, v_idx_436_, v_state_429_, v_upper_428_);
return v___x_437_;
}
default: 
{
lean_object* v_l_438_; lean_object* v_r_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v_val_442_; lean_object* v___x_443_; lean_object* v_val_444_; lean_object* v_val_445_; 
v_l_438_ = lean_ctor_get(v_decl_434_, 0);
v_r_439_ = lean_ctor_get(v_decl_434_, 1);
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_shiftr(v_l_438_, v___x_440_);
v_val_442_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_427_, v___x_441_, v_state_429_);
v___x_443_ = lean_nat_shiftr(v_r_439_, v___x_440_);
v_val_444_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_427_, v___x_443_, v_val_442_);
v_val_445_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_addGate___redArg(v_l_438_, v_r_439_, v_val_444_, v_upper_428_);
return v_val_445_;
}
}
}
else
{
lean_dec(v_upper_428_);
return v_state_429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg___boxed(lean_object* v_aig_446_, lean_object* v_upper_447_, lean_object* v_state_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_446_, v_upper_447_, v_state_448_);
lean_dec_ref(v_aig_446_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go(lean_object* v_aig_450_, lean_object* v_upper_451_, lean_object* v_h_452_, lean_object* v_state_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_450_, v_upper_451_, v_state_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___boxed(lean_object* v_aig_455_, lean_object* v_upper_456_, lean_object* v_h_457_, lean_object* v_state_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go(v_aig_455_, v_upper_456_, v_h_457_, v_state_458_);
lean_dec_ref(v_aig_455_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__13_splitter___redArg(lean_object* v_decl_460_, lean_object* v_h__1_461_, lean_object* v_h__2_462_, lean_object* v_h__3_463_){
_start:
{
switch(lean_obj_tag(v_decl_460_))
{
case 0:
{
lean_object* v___x_464_; 
lean_dec(v_h__3_463_);
lean_dec(v_h__2_462_);
v___x_464_ = lean_apply_1(v_h__1_461_, lean_box(0));
return v___x_464_;
}
case 1:
{
lean_object* v_idx_465_; lean_object* v___x_466_; 
lean_dec(v_h__3_463_);
lean_dec(v_h__1_461_);
v_idx_465_ = lean_ctor_get(v_decl_460_, 0);
lean_inc(v_idx_465_);
lean_dec_ref(v_decl_460_);
v___x_466_ = lean_apply_2(v_h__2_462_, v_idx_465_, lean_box(0));
return v___x_466_;
}
default: 
{
lean_object* v_l_467_; lean_object* v_r_468_; lean_object* v___x_469_; 
lean_dec(v_h__2_462_);
lean_dec(v_h__1_461_);
v_l_467_ = lean_ctor_get(v_decl_460_, 0);
lean_inc(v_l_467_);
v_r_468_ = lean_ctor_get(v_decl_460_, 1);
lean_inc(v_r_468_);
lean_dec_ref(v_decl_460_);
v___x_469_ = lean_apply_3(v_h__3_463_, v_l_467_, v_r_468_, lean_box(0));
return v___x_469_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go_match__13_splitter(lean_object* v_motive_470_, lean_object* v_decl_471_, lean_object* v_h__1_472_, lean_object* v_h__2_473_, lean_object* v_h__3_474_){
_start:
{
switch(lean_obj_tag(v_decl_471_))
{
case 0:
{
lean_object* v___x_475_; 
lean_dec(v_h__3_474_);
lean_dec(v_h__2_473_);
v___x_475_ = lean_apply_1(v_h__1_472_, lean_box(0));
return v___x_475_;
}
case 1:
{
lean_object* v_idx_476_; lean_object* v___x_477_; 
lean_dec(v_h__3_474_);
lean_dec(v_h__1_472_);
v_idx_476_ = lean_ctor_get(v_decl_471_, 0);
lean_inc(v_idx_476_);
lean_dec_ref(v_decl_471_);
v___x_477_ = lean_apply_2(v_h__2_473_, v_idx_476_, lean_box(0));
return v___x_477_;
}
default: 
{
lean_object* v_l_478_; lean_object* v_r_479_; lean_object* v___x_480_; 
lean_dec(v_h__2_473_);
lean_dec(v_h__1_472_);
v_l_478_ = lean_ctor_get(v_decl_471_, 0);
lean_inc(v_l_478_);
v_r_479_ = lean_ctor_get(v_decl_471_, 1);
lean_inc(v_r_479_);
lean_dec_ref(v_decl_471_);
v___x_480_ = lean_apply_3(v_h__3_474_, v_l_478_, v_r_479_, lean_box(0));
return v___x_480_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__21_splitter___redArg(lean_object* v_x_481_, lean_object* v_h__1_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = lean_apply_2(v_h__1_482_, v_x_481_, lean_box(0));
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__21_splitter(lean_object* v_aig_484_, lean_object* v_upper_485_, lean_object* v_h_486_, lean_object* v_state_487_, lean_object* v_lhs_488_, lean_object* v_rhs_489_, lean_object* v_this_490_, lean_object* v_motive_491_, lean_object* v_x_492_, lean_object* v_h__1_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = lean_apply_2(v_h__1_493_, v_x_492_, lean_box(0));
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__21_splitter___boxed(lean_object* v_aig_495_, lean_object* v_upper_496_, lean_object* v_h_497_, lean_object* v_state_498_, lean_object* v_lhs_499_, lean_object* v_rhs_500_, lean_object* v_this_501_, lean_object* v_motive_502_, lean_object* v_x_503_, lean_object* v_h__1_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__21_splitter(v_aig_495_, v_upper_496_, v_h_497_, v_state_498_, v_lhs_499_, v_rhs_500_, v_this_501_, v_motive_502_, v_x_503_, v_h__1_504_);
lean_dec(v_rhs_500_);
lean_dec(v_lhs_499_);
lean_dec_ref(v_state_498_);
lean_dec(v_upper_496_);
lean_dec_ref(v_aig_495_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__19_splitter___redArg(lean_object* v_x_506_, lean_object* v_h__1_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = lean_apply_2(v_h__1_507_, v_x_506_, lean_box(0));
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__19_splitter(lean_object* v_aig_509_, lean_object* v_upper_510_, lean_object* v_h_511_, lean_object* v_lhs_512_, lean_object* v_rhs_513_, lean_object* v_this_514_, lean_object* v_lstate_515_, lean_object* v_motive_516_, lean_object* v_x_517_, lean_object* v_h__1_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = lean_apply_2(v_h__1_518_, v_x_517_, lean_box(0));
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__19_splitter___boxed(lean_object* v_aig_520_, lean_object* v_upper_521_, lean_object* v_h_522_, lean_object* v_lhs_523_, lean_object* v_rhs_524_, lean_object* v_this_525_, lean_object* v_lstate_526_, lean_object* v_motive_527_, lean_object* v_x_528_, lean_object* v_h__1_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__19_splitter(v_aig_520_, v_upper_521_, v_h_522_, v_lhs_523_, v_rhs_524_, v_this_525_, v_lstate_526_, v_motive_527_, v_x_528_, v_h__1_529_);
lean_dec_ref(v_lstate_526_);
lean_dec(v_rhs_524_);
lean_dec(v_lhs_523_);
lean_dec(v_upper_521_);
lean_dec_ref(v_aig_520_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__16_splitter___redArg(lean_object* v_x_531_, lean_object* v_h__1_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = lean_apply_2(v_h__1_532_, v_x_531_, lean_box(0));
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__16_splitter(lean_object* v_aig_534_, lean_object* v_upper_535_, lean_object* v_h_536_, lean_object* v_rstate_537_, lean_object* v_motive_538_, lean_object* v_x_539_, lean_object* v_h__1_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = lean_apply_2(v_h__1_540_, v_x_539_, lean_box(0));
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__16_splitter___boxed(lean_object* v_aig_542_, lean_object* v_upper_543_, lean_object* v_h_544_, lean_object* v_rstate_545_, lean_object* v_motive_546_, lean_object* v_x_547_, lean_object* v_h__1_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_match__16_splitter(v_aig_542_, v_upper_543_, v_h_544_, v_rstate_545_, v_motive_546_, v_x_547_, v_h__1_548_);
lean_dec_ref(v_rstate_545_);
lean_dec(v_upper_543_);
lean_dec_ref(v_aig_542_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF(lean_object* v_entry_550_){
_start:
{
lean_object* v_ref_551_; lean_object* v_aig_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_579_; 
v_ref_551_ = lean_ctor_get(v_entry_550_, 1);
v_aig_552_ = lean_ctor_get(v_entry_550_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v_entry_550_);
if (v_isSharedCheck_579_ == 0)
{
v___x_554_ = v_entry_550_;
v_isShared_555_ = v_isSharedCheck_579_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_ref_551_);
lean_inc(v_aig_552_);
lean_dec(v_entry_550_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_579_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v_gate_556_; uint8_t v_invert_557_; lean_object* v___x_558_; lean_object* v_val_559_; uint8_t v___y_561_; 
v_gate_556_ = lean_ctor_get(v_ref_551_, 0);
lean_inc(v_gate_556_);
v_invert_557_ = lean_ctor_get_uint8(v_ref_551_, sizeof(void*)*1);
lean_dec_ref(v_ref_551_);
lean_inc_ref(v_aig_552_);
v___x_558_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_State_empty(v_aig_552_);
lean_inc(v_gate_556_);
v_val_559_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_go___redArg(v_aig_552_, v_gate_556_, v___x_558_);
lean_dec_ref(v_aig_552_);
if (v_invert_557_ == 0)
{
uint8_t v___x_577_; 
v___x_577_ = 1;
v___y_561_ = v___x_577_;
goto v___jp_560_;
}
else
{
uint8_t v___x_578_; 
v___x_578_ = 0;
v___y_561_ = v___x_578_;
goto v___jp_560_;
}
v___jp_560_:
{
lean_object* v_cnf_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_575_; 
v_cnf_562_ = lean_ctor_get(v_val_559_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v_val_559_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; 
v_unused_576_ = lean_ctor_get(v_val_559_, 1);
lean_dec(v_unused_576_);
v___x_564_ = v_val_559_;
v_isShared_565_ = v_isSharedCheck_575_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_cnf_562_);
lean_dec(v_val_559_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_575_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_566_ = lean_box(v___y_561_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 1, v___x_566_);
lean_ctor_set(v___x_564_, 0, v_gate_556_);
v___x_568_ = v___x_564_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_gate_556_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v___x_566_);
v___x_568_ = v_reuseFailAlloc_574_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_569_ = lean_box(0);
if (v_isShared_555_ == 0)
{
lean_ctor_set_tag(v___x_554_, 1);
lean_ctor_set(v___x_554_, 1, v___x_569_);
lean_ctor_set(v___x_554_, 0, v___x_568_);
v___x_571_ = v___x_554_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_569_);
v___x_571_ = v_reuseFailAlloc_573_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; 
v___x_572_ = lean_array_push(v_cnf_562_, v___x_571_);
return v___x_572_;
}
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
