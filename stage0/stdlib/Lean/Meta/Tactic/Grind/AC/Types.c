// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.Types
// Imports: public import Init.Grind.AC public import Std.Data.HashMap public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.AC.Seq
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
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_obj_tag_nat(lean_object*);
extern lean_object* l_Lean_Grind_AC_instInhabitedExpr_default;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Grind_AC_instInhabitedSeq_default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Grind_registerSolverExtension___redArg(lean_object*);
lean_object* l_Lean_Grind_AC_Seq_length(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_AC_instHashableExpr__lean = (const lean_object*)&l_Lean_Meta_Grind_AC_instHashableExpr__lean___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_AC_instHashableSeq__lean = (const lean_object*)&l_Lean_Meta_Grind_AC_instHashableSeq__lean___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_core_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_core_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase0_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase0_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_swap_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_swap_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__exact_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__exact_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__ac_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__ac_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__suffix_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__suffix_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__prefix_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__prefix_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__middle_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__middle_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac__idempotent_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac__idempotent_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__head__idempotent_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__head__idempotent_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__tail__idempotent_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__tail__idempotent_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_refl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_refl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup__rhs_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup__rhs_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase0__rhs_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase0__rhs_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof;
static lean_once_cell_t l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instInhabitedEqCnstr;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_AC_EqCnstr_compare(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_compare___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_core_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_core_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase__dup_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase__dup_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase0_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase0_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__exact_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__exact_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__ac_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__ac_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__suffix_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__suffix_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__prefix_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__prefix_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__middle_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__middle_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instInhabitedStruct_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instInhabitedStruct;
static const lean_array_object l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instInhabitedState;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_acExt;
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v_x_2_; uint64_t v___x_3_; uint64_t v___x_4_; uint64_t v___x_5_; 
v_x_2_ = lean_ctor_get(v_x_1_, 0);
v___x_3_ = 0ULL;
v___x_4_ = lean_uint64_of_nat(v_x_2_);
v___x_5_ = lean_uint64_mix_hash(v___x_3_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_lhs_6_; lean_object* v_rhs_7_; uint64_t v___x_8_; uint64_t v___x_9_; uint64_t v___x_10_; uint64_t v___x_11_; uint64_t v___x_12_; 
v_lhs_6_ = lean_ctor_get(v_x_1_, 0);
v_rhs_7_ = lean_ctor_get(v_x_1_, 1);
v___x_8_ = 1ULL;
v___x_9_ = l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(v_lhs_6_);
v___x_10_ = lean_uint64_mix_hash(v___x_8_, v___x_9_);
v___x_11_ = l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(v_rhs_7_);
v___x_12_ = lean_uint64_mix_hash(v___x_10_, v___x_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash___boxed(lean_object* v_x_13_){
_start:
{
uint64_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(v_x_13_);
lean_dec_ref(v_x_13_);
v_r_15_ = lean_box_uint64(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(lean_object* v_x_18_){
_start:
{
if (lean_obj_tag(v_x_18_) == 0)
{
lean_object* v_x_19_; uint64_t v___x_20_; uint64_t v___x_21_; uint64_t v___x_22_; 
v_x_19_ = lean_ctor_get(v_x_18_, 0);
v___x_20_ = 0ULL;
v___x_21_ = lean_uint64_of_nat(v_x_19_);
v___x_22_ = lean_uint64_mix_hash(v___x_20_, v___x_21_);
return v___x_22_;
}
else
{
lean_object* v_x_23_; lean_object* v_s_24_; uint64_t v___x_25_; uint64_t v___x_26_; uint64_t v___x_27_; uint64_t v___x_28_; uint64_t v___x_29_; 
v_x_23_ = lean_ctor_get(v_x_18_, 0);
v_s_24_ = lean_ctor_get(v_x_18_, 1);
v___x_25_ = 1ULL;
v___x_26_ = lean_uint64_of_nat(v_x_23_);
v___x_27_ = lean_uint64_mix_hash(v___x_25_, v___x_26_);
v___x_28_ = l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(v_s_24_);
v___x_29_ = lean_uint64_mix_hash(v___x_27_, v___x_28_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash___boxed(lean_object* v_x_30_){
_start:
{
uint64_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(v_x_30_);
lean_dec_ref(v_x_30_);
v_r_32_ = lean_box_uint64(v_res_31_);
return v_r_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx___impl(lean_object* v_x_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_obj_tag_nat(v_x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx___impl(v_x_37_);
lean_dec_ref(v_x_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(lean_object* v_t_39_, lean_object* v_k_40_){
_start:
{
switch(lean_obj_tag(v_t_39_))
{
case 0:
{
lean_object* v_a_41_; lean_object* v_b_42_; lean_object* v_ea_43_; lean_object* v_eb_44_; lean_object* v___x_45_; 
v_a_41_ = lean_ctor_get(v_t_39_, 0);
lean_inc_ref(v_a_41_);
v_b_42_ = lean_ctor_get(v_t_39_, 1);
lean_inc_ref(v_b_42_);
v_ea_43_ = lean_ctor_get(v_t_39_, 2);
lean_inc_ref(v_ea_43_);
v_eb_44_ = lean_ctor_get(v_t_39_, 3);
lean_inc_ref(v_eb_44_);
lean_dec_ref_known(v_t_39_, 4);
v___x_45_ = lean_apply_4(v_k_40_, v_a_41_, v_b_42_, v_ea_43_, v_eb_44_);
return v___x_45_;
}
case 4:
{
uint8_t v_lhs_46_; lean_object* v_c_u2081_47_; lean_object* v_c_u2082_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_lhs_46_ = lean_ctor_get_uint8(v_t_39_, sizeof(void*)*2);
v_c_u2081_47_ = lean_ctor_get(v_t_39_, 0);
lean_inc_ref(v_c_u2081_47_);
v_c_u2082_48_ = lean_ctor_get(v_t_39_, 1);
lean_inc_ref(v_c_u2082_48_);
lean_dec_ref_known(v_t_39_, 2);
v___x_49_ = lean_box(v_lhs_46_);
v___x_50_ = lean_apply_3(v_k_40_, v___x_49_, v_c_u2081_47_, v_c_u2082_48_);
return v___x_50_;
}
case 5:
{
uint8_t v_lhs_51_; lean_object* v_s_52_; lean_object* v_c_u2081_53_; lean_object* v_c_u2082_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_lhs_51_ = lean_ctor_get_uint8(v_t_39_, sizeof(void*)*3);
v_s_52_ = lean_ctor_get(v_t_39_, 0);
lean_inc_ref(v_s_52_);
v_c_u2081_53_ = lean_ctor_get(v_t_39_, 1);
lean_inc_ref(v_c_u2081_53_);
v_c_u2082_54_ = lean_ctor_get(v_t_39_, 2);
lean_inc_ref(v_c_u2082_54_);
lean_dec_ref_known(v_t_39_, 3);
v___x_55_ = lean_box(v_lhs_51_);
v___x_56_ = lean_apply_4(v_k_40_, v___x_55_, v_s_52_, v_c_u2081_53_, v_c_u2082_54_);
return v___x_56_;
}
case 6:
{
uint8_t v_lhs_57_; lean_object* v_s_58_; lean_object* v_c_u2081_59_; lean_object* v_c_u2082_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_lhs_57_ = lean_ctor_get_uint8(v_t_39_, sizeof(void*)*3);
v_s_58_ = lean_ctor_get(v_t_39_, 0);
lean_inc_ref(v_s_58_);
v_c_u2081_59_ = lean_ctor_get(v_t_39_, 1);
lean_inc_ref(v_c_u2081_59_);
v_c_u2082_60_ = lean_ctor_get(v_t_39_, 2);
lean_inc_ref(v_c_u2082_60_);
lean_dec_ref_known(v_t_39_, 3);
v___x_61_ = lean_box(v_lhs_57_);
v___x_62_ = lean_apply_4(v_k_40_, v___x_61_, v_s_58_, v_c_u2081_59_, v_c_u2082_60_);
return v___x_62_;
}
case 7:
{
uint8_t v_lhs_63_; lean_object* v_s_64_; lean_object* v_c_u2081_65_; lean_object* v_c_u2082_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_lhs_63_ = lean_ctor_get_uint8(v_t_39_, sizeof(void*)*3);
v_s_64_ = lean_ctor_get(v_t_39_, 0);
lean_inc_ref(v_s_64_);
v_c_u2081_65_ = lean_ctor_get(v_t_39_, 1);
lean_inc_ref(v_c_u2081_65_);
v_c_u2082_66_ = lean_ctor_get(v_t_39_, 2);
lean_inc_ref(v_c_u2082_66_);
lean_dec_ref_known(v_t_39_, 3);
v___x_67_ = lean_box(v_lhs_63_);
v___x_68_ = lean_apply_4(v_k_40_, v___x_67_, v_s_64_, v_c_u2081_65_, v_c_u2082_66_);
return v___x_68_;
}
case 8:
{
uint8_t v_lhs_69_; lean_object* v_s_u2081_70_; lean_object* v_s_u2082_71_; lean_object* v_c_u2081_72_; lean_object* v_c_u2082_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_lhs_69_ = lean_ctor_get_uint8(v_t_39_, sizeof(void*)*4);
v_s_u2081_70_ = lean_ctor_get(v_t_39_, 0);
lean_inc_ref(v_s_u2081_70_);
v_s_u2082_71_ = lean_ctor_get(v_t_39_, 1);
lean_inc_ref(v_s_u2082_71_);
v_c_u2081_72_ = lean_ctor_get(v_t_39_, 2);
lean_inc_ref(v_c_u2081_72_);
v_c_u2082_73_ = lean_ctor_get(v_t_39_, 3);
lean_inc_ref(v_c_u2082_73_);
lean_dec_ref_known(v_t_39_, 4);
v___x_74_ = lean_box(v_lhs_69_);
v___x_75_ = lean_apply_5(v_k_40_, v___x_74_, v_s_u2081_70_, v_s_u2082_71_, v_c_u2081_72_, v_c_u2082_73_);
return v___x_75_;
}
case 9:
{
lean_object* v_r_u2081_76_; lean_object* v_c_77_; lean_object* v_r_u2082_78_; lean_object* v_c_u2081_79_; lean_object* v_c_u2082_80_; lean_object* v___x_81_; 
v_r_u2081_76_ = lean_ctor_get(v_t_39_, 0);
lean_inc_ref(v_r_u2081_76_);
v_c_77_ = lean_ctor_get(v_t_39_, 1);
lean_inc_ref(v_c_77_);
v_r_u2082_78_ = lean_ctor_get(v_t_39_, 2);
lean_inc_ref(v_r_u2082_78_);
v_c_u2081_79_ = lean_ctor_get(v_t_39_, 3);
lean_inc_ref(v_c_u2081_79_);
v_c_u2082_80_ = lean_ctor_get(v_t_39_, 4);
lean_inc_ref(v_c_u2082_80_);
lean_dec_ref_known(v_t_39_, 5);
v___x_81_ = lean_apply_5(v_k_40_, v_r_u2081_76_, v_c_77_, v_r_u2082_78_, v_c_u2081_79_, v_c_u2082_80_);
return v___x_81_;
}
case 10:
{
lean_object* v_p_82_; lean_object* v_s_83_; lean_object* v_c_84_; lean_object* v_c_u2081_85_; lean_object* v_c_u2082_86_; lean_object* v___x_87_; 
v_p_82_ = lean_ctor_get(v_t_39_, 0);
lean_inc_ref(v_p_82_);
v_s_83_ = lean_ctor_get(v_t_39_, 1);
lean_inc_ref(v_s_83_);
v_c_84_ = lean_ctor_get(v_t_39_, 2);
lean_inc_ref(v_c_84_);
v_c_u2081_85_ = lean_ctor_get(v_t_39_, 3);
lean_inc_ref(v_c_u2081_85_);
v_c_u2082_86_ = lean_ctor_get(v_t_39_, 4);
lean_inc_ref(v_c_u2082_86_);
lean_dec_ref_known(v_t_39_, 5);
v___x_87_ = lean_apply_5(v_k_40_, v_p_82_, v_s_83_, v_c_84_, v_c_u2081_85_, v_c_u2082_86_);
return v___x_87_;
}
case 11:
{
lean_object* v_x_88_; lean_object* v_c_u2081_89_; lean_object* v___x_90_; 
v_x_88_ = lean_ctor_get(v_t_39_, 0);
lean_inc(v_x_88_);
v_c_u2081_89_ = lean_ctor_get(v_t_39_, 1);
lean_inc_ref(v_c_u2081_89_);
lean_dec_ref_known(v_t_39_, 2);
v___x_90_ = lean_apply_2(v_k_40_, v_x_88_, v_c_u2081_89_);
return v___x_90_;
}
case 12:
{
lean_object* v_x_91_; lean_object* v_c_u2081_92_; lean_object* v___x_93_; 
v_x_91_ = lean_ctor_get(v_t_39_, 0);
lean_inc(v_x_91_);
v_c_u2081_92_ = lean_ctor_get(v_t_39_, 1);
lean_inc_ref(v_c_u2081_92_);
lean_dec_ref_known(v_t_39_, 2);
v___x_93_ = lean_apply_2(v_k_40_, v_x_91_, v_c_u2081_92_);
return v___x_93_;
}
case 13:
{
lean_object* v_x_94_; lean_object* v_c_u2081_95_; lean_object* v___x_96_; 
v_x_94_ = lean_ctor_get(v_t_39_, 0);
lean_inc(v_x_94_);
v_c_u2081_95_ = lean_ctor_get(v_t_39_, 1);
lean_inc_ref(v_c_u2081_95_);
lean_dec_ref_known(v_t_39_, 2);
v___x_96_ = lean_apply_2(v_k_40_, v_x_94_, v_c_u2081_95_);
return v___x_96_;
}
default: 
{
lean_object* v_c_97_; lean_object* v___x_98_; 
v_c_97_ = lean_ctor_get(v_t_39_, 0);
lean_inc_ref(v_c_97_);
lean_dec_ref(v_t_39_);
v___x_98_ = lean_apply_1(v_k_40_, v_c_97_);
return v___x_98_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim(lean_object* v_motive__2_99_, lean_object* v_ctorIdx_100_, lean_object* v_t_101_, lean_object* v_h_102_, lean_object* v_k_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_101_, v_k_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_105_, lean_object* v_ctorIdx_106_, lean_object* v_t_107_, lean_object* v_h_108_, lean_object* v_k_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim(v_motive__2_105_, v_ctorIdx_106_, v_t_107_, v_h_108_, v_k_109_);
lean_dec(v_ctorIdx_106_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_core_elim___redArg(lean_object* v_t_111_, lean_object* v_core_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_111_, v_core_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_core_elim(lean_object* v_motive__2_114_, lean_object* v_t_115_, lean_object* v_h_116_, lean_object* v_core_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_115_, v_core_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup_elim___redArg(lean_object* v_t_119_, lean_object* v_erase__dup_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_119_, v_erase__dup_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup_elim(lean_object* v_motive__2_122_, lean_object* v_t_123_, lean_object* v_h_124_, lean_object* v_erase__dup_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_123_, v_erase__dup_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase0_elim___redArg(lean_object* v_t_127_, lean_object* v_erase0_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_127_, v_erase0_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase0_elim(lean_object* v_motive__2_130_, lean_object* v_t_131_, lean_object* v_h_132_, lean_object* v_erase0_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_131_, v_erase0_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_swap_elim___redArg(lean_object* v_t_135_, lean_object* v_swap_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_135_, v_swap_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_swap_elim(lean_object* v_motive__2_138_, lean_object* v_t_139_, lean_object* v_h_140_, lean_object* v_swap_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_139_, v_swap_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__exact_elim___redArg(lean_object* v_t_143_, lean_object* v_simp__exact_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_143_, v_simp__exact_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__exact_elim(lean_object* v_motive__2_146_, lean_object* v_t_147_, lean_object* v_h_148_, lean_object* v_simp__exact_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_147_, v_simp__exact_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__ac_elim___redArg(lean_object* v_t_151_, lean_object* v_simp__ac_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_151_, v_simp__ac_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__ac_elim(lean_object* v_motive__2_154_, lean_object* v_t_155_, lean_object* v_h_156_, lean_object* v_simp__ac_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_155_, v_simp__ac_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__suffix_elim___redArg(lean_object* v_t_159_, lean_object* v_simp__suffix_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_159_, v_simp__suffix_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__suffix_elim(lean_object* v_motive__2_162_, lean_object* v_t_163_, lean_object* v_h_164_, lean_object* v_simp__suffix_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_163_, v_simp__suffix_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__prefix_elim___redArg(lean_object* v_t_167_, lean_object* v_simp__prefix_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_167_, v_simp__prefix_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__prefix_elim(lean_object* v_motive__2_170_, lean_object* v_t_171_, lean_object* v_h_172_, lean_object* v_simp__prefix_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_171_, v_simp__prefix_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__middle_elim___redArg(lean_object* v_t_175_, lean_object* v_simp__middle_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_175_, v_simp__middle_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__middle_elim(lean_object* v_motive__2_178_, lean_object* v_t_179_, lean_object* v_h_180_, lean_object* v_simp__middle_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_179_, v_simp__middle_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac_elim___redArg(lean_object* v_t_183_, lean_object* v_superpose__ac_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_183_, v_superpose__ac_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac_elim(lean_object* v_motive__2_186_, lean_object* v_t_187_, lean_object* v_h_188_, lean_object* v_superpose__ac_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_187_, v_superpose__ac_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose_elim___redArg(lean_object* v_t_191_, lean_object* v_superpose_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_191_, v_superpose_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose_elim(lean_object* v_motive__2_194_, lean_object* v_t_195_, lean_object* v_h_196_, lean_object* v_superpose_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_195_, v_superpose_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac__idempotent_elim___redArg(lean_object* v_t_199_, lean_object* v_superpose__ac__idempotent_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_199_, v_superpose__ac__idempotent_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac__idempotent_elim(lean_object* v_motive__2_202_, lean_object* v_t_203_, lean_object* v_h_204_, lean_object* v_superpose__ac__idempotent_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_203_, v_superpose__ac__idempotent_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__head__idempotent_elim___redArg(lean_object* v_t_207_, lean_object* v_superpose__head__idempotent_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_207_, v_superpose__head__idempotent_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__head__idempotent_elim(lean_object* v_motive__2_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_superpose__head__idempotent_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_211_, v_superpose__head__idempotent_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__tail__idempotent_elim___redArg(lean_object* v_t_215_, lean_object* v_superpose__tail__idempotent_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_215_, v_superpose__tail__idempotent_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__tail__idempotent_elim(lean_object* v_motive__2_218_, lean_object* v_t_219_, lean_object* v_h_220_, lean_object* v_superpose__tail__idempotent_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_219_, v_superpose__tail__idempotent_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_refl_elim___redArg(lean_object* v_t_223_, lean_object* v_refl_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_223_, v_refl_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_refl_elim(lean_object* v_motive__2_226_, lean_object* v_t_227_, lean_object* v_h_228_, lean_object* v_refl_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_227_, v_refl_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup__rhs_elim___redArg(lean_object* v_t_231_, lean_object* v_erase__dup__rhs_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_231_, v_erase__dup__rhs_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup__rhs_elim(lean_object* v_motive__2_234_, lean_object* v_t_235_, lean_object* v_h_236_, lean_object* v_erase__dup__rhs_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_235_, v_erase__dup__rhs_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase0__rhs_elim___redArg(lean_object* v_t_239_, lean_object* v_erase0__rhs_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_239_, v_erase0__rhs_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase0__rhs_elim(lean_object* v_motive__2_242_, lean_object* v_t_243_, lean_object* v_h_244_, lean_object* v_erase0__rhs_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_243_, v_erase0__rhs_245_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = lean_box(0);
v___x_251_ = ((lean_object*)(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1));
v___x_252_ = l_Lean_Expr_const___override(v___x_251_, v___x_250_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = l_Lean_Grind_AC_instInhabitedExpr_default;
v___x_254_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2, &l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2_once, _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2);
v___x_255_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
lean_ctor_set(v___x_255_, 2, v___x_253_);
lean_ctor_set(v___x_255_, 3, v___x_253_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof(void){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3, &l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3_once, _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3, &l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3_once, _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3);
v___x_259_ = l_Lean_Grind_AC_instInhabitedSeq_default;
v___x_260_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
lean_ctor_set(v___x_260_, 2, v___x_258_);
lean_ctor_set(v___x_260_, 3, v___x_257_);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr(void){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0, &l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0_once, _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0);
return v___x_261_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_AC_EqCnstr_compare(lean_object* v_c_u2081_262_, lean_object* v_c_u2082_263_){
_start:
{
lean_object* v_lhs_264_; lean_object* v_id_265_; lean_object* v_lhs_266_; lean_object* v_id_267_; lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v_lhs_264_ = lean_ctor_get(v_c_u2081_262_, 0);
v_id_265_ = lean_ctor_get(v_c_u2081_262_, 3);
v_lhs_266_ = lean_ctor_get(v_c_u2082_263_, 0);
v_id_267_ = lean_ctor_get(v_c_u2082_263_, 3);
v___x_268_ = l_Lean_Grind_AC_Seq_length(v_lhs_264_);
v___x_269_ = l_Lean_Grind_AC_Seq_length(v_lhs_266_);
v___x_270_ = lean_nat_dec_lt(v___x_268_, v___x_269_);
if (v___x_270_ == 0)
{
uint8_t v___x_271_; 
v___x_271_ = lean_nat_dec_eq(v___x_268_, v___x_269_);
lean_dec(v___x_269_);
lean_dec(v___x_268_);
if (v___x_271_ == 0)
{
uint8_t v___x_272_; 
v___x_272_ = 2;
return v___x_272_;
}
else
{
uint8_t v___x_273_; 
v___x_273_ = lean_nat_dec_lt(v_id_265_, v_id_267_);
if (v___x_273_ == 0)
{
uint8_t v___x_274_; 
v___x_274_ = lean_nat_dec_eq(v_id_265_, v_id_267_);
if (v___x_274_ == 0)
{
uint8_t v___x_275_; 
v___x_275_ = 2;
return v___x_275_;
}
else
{
uint8_t v___x_276_; 
v___x_276_ = 1;
return v___x_276_;
}
}
else
{
uint8_t v___x_277_; 
v___x_277_ = 0;
return v___x_277_;
}
}
}
else
{
uint8_t v___x_278_; 
lean_dec(v___x_269_);
lean_dec(v___x_268_);
v___x_278_ = 0;
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_compare___boxed(lean_object* v_c_u2081_279_, lean_object* v_c_u2082_280_){
_start:
{
uint8_t v_res_281_; lean_object* v_r_282_; 
v_res_281_ = l_Lean_Meta_Grind_AC_EqCnstr_compare(v_c_u2081_279_, v_c_u2082_280_);
lean_dec_ref(v_c_u2082_280_);
lean_dec_ref(v_c_u2081_279_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx___impl(lean_object* v_x_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = lean_obj_tag_nat(v_x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx___impl(v_x_285_);
lean_dec_ref(v_x_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(lean_object* v_t_287_, lean_object* v_k_288_){
_start:
{
switch(lean_obj_tag(v_t_287_))
{
case 0:
{
lean_object* v_a_289_; lean_object* v_b_290_; lean_object* v_ea_291_; lean_object* v_eb_292_; lean_object* v___x_293_; 
v_a_289_ = lean_ctor_get(v_t_287_, 0);
lean_inc_ref(v_a_289_);
v_b_290_ = lean_ctor_get(v_t_287_, 1);
lean_inc_ref(v_b_290_);
v_ea_291_ = lean_ctor_get(v_t_287_, 2);
lean_inc_ref(v_ea_291_);
v_eb_292_ = lean_ctor_get(v_t_287_, 3);
lean_inc_ref(v_eb_292_);
lean_dec_ref_known(v_t_287_, 4);
v___x_293_ = lean_apply_4(v_k_288_, v_a_289_, v_b_290_, v_ea_291_, v_eb_292_);
return v___x_293_;
}
case 1:
{
lean_object* v_c_294_; lean_object* v___x_295_; 
v_c_294_ = lean_ctor_get(v_t_287_, 0);
lean_inc_ref(v_c_294_);
lean_dec_ref_known(v_t_287_, 1);
v___x_295_ = lean_apply_1(v_k_288_, v_c_294_);
return v___x_295_;
}
case 2:
{
lean_object* v_c_296_; lean_object* v___x_297_; 
v_c_296_ = lean_ctor_get(v_t_287_, 0);
lean_inc_ref(v_c_296_);
lean_dec_ref_known(v_t_287_, 1);
v___x_297_ = lean_apply_1(v_k_288_, v_c_296_);
return v___x_297_;
}
case 3:
{
uint8_t v_lhs_298_; lean_object* v_c_u2081_299_; lean_object* v_c_u2082_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_lhs_298_ = lean_ctor_get_uint8(v_t_287_, sizeof(void*)*2);
v_c_u2081_299_ = lean_ctor_get(v_t_287_, 0);
lean_inc_ref(v_c_u2081_299_);
v_c_u2082_300_ = lean_ctor_get(v_t_287_, 1);
lean_inc_ref(v_c_u2082_300_);
lean_dec_ref_known(v_t_287_, 2);
v___x_301_ = lean_box(v_lhs_298_);
v___x_302_ = lean_apply_3(v_k_288_, v___x_301_, v_c_u2081_299_, v_c_u2082_300_);
return v___x_302_;
}
case 7:
{
uint8_t v_lhs_303_; lean_object* v_s_u2081_304_; lean_object* v_s_u2082_305_; lean_object* v_c_u2081_306_; lean_object* v_c_u2082_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_lhs_303_ = lean_ctor_get_uint8(v_t_287_, sizeof(void*)*4);
v_s_u2081_304_ = lean_ctor_get(v_t_287_, 0);
lean_inc_ref(v_s_u2081_304_);
v_s_u2082_305_ = lean_ctor_get(v_t_287_, 1);
lean_inc_ref(v_s_u2082_305_);
v_c_u2081_306_ = lean_ctor_get(v_t_287_, 2);
lean_inc_ref(v_c_u2081_306_);
v_c_u2082_307_ = lean_ctor_get(v_t_287_, 3);
lean_inc_ref(v_c_u2082_307_);
lean_dec_ref_known(v_t_287_, 4);
v___x_308_ = lean_box(v_lhs_303_);
v___x_309_ = lean_apply_5(v_k_288_, v___x_308_, v_s_u2081_304_, v_s_u2082_305_, v_c_u2081_306_, v_c_u2082_307_);
return v___x_309_;
}
default: 
{
uint8_t v_lhs_310_; lean_object* v_s_311_; lean_object* v_c_u2081_312_; lean_object* v_c_u2082_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_lhs_310_ = lean_ctor_get_uint8(v_t_287_, sizeof(void*)*3);
v_s_311_ = lean_ctor_get(v_t_287_, 0);
lean_inc_ref(v_s_311_);
v_c_u2081_312_ = lean_ctor_get(v_t_287_, 1);
lean_inc_ref(v_c_u2081_312_);
v_c_u2082_313_ = lean_ctor_get(v_t_287_, 2);
lean_inc_ref(v_c_u2082_313_);
lean_dec_ref(v_t_287_);
v___x_314_ = lean_box(v_lhs_310_);
v___x_315_ = lean_apply_4(v_k_288_, v___x_314_, v_s_311_, v_c_u2081_312_, v_c_u2082_313_);
return v___x_315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim(lean_object* v_motive__2_316_, lean_object* v_ctorIdx_317_, lean_object* v_t_318_, lean_object* v_h_319_, lean_object* v_k_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_318_, v_k_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_322_, lean_object* v_ctorIdx_323_, lean_object* v_t_324_, lean_object* v_h_325_, lean_object* v_k_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim(v_motive__2_322_, v_ctorIdx_323_, v_t_324_, v_h_325_, v_k_326_);
lean_dec(v_ctorIdx_323_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_core_elim___redArg(lean_object* v_t_328_, lean_object* v_core_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_328_, v_core_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_core_elim(lean_object* v_motive__2_331_, lean_object* v_t_332_, lean_object* v_h_333_, lean_object* v_core_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_332_, v_core_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase__dup_elim___redArg(lean_object* v_t_336_, lean_object* v_erase__dup_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_336_, v_erase__dup_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase__dup_elim(lean_object* v_motive__2_339_, lean_object* v_t_340_, lean_object* v_h_341_, lean_object* v_erase__dup_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_340_, v_erase__dup_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase0_elim___redArg(lean_object* v_t_344_, lean_object* v_erase0_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_344_, v_erase0_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase0_elim(lean_object* v_motive__2_347_, lean_object* v_t_348_, lean_object* v_h_349_, lean_object* v_erase0_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_348_, v_erase0_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__exact_elim___redArg(lean_object* v_t_352_, lean_object* v_simp__exact_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_352_, v_simp__exact_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__exact_elim(lean_object* v_motive__2_355_, lean_object* v_t_356_, lean_object* v_h_357_, lean_object* v_simp__exact_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_356_, v_simp__exact_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__ac_elim___redArg(lean_object* v_t_360_, lean_object* v_simp__ac_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_360_, v_simp__ac_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__ac_elim(lean_object* v_motive__2_363_, lean_object* v_t_364_, lean_object* v_h_365_, lean_object* v_simp__ac_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_364_, v_simp__ac_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__suffix_elim___redArg(lean_object* v_t_368_, lean_object* v_simp__suffix_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_368_, v_simp__suffix_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__suffix_elim(lean_object* v_motive__2_371_, lean_object* v_t_372_, lean_object* v_h_373_, lean_object* v_simp__suffix_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_372_, v_simp__suffix_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__prefix_elim___redArg(lean_object* v_t_376_, lean_object* v_simp__prefix_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_376_, v_simp__prefix_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__prefix_elim(lean_object* v_motive__2_379_, lean_object* v_t_380_, lean_object* v_h_381_, lean_object* v_simp__prefix_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_380_, v_simp__prefix_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__middle_elim___redArg(lean_object* v_t_384_, lean_object* v_simp__middle_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_384_, v_simp__middle_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__middle_elim(lean_object* v_motive__2_387_, lean_object* v_t_388_, lean_object* v_h_389_, lean_object* v_simp__middle_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_388_, v_simp__middle_390_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = lean_unsigned_to_nat(32u);
v___x_393_ = lean_mk_empty_array_with_capacity(v___x_392_);
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1(void){
_start:
{
size_t v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_395_ = ((size_t)5ULL);
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = lean_unsigned_to_nat(32u);
v___x_398_ = lean_mk_empty_array_with_capacity(v___x_397_);
v___x_399_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0, &l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0_once, _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0);
v___x_400_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v___x_398_);
lean_ctor_set(v___x_400_, 2, v___x_396_);
lean_ctor_set(v___x_400_, 3, v___x_396_);
lean_ctor_set_usize(v___x_400_, 4, v___x_395_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2(void){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_401_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2, &l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2_once, _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2);
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4(void){
_start:
{
uint8_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_404_ = 0;
v___x_405_ = lean_box(0);
v___x_406_ = lean_box(1);
v___x_407_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3, &l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3_once, _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3);
v___x_408_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1, &l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1_once, _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1);
v___x_409_ = lean_box(0);
v___x_410_ = lean_box(0);
v___x_411_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2, &l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2_once, _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2);
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v___x_411_);
lean_ctor_set(v___x_413_, 2, v___x_410_);
lean_ctor_set(v___x_413_, 3, v___x_411_);
lean_ctor_set(v___x_413_, 4, v___x_409_);
lean_ctor_set(v___x_413_, 5, v___x_411_);
lean_ctor_set(v___x_413_, 6, v___x_409_);
lean_ctor_set(v___x_413_, 7, v___x_409_);
lean_ctor_set(v___x_413_, 8, v___x_409_);
lean_ctor_set(v___x_413_, 9, v___x_412_);
lean_ctor_set(v___x_413_, 10, v___x_408_);
lean_ctor_set(v___x_413_, 11, v___x_407_);
lean_ctor_set(v___x_413_, 12, v___x_407_);
lean_ctor_set(v___x_413_, 13, v___x_408_);
lean_ctor_set(v___x_413_, 14, v___x_406_);
lean_ctor_set(v___x_413_, 15, v___x_405_);
lean_ctor_set(v___x_413_, 16, v___x_408_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*17, v___x_404_);
return v___x_413_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default(void){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4, &l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4_once, _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4);
return v___x_414_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct(void){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Meta_Grind_AC_instInhabitedStruct_default;
return v___x_415_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2, &l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2_once, _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1);
v___x_422_ = ((lean_object*)(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__0));
v___x_423_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_421_);
lean_ctor_set(v___x_423_, 2, v___x_421_);
lean_ctor_set(v___x_423_, 3, v___x_420_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedState_default(void){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2, &l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedState(void){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_Meta_Grind_AC_instInhabitedState_default;
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(lean_object* v___x_426_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed(lean_object* v___x_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(v___x_429_);
return v_res_431_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_432_; lean_object* v___f_433_; 
v___x_432_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2, &l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2);
v___f_433_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_433_, 0, v___x_432_);
return v___f_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_435_; lean_object* v___x_436_; 
v___f_435_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_);
v___x_436_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed(lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_();
return v_res_438_;
}
}
lean_object* runtime_initialize_Init_Grind_AC(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof = _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof);
l_Lean_Meta_Grind_AC_instInhabitedEqCnstr = _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedEqCnstr);
l_Lean_Meta_Grind_AC_instInhabitedStruct_default = _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedStruct_default);
l_Lean_Meta_Grind_AC_instInhabitedStruct = _init_l_Lean_Meta_Grind_AC_instInhabitedStruct();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedStruct);
l_Lean_Meta_Grind_AC_instInhabitedState_default = _init_l_Lean_Meta_Grind_AC_instInhabitedState_default();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedState_default);
l_Lean_Meta_Grind_AC_instInhabitedState = _init_l_Lean_Meta_Grind_AC_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instInhabitedState);
res = l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_AC_acExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_AC_acExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_AC_Types(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_AC(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Seq(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Types(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC_Seq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
}
#ifdef __cplusplus
}
#endif
