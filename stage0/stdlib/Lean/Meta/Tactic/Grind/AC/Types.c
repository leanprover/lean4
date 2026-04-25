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
extern lean_object* l_Lean_Grind_AC_instInhabitedExpr_default;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Grind_AC_instInhabitedSeq_default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx(lean_object* v_x_35_){
_start:
{
switch(lean_obj_tag(v_x_35_))
{
case 0:
{
lean_object* v___x_36_; 
v___x_36_ = lean_unsigned_to_nat(0u);
return v___x_36_;
}
case 1:
{
lean_object* v___x_37_; 
v___x_37_ = lean_unsigned_to_nat(1u);
return v___x_37_;
}
case 2:
{
lean_object* v___x_38_; 
v___x_38_ = lean_unsigned_to_nat(2u);
return v___x_38_;
}
case 3:
{
lean_object* v___x_39_; 
v___x_39_ = lean_unsigned_to_nat(3u);
return v___x_39_;
}
case 4:
{
lean_object* v___x_40_; 
v___x_40_ = lean_unsigned_to_nat(4u);
return v___x_40_;
}
case 5:
{
lean_object* v___x_41_; 
v___x_41_ = lean_unsigned_to_nat(5u);
return v___x_41_;
}
case 6:
{
lean_object* v___x_42_; 
v___x_42_ = lean_unsigned_to_nat(6u);
return v___x_42_;
}
case 7:
{
lean_object* v___x_43_; 
v___x_43_ = lean_unsigned_to_nat(7u);
return v___x_43_;
}
case 8:
{
lean_object* v___x_44_; 
v___x_44_ = lean_unsigned_to_nat(8u);
return v___x_44_;
}
case 9:
{
lean_object* v___x_45_; 
v___x_45_ = lean_unsigned_to_nat(9u);
return v___x_45_;
}
case 10:
{
lean_object* v___x_46_; 
v___x_46_ = lean_unsigned_to_nat(10u);
return v___x_46_;
}
case 11:
{
lean_object* v___x_47_; 
v___x_47_ = lean_unsigned_to_nat(11u);
return v___x_47_;
}
case 12:
{
lean_object* v___x_48_; 
v___x_48_ = lean_unsigned_to_nat(12u);
return v___x_48_;
}
case 13:
{
lean_object* v___x_49_; 
v___x_49_ = lean_unsigned_to_nat(13u);
return v___x_49_;
}
case 14:
{
lean_object* v___x_50_; 
v___x_50_ = lean_unsigned_to_nat(14u);
return v___x_50_;
}
case 15:
{
lean_object* v___x_51_; 
v___x_51_ = lean_unsigned_to_nat(15u);
return v___x_51_;
}
default: 
{
lean_object* v___x_52_; 
v___x_52_ = lean_unsigned_to_nat(16u);
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx___boxed(lean_object* v_x_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx(v_x_53_);
lean_dec_ref(v_x_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(lean_object* v_t_55_, lean_object* v_k_56_){
_start:
{
switch(lean_obj_tag(v_t_55_))
{
case 0:
{
lean_object* v_a_57_; lean_object* v_b_58_; lean_object* v_ea_59_; lean_object* v_eb_60_; lean_object* v___x_61_; 
v_a_57_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_a_57_);
v_b_58_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_b_58_);
v_ea_59_ = lean_ctor_get(v_t_55_, 2);
lean_inc_ref(v_ea_59_);
v_eb_60_ = lean_ctor_get(v_t_55_, 3);
lean_inc_ref(v_eb_60_);
lean_dec_ref(v_t_55_);
v___x_61_ = lean_apply_4(v_k_56_, v_a_57_, v_b_58_, v_ea_59_, v_eb_60_);
return v___x_61_;
}
case 4:
{
uint8_t v_lhs_62_; lean_object* v_c_u2081_63_; lean_object* v_c_u2082_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v_lhs_62_ = lean_ctor_get_uint8(v_t_55_, sizeof(void*)*2);
v_c_u2081_63_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_c_u2081_63_);
v_c_u2082_64_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_c_u2082_64_);
lean_dec_ref(v_t_55_);
v___x_65_ = lean_box(v_lhs_62_);
v___x_66_ = lean_apply_3(v_k_56_, v___x_65_, v_c_u2081_63_, v_c_u2082_64_);
return v___x_66_;
}
case 5:
{
uint8_t v_lhs_67_; lean_object* v_s_68_; lean_object* v_c_u2081_69_; lean_object* v_c_u2082_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_lhs_67_ = lean_ctor_get_uint8(v_t_55_, sizeof(void*)*3);
v_s_68_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_s_68_);
v_c_u2081_69_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_c_u2081_69_);
v_c_u2082_70_ = lean_ctor_get(v_t_55_, 2);
lean_inc_ref(v_c_u2082_70_);
lean_dec_ref(v_t_55_);
v___x_71_ = lean_box(v_lhs_67_);
v___x_72_ = lean_apply_4(v_k_56_, v___x_71_, v_s_68_, v_c_u2081_69_, v_c_u2082_70_);
return v___x_72_;
}
case 6:
{
uint8_t v_lhs_73_; lean_object* v_s_74_; lean_object* v_c_u2081_75_; lean_object* v_c_u2082_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_lhs_73_ = lean_ctor_get_uint8(v_t_55_, sizeof(void*)*3);
v_s_74_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_s_74_);
v_c_u2081_75_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_c_u2081_75_);
v_c_u2082_76_ = lean_ctor_get(v_t_55_, 2);
lean_inc_ref(v_c_u2082_76_);
lean_dec_ref(v_t_55_);
v___x_77_ = lean_box(v_lhs_73_);
v___x_78_ = lean_apply_4(v_k_56_, v___x_77_, v_s_74_, v_c_u2081_75_, v_c_u2082_76_);
return v___x_78_;
}
case 7:
{
uint8_t v_lhs_79_; lean_object* v_s_80_; lean_object* v_c_u2081_81_; lean_object* v_c_u2082_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_lhs_79_ = lean_ctor_get_uint8(v_t_55_, sizeof(void*)*3);
v_s_80_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_s_80_);
v_c_u2081_81_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_c_u2081_81_);
v_c_u2082_82_ = lean_ctor_get(v_t_55_, 2);
lean_inc_ref(v_c_u2082_82_);
lean_dec_ref(v_t_55_);
v___x_83_ = lean_box(v_lhs_79_);
v___x_84_ = lean_apply_4(v_k_56_, v___x_83_, v_s_80_, v_c_u2081_81_, v_c_u2082_82_);
return v___x_84_;
}
case 8:
{
uint8_t v_lhs_85_; lean_object* v_s_u2081_86_; lean_object* v_s_u2082_87_; lean_object* v_c_u2081_88_; lean_object* v_c_u2082_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v_lhs_85_ = lean_ctor_get_uint8(v_t_55_, sizeof(void*)*4);
v_s_u2081_86_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_s_u2081_86_);
v_s_u2082_87_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_s_u2082_87_);
v_c_u2081_88_ = lean_ctor_get(v_t_55_, 2);
lean_inc_ref(v_c_u2081_88_);
v_c_u2082_89_ = lean_ctor_get(v_t_55_, 3);
lean_inc_ref(v_c_u2082_89_);
lean_dec_ref(v_t_55_);
v___x_90_ = lean_box(v_lhs_85_);
v___x_91_ = lean_apply_5(v_k_56_, v___x_90_, v_s_u2081_86_, v_s_u2082_87_, v_c_u2081_88_, v_c_u2082_89_);
return v___x_91_;
}
case 9:
{
lean_object* v_r_u2081_92_; lean_object* v_c_93_; lean_object* v_r_u2082_94_; lean_object* v_c_u2081_95_; lean_object* v_c_u2082_96_; lean_object* v___x_97_; 
v_r_u2081_92_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_r_u2081_92_);
v_c_93_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_c_93_);
v_r_u2082_94_ = lean_ctor_get(v_t_55_, 2);
lean_inc_ref(v_r_u2082_94_);
v_c_u2081_95_ = lean_ctor_get(v_t_55_, 3);
lean_inc_ref(v_c_u2081_95_);
v_c_u2082_96_ = lean_ctor_get(v_t_55_, 4);
lean_inc_ref(v_c_u2082_96_);
lean_dec_ref(v_t_55_);
v___x_97_ = lean_apply_5(v_k_56_, v_r_u2081_92_, v_c_93_, v_r_u2082_94_, v_c_u2081_95_, v_c_u2082_96_);
return v___x_97_;
}
case 10:
{
lean_object* v_p_98_; lean_object* v_s_99_; lean_object* v_c_100_; lean_object* v_c_u2081_101_; lean_object* v_c_u2082_102_; lean_object* v___x_103_; 
v_p_98_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_p_98_);
v_s_99_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_s_99_);
v_c_100_ = lean_ctor_get(v_t_55_, 2);
lean_inc_ref(v_c_100_);
v_c_u2081_101_ = lean_ctor_get(v_t_55_, 3);
lean_inc_ref(v_c_u2081_101_);
v_c_u2082_102_ = lean_ctor_get(v_t_55_, 4);
lean_inc_ref(v_c_u2082_102_);
lean_dec_ref(v_t_55_);
v___x_103_ = lean_apply_5(v_k_56_, v_p_98_, v_s_99_, v_c_100_, v_c_u2081_101_, v_c_u2082_102_);
return v___x_103_;
}
case 11:
{
lean_object* v_x_104_; lean_object* v_c_u2081_105_; lean_object* v___x_106_; 
v_x_104_ = lean_ctor_get(v_t_55_, 0);
lean_inc(v_x_104_);
v_c_u2081_105_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_c_u2081_105_);
lean_dec_ref(v_t_55_);
v___x_106_ = lean_apply_2(v_k_56_, v_x_104_, v_c_u2081_105_);
return v___x_106_;
}
case 12:
{
lean_object* v_x_107_; lean_object* v_c_u2081_108_; lean_object* v___x_109_; 
v_x_107_ = lean_ctor_get(v_t_55_, 0);
lean_inc(v_x_107_);
v_c_u2081_108_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_c_u2081_108_);
lean_dec_ref(v_t_55_);
v___x_109_ = lean_apply_2(v_k_56_, v_x_107_, v_c_u2081_108_);
return v___x_109_;
}
case 13:
{
lean_object* v_x_110_; lean_object* v_c_u2081_111_; lean_object* v___x_112_; 
v_x_110_ = lean_ctor_get(v_t_55_, 0);
lean_inc(v_x_110_);
v_c_u2081_111_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_c_u2081_111_);
lean_dec_ref(v_t_55_);
v___x_112_ = lean_apply_2(v_k_56_, v_x_110_, v_c_u2081_111_);
return v___x_112_;
}
default: 
{
lean_object* v_c_113_; lean_object* v___x_114_; 
v_c_113_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_c_113_);
lean_dec_ref(v_t_55_);
v___x_114_ = lean_apply_1(v_k_56_, v_c_113_);
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim(lean_object* v_motive__2_115_, lean_object* v_ctorIdx_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_k_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_117_, v_k_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_121_, lean_object* v_ctorIdx_122_, lean_object* v_t_123_, lean_object* v_h_124_, lean_object* v_k_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim(v_motive__2_121_, v_ctorIdx_122_, v_t_123_, v_h_124_, v_k_125_);
lean_dec(v_ctorIdx_122_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_core_elim___redArg(lean_object* v_t_127_, lean_object* v_core_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_127_, v_core_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_core_elim(lean_object* v_motive__2_130_, lean_object* v_t_131_, lean_object* v_h_132_, lean_object* v_core_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_131_, v_core_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup_elim___redArg(lean_object* v_t_135_, lean_object* v_erase__dup_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_135_, v_erase__dup_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup_elim(lean_object* v_motive__2_138_, lean_object* v_t_139_, lean_object* v_h_140_, lean_object* v_erase__dup_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_139_, v_erase__dup_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase0_elim___redArg(lean_object* v_t_143_, lean_object* v_erase0_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_143_, v_erase0_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase0_elim(lean_object* v_motive__2_146_, lean_object* v_t_147_, lean_object* v_h_148_, lean_object* v_erase0_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_147_, v_erase0_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_swap_elim___redArg(lean_object* v_t_151_, lean_object* v_swap_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_151_, v_swap_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_swap_elim(lean_object* v_motive__2_154_, lean_object* v_t_155_, lean_object* v_h_156_, lean_object* v_swap_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_155_, v_swap_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__exact_elim___redArg(lean_object* v_t_159_, lean_object* v_simp__exact_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_159_, v_simp__exact_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__exact_elim(lean_object* v_motive__2_162_, lean_object* v_t_163_, lean_object* v_h_164_, lean_object* v_simp__exact_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_163_, v_simp__exact_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__ac_elim___redArg(lean_object* v_t_167_, lean_object* v_simp__ac_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_167_, v_simp__ac_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__ac_elim(lean_object* v_motive__2_170_, lean_object* v_t_171_, lean_object* v_h_172_, lean_object* v_simp__ac_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_171_, v_simp__ac_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__suffix_elim___redArg(lean_object* v_t_175_, lean_object* v_simp__suffix_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_175_, v_simp__suffix_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__suffix_elim(lean_object* v_motive__2_178_, lean_object* v_t_179_, lean_object* v_h_180_, lean_object* v_simp__suffix_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_179_, v_simp__suffix_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__prefix_elim___redArg(lean_object* v_t_183_, lean_object* v_simp__prefix_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_183_, v_simp__prefix_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__prefix_elim(lean_object* v_motive__2_186_, lean_object* v_t_187_, lean_object* v_h_188_, lean_object* v_simp__prefix_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_187_, v_simp__prefix_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__middle_elim___redArg(lean_object* v_t_191_, lean_object* v_simp__middle_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_191_, v_simp__middle_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__middle_elim(lean_object* v_motive__2_194_, lean_object* v_t_195_, lean_object* v_h_196_, lean_object* v_simp__middle_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_195_, v_simp__middle_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac_elim___redArg(lean_object* v_t_199_, lean_object* v_superpose__ac_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_199_, v_superpose__ac_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac_elim(lean_object* v_motive__2_202_, lean_object* v_t_203_, lean_object* v_h_204_, lean_object* v_superpose__ac_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_203_, v_superpose__ac_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose_elim___redArg(lean_object* v_t_207_, lean_object* v_superpose_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_207_, v_superpose_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose_elim(lean_object* v_motive__2_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_superpose_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_211_, v_superpose_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac__idempotent_elim___redArg(lean_object* v_t_215_, lean_object* v_superpose__ac__idempotent_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_215_, v_superpose__ac__idempotent_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac__idempotent_elim(lean_object* v_motive__2_218_, lean_object* v_t_219_, lean_object* v_h_220_, lean_object* v_superpose__ac__idempotent_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_219_, v_superpose__ac__idempotent_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__head__idempotent_elim___redArg(lean_object* v_t_223_, lean_object* v_superpose__head__idempotent_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_223_, v_superpose__head__idempotent_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__head__idempotent_elim(lean_object* v_motive__2_226_, lean_object* v_t_227_, lean_object* v_h_228_, lean_object* v_superpose__head__idempotent_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_227_, v_superpose__head__idempotent_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__tail__idempotent_elim___redArg(lean_object* v_t_231_, lean_object* v_superpose__tail__idempotent_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_231_, v_superpose__tail__idempotent_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__tail__idempotent_elim(lean_object* v_motive__2_234_, lean_object* v_t_235_, lean_object* v_h_236_, lean_object* v_superpose__tail__idempotent_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_235_, v_superpose__tail__idempotent_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_refl_elim___redArg(lean_object* v_t_239_, lean_object* v_refl_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_239_, v_refl_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_refl_elim(lean_object* v_motive__2_242_, lean_object* v_t_243_, lean_object* v_h_244_, lean_object* v_refl_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_243_, v_refl_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup__rhs_elim___redArg(lean_object* v_t_247_, lean_object* v_erase__dup__rhs_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_247_, v_erase__dup__rhs_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup__rhs_elim(lean_object* v_motive__2_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_erase__dup__rhs_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_251_, v_erase__dup__rhs_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase0__rhs_elim___redArg(lean_object* v_t_255_, lean_object* v_erase0__rhs_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_255_, v_erase0__rhs_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase0__rhs_elim(lean_object* v_motive__2_258_, lean_object* v_t_259_, lean_object* v_h_260_, lean_object* v_erase0__rhs_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_259_, v_erase0__rhs_261_);
return v___x_262_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_box(0);
v___x_267_ = ((lean_object*)(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1));
v___x_268_ = l_Lean_Expr_const___override(v___x_267_, v___x_266_);
return v___x_268_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = l_Lean_Grind_AC_instInhabitedExpr_default;
v___x_270_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2, &l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2_once, _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2);
v___x_271_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
lean_ctor_set(v___x_271_, 2, v___x_269_);
lean_ctor_set(v___x_271_, 3, v___x_269_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof(void){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3, &l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3_once, _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3, &l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3_once, _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3);
v___x_275_ = l_Lean_Grind_AC_instInhabitedSeq_default;
v___x_276_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
lean_ctor_set(v___x_276_, 2, v___x_274_);
lean_ctor_set(v___x_276_, 3, v___x_273_);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr(void){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0, &l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0_once, _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0);
return v___x_277_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_AC_EqCnstr_compare(lean_object* v_c_u2081_278_, lean_object* v_c_u2082_279_){
_start:
{
lean_object* v_lhs_280_; lean_object* v_id_281_; lean_object* v_lhs_282_; lean_object* v_id_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v_lhs_280_ = lean_ctor_get(v_c_u2081_278_, 0);
v_id_281_ = lean_ctor_get(v_c_u2081_278_, 3);
v_lhs_282_ = lean_ctor_get(v_c_u2082_279_, 0);
v_id_283_ = lean_ctor_get(v_c_u2082_279_, 3);
v___x_284_ = l_Lean_Grind_AC_Seq_length(v_lhs_280_);
v___x_285_ = l_Lean_Grind_AC_Seq_length(v_lhs_282_);
v___x_286_ = lean_nat_dec_lt(v___x_284_, v___x_285_);
if (v___x_286_ == 0)
{
uint8_t v___x_287_; 
v___x_287_ = lean_nat_dec_eq(v___x_284_, v___x_285_);
lean_dec(v___x_285_);
lean_dec(v___x_284_);
if (v___x_287_ == 0)
{
uint8_t v___x_288_; 
v___x_288_ = 2;
return v___x_288_;
}
else
{
uint8_t v___x_289_; 
v___x_289_ = lean_nat_dec_lt(v_id_281_, v_id_283_);
if (v___x_289_ == 0)
{
uint8_t v___x_290_; 
v___x_290_ = lean_nat_dec_eq(v_id_281_, v_id_283_);
if (v___x_290_ == 0)
{
uint8_t v___x_291_; 
v___x_291_ = 2;
return v___x_291_;
}
else
{
uint8_t v___x_292_; 
v___x_292_ = 1;
return v___x_292_;
}
}
else
{
uint8_t v___x_293_; 
v___x_293_ = 0;
return v___x_293_;
}
}
}
else
{
uint8_t v___x_294_; 
lean_dec(v___x_285_);
lean_dec(v___x_284_);
v___x_294_ = 0;
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_compare___boxed(lean_object* v_c_u2081_295_, lean_object* v_c_u2082_296_){
_start:
{
uint8_t v_res_297_; lean_object* v_r_298_; 
v_res_297_ = l_Lean_Meta_Grind_AC_EqCnstr_compare(v_c_u2081_295_, v_c_u2082_296_);
lean_dec_ref(v_c_u2082_296_);
lean_dec_ref(v_c_u2081_295_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx(lean_object* v_x_299_){
_start:
{
switch(lean_obj_tag(v_x_299_))
{
case 0:
{
lean_object* v___x_300_; 
v___x_300_ = lean_unsigned_to_nat(0u);
return v___x_300_;
}
case 1:
{
lean_object* v___x_301_; 
v___x_301_ = lean_unsigned_to_nat(1u);
return v___x_301_;
}
case 2:
{
lean_object* v___x_302_; 
v___x_302_ = lean_unsigned_to_nat(2u);
return v___x_302_;
}
case 3:
{
lean_object* v___x_303_; 
v___x_303_ = lean_unsigned_to_nat(3u);
return v___x_303_;
}
case 4:
{
lean_object* v___x_304_; 
v___x_304_ = lean_unsigned_to_nat(4u);
return v___x_304_;
}
case 5:
{
lean_object* v___x_305_; 
v___x_305_ = lean_unsigned_to_nat(5u);
return v___x_305_;
}
case 6:
{
lean_object* v___x_306_; 
v___x_306_ = lean_unsigned_to_nat(6u);
return v___x_306_;
}
default: 
{
lean_object* v___x_307_; 
v___x_307_ = lean_unsigned_to_nat(7u);
return v___x_307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx___boxed(lean_object* v_x_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx(v_x_308_);
lean_dec_ref(v_x_308_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(lean_object* v_t_310_, lean_object* v_k_311_){
_start:
{
switch(lean_obj_tag(v_t_310_))
{
case 0:
{
lean_object* v_a_312_; lean_object* v_b_313_; lean_object* v_ea_314_; lean_object* v_eb_315_; lean_object* v___x_316_; 
v_a_312_ = lean_ctor_get(v_t_310_, 0);
lean_inc_ref(v_a_312_);
v_b_313_ = lean_ctor_get(v_t_310_, 1);
lean_inc_ref(v_b_313_);
v_ea_314_ = lean_ctor_get(v_t_310_, 2);
lean_inc_ref(v_ea_314_);
v_eb_315_ = lean_ctor_get(v_t_310_, 3);
lean_inc_ref(v_eb_315_);
lean_dec_ref(v_t_310_);
v___x_316_ = lean_apply_4(v_k_311_, v_a_312_, v_b_313_, v_ea_314_, v_eb_315_);
return v___x_316_;
}
case 1:
{
lean_object* v_c_317_; lean_object* v___x_318_; 
v_c_317_ = lean_ctor_get(v_t_310_, 0);
lean_inc_ref(v_c_317_);
lean_dec_ref(v_t_310_);
v___x_318_ = lean_apply_1(v_k_311_, v_c_317_);
return v___x_318_;
}
case 2:
{
lean_object* v_c_319_; lean_object* v___x_320_; 
v_c_319_ = lean_ctor_get(v_t_310_, 0);
lean_inc_ref(v_c_319_);
lean_dec_ref(v_t_310_);
v___x_320_ = lean_apply_1(v_k_311_, v_c_319_);
return v___x_320_;
}
case 3:
{
uint8_t v_lhs_321_; lean_object* v_c_u2081_322_; lean_object* v_c_u2082_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_lhs_321_ = lean_ctor_get_uint8(v_t_310_, sizeof(void*)*2);
v_c_u2081_322_ = lean_ctor_get(v_t_310_, 0);
lean_inc_ref(v_c_u2081_322_);
v_c_u2082_323_ = lean_ctor_get(v_t_310_, 1);
lean_inc_ref(v_c_u2082_323_);
lean_dec_ref(v_t_310_);
v___x_324_ = lean_box(v_lhs_321_);
v___x_325_ = lean_apply_3(v_k_311_, v___x_324_, v_c_u2081_322_, v_c_u2082_323_);
return v___x_325_;
}
case 7:
{
uint8_t v_lhs_326_; lean_object* v_s_u2081_327_; lean_object* v_s_u2082_328_; lean_object* v_c_u2081_329_; lean_object* v_c_u2082_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_lhs_326_ = lean_ctor_get_uint8(v_t_310_, sizeof(void*)*4);
v_s_u2081_327_ = lean_ctor_get(v_t_310_, 0);
lean_inc_ref(v_s_u2081_327_);
v_s_u2082_328_ = lean_ctor_get(v_t_310_, 1);
lean_inc_ref(v_s_u2082_328_);
v_c_u2081_329_ = lean_ctor_get(v_t_310_, 2);
lean_inc_ref(v_c_u2081_329_);
v_c_u2082_330_ = lean_ctor_get(v_t_310_, 3);
lean_inc_ref(v_c_u2082_330_);
lean_dec_ref(v_t_310_);
v___x_331_ = lean_box(v_lhs_326_);
v___x_332_ = lean_apply_5(v_k_311_, v___x_331_, v_s_u2081_327_, v_s_u2082_328_, v_c_u2081_329_, v_c_u2082_330_);
return v___x_332_;
}
default: 
{
uint8_t v_lhs_333_; lean_object* v_s_334_; lean_object* v_c_u2081_335_; lean_object* v_c_u2082_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_lhs_333_ = lean_ctor_get_uint8(v_t_310_, sizeof(void*)*3);
v_s_334_ = lean_ctor_get(v_t_310_, 0);
lean_inc_ref(v_s_334_);
v_c_u2081_335_ = lean_ctor_get(v_t_310_, 1);
lean_inc_ref(v_c_u2081_335_);
v_c_u2082_336_ = lean_ctor_get(v_t_310_, 2);
lean_inc_ref(v_c_u2082_336_);
lean_dec_ref(v_t_310_);
v___x_337_ = lean_box(v_lhs_333_);
v___x_338_ = lean_apply_4(v_k_311_, v___x_337_, v_s_334_, v_c_u2081_335_, v_c_u2082_336_);
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim(lean_object* v_motive__2_339_, lean_object* v_ctorIdx_340_, lean_object* v_t_341_, lean_object* v_h_342_, lean_object* v_k_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_341_, v_k_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_345_, lean_object* v_ctorIdx_346_, lean_object* v_t_347_, lean_object* v_h_348_, lean_object* v_k_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim(v_motive__2_345_, v_ctorIdx_346_, v_t_347_, v_h_348_, v_k_349_);
lean_dec(v_ctorIdx_346_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_core_elim___redArg(lean_object* v_t_351_, lean_object* v_core_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_351_, v_core_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_core_elim(lean_object* v_motive__2_354_, lean_object* v_t_355_, lean_object* v_h_356_, lean_object* v_core_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_355_, v_core_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase__dup_elim___redArg(lean_object* v_t_359_, lean_object* v_erase__dup_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_359_, v_erase__dup_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase__dup_elim(lean_object* v_motive__2_362_, lean_object* v_t_363_, lean_object* v_h_364_, lean_object* v_erase__dup_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_363_, v_erase__dup_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase0_elim___redArg(lean_object* v_t_367_, lean_object* v_erase0_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_367_, v_erase0_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase0_elim(lean_object* v_motive__2_370_, lean_object* v_t_371_, lean_object* v_h_372_, lean_object* v_erase0_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_371_, v_erase0_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__exact_elim___redArg(lean_object* v_t_375_, lean_object* v_simp__exact_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_375_, v_simp__exact_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__exact_elim(lean_object* v_motive__2_378_, lean_object* v_t_379_, lean_object* v_h_380_, lean_object* v_simp__exact_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_379_, v_simp__exact_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__ac_elim___redArg(lean_object* v_t_383_, lean_object* v_simp__ac_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_383_, v_simp__ac_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__ac_elim(lean_object* v_motive__2_386_, lean_object* v_t_387_, lean_object* v_h_388_, lean_object* v_simp__ac_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_387_, v_simp__ac_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__suffix_elim___redArg(lean_object* v_t_391_, lean_object* v_simp__suffix_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_391_, v_simp__suffix_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__suffix_elim(lean_object* v_motive__2_394_, lean_object* v_t_395_, lean_object* v_h_396_, lean_object* v_simp__suffix_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_395_, v_simp__suffix_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__prefix_elim___redArg(lean_object* v_t_399_, lean_object* v_simp__prefix_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_399_, v_simp__prefix_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__prefix_elim(lean_object* v_motive__2_402_, lean_object* v_t_403_, lean_object* v_h_404_, lean_object* v_simp__prefix_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_403_, v_simp__prefix_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__middle_elim___redArg(lean_object* v_t_407_, lean_object* v_simp__middle_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_407_, v_simp__middle_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__middle_elim(lean_object* v_motive__2_410_, lean_object* v_t_411_, lean_object* v_h_412_, lean_object* v_simp__middle_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_411_, v_simp__middle_413_);
return v___x_414_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = lean_unsigned_to_nat(32u);
v___x_416_ = lean_mk_empty_array_with_capacity(v___x_415_);
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1(void){
_start:
{
size_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_418_ = ((size_t)5ULL);
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = lean_unsigned_to_nat(32u);
v___x_421_ = lean_mk_empty_array_with_capacity(v___x_420_);
v___x_422_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0, &l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0_once, _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0);
v___x_423_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_421_);
lean_ctor_set(v___x_423_, 2, v___x_419_);
lean_ctor_set(v___x_423_, 3, v___x_419_);
lean_ctor_set_usize(v___x_423_, 4, v___x_418_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2(void){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_424_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2, &l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2_once, _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4(void){
_start:
{
uint8_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_427_ = 0;
v___x_428_ = lean_box(0);
v___x_429_ = lean_box(1);
v___x_430_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3, &l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3_once, _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3);
v___x_431_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1, &l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1_once, _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1);
v___x_432_ = lean_box(0);
v___x_433_ = lean_box(0);
v___x_434_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2, &l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2_once, _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2);
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v___x_434_);
lean_ctor_set(v___x_436_, 2, v___x_433_);
lean_ctor_set(v___x_436_, 3, v___x_434_);
lean_ctor_set(v___x_436_, 4, v___x_432_);
lean_ctor_set(v___x_436_, 5, v___x_434_);
lean_ctor_set(v___x_436_, 6, v___x_432_);
lean_ctor_set(v___x_436_, 7, v___x_432_);
lean_ctor_set(v___x_436_, 8, v___x_432_);
lean_ctor_set(v___x_436_, 9, v___x_435_);
lean_ctor_set(v___x_436_, 10, v___x_431_);
lean_ctor_set(v___x_436_, 11, v___x_430_);
lean_ctor_set(v___x_436_, 12, v___x_430_);
lean_ctor_set(v___x_436_, 13, v___x_431_);
lean_ctor_set(v___x_436_, 14, v___x_429_);
lean_ctor_set(v___x_436_, 15, v___x_428_);
lean_ctor_set(v___x_436_, 16, v___x_431_);
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*17, v___x_427_);
return v___x_436_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default(void){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4, &l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4_once, _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct(void){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Meta_Grind_AC_instInhabitedStruct_default;
return v___x_438_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_441_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2, &l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2);
v___x_446_ = ((lean_object*)(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__0));
v___x_447_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v___x_445_);
lean_ctor_set(v___x_447_, 2, v___x_445_);
lean_ctor_set(v___x_447_, 3, v___x_444_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedState_default(void){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedState(void){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_Meta_Grind_AC_instInhabitedState_default;
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(lean_object* v___x_450_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_450_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed(lean_object* v___x_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(v___x_453_);
return v_res_455_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_456_; lean_object* v___f_457_; 
v___x_456_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__3);
v___f_457_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_457_, 0, v___x_456_);
return v___f_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_459_; lean_object* v___x_460_; 
v___f_459_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_);
v___x_460_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed(lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_();
return v_res_462_;
}
}
lean_object* runtime_initialize_Init_Grind_AC(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Seq(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
