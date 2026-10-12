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
uint64_t l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(lean_object* v_x_1_){
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
LEAN_EXPORT void l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
uint64_t v_res_13_;
v_res_13_ = l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(v_x_1_);
stack->m_num = v_res_13_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash___boxed(lean_object* v_x_14_){
_start:
{
uint64_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Lean_Meta_Grind_AC_instHashableExpr__lean_hash(v_x_14_);
lean_dec_ref(v_x_14_);
v_r_16_ = lean_box_uint64(v_res_15_);
return v_r_16_;
}
}
uint64_t l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(lean_object* v_x_19_){
_start:
{
if (lean_obj_tag(v_x_19_) == 0)
{
lean_object* v_x_20_; uint64_t v___x_21_; uint64_t v___x_22_; uint64_t v___x_23_; 
v_x_20_ = lean_ctor_get(v_x_19_, 0);
v___x_21_ = 0ULL;
v___x_22_ = lean_uint64_of_nat(v_x_20_);
v___x_23_ = lean_uint64_mix_hash(v___x_21_, v___x_22_);
return v___x_23_;
}
else
{
lean_object* v_x_24_; lean_object* v_s_25_; uint64_t v___x_26_; uint64_t v___x_27_; uint64_t v___x_28_; uint64_t v___x_29_; uint64_t v___x_30_; 
v_x_24_ = lean_ctor_get(v_x_19_, 0);
v_s_25_ = lean_ctor_get(v_x_19_, 1);
v___x_26_ = 1ULL;
v___x_27_ = lean_uint64_of_nat(v_x_24_);
v___x_28_ = lean_uint64_mix_hash(v___x_26_, v___x_27_);
v___x_29_ = l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(v_s_25_);
v___x_30_ = lean_uint64_mix_hash(v___x_28_, v___x_29_);
return v___x_30_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_19_ = stack[0].m_obj;
uint64_t v_res_31_;
v_res_31_ = l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(v_x_19_);
stack->m_num = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash___boxed(lean_object* v_x_32_){
_start:
{
uint64_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = l_Lean_Meta_Grind_AC_instHashableSeq__lean_hash(v_x_32_);
lean_dec_ref(v_x_32_);
v_r_34_ = lean_box_uint64(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx___impl(lean_object* v_x_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_obj_tag_nat(v_x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorIdx___impl(v_x_39_);
lean_dec_ref(v_x_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(lean_object* v_t_41_, lean_object* v_k_42_){
_start:
{
switch(lean_obj_tag(v_t_41_))
{
case 0:
{
lean_object* v_a_43_; lean_object* v_b_44_; lean_object* v_ea_45_; lean_object* v_eb_46_; lean_object* v___x_47_; 
v_a_43_ = lean_ctor_get(v_t_41_, 0);
lean_inc_ref(v_a_43_);
v_b_44_ = lean_ctor_get(v_t_41_, 1);
lean_inc_ref(v_b_44_);
v_ea_45_ = lean_ctor_get(v_t_41_, 2);
lean_inc_ref(v_ea_45_);
v_eb_46_ = lean_ctor_get(v_t_41_, 3);
lean_inc_ref(v_eb_46_);
lean_dec_ref_known(v_t_41_, 4);
v___x_47_ = lean_apply_4(v_k_42_, v_a_43_, v_b_44_, v_ea_45_, v_eb_46_);
return v___x_47_;
}
case 4:
{
uint8_t v_lhs_48_; lean_object* v_c_u2081_49_; lean_object* v_c_u2082_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_lhs_48_ = lean_ctor_get_uint8(v_t_41_, sizeof(void*)*2);
v_c_u2081_49_ = lean_ctor_get(v_t_41_, 0);
lean_inc_ref(v_c_u2081_49_);
v_c_u2082_50_ = lean_ctor_get(v_t_41_, 1);
lean_inc_ref(v_c_u2082_50_);
lean_dec_ref_known(v_t_41_, 2);
v___x_51_ = lean_box(v_lhs_48_);
v___x_52_ = lean_apply_3(v_k_42_, v___x_51_, v_c_u2081_49_, v_c_u2082_50_);
return v___x_52_;
}
case 5:
{
uint8_t v_lhs_53_; lean_object* v_s_54_; lean_object* v_c_u2081_55_; lean_object* v_c_u2082_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v_lhs_53_ = lean_ctor_get_uint8(v_t_41_, sizeof(void*)*3);
v_s_54_ = lean_ctor_get(v_t_41_, 0);
lean_inc_ref(v_s_54_);
v_c_u2081_55_ = lean_ctor_get(v_t_41_, 1);
lean_inc_ref(v_c_u2081_55_);
v_c_u2082_56_ = lean_ctor_get(v_t_41_, 2);
lean_inc_ref(v_c_u2082_56_);
lean_dec_ref_known(v_t_41_, 3);
v___x_57_ = lean_box(v_lhs_53_);
v___x_58_ = lean_apply_4(v_k_42_, v___x_57_, v_s_54_, v_c_u2081_55_, v_c_u2082_56_);
return v___x_58_;
}
case 6:
{
uint8_t v_lhs_59_; lean_object* v_s_60_; lean_object* v_c_u2081_61_; lean_object* v_c_u2082_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v_lhs_59_ = lean_ctor_get_uint8(v_t_41_, sizeof(void*)*3);
v_s_60_ = lean_ctor_get(v_t_41_, 0);
lean_inc_ref(v_s_60_);
v_c_u2081_61_ = lean_ctor_get(v_t_41_, 1);
lean_inc_ref(v_c_u2081_61_);
v_c_u2082_62_ = lean_ctor_get(v_t_41_, 2);
lean_inc_ref(v_c_u2082_62_);
lean_dec_ref_known(v_t_41_, 3);
v___x_63_ = lean_box(v_lhs_59_);
v___x_64_ = lean_apply_4(v_k_42_, v___x_63_, v_s_60_, v_c_u2081_61_, v_c_u2082_62_);
return v___x_64_;
}
case 7:
{
uint8_t v_lhs_65_; lean_object* v_s_66_; lean_object* v_c_u2081_67_; lean_object* v_c_u2082_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_lhs_65_ = lean_ctor_get_uint8(v_t_41_, sizeof(void*)*3);
v_s_66_ = lean_ctor_get(v_t_41_, 0);
lean_inc_ref(v_s_66_);
v_c_u2081_67_ = lean_ctor_get(v_t_41_, 1);
lean_inc_ref(v_c_u2081_67_);
v_c_u2082_68_ = lean_ctor_get(v_t_41_, 2);
lean_inc_ref(v_c_u2082_68_);
lean_dec_ref_known(v_t_41_, 3);
v___x_69_ = lean_box(v_lhs_65_);
v___x_70_ = lean_apply_4(v_k_42_, v___x_69_, v_s_66_, v_c_u2081_67_, v_c_u2082_68_);
return v___x_70_;
}
case 8:
{
uint8_t v_lhs_71_; lean_object* v_s_u2081_72_; lean_object* v_s_u2082_73_; lean_object* v_c_u2081_74_; lean_object* v_c_u2082_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v_lhs_71_ = lean_ctor_get_uint8(v_t_41_, sizeof(void*)*4);
v_s_u2081_72_ = lean_ctor_get(v_t_41_, 0);
lean_inc_ref(v_s_u2081_72_);
v_s_u2082_73_ = lean_ctor_get(v_t_41_, 1);
lean_inc_ref(v_s_u2082_73_);
v_c_u2081_74_ = lean_ctor_get(v_t_41_, 2);
lean_inc_ref(v_c_u2081_74_);
v_c_u2082_75_ = lean_ctor_get(v_t_41_, 3);
lean_inc_ref(v_c_u2082_75_);
lean_dec_ref_known(v_t_41_, 4);
v___x_76_ = lean_box(v_lhs_71_);
v___x_77_ = lean_apply_5(v_k_42_, v___x_76_, v_s_u2081_72_, v_s_u2082_73_, v_c_u2081_74_, v_c_u2082_75_);
return v___x_77_;
}
case 9:
{
lean_object* v_r_u2081_78_; lean_object* v_c_79_; lean_object* v_r_u2082_80_; lean_object* v_c_u2081_81_; lean_object* v_c_u2082_82_; lean_object* v___x_83_; 
v_r_u2081_78_ = lean_ctor_get(v_t_41_, 0);
lean_inc_ref(v_r_u2081_78_);
v_c_79_ = lean_ctor_get(v_t_41_, 1);
lean_inc_ref(v_c_79_);
v_r_u2082_80_ = lean_ctor_get(v_t_41_, 2);
lean_inc_ref(v_r_u2082_80_);
v_c_u2081_81_ = lean_ctor_get(v_t_41_, 3);
lean_inc_ref(v_c_u2081_81_);
v_c_u2082_82_ = lean_ctor_get(v_t_41_, 4);
lean_inc_ref(v_c_u2082_82_);
lean_dec_ref_known(v_t_41_, 5);
v___x_83_ = lean_apply_5(v_k_42_, v_r_u2081_78_, v_c_79_, v_r_u2082_80_, v_c_u2081_81_, v_c_u2082_82_);
return v___x_83_;
}
case 10:
{
lean_object* v_p_84_; lean_object* v_s_85_; lean_object* v_c_86_; lean_object* v_c_u2081_87_; lean_object* v_c_u2082_88_; lean_object* v___x_89_; 
v_p_84_ = lean_ctor_get(v_t_41_, 0);
lean_inc_ref(v_p_84_);
v_s_85_ = lean_ctor_get(v_t_41_, 1);
lean_inc_ref(v_s_85_);
v_c_86_ = lean_ctor_get(v_t_41_, 2);
lean_inc_ref(v_c_86_);
v_c_u2081_87_ = lean_ctor_get(v_t_41_, 3);
lean_inc_ref(v_c_u2081_87_);
v_c_u2082_88_ = lean_ctor_get(v_t_41_, 4);
lean_inc_ref(v_c_u2082_88_);
lean_dec_ref_known(v_t_41_, 5);
v___x_89_ = lean_apply_5(v_k_42_, v_p_84_, v_s_85_, v_c_86_, v_c_u2081_87_, v_c_u2082_88_);
return v___x_89_;
}
case 11:
{
lean_object* v_x_90_; lean_object* v_c_u2081_91_; lean_object* v___x_92_; 
v_x_90_ = lean_ctor_get(v_t_41_, 0);
lean_inc(v_x_90_);
v_c_u2081_91_ = lean_ctor_get(v_t_41_, 1);
lean_inc_ref(v_c_u2081_91_);
lean_dec_ref_known(v_t_41_, 2);
v___x_92_ = lean_apply_2(v_k_42_, v_x_90_, v_c_u2081_91_);
return v___x_92_;
}
case 12:
{
lean_object* v_x_93_; lean_object* v_c_u2081_94_; lean_object* v___x_95_; 
v_x_93_ = lean_ctor_get(v_t_41_, 0);
lean_inc(v_x_93_);
v_c_u2081_94_ = lean_ctor_get(v_t_41_, 1);
lean_inc_ref(v_c_u2081_94_);
lean_dec_ref_known(v_t_41_, 2);
v___x_95_ = lean_apply_2(v_k_42_, v_x_93_, v_c_u2081_94_);
return v___x_95_;
}
case 13:
{
lean_object* v_x_96_; lean_object* v_c_u2081_97_; lean_object* v___x_98_; 
v_x_96_ = lean_ctor_get(v_t_41_, 0);
lean_inc(v_x_96_);
v_c_u2081_97_ = lean_ctor_get(v_t_41_, 1);
lean_inc_ref(v_c_u2081_97_);
lean_dec_ref_known(v_t_41_, 2);
v___x_98_ = lean_apply_2(v_k_42_, v_x_96_, v_c_u2081_97_);
return v___x_98_;
}
default: 
{
lean_object* v_c_99_; lean_object* v___x_100_; 
v_c_99_ = lean_ctor_get(v_t_41_, 0);
lean_inc_ref(v_c_99_);
lean_dec_ref(v_t_41_);
v___x_100_ = lean_apply_1(v_k_42_, v_c_99_);
return v___x_100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim(lean_object* v_motive__2_101_, lean_object* v_ctorIdx_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_k_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_103_, v_k_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_107_, lean_object* v_ctorIdx_108_, lean_object* v_t_109_, lean_object* v_h_110_, lean_object* v_k_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim(v_motive__2_107_, v_ctorIdx_108_, v_t_109_, v_h_110_, v_k_111_);
lean_dec(v_ctorIdx_108_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_core_elim___redArg(lean_object* v_t_113_, lean_object* v_core_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_113_, v_core_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_core_elim(lean_object* v_motive__2_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_core_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_117_, v_core_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup_elim___redArg(lean_object* v_t_121_, lean_object* v_erase__dup_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_121_, v_erase__dup_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup_elim(lean_object* v_motive__2_124_, lean_object* v_t_125_, lean_object* v_h_126_, lean_object* v_erase__dup_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_125_, v_erase__dup_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase0_elim___redArg(lean_object* v_t_129_, lean_object* v_erase0_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_129_, v_erase0_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase0_elim(lean_object* v_motive__2_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_erase0_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_133_, v_erase0_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_swap_elim___redArg(lean_object* v_t_137_, lean_object* v_swap_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_137_, v_swap_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_swap_elim(lean_object* v_motive__2_140_, lean_object* v_t_141_, lean_object* v_h_142_, lean_object* v_swap_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_141_, v_swap_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__exact_elim___redArg(lean_object* v_t_145_, lean_object* v_simp__exact_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_145_, v_simp__exact_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__exact_elim(lean_object* v_motive__2_148_, lean_object* v_t_149_, lean_object* v_h_150_, lean_object* v_simp__exact_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_149_, v_simp__exact_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__ac_elim___redArg(lean_object* v_t_153_, lean_object* v_simp__ac_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_153_, v_simp__ac_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__ac_elim(lean_object* v_motive__2_156_, lean_object* v_t_157_, lean_object* v_h_158_, lean_object* v_simp__ac_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_157_, v_simp__ac_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__suffix_elim___redArg(lean_object* v_t_161_, lean_object* v_simp__suffix_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_161_, v_simp__suffix_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__suffix_elim(lean_object* v_motive__2_164_, lean_object* v_t_165_, lean_object* v_h_166_, lean_object* v_simp__suffix_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_165_, v_simp__suffix_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__prefix_elim___redArg(lean_object* v_t_169_, lean_object* v_simp__prefix_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_169_, v_simp__prefix_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__prefix_elim(lean_object* v_motive__2_172_, lean_object* v_t_173_, lean_object* v_h_174_, lean_object* v_simp__prefix_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_173_, v_simp__prefix_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__middle_elim___redArg(lean_object* v_t_177_, lean_object* v_simp__middle_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_177_, v_simp__middle_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_simp__middle_elim(lean_object* v_motive__2_180_, lean_object* v_t_181_, lean_object* v_h_182_, lean_object* v_simp__middle_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_181_, v_simp__middle_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac_elim___redArg(lean_object* v_t_185_, lean_object* v_superpose__ac_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_185_, v_superpose__ac_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac_elim(lean_object* v_motive__2_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_superpose__ac_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_189_, v_superpose__ac_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose_elim___redArg(lean_object* v_t_193_, lean_object* v_superpose_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_193_, v_superpose_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose_elim(lean_object* v_motive__2_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_superpose_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_197_, v_superpose_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac__idempotent_elim___redArg(lean_object* v_t_201_, lean_object* v_superpose__ac__idempotent_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_201_, v_superpose__ac__idempotent_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__ac__idempotent_elim(lean_object* v_motive__2_204_, lean_object* v_t_205_, lean_object* v_h_206_, lean_object* v_superpose__ac__idempotent_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_205_, v_superpose__ac__idempotent_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__head__idempotent_elim___redArg(lean_object* v_t_209_, lean_object* v_superpose__head__idempotent_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_209_, v_superpose__head__idempotent_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__head__idempotent_elim(lean_object* v_motive__2_212_, lean_object* v_t_213_, lean_object* v_h_214_, lean_object* v_superpose__head__idempotent_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_213_, v_superpose__head__idempotent_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__tail__idempotent_elim___redArg(lean_object* v_t_217_, lean_object* v_superpose__tail__idempotent_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_217_, v_superpose__tail__idempotent_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_superpose__tail__idempotent_elim(lean_object* v_motive__2_220_, lean_object* v_t_221_, lean_object* v_h_222_, lean_object* v_superpose__tail__idempotent_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_221_, v_superpose__tail__idempotent_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_refl_elim___redArg(lean_object* v_t_225_, lean_object* v_refl_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_225_, v_refl_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_refl_elim(lean_object* v_motive__2_228_, lean_object* v_t_229_, lean_object* v_h_230_, lean_object* v_refl_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_229_, v_refl_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup__rhs_elim___redArg(lean_object* v_t_233_, lean_object* v_erase__dup__rhs_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_233_, v_erase__dup__rhs_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase__dup__rhs_elim(lean_object* v_motive__2_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_erase__dup__rhs_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_237_, v_erase__dup__rhs_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase0__rhs_elim___redArg(lean_object* v_t_241_, lean_object* v_erase0__rhs_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_241_, v_erase0__rhs_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstrProof_erase0__rhs_elim(lean_object* v_motive__2_244_, lean_object* v_t_245_, lean_object* v_h_246_, lean_object* v_erase0__rhs_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Meta_Grind_AC_EqCnstrProof_ctorElim___redArg(v_t_245_, v_erase0__rhs_247_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_box(0);
v___x_253_ = ((lean_object*)(l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__1));
v___x_254_ = l_Lean_Expr_const___override(v___x_253_, v___x_252_);
return v___x_254_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_255_ = l_Lean_Grind_AC_instInhabitedExpr_default;
v___x_256_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2, &l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2_once, _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2);
v___x_257_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
lean_ctor_set(v___x_257_, 2, v___x_255_);
lean_ctor_set(v___x_257_, 3, v___x_255_);
return v___x_257_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof(void){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3, &l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3_once, _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3, &l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3_once, _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__3);
v___x_261_ = l_Lean_Grind_AC_instInhabitedSeq_default;
v___x_262_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
lean_ctor_set(v___x_262_, 2, v___x_260_);
lean_ctor_set(v___x_262_, 3, v___x_259_);
return v___x_262_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr(void){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0, &l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0_once, _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstr___closed__0);
return v___x_263_;
}
}
uint8_t l_Lean_Meta_Grind_AC_EqCnstr_compare(lean_object* v_c_u2081_264_, lean_object* v_c_u2082_265_){
_start:
{
lean_object* v_lhs_266_; lean_object* v_id_267_; lean_object* v_lhs_268_; lean_object* v_id_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_lhs_266_ = lean_ctor_get(v_c_u2081_264_, 0);
v_id_267_ = lean_ctor_get(v_c_u2081_264_, 3);
v_lhs_268_ = lean_ctor_get(v_c_u2082_265_, 0);
v_id_269_ = lean_ctor_get(v_c_u2082_265_, 3);
v___x_270_ = l_Lean_Grind_AC_Seq_length(v_lhs_266_);
v___x_271_ = l_Lean_Grind_AC_Seq_length(v_lhs_268_);
v___x_272_ = lean_nat_dec_lt(v___x_270_, v___x_271_);
if (v___x_272_ == 0)
{
uint8_t v___x_273_; 
v___x_273_ = lean_nat_dec_eq(v___x_270_, v___x_271_);
lean_dec(v___x_271_);
lean_dec(v___x_270_);
if (v___x_273_ == 0)
{
uint8_t v___x_274_; 
v___x_274_ = 2;
return v___x_274_;
}
else
{
uint8_t v___x_275_; 
v___x_275_ = lean_nat_dec_lt(v_id_267_, v_id_269_);
if (v___x_275_ == 0)
{
uint8_t v___x_276_; 
v___x_276_ = lean_nat_dec_eq(v_id_267_, v_id_269_);
if (v___x_276_ == 0)
{
uint8_t v___x_277_; 
v___x_277_ = 2;
return v___x_277_;
}
else
{
uint8_t v___x_278_; 
v___x_278_ = 1;
return v___x_278_;
}
}
else
{
uint8_t v___x_279_; 
v___x_279_ = 0;
return v___x_279_;
}
}
}
else
{
uint8_t v___x_280_; 
lean_dec(v___x_271_);
lean_dec(v___x_270_);
v___x_280_ = 0;
return v___x_280_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_EqCnstr_compare_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_u2081_264_ = stack[0].m_obj;
lean_object* v_c_u2082_265_ = stack[1].m_obj;
uint8_t v_res_281_;
v_res_281_ = l_Lean_Meta_Grind_AC_EqCnstr_compare(v_c_u2081_264_, v_c_u2082_265_);
stack->m_num = v_res_281_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_compare___boxed(lean_object* v_c_u2081_282_, lean_object* v_c_u2082_283_){
_start:
{
uint8_t v_res_284_; lean_object* v_r_285_; 
v_res_284_ = l_Lean_Meta_Grind_AC_EqCnstr_compare(v_c_u2081_282_, v_c_u2082_283_);
lean_dec_ref(v_c_u2082_283_);
lean_dec_ref(v_c_u2081_282_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx___impl(lean_object* v_x_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_obj_tag_nat(v_x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorIdx___impl(v_x_288_);
lean_dec_ref(v_x_288_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(lean_object* v_t_290_, lean_object* v_k_291_){
_start:
{
switch(lean_obj_tag(v_t_290_))
{
case 0:
{
lean_object* v_a_292_; lean_object* v_b_293_; lean_object* v_ea_294_; lean_object* v_eb_295_; lean_object* v___x_296_; 
v_a_292_ = lean_ctor_get(v_t_290_, 0);
lean_inc_ref(v_a_292_);
v_b_293_ = lean_ctor_get(v_t_290_, 1);
lean_inc_ref(v_b_293_);
v_ea_294_ = lean_ctor_get(v_t_290_, 2);
lean_inc_ref(v_ea_294_);
v_eb_295_ = lean_ctor_get(v_t_290_, 3);
lean_inc_ref(v_eb_295_);
lean_dec_ref_known(v_t_290_, 4);
v___x_296_ = lean_apply_4(v_k_291_, v_a_292_, v_b_293_, v_ea_294_, v_eb_295_);
return v___x_296_;
}
case 1:
{
lean_object* v_c_297_; lean_object* v___x_298_; 
v_c_297_ = lean_ctor_get(v_t_290_, 0);
lean_inc_ref(v_c_297_);
lean_dec_ref_known(v_t_290_, 1);
v___x_298_ = lean_apply_1(v_k_291_, v_c_297_);
return v___x_298_;
}
case 2:
{
lean_object* v_c_299_; lean_object* v___x_300_; 
v_c_299_ = lean_ctor_get(v_t_290_, 0);
lean_inc_ref(v_c_299_);
lean_dec_ref_known(v_t_290_, 1);
v___x_300_ = lean_apply_1(v_k_291_, v_c_299_);
return v___x_300_;
}
case 3:
{
uint8_t v_lhs_301_; lean_object* v_c_u2081_302_; lean_object* v_c_u2082_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_lhs_301_ = lean_ctor_get_uint8(v_t_290_, sizeof(void*)*2);
v_c_u2081_302_ = lean_ctor_get(v_t_290_, 0);
lean_inc_ref(v_c_u2081_302_);
v_c_u2082_303_ = lean_ctor_get(v_t_290_, 1);
lean_inc_ref(v_c_u2082_303_);
lean_dec_ref_known(v_t_290_, 2);
v___x_304_ = lean_box(v_lhs_301_);
v___x_305_ = lean_apply_3(v_k_291_, v___x_304_, v_c_u2081_302_, v_c_u2082_303_);
return v___x_305_;
}
case 7:
{
uint8_t v_lhs_306_; lean_object* v_s_u2081_307_; lean_object* v_s_u2082_308_; lean_object* v_c_u2081_309_; lean_object* v_c_u2082_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_lhs_306_ = lean_ctor_get_uint8(v_t_290_, sizeof(void*)*4);
v_s_u2081_307_ = lean_ctor_get(v_t_290_, 0);
lean_inc_ref(v_s_u2081_307_);
v_s_u2082_308_ = lean_ctor_get(v_t_290_, 1);
lean_inc_ref(v_s_u2082_308_);
v_c_u2081_309_ = lean_ctor_get(v_t_290_, 2);
lean_inc_ref(v_c_u2081_309_);
v_c_u2082_310_ = lean_ctor_get(v_t_290_, 3);
lean_inc_ref(v_c_u2082_310_);
lean_dec_ref_known(v_t_290_, 4);
v___x_311_ = lean_box(v_lhs_306_);
v___x_312_ = lean_apply_5(v_k_291_, v___x_311_, v_s_u2081_307_, v_s_u2082_308_, v_c_u2081_309_, v_c_u2082_310_);
return v___x_312_;
}
default: 
{
uint8_t v_lhs_313_; lean_object* v_s_314_; lean_object* v_c_u2081_315_; lean_object* v_c_u2082_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_lhs_313_ = lean_ctor_get_uint8(v_t_290_, sizeof(void*)*3);
v_s_314_ = lean_ctor_get(v_t_290_, 0);
lean_inc_ref(v_s_314_);
v_c_u2081_315_ = lean_ctor_get(v_t_290_, 1);
lean_inc_ref(v_c_u2081_315_);
v_c_u2082_316_ = lean_ctor_get(v_t_290_, 2);
lean_inc_ref(v_c_u2082_316_);
lean_dec_ref(v_t_290_);
v___x_317_ = lean_box(v_lhs_313_);
v___x_318_ = lean_apply_4(v_k_291_, v___x_317_, v_s_314_, v_c_u2081_315_, v_c_u2082_316_);
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim(lean_object* v_motive__2_319_, lean_object* v_ctorIdx_320_, lean_object* v_t_321_, lean_object* v_h_322_, lean_object* v_k_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_321_, v_k_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_325_, lean_object* v_ctorIdx_326_, lean_object* v_t_327_, lean_object* v_h_328_, lean_object* v_k_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim(v_motive__2_325_, v_ctorIdx_326_, v_t_327_, v_h_328_, v_k_329_);
lean_dec(v_ctorIdx_326_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_core_elim___redArg(lean_object* v_t_331_, lean_object* v_core_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_331_, v_core_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_core_elim(lean_object* v_motive__2_334_, lean_object* v_t_335_, lean_object* v_h_336_, lean_object* v_core_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_335_, v_core_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase__dup_elim___redArg(lean_object* v_t_339_, lean_object* v_erase__dup_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_339_, v_erase__dup_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase__dup_elim(lean_object* v_motive__2_342_, lean_object* v_t_343_, lean_object* v_h_344_, lean_object* v_erase__dup_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_343_, v_erase__dup_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase0_elim___redArg(lean_object* v_t_347_, lean_object* v_erase0_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_347_, v_erase0_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_erase0_elim(lean_object* v_motive__2_350_, lean_object* v_t_351_, lean_object* v_h_352_, lean_object* v_erase0_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_351_, v_erase0_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__exact_elim___redArg(lean_object* v_t_355_, lean_object* v_simp__exact_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_355_, v_simp__exact_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__exact_elim(lean_object* v_motive__2_358_, lean_object* v_t_359_, lean_object* v_h_360_, lean_object* v_simp__exact_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_359_, v_simp__exact_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__ac_elim___redArg(lean_object* v_t_363_, lean_object* v_simp__ac_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_363_, v_simp__ac_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__ac_elim(lean_object* v_motive__2_366_, lean_object* v_t_367_, lean_object* v_h_368_, lean_object* v_simp__ac_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_367_, v_simp__ac_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__suffix_elim___redArg(lean_object* v_t_371_, lean_object* v_simp__suffix_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_371_, v_simp__suffix_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__suffix_elim(lean_object* v_motive__2_374_, lean_object* v_t_375_, lean_object* v_h_376_, lean_object* v_simp__suffix_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_375_, v_simp__suffix_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__prefix_elim___redArg(lean_object* v_t_379_, lean_object* v_simp__prefix_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_379_, v_simp__prefix_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__prefix_elim(lean_object* v_motive__2_382_, lean_object* v_t_383_, lean_object* v_h_384_, lean_object* v_simp__prefix_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_383_, v_simp__prefix_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__middle_elim___redArg(lean_object* v_t_387_, lean_object* v_simp__middle_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_387_, v_simp__middle_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstrProof_simp__middle_elim(lean_object* v_motive__2_390_, lean_object* v_t_391_, lean_object* v_h_392_, lean_object* v_simp__middle_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Meta_Grind_AC_DiseqCnstrProof_ctorElim___redArg(v_t_391_, v_simp__middle_393_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_395_ = lean_unsigned_to_nat(32u);
v___x_396_ = lean_mk_empty_array_with_capacity(v___x_395_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1(void){
_start:
{
size_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_398_ = ((size_t)5ULL);
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = lean_unsigned_to_nat(32u);
v___x_401_ = lean_mk_empty_array_with_capacity(v___x_400_);
v___x_402_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0, &l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0_once, _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__0);
v___x_403_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_401_);
lean_ctor_set(v___x_403_, 2, v___x_399_);
lean_ctor_set(v___x_403_, 3, v___x_399_);
lean_ctor_set_usize(v___x_403_, 4, v___x_398_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2(void){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_404_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2, &l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2_once, _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4(void){
_start:
{
uint8_t v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_407_ = 0;
v___x_408_ = lean_box(0);
v___x_409_ = lean_box(1);
v___x_410_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3, &l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3_once, _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__3);
v___x_411_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1, &l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1_once, _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__1);
v___x_412_ = lean_box(0);
v___x_413_ = lean_box(0);
v___x_414_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2, &l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2_once, _init_l_Lean_Meta_Grind_AC_instInhabitedEqCnstrProof___closed__2);
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___x_414_);
lean_ctor_set(v___x_416_, 2, v___x_413_);
lean_ctor_set(v___x_416_, 3, v___x_414_);
lean_ctor_set(v___x_416_, 4, v___x_412_);
lean_ctor_set(v___x_416_, 5, v___x_414_);
lean_ctor_set(v___x_416_, 6, v___x_412_);
lean_ctor_set(v___x_416_, 7, v___x_412_);
lean_ctor_set(v___x_416_, 8, v___x_412_);
lean_ctor_set(v___x_416_, 9, v___x_415_);
lean_ctor_set(v___x_416_, 10, v___x_411_);
lean_ctor_set(v___x_416_, 11, v___x_410_);
lean_ctor_set(v___x_416_, 12, v___x_410_);
lean_ctor_set(v___x_416_, 13, v___x_411_);
lean_ctor_set(v___x_416_, 14, v___x_409_);
lean_ctor_set(v___x_416_, 15, v___x_408_);
lean_ctor_set(v___x_416_, 16, v___x_411_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*17, v___x_407_);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default(void){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4, &l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4_once, _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__4);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedStruct(void){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Meta_Grind_AC_instInhabitedStruct_default;
return v___x_418_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2, &l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2_once, _init_l_Lean_Meta_Grind_AC_instInhabitedStruct_default___closed__2);
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__1);
v___x_425_ = ((lean_object*)(l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__0));
v___x_426_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v___x_424_);
lean_ctor_set(v___x_426_, 2, v___x_424_);
lean_ctor_set(v___x_426_, 3, v___x_423_);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedState_default(void){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2, &l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2);
return v___x_427_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instInhabitedState(void){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_Meta_Grind_AC_instInhabitedState_default;
return v___x_428_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(lean_object* v___x_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
return v___x_431_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_429_ = stack[0].m_obj;
lean_object* v_res_432_;
v_res_432_ = l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(v___x_429_);
stack->m_obj
 = v_res_432_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed(lean_object* v___x_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(v___x_433_);
return v_res_435_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_436_; lean_object* v___f_437_; 
v___x_436_ = lean_obj_once(&l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2, &l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Grind_AC_instInhabitedState_default___closed__2);
v___f_437_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_437_, 0, v___x_436_);
return v___f_437_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_439_; lean_object* v___x_440_; 
v___f_439_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_);
v___x_440_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_439_);
return v___x_440_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_441_;
v_res_441_ = l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_();
stack->m_obj
 = v_res_441_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2____boxed(lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l___private_Lean_Meta_Tactic_Grind_AC_Types_0__Lean_Meta_Grind_AC_initFn_00___x40_Lean_Meta_Tactic_Grind_AC_Types_2212383860____hygCtx___hyg_2_();
return v_res_443_;
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
