// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Normalize.ShortCircuit
// Imports: public import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic public import Std.Tactic.BVDecide.Normalize.BitVec
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_simpGlobalConfig;
lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "mul_beq_mul_short_circuit_right"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 40, 88, 243, 189, 216, 201, 25)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___boxed(lean_object**);
static const lean_array_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "mul_beq_mul_short_circuit_left"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(204, 153, 253, 100, 53, 72, 164, 67)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Normalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(105, 120, 51, 161, 199, 191, 75, 23)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(6, 181, 64, 73, 102, 44, 61, 193)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(53, 48, 36, 136, 58, 30, 220, 150)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "shortCircuitPass"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(45, 197, 199, 240, 107, 41, 97, 28)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_9_; 
lean_inc(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_9_ = lean_apply_7(v_x_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___lam__0___boxed(lean_object* v_x_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___lam__0(v_x_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_12_);
lean_dec_ref(v___y_11_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg(lean_object* v_mvarId_19_, lean_object* v_x_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; 
lean_inc(v___y_22_);
lean_inc_ref(v___y_21_);
v___f_28_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_28_, 0, v_x_20_);
lean_closure_set(v___f_28_, 1, v___y_21_);
lean_closure_set(v___f_28_, 2, v___y_22_);
v___x_29_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_19_, v___f_28_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_29_) == 0)
{
return v___x_29_;
}
else
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___boxed(lean_object* v_mvarId_38_, lean_object* v_x_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg(v_mvarId_38_, v_x_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0(lean_object* v_00_u03b1_48_, lean_object* v_mvarId_49_, lean_object* v_x_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg(v_mvarId_49_, v_x_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___boxed(lean_object* v_00_u03b1_59_, lean_object* v_mvarId_60_, lean_object* v_x_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0(v_00_u03b1_59_, v_mvarId_60_, v_x_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
return v_res_69_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__2(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_73_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__3(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__2);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__4(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_unsigned_to_nat(32u);
v___x_77_ = lean_mk_empty_array_with_capacity(v___x_76_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0(lean_object* v_theorems_79_, lean_object* v___x_80_, lean_object* v___x_81_, lean_object* v___x_82_, uint8_t v___x_83_, uint8_t v___x_84_, lean_object* v___x_85_, lean_object* v___x_86_, lean_object* v___x_87_, lean_object* v___x_88_, lean_object* v___x_89_, lean_object* v___x_90_, lean_object* v___x_91_, lean_object* v_goal_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___x_100_; 
lean_inc_ref(v___x_82_);
v___x_100_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(v_theorems_79_, v___x_80_, v___x_81_, v___x_82_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_a_101_);
lean_dec_ref(v___x_100_);
v___x_102_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__0));
v___x_103_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__1));
v___x_104_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set_uint8(v___x_104_, sizeof(void*)*1, v___x_83_);
lean_ctor_set_uint8(v___x_104_, sizeof(void*)*1 + 1, v___x_84_);
v___x_105_ = l_Lean_Name_mkStr6(v___x_85_, v___x_86_, v___x_87_, v___x_88_, v___x_89_, v___x_102_);
v___x_106_ = l_Lean_mkConst(v___x_105_, v___x_90_);
v___x_107_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(v_a_101_, v___x_104_, v___x_106_, v___x_82_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_109_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_a_108_);
lean_dec_ref(v___x_107_);
v___x_109_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_98_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v_maxSteps_111_; lean_object* v___x_112_; uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_a_110_);
lean_dec_ref(v___x_109_);
v_maxSteps_111_ = lean_ctor_get(v___y_93_, 1);
v___x_112_ = lean_unsigned_to_nat(2u);
v___x_113_ = 0;
v___x_114_ = lean_box(0);
lean_inc(v_maxSteps_111_);
v___x_115_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_115_, 0, v_maxSteps_111_);
lean_ctor_set(v___x_115_, 1, v___x_112_);
lean_ctor_set(v___x_115_, 2, v___x_114_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3, v___x_84_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 1, v___x_83_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 2, v___x_83_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 3, v___x_83_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 4, v___x_83_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 5, v___x_83_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 6, v___x_113_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 7, v___x_83_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 8, v___x_83_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 9, v___x_84_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 10, v___x_84_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 11, v___x_84_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 12, v___x_83_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 13, v___x_84_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 14, v___x_84_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 15, v___x_84_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 16, v___x_83_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 17, v___x_83_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 18, v___x_83_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 19, v___x_83_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 20, v___x_83_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 21, v___x_83_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 22, v___x_83_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 23, v___x_83_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 24, v___x_83_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 25, v___x_83_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 26, v___x_84_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 27, v___x_84_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 28, v___x_84_);
v___x_116_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_115_, v_a_108_, v_a_110_, v___y_95_, v___y_97_, v___y_98_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_118_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref(v___x_116_);
v___x_118_ = l_Lean_Meta_getPropHyps(v___y_95_, v___y_96_, v___y_97_, v___y_98_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; size_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_a_119_);
lean_dec_ref(v___x_118_);
v___x_120_ = lean_mk_empty_array_with_capacity(v___x_91_);
v___x_121_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__3);
lean_inc_n(v___x_91_, 2);
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
lean_ctor_set(v___x_122_, 1, v___x_91_);
v___x_123_ = lean_unsigned_to_nat(32u);
v___x_124_ = lean_mk_empty_array_with_capacity(v___x_123_);
v___x_125_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___closed__4);
v___x_126_ = ((size_t)5ULL);
v___x_127_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_127_, 0, v___x_125_);
lean_ctor_set(v___x_127_, 1, v___x_124_);
lean_ctor_set(v___x_127_, 2, v___x_91_);
lean_ctor_set(v___x_127_, 3, v___x_91_);
lean_ctor_set_usize(v___x_127_, 4, v___x_126_);
v___x_128_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_128_, 0, v___x_121_);
lean_ctor_set(v___x_128_, 1, v___x_121_);
lean_ctor_set(v___x_128_, 2, v___x_121_);
lean_ctor_set(v___x_128_, 3, v___x_127_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_122_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = l_Lean_Meta_simpGoal(v_goal_92_, v_a_117_, v___x_120_, v___x_114_, v___x_83_, v_a_119_, v___x_129_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_151_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_151_ == 0)
{
v___x_133_ = v___x_130_;
v_isShared_134_ = v_isSharedCheck_151_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_151_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v_fst_135_; 
v_fst_135_ = lean_ctor_get(v_a_131_, 0);
lean_inc(v_fst_135_);
lean_dec(v_a_131_);
if (lean_obj_tag(v_fst_135_) == 1)
{
lean_object* v_val_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_147_; 
v_val_136_ = lean_ctor_get(v_fst_135_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v_fst_135_);
if (v_isSharedCheck_147_ == 0)
{
v___x_138_ = v_fst_135_;
v_isShared_139_ = v_isSharedCheck_147_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_val_136_);
lean_dec(v_fst_135_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_147_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v_snd_140_; lean_object* v___x_142_; 
v_snd_140_ = lean_ctor_get(v_val_136_, 1);
lean_inc(v_snd_140_);
lean_dec(v_val_136_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v_snd_140_);
v___x_142_ = v___x_138_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_snd_140_);
v___x_142_ = v_reuseFailAlloc_146_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_144_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_142_);
v___x_144_ = v___x_133_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
else
{
lean_object* v___x_149_; 
lean_dec(v_fst_135_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_114_);
v___x_149_ = v___x_133_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_114_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
v_a_152_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_130_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_130_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
lean_dec(v_a_117_);
lean_dec(v_goal_92_);
lean_dec(v___x_91_);
v_a_160_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_118_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_118_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
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
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
lean_dec(v_goal_92_);
lean_dec(v___x_91_);
v_a_168_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_175_ == 0)
{
v___x_170_ = v___x_116_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_116_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
lean_dec(v_a_108_);
lean_dec(v_goal_92_);
lean_dec(v___x_91_);
v_a_176_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_109_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_109_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
lean_dec(v_goal_92_);
lean_dec(v___x_91_);
v_a_184_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_107_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_107_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec(v_goal_92_);
lean_dec(v___x_91_);
lean_dec(v___x_90_);
lean_dec_ref(v___x_89_);
lean_dec_ref(v___x_88_);
lean_dec_ref(v___x_87_);
lean_dec_ref(v___x_86_);
lean_dec_ref(v___x_85_);
lean_dec_ref(v___x_82_);
v_a_192_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_100_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_100_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___boxed(lean_object** _args){
lean_object* v_theorems_200_ = _args[0];
lean_object* v___x_201_ = _args[1];
lean_object* v___x_202_ = _args[2];
lean_object* v___x_203_ = _args[3];
lean_object* v___x_204_ = _args[4];
lean_object* v___x_205_ = _args[5];
lean_object* v___x_206_ = _args[6];
lean_object* v___x_207_ = _args[7];
lean_object* v___x_208_ = _args[8];
lean_object* v___x_209_ = _args[9];
lean_object* v___x_210_ = _args[10];
lean_object* v___x_211_ = _args[11];
lean_object* v___x_212_ = _args[12];
lean_object* v_goal_213_ = _args[13];
lean_object* v___y_214_ = _args[14];
lean_object* v___y_215_ = _args[15];
lean_object* v___y_216_ = _args[16];
lean_object* v___y_217_ = _args[17];
lean_object* v___y_218_ = _args[18];
lean_object* v___y_219_ = _args[19];
lean_object* v___y_220_ = _args[20];
_start:
{
uint8_t v___x_5231__boxed_221_; uint8_t v___x_5232__boxed_222_; lean_object* v_res_223_; 
v___x_5231__boxed_221_ = lean_unbox(v___x_204_);
v___x_5232__boxed_222_ = lean_unbox(v___x_205_);
v_res_223_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0(v_theorems_200_, v___x_201_, v___x_202_, v___x_203_, v___x_5231__boxed_221_, v___x_5232__boxed_222_, v___x_206_, v___x_207_, v___x_208_, v___x_209_, v___x_210_, v___x_211_, v___x_212_, v_goal_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
return v_res_223_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__10(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = lean_box(0);
v___x_246_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__9));
v___x_247_ = l_Lean_mkConst(v___x_246_, v___x_245_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1(lean_object* v_goal_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_256_; lean_object* v_theorems_257_; uint8_t v___x_258_; uint8_t v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___f_271_; lean_object* v___x_272_; 
v___x_256_ = lean_unsigned_to_nat(0u);
v_theorems_257_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__0));
v___x_258_ = 1;
v___x_259_ = 0;
v___x_260_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__3));
v___x_261_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__4));
v___x_262_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__5));
v___x_263_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__6));
v___x_264_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__7));
v___x_265_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__8));
v___x_266_ = lean_box(0);
v___x_267_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___closed__10);
v___x_268_ = l_Lean_Meta_simpGlobalConfig;
v___x_269_ = lean_box(v___x_258_);
v___x_270_ = lean_box(v___x_259_);
lean_inc(v_goal_248_);
v___f_271_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___boxed), 21, 14);
lean_closure_set(v___f_271_, 0, v_theorems_257_);
lean_closure_set(v___f_271_, 1, v___x_260_);
lean_closure_set(v___f_271_, 2, v___x_267_);
lean_closure_set(v___f_271_, 3, v___x_268_);
lean_closure_set(v___f_271_, 4, v___x_269_);
lean_closure_set(v___f_271_, 5, v___x_270_);
lean_closure_set(v___f_271_, 6, v___x_261_);
lean_closure_set(v___f_271_, 7, v___x_262_);
lean_closure_set(v___f_271_, 8, v___x_263_);
lean_closure_set(v___f_271_, 9, v___x_264_);
lean_closure_set(v___f_271_, 10, v___x_265_);
lean_closure_set(v___f_271_, 11, v___x_266_);
lean_closure_set(v___f_271_, 12, v___x_256_);
lean_closure_set(v___f_271_, 13, v_goal_248_);
v___x_272_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg(v_goal_248_, v___f_271_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___boxed(lean_object* v_goal_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1(v_goal_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
return v_res_281_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Normalize_BitVec(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ShortCircuit(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Normalize_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ShortCircuit(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Normalize_BitVec(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ShortCircuit(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Normalize_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ShortCircuit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ShortCircuit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ShortCircuit(builtin);
}
#ifdef __cplusplus
}
#endif
