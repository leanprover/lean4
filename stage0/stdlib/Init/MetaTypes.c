// Lean compiler output
// Module: Init.MetaTypes
// Imports: public import Init.Core
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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqList___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_string_object l_Lean_instInhabitedNameGenerator_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_Lean_instInhabitedNameGenerator_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedNameGenerator_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedNameGenerator_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedNameGenerator_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_Lean_instInhabitedNameGenerator_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedNameGenerator_default___closed__1_value;
static const lean_ctor_object l_Lean_instInhabitedNameGenerator_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedNameGenerator_default___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instInhabitedNameGenerator_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedNameGenerator_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedNameGenerator_default = (const lean_object*)&l_Lean_instInhabitedNameGenerator_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedNameGenerator = (const lean_object*)&l_Lean_instInhabitedNameGenerator_default___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedTransparencyMode_default;
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedTransparencyMode;
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqTransparencyMode_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instBEqTransparencyMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instBEqTransparencyMode_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instBEqTransparencyMode___closed__0 = (const lean_object*)&l_Lean_Meta_instBEqTransparencyMode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instBEqTransparencyMode = (const lean_object*)&l_Lean_Meta_instBEqTransparencyMode___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedEtaStructMode_default;
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedEtaStructMode;
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqEtaStructMode_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqEtaStructMode_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instBEqEtaStructMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instBEqEtaStructMode_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instBEqEtaStructMode___closed__0 = (const lean_object*)&l_Lean_Meta_instBEqEtaStructMode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instBEqEtaStructMode = (const lean_object*)&l_Lean_Meta_instBEqEtaStructMode___closed__0_value;
static const lean_ctor_object l_Lean_Meta_DSimp_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 16, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 1, 1, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 1, 1, 1, 0, 0)}};
static const lean_object* l_Lean_Meta_DSimp_instInhabitedConfig_default___closed__0 = (const lean_object*)&l_Lean_Meta_DSimp_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_DSimp_instInhabitedConfig_default = (const lean_object*)&l_Lean_Meta_DSimp_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_DSimp_instInhabitedConfig = (const lean_object*)&l_Lean_Meta_DSimp_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_DSimp_instBEqConfig_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DSimp_instBEqConfig_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_DSimp_instBEqConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DSimp_instBEqConfig_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DSimp_instBEqConfig___closed__0 = (const lean_object*)&l_Lean_Meta_DSimp_instBEqConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_DSimp_instBEqConfig = (const lean_object*)&l_Lean_Meta_DSimp_instBEqConfig___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
static const lean_ctor_object l_Lean_Meta_Simp_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 32, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 1, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 1, 1, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Simp_instInhabitedConfig_default___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Simp_instInhabitedConfig_default = (const lean_object*)&l_Lean_Meta_Simp_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Simp_instInhabitedConfig = (const lean_object*)&l_Lean_Meta_Simp_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_instBEqConfig_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instBEqConfig_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_instBEqConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_instBEqConfig_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_instBEqConfig___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_instBEqConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Simp_instBEqConfig = (const lean_object*)&l_Lean_Meta_Simp_instBEqConfig___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_neutralConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 32, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 1, 1, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 0, 1, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Simp_neutralConfig___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_neutralConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Simp_neutralConfig = (const lean_object*)&l_Lean_Meta_Simp_neutralConfig___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_all_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_all_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_pos_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_pos_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_neg_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_neg_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedOccurrences_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedOccurrences;
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqOccurrences_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqOccurrences_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instBEqOccurrences___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instBEqOccurrences_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instBEqOccurrences___closed__0 = (const lean_object*)&l_Lean_Meta_instBEqOccurrences___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instBEqOccurrences = (const lean_object*)&l_Lean_Meta_instBEqOccurrences___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instCoeListNatOccurrences___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_instCoeListNatOccurrences___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instCoeListNatOccurrences___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instCoeListNatOccurrences___closed__0 = (const lean_object*)&l_Lean_Meta_instCoeListNatOccurrences___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instCoeListNatOccurrences = (const lean_object*)&l_Lean_Meta_instCoeListNatOccurrences___closed__0_value;
lean_object* l_Lean_Meta_TransparencyMode_ctorIdx___impl(uint8_t v_x_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_box(v_x_9_);
v___x_11_ = lean_obj_tag_nat(v___x_10_);
lean_dec(v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT void l_Lean_Meta_TransparencyMode_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_9_ = stack[0].m_num;
lean_object* v_res_12_;
v_res_12_ = l_Lean_Meta_TransparencyMode_ctorIdx___impl(v_x_9_);
stack->m_obj
 = v_res_12_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorIdx___impl___boxed(lean_object* v_x_13_){
_start:
{
uint8_t v_x_4__boxed_14_; lean_object* v_res_15_; 
v_x_4__boxed_14_ = lean_unbox(v_x_13_);
v_res_15_ = l_Lean_Meta_TransparencyMode_ctorIdx___impl(v_x_4__boxed_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___redArg(lean_object* v_k_16_){
_start:
{
lean_inc(v_k_16_);
return v_k_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___redArg___boxed(lean_object* v_k_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_TransparencyMode_ctorElim___redArg(v_k_17_);
lean_dec(v_k_17_);
return v_res_18_;
}
}
lean_object* l_Lean_Meta_TransparencyMode_ctorElim(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, uint8_t v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_inc(v_k_23_);
return v_k_23_;
}
}
LEAN_EXPORT void l_Lean_Meta_TransparencyMode_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_20_ = stack[1].m_obj;
uint8_t v_t_21_ = stack[2].m_num;
lean_object* v_k_23_ = stack[4].m_obj;
lean_object* v_res_24_;
v_res_24_ = l_Lean_Meta_TransparencyMode_ctorElim(lean_box(0), v_ctorIdx_20_, v_t_21_, lean_box(0), v_k_23_);
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___boxed(lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
uint8_t v_t_boxed_30_; lean_object* v_res_31_; 
v_t_boxed_30_ = lean_unbox(v_t_27_);
v_res_31_ = l_Lean_Meta_TransparencyMode_ctorElim(v_motive_25_, v_ctorIdx_26_, v_t_boxed_30_, v_h_28_, v_k_29_);
lean_dec(v_k_29_);
lean_dec(v_ctorIdx_26_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___redArg(lean_object* v_all_32_){
_start:
{
lean_inc(v_all_32_);
return v_all_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___redArg___boxed(lean_object* v_all_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Meta_TransparencyMode_all_elim___redArg(v_all_33_);
lean_dec(v_all_33_);
return v_res_34_;
}
}
lean_object* l_Lean_Meta_TransparencyMode_all_elim(lean_object* v_motive_35_, uint8_t v_t_36_, lean_object* v_h_37_, lean_object* v_all_38_){
_start:
{
lean_inc(v_all_38_);
return v_all_38_;
}
}
LEAN_EXPORT void l_Lean_Meta_TransparencyMode_all_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_36_ = stack[1].m_num;
lean_object* v_all_38_ = stack[3].m_obj;
lean_object* v_res_39_;
v_res_39_ = l_Lean_Meta_TransparencyMode_all_elim(lean_box(0), v_t_36_, lean_box(0), v_all_38_);
stack->m_obj
 = v_res_39_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___boxed(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_all_43_){
_start:
{
uint8_t v_t_boxed_44_; lean_object* v_res_45_; 
v_t_boxed_44_ = lean_unbox(v_t_41_);
v_res_45_ = l_Lean_Meta_TransparencyMode_all_elim(v_motive_40_, v_t_boxed_44_, v_h_42_, v_all_43_);
lean_dec(v_all_43_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___redArg(lean_object* v_default_46_){
_start:
{
lean_inc(v_default_46_);
return v_default_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___redArg___boxed(lean_object* v_default_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_Meta_TransparencyMode_default_elim___redArg(v_default_47_);
lean_dec(v_default_47_);
return v_res_48_;
}
}
lean_object* l_Lean_Meta_TransparencyMode_default_elim(lean_object* v_motive_49_, uint8_t v_t_50_, lean_object* v_h_51_, lean_object* v_default_52_){
_start:
{
lean_inc(v_default_52_);
return v_default_52_;
}
}
LEAN_EXPORT void l_Lean_Meta_TransparencyMode_default_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_50_ = stack[1].m_num;
lean_object* v_default_52_ = stack[3].m_obj;
lean_object* v_res_53_;
v_res_53_ = l_Lean_Meta_TransparencyMode_default_elim(lean_box(0), v_t_50_, lean_box(0), v_default_52_);
stack->m_obj
 = v_res_53_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___boxed(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_default_57_){
_start:
{
uint8_t v_t_boxed_58_; lean_object* v_res_59_; 
v_t_boxed_58_ = lean_unbox(v_t_55_);
v_res_59_ = l_Lean_Meta_TransparencyMode_default_elim(v_motive_54_, v_t_boxed_58_, v_h_56_, v_default_57_);
lean_dec(v_default_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim___redArg(lean_object* v_reducible_60_){
_start:
{
lean_inc(v_reducible_60_);
return v_reducible_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim___redArg___boxed(lean_object* v_reducible_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Meta_TransparencyMode_reducible_elim___redArg(v_reducible_61_);
lean_dec(v_reducible_61_);
return v_res_62_;
}
}
lean_object* l_Lean_Meta_TransparencyMode_reducible_elim(lean_object* v_motive_63_, uint8_t v_t_64_, lean_object* v_h_65_, lean_object* v_reducible_66_){
_start:
{
lean_inc(v_reducible_66_);
return v_reducible_66_;
}
}
LEAN_EXPORT void l_Lean_Meta_TransparencyMode_reducible_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_64_ = stack[1].m_num;
lean_object* v_reducible_66_ = stack[3].m_obj;
lean_object* v_res_67_;
v_res_67_ = l_Lean_Meta_TransparencyMode_reducible_elim(lean_box(0), v_t_64_, lean_box(0), v_reducible_66_);
stack->m_obj
 = v_res_67_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_reducible_71_){
_start:
{
uint8_t v_t_boxed_72_; lean_object* v_res_73_; 
v_t_boxed_72_ = lean_unbox(v_t_69_);
v_res_73_ = l_Lean_Meta_TransparencyMode_reducible_elim(v_motive_68_, v_t_boxed_72_, v_h_70_, v_reducible_71_);
lean_dec(v_reducible_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___redArg(lean_object* v_instances_74_){
_start:
{
lean_inc(v_instances_74_);
return v_instances_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___redArg___boxed(lean_object* v_instances_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Meta_TransparencyMode_instances_elim___redArg(v_instances_75_);
lean_dec(v_instances_75_);
return v_res_76_;
}
}
lean_object* l_Lean_Meta_TransparencyMode_instances_elim(lean_object* v_motive_77_, uint8_t v_t_78_, lean_object* v_h_79_, lean_object* v_instances_80_){
_start:
{
lean_inc(v_instances_80_);
return v_instances_80_;
}
}
LEAN_EXPORT void l_Lean_Meta_TransparencyMode_instances_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_78_ = stack[1].m_num;
lean_object* v_instances_80_ = stack[3].m_obj;
lean_object* v_res_81_;
v_res_81_ = l_Lean_Meta_TransparencyMode_instances_elim(lean_box(0), v_t_78_, lean_box(0), v_instances_80_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___boxed(lean_object* v_motive_82_, lean_object* v_t_83_, lean_object* v_h_84_, lean_object* v_instances_85_){
_start:
{
uint8_t v_t_boxed_86_; lean_object* v_res_87_; 
v_t_boxed_86_ = lean_unbox(v_t_83_);
v_res_87_ = l_Lean_Meta_TransparencyMode_instances_elim(v_motive_82_, v_t_boxed_86_, v_h_84_, v_instances_85_);
lean_dec(v_instances_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___redArg(lean_object* v_none_88_){
_start:
{
lean_inc(v_none_88_);
return v_none_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___redArg___boxed(lean_object* v_none_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Meta_TransparencyMode_none_elim___redArg(v_none_89_);
lean_dec(v_none_89_);
return v_res_90_;
}
}
lean_object* l_Lean_Meta_TransparencyMode_none_elim(lean_object* v_motive_91_, uint8_t v_t_92_, lean_object* v_h_93_, lean_object* v_none_94_){
_start:
{
lean_inc(v_none_94_);
return v_none_94_;
}
}
LEAN_EXPORT void l_Lean_Meta_TransparencyMode_none_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_92_ = stack[1].m_num;
lean_object* v_none_94_ = stack[3].m_obj;
lean_object* v_res_95_;
v_res_95_ = l_Lean_Meta_TransparencyMode_none_elim(lean_box(0), v_t_92_, lean_box(0), v_none_94_);
stack->m_obj
 = v_res_95_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___boxed(lean_object* v_motive_96_, lean_object* v_t_97_, lean_object* v_h_98_, lean_object* v_none_99_){
_start:
{
uint8_t v_t_boxed_100_; lean_object* v_res_101_; 
v_t_boxed_100_ = lean_unbox(v_t_97_);
v_res_101_ = l_Lean_Meta_TransparencyMode_none_elim(v_motive_96_, v_t_boxed_100_, v_h_98_, v_none_99_);
lean_dec(v_none_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim___redArg(lean_object* v_implicit_102_){
_start:
{
lean_inc(v_implicit_102_);
return v_implicit_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim___redArg___boxed(lean_object* v_implicit_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Meta_TransparencyMode_implicit_elim___redArg(v_implicit_103_);
lean_dec(v_implicit_103_);
return v_res_104_;
}
}
lean_object* l_Lean_Meta_TransparencyMode_implicit_elim(lean_object* v_motive_105_, uint8_t v_t_106_, lean_object* v_h_107_, lean_object* v_implicit_108_){
_start:
{
lean_inc(v_implicit_108_);
return v_implicit_108_;
}
}
LEAN_EXPORT void l_Lean_Meta_TransparencyMode_implicit_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_106_ = stack[1].m_num;
lean_object* v_implicit_108_ = stack[3].m_obj;
lean_object* v_res_109_;
v_res_109_ = l_Lean_Meta_TransparencyMode_implicit_elim(lean_box(0), v_t_106_, lean_box(0), v_implicit_108_);
stack->m_obj
 = v_res_109_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim___boxed(lean_object* v_motive_110_, lean_object* v_t_111_, lean_object* v_h_112_, lean_object* v_implicit_113_){
_start:
{
uint8_t v_t_boxed_114_; lean_object* v_res_115_; 
v_t_boxed_114_ = lean_unbox(v_t_111_);
v_res_115_ = l_Lean_Meta_TransparencyMode_implicit_elim(v_motive_110_, v_t_boxed_114_, v_h_112_, v_implicit_113_);
lean_dec(v_implicit_113_);
return v_res_115_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedTransparencyMode_default(void){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = 0;
return v___x_116_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedTransparencyMode(void){
_start:
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
}
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t v_x_118_, uint8_t v_y_119_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_120_ = lean_box(v_x_118_);
v___x_121_ = lean_obj_tag_nat(v___x_120_);
lean_dec(v___x_120_);
v___x_122_ = lean_box(v_y_119_);
v___x_123_ = lean_obj_tag_nat(v___x_122_);
lean_dec(v___x_122_);
v___x_124_ = lean_nat_dec_eq(v___x_121_, v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT void l_Lean_Meta_instBEqTransparencyMode_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_118_ = stack[0].m_num;
uint8_t v_y_119_ = stack[1].m_num;
uint8_t v_res_125_;
v_res_125_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_x_118_, v_y_119_);
stack->m_num = v_res_125_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqTransparencyMode_beq___boxed(lean_object* v_x_126_, lean_object* v_y_127_){
_start:
{
uint8_t v_x_24__boxed_128_; uint8_t v_y_25__boxed_129_; uint8_t v_res_130_; lean_object* v_r_131_; 
v_x_24__boxed_128_ = lean_unbox(v_x_126_);
v_y_25__boxed_129_ = lean_unbox(v_y_127_);
v_res_130_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_x_24__boxed_128_, v_y_25__boxed_129_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
lean_object* l_Lean_Meta_EtaStructMode_ctorIdx___impl(uint8_t v_x_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_box(v_x_134_);
v___x_136_ = lean_obj_tag_nat(v___x_135_);
lean_dec(v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT void l_Lean_Meta_EtaStructMode_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_134_ = stack[0].m_num;
lean_object* v_res_137_;
v_res_137_ = l_Lean_Meta_EtaStructMode_ctorIdx___impl(v_x_134_);
stack->m_obj
 = v_res_137_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorIdx___impl___boxed(lean_object* v_x_138_){
_start:
{
uint8_t v_x_4__boxed_139_; lean_object* v_res_140_; 
v_x_4__boxed_139_ = lean_unbox(v_x_138_);
v_res_140_ = l_Lean_Meta_EtaStructMode_ctorIdx___impl(v_x_4__boxed_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___redArg(lean_object* v_k_141_){
_start:
{
lean_inc(v_k_141_);
return v_k_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___redArg___boxed(lean_object* v_k_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Meta_EtaStructMode_ctorElim___redArg(v_k_142_);
lean_dec(v_k_142_);
return v_res_143_;
}
}
lean_object* l_Lean_Meta_EtaStructMode_ctorElim(lean_object* v_motive_144_, lean_object* v_ctorIdx_145_, uint8_t v_t_146_, lean_object* v_h_147_, lean_object* v_k_148_){
_start:
{
lean_inc(v_k_148_);
return v_k_148_;
}
}
LEAN_EXPORT void l_Lean_Meta_EtaStructMode_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_145_ = stack[1].m_obj;
uint8_t v_t_146_ = stack[2].m_num;
lean_object* v_k_148_ = stack[4].m_obj;
lean_object* v_res_149_;
v_res_149_ = l_Lean_Meta_EtaStructMode_ctorElim(lean_box(0), v_ctorIdx_145_, v_t_146_, lean_box(0), v_k_148_);
stack->m_obj
 = v_res_149_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___boxed(lean_object* v_motive_150_, lean_object* v_ctorIdx_151_, lean_object* v_t_152_, lean_object* v_h_153_, lean_object* v_k_154_){
_start:
{
uint8_t v_t_boxed_155_; lean_object* v_res_156_; 
v_t_boxed_155_ = lean_unbox(v_t_152_);
v_res_156_ = l_Lean_Meta_EtaStructMode_ctorElim(v_motive_150_, v_ctorIdx_151_, v_t_boxed_155_, v_h_153_, v_k_154_);
lean_dec(v_k_154_);
lean_dec(v_ctorIdx_151_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___redArg(lean_object* v_all_157_){
_start:
{
lean_inc(v_all_157_);
return v_all_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___redArg___boxed(lean_object* v_all_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Meta_EtaStructMode_all_elim___redArg(v_all_158_);
lean_dec(v_all_158_);
return v_res_159_;
}
}
lean_object* l_Lean_Meta_EtaStructMode_all_elim(lean_object* v_motive_160_, uint8_t v_t_161_, lean_object* v_h_162_, lean_object* v_all_163_){
_start:
{
lean_inc(v_all_163_);
return v_all_163_;
}
}
LEAN_EXPORT void l_Lean_Meta_EtaStructMode_all_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_161_ = stack[1].m_num;
lean_object* v_all_163_ = stack[3].m_obj;
lean_object* v_res_164_;
v_res_164_ = l_Lean_Meta_EtaStructMode_all_elim(lean_box(0), v_t_161_, lean_box(0), v_all_163_);
stack->m_obj
 = v_res_164_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___boxed(lean_object* v_motive_165_, lean_object* v_t_166_, lean_object* v_h_167_, lean_object* v_all_168_){
_start:
{
uint8_t v_t_boxed_169_; lean_object* v_res_170_; 
v_t_boxed_169_ = lean_unbox(v_t_166_);
v_res_170_ = l_Lean_Meta_EtaStructMode_all_elim(v_motive_165_, v_t_boxed_169_, v_h_167_, v_all_168_);
lean_dec(v_all_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___redArg(lean_object* v_notClasses_171_){
_start:
{
lean_inc(v_notClasses_171_);
return v_notClasses_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___redArg___boxed(lean_object* v_notClasses_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Meta_EtaStructMode_notClasses_elim___redArg(v_notClasses_172_);
lean_dec(v_notClasses_172_);
return v_res_173_;
}
}
lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim(lean_object* v_motive_174_, uint8_t v_t_175_, lean_object* v_h_176_, lean_object* v_notClasses_177_){
_start:
{
lean_inc(v_notClasses_177_);
return v_notClasses_177_;
}
}
LEAN_EXPORT void l_Lean_Meta_EtaStructMode_notClasses_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_175_ = stack[1].m_num;
lean_object* v_notClasses_177_ = stack[3].m_obj;
lean_object* v_res_178_;
v_res_178_ = l_Lean_Meta_EtaStructMode_notClasses_elim(lean_box(0), v_t_175_, lean_box(0), v_notClasses_177_);
stack->m_obj
 = v_res_178_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___boxed(lean_object* v_motive_179_, lean_object* v_t_180_, lean_object* v_h_181_, lean_object* v_notClasses_182_){
_start:
{
uint8_t v_t_boxed_183_; lean_object* v_res_184_; 
v_t_boxed_183_ = lean_unbox(v_t_180_);
v_res_184_ = l_Lean_Meta_EtaStructMode_notClasses_elim(v_motive_179_, v_t_boxed_183_, v_h_181_, v_notClasses_182_);
lean_dec(v_notClasses_182_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___redArg(lean_object* v_none_185_){
_start:
{
lean_inc(v_none_185_);
return v_none_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___redArg___boxed(lean_object* v_none_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Meta_EtaStructMode_none_elim___redArg(v_none_186_);
lean_dec(v_none_186_);
return v_res_187_;
}
}
lean_object* l_Lean_Meta_EtaStructMode_none_elim(lean_object* v_motive_188_, uint8_t v_t_189_, lean_object* v_h_190_, lean_object* v_none_191_){
_start:
{
lean_inc(v_none_191_);
return v_none_191_;
}
}
LEAN_EXPORT void l_Lean_Meta_EtaStructMode_none_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_189_ = stack[1].m_num;
lean_object* v_none_191_ = stack[3].m_obj;
lean_object* v_res_192_;
v_res_192_ = l_Lean_Meta_EtaStructMode_none_elim(lean_box(0), v_t_189_, lean_box(0), v_none_191_);
stack->m_obj
 = v_res_192_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___boxed(lean_object* v_motive_193_, lean_object* v_t_194_, lean_object* v_h_195_, lean_object* v_none_196_){
_start:
{
uint8_t v_t_boxed_197_; lean_object* v_res_198_; 
v_t_boxed_197_ = lean_unbox(v_t_194_);
v_res_198_ = l_Lean_Meta_EtaStructMode_none_elim(v_motive_193_, v_t_boxed_197_, v_h_195_, v_none_196_);
lean_dec(v_none_196_);
return v_res_198_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedEtaStructMode_default(void){
_start:
{
uint8_t v___x_199_; 
v___x_199_ = 0;
return v___x_199_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedEtaStructMode(void){
_start:
{
uint8_t v___x_200_; 
v___x_200_ = 0;
return v___x_200_;
}
}
uint8_t l_Lean_Meta_instBEqEtaStructMode_beq(uint8_t v_x_201_, uint8_t v_y_202_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_203_ = lean_box(v_x_201_);
v___x_204_ = lean_obj_tag_nat(v___x_203_);
lean_dec(v___x_203_);
v___x_205_ = lean_box(v_y_202_);
v___x_206_ = lean_obj_tag_nat(v___x_205_);
lean_dec(v___x_205_);
v___x_207_ = lean_nat_dec_eq(v___x_204_, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT void l_Lean_Meta_instBEqEtaStructMode_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_201_ = stack[0].m_num;
uint8_t v_y_202_ = stack[1].m_num;
uint8_t v_res_208_;
v_res_208_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_x_201_, v_y_202_);
stack->m_num = v_res_208_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqEtaStructMode_beq___boxed(lean_object* v_x_209_, lean_object* v_y_210_){
_start:
{
uint8_t v_x_24__boxed_211_; uint8_t v_y_25__boxed_212_; uint8_t v_res_213_; lean_object* v_r_214_; 
v_x_24__boxed_211_ = lean_unbox(v_x_209_);
v_y_25__boxed_212_ = lean_unbox(v_y_210_);
v_res_213_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_x_24__boxed_211_, v_y_25__boxed_212_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
uint8_t l_Lean_Meta_DSimp_instBEqConfig_beq(lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
uint8_t v_zeta_225_; uint8_t v_beta_226_; uint8_t v_eta_227_; uint8_t v_etaStruct_228_; uint8_t v_iota_229_; uint8_t v_proj_230_; uint8_t v_decide_231_; uint8_t v_autoUnfold_232_; uint8_t v_failIfUnchanged_233_; uint8_t v_unfoldPartialApp_234_; uint8_t v_zetaDelta_235_; uint8_t v_index_236_; uint8_t v_zetaUnused_237_; uint8_t v_zetaHave_238_; uint8_t v_locals_239_; uint8_t v_instances_240_; uint8_t v_zeta_241_; uint8_t v_beta_242_; uint8_t v_eta_243_; uint8_t v_etaStruct_244_; uint8_t v_iota_245_; uint8_t v_proj_246_; uint8_t v_decide_247_; uint8_t v_autoUnfold_248_; uint8_t v_failIfUnchanged_249_; uint8_t v_unfoldPartialApp_250_; uint8_t v_zetaDelta_251_; uint8_t v_index_252_; uint8_t v_zetaUnused_253_; uint8_t v_zetaHave_254_; uint8_t v_locals_255_; uint8_t v_instances_256_; uint8_t v___y_258_; uint8_t v___y_260_; uint8_t v___y_262_; uint8_t v___y_264_; uint8_t v___y_266_; uint8_t v___y_268_; uint8_t v___y_270_; uint8_t v___y_272_; uint8_t v___y_274_; uint8_t v___y_276_; uint8_t v___y_278_; 
v_zeta_225_ = lean_ctor_get_uint8(v_x_223_, 0);
v_beta_226_ = lean_ctor_get_uint8(v_x_223_, 1);
v_eta_227_ = lean_ctor_get_uint8(v_x_223_, 2);
v_etaStruct_228_ = lean_ctor_get_uint8(v_x_223_, 3);
v_iota_229_ = lean_ctor_get_uint8(v_x_223_, 4);
v_proj_230_ = lean_ctor_get_uint8(v_x_223_, 5);
v_decide_231_ = lean_ctor_get_uint8(v_x_223_, 6);
v_autoUnfold_232_ = lean_ctor_get_uint8(v_x_223_, 7);
v_failIfUnchanged_233_ = lean_ctor_get_uint8(v_x_223_, 8);
v_unfoldPartialApp_234_ = lean_ctor_get_uint8(v_x_223_, 9);
v_zetaDelta_235_ = lean_ctor_get_uint8(v_x_223_, 10);
v_index_236_ = lean_ctor_get_uint8(v_x_223_, 11);
v_zetaUnused_237_ = lean_ctor_get_uint8(v_x_223_, 12);
v_zetaHave_238_ = lean_ctor_get_uint8(v_x_223_, 13);
v_locals_239_ = lean_ctor_get_uint8(v_x_223_, 14);
v_instances_240_ = lean_ctor_get_uint8(v_x_223_, 15);
v_zeta_241_ = lean_ctor_get_uint8(v_x_224_, 0);
v_beta_242_ = lean_ctor_get_uint8(v_x_224_, 1);
v_eta_243_ = lean_ctor_get_uint8(v_x_224_, 2);
v_etaStruct_244_ = lean_ctor_get_uint8(v_x_224_, 3);
v_iota_245_ = lean_ctor_get_uint8(v_x_224_, 4);
v_proj_246_ = lean_ctor_get_uint8(v_x_224_, 5);
v_decide_247_ = lean_ctor_get_uint8(v_x_224_, 6);
v_autoUnfold_248_ = lean_ctor_get_uint8(v_x_224_, 7);
v_failIfUnchanged_249_ = lean_ctor_get_uint8(v_x_224_, 8);
v_unfoldPartialApp_250_ = lean_ctor_get_uint8(v_x_224_, 9);
v_zetaDelta_251_ = lean_ctor_get_uint8(v_x_224_, 10);
v_index_252_ = lean_ctor_get_uint8(v_x_224_, 11);
v_zetaUnused_253_ = lean_ctor_get_uint8(v_x_224_, 12);
v_zetaHave_254_ = lean_ctor_get_uint8(v_x_224_, 13);
v_locals_255_ = lean_ctor_get_uint8(v_x_224_, 14);
v_instances_256_ = lean_ctor_get_uint8(v_x_224_, 15);
if (v_zeta_241_ == 0)
{
if (v_zeta_225_ == 0)
{
goto v___jp_282_;
}
else
{
return v_zeta_241_;
}
}
else
{
if (v_zeta_225_ == 0)
{
return v_zeta_225_;
}
else
{
goto v___jp_282_;
}
}
v___jp_257_:
{
if (v_instances_256_ == 0)
{
if (v_instances_240_ == 0)
{
return v___y_258_;
}
else
{
return v_instances_256_;
}
}
else
{
return v_instances_240_;
}
}
v___jp_259_:
{
if (v_locals_255_ == 0)
{
if (v_locals_239_ == 0)
{
v___y_258_ = v___y_260_;
goto v___jp_257_;
}
else
{
return v_locals_255_;
}
}
else
{
if (v_locals_239_ == 0)
{
return v_locals_239_;
}
else
{
v___y_258_ = v_locals_239_;
goto v___jp_257_;
}
}
}
v___jp_261_:
{
if (v_zetaHave_254_ == 0)
{
if (v_zetaHave_238_ == 0)
{
v___y_260_ = v___y_262_;
goto v___jp_259_;
}
else
{
return v_zetaHave_254_;
}
}
else
{
if (v_zetaHave_238_ == 0)
{
return v_zetaHave_238_;
}
else
{
v___y_260_ = v_zetaHave_238_;
goto v___jp_259_;
}
}
}
v___jp_263_:
{
if (v_zetaUnused_253_ == 0)
{
if (v_zetaUnused_237_ == 0)
{
v___y_262_ = v___y_264_;
goto v___jp_261_;
}
else
{
return v_zetaUnused_253_;
}
}
else
{
if (v_zetaUnused_237_ == 0)
{
return v_zetaUnused_237_;
}
else
{
v___y_262_ = v_zetaUnused_237_;
goto v___jp_261_;
}
}
}
v___jp_265_:
{
if (v_index_252_ == 0)
{
if (v_index_236_ == 0)
{
v___y_264_ = v___y_266_;
goto v___jp_263_;
}
else
{
return v_index_252_;
}
}
else
{
if (v_index_236_ == 0)
{
return v_index_236_;
}
else
{
v___y_264_ = v_index_236_;
goto v___jp_263_;
}
}
}
v___jp_267_:
{
if (v_zetaDelta_251_ == 0)
{
if (v_zetaDelta_235_ == 0)
{
v___y_266_ = v___y_268_;
goto v___jp_265_;
}
else
{
return v_zetaDelta_251_;
}
}
else
{
if (v_zetaDelta_235_ == 0)
{
return v_zetaDelta_235_;
}
else
{
v___y_266_ = v_zetaDelta_235_;
goto v___jp_265_;
}
}
}
v___jp_269_:
{
if (v_unfoldPartialApp_250_ == 0)
{
if (v_unfoldPartialApp_234_ == 0)
{
v___y_268_ = v___y_270_;
goto v___jp_267_;
}
else
{
return v_unfoldPartialApp_250_;
}
}
else
{
if (v_unfoldPartialApp_234_ == 0)
{
return v_unfoldPartialApp_234_;
}
else
{
v___y_268_ = v_unfoldPartialApp_234_;
goto v___jp_267_;
}
}
}
v___jp_271_:
{
if (v_failIfUnchanged_249_ == 0)
{
if (v_failIfUnchanged_233_ == 0)
{
v___y_270_ = v___y_272_;
goto v___jp_269_;
}
else
{
return v_failIfUnchanged_249_;
}
}
else
{
if (v_failIfUnchanged_233_ == 0)
{
return v_failIfUnchanged_233_;
}
else
{
v___y_270_ = v_failIfUnchanged_233_;
goto v___jp_269_;
}
}
}
v___jp_273_:
{
if (v_autoUnfold_248_ == 0)
{
if (v_autoUnfold_232_ == 0)
{
v___y_272_ = v___y_274_;
goto v___jp_271_;
}
else
{
return v_autoUnfold_248_;
}
}
else
{
if (v_autoUnfold_232_ == 0)
{
return v_autoUnfold_232_;
}
else
{
v___y_272_ = v_autoUnfold_232_;
goto v___jp_271_;
}
}
}
v___jp_275_:
{
if (v_decide_247_ == 0)
{
if (v_decide_231_ == 0)
{
v___y_274_ = v___y_276_;
goto v___jp_273_;
}
else
{
return v_decide_247_;
}
}
else
{
if (v_decide_231_ == 0)
{
return v_decide_231_;
}
else
{
v___y_274_ = v_decide_231_;
goto v___jp_273_;
}
}
}
v___jp_277_:
{
if (v___y_278_ == 0)
{
return v___y_278_;
}
else
{
if (v_proj_246_ == 0)
{
if (v_proj_230_ == 0)
{
v___y_276_ = v___y_278_;
goto v___jp_275_;
}
else
{
return v_proj_246_;
}
}
else
{
if (v_proj_230_ == 0)
{
return v_proj_230_;
}
else
{
v___y_276_ = v_proj_230_;
goto v___jp_275_;
}
}
}
}
v___jp_279_:
{
uint8_t v___x_280_; 
v___x_280_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_228_, v_etaStruct_244_);
if (v___x_280_ == 0)
{
return v___x_280_;
}
else
{
if (v_iota_245_ == 0)
{
if (v_iota_229_ == 0)
{
v___y_278_ = v___x_280_;
goto v___jp_277_;
}
else
{
return v_iota_245_;
}
}
else
{
v___y_278_ = v_iota_229_;
goto v___jp_277_;
}
}
}
v___jp_281_:
{
if (v_eta_243_ == 0)
{
if (v_eta_227_ == 0)
{
goto v___jp_279_;
}
else
{
return v_eta_243_;
}
}
else
{
if (v_eta_227_ == 0)
{
return v_eta_227_;
}
else
{
goto v___jp_279_;
}
}
}
v___jp_282_:
{
if (v_beta_242_ == 0)
{
if (v_beta_226_ == 0)
{
goto v___jp_281_;
}
else
{
return v_beta_242_;
}
}
else
{
if (v_beta_226_ == 0)
{
return v_beta_226_;
}
else
{
goto v___jp_281_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_DSimp_instBEqConfig_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_223_ = stack[0].m_obj;
lean_object* v_x_224_ = stack[1].m_obj;
uint8_t v_res_283_;
v_res_283_ = l_Lean_Meta_DSimp_instBEqConfig_beq(v_x_223_, v_x_224_);
stack->m_num = v_res_283_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DSimp_instBEqConfig_beq___boxed(lean_object* v_x_284_, lean_object* v_x_285_){
_start:
{
uint8_t v_res_286_; lean_object* v_r_287_; 
v_res_286_ = l_Lean_Meta_DSimp_instBEqConfig_beq(v_x_284_, v_x_285_);
lean_dec_ref(v_x_285_);
lean_dec_ref(v_x_284_);
v_r_287_ = lean_box(v_res_286_);
return v_r_287_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_defaultMaxSteps(void){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_unsigned_to_nat(100000u);
return v___x_290_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
if (lean_obj_tag(v_x_300_) == 0)
{
if (lean_obj_tag(v_x_301_) == 0)
{
uint8_t v___x_302_; 
v___x_302_ = 1;
return v___x_302_;
}
else
{
uint8_t v___x_303_; 
v___x_303_ = 0;
return v___x_303_;
}
}
else
{
if (lean_obj_tag(v_x_301_) == 0)
{
uint8_t v___x_304_; 
v___x_304_ = 0;
return v___x_304_;
}
else
{
lean_object* v_val_305_; lean_object* v_val_306_; uint8_t v___x_307_; 
v_val_305_ = lean_ctor_get(v_x_300_, 0);
v_val_306_ = lean_ctor_get(v_x_301_, 0);
v___x_307_ = lean_nat_dec_eq(v_val_305_, v_val_306_);
return v___x_307_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_300_ = stack[0].m_obj;
lean_object* v_x_301_ = stack[1].m_obj;
uint8_t v_res_308_;
v_res_308_ = l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(v_x_300_, v_x_301_);
stack->m_num = v_res_308_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0___boxed(lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
uint8_t v_res_311_; lean_object* v_r_312_; 
v_res_311_ = l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(v_x_309_, v_x_310_);
lean_dec(v_x_310_);
lean_dec(v_x_309_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
uint8_t l_Lean_Meta_Simp_instBEqConfig_beq(lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
lean_object* v_maxSteps_315_; lean_object* v_maxDischargeDepth_316_; uint8_t v_contextual_317_; uint8_t v_memoize_318_; uint8_t v_singlePass_319_; uint8_t v_zeta_320_; uint8_t v_beta_321_; uint8_t v_eta_322_; uint8_t v_etaStruct_323_; uint8_t v_iota_324_; uint8_t v_proj_325_; uint8_t v_decide_326_; uint8_t v_arith_327_; uint8_t v_autoUnfold_328_; uint8_t v_dsimp_329_; uint8_t v_failIfUnchanged_330_; uint8_t v_ground_331_; uint8_t v_unfoldPartialApp_332_; uint8_t v_zetaDelta_333_; uint8_t v_index_334_; uint8_t v_implicitDefEqProofs_335_; uint8_t v_zetaUnused_336_; uint8_t v_catchRuntime_337_; uint8_t v_zetaHave_338_; uint8_t v_letToHave_339_; uint8_t v_congrConsts_340_; uint8_t v_bitVecOfNat_341_; uint8_t v_warnExponents_342_; uint8_t v_suggestions_343_; lean_object* v_maxSuggestions_344_; uint8_t v_locals_345_; uint8_t v_instances_346_; lean_object* v_maxSteps_347_; lean_object* v_maxDischargeDepth_348_; uint8_t v_contextual_349_; uint8_t v_memoize_350_; uint8_t v_singlePass_351_; uint8_t v_zeta_352_; uint8_t v_beta_353_; uint8_t v_eta_354_; uint8_t v_etaStruct_355_; uint8_t v_iota_356_; uint8_t v_proj_357_; uint8_t v_decide_358_; uint8_t v_arith_359_; uint8_t v_autoUnfold_360_; uint8_t v_dsimp_361_; uint8_t v_failIfUnchanged_362_; uint8_t v_ground_363_; uint8_t v_unfoldPartialApp_364_; uint8_t v_zetaDelta_365_; uint8_t v_index_366_; uint8_t v_implicitDefEqProofs_367_; uint8_t v_zetaUnused_368_; uint8_t v_catchRuntime_369_; uint8_t v_zetaHave_370_; uint8_t v_letToHave_371_; uint8_t v_congrConsts_372_; uint8_t v_bitVecOfNat_373_; uint8_t v_warnExponents_374_; uint8_t v_suggestions_375_; lean_object* v_maxSuggestions_376_; uint8_t v_locals_377_; uint8_t v_instances_378_; uint8_t v___y_380_; uint8_t v___y_402_; uint8_t v___y_410_; uint8_t v___x_411_; 
v_maxSteps_315_ = lean_ctor_get(v_x_313_, 0);
v_maxDischargeDepth_316_ = lean_ctor_get(v_x_313_, 1);
v_contextual_317_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3);
v_memoize_318_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 1);
v_singlePass_319_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 2);
v_zeta_320_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 3);
v_beta_321_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 4);
v_eta_322_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 5);
v_etaStruct_323_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 6);
v_iota_324_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 7);
v_proj_325_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 8);
v_decide_326_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 9);
v_arith_327_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 10);
v_autoUnfold_328_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 11);
v_dsimp_329_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 12);
v_failIfUnchanged_330_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 13);
v_ground_331_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_332_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 15);
v_zetaDelta_333_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 16);
v_index_334_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_335_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 18);
v_zetaUnused_336_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 19);
v_catchRuntime_337_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 20);
v_zetaHave_338_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 21);
v_letToHave_339_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 22);
v_congrConsts_340_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 23);
v_bitVecOfNat_341_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 24);
v_warnExponents_342_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 25);
v_suggestions_343_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 26);
v_maxSuggestions_344_ = lean_ctor_get(v_x_313_, 2);
v_locals_345_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 27);
v_instances_346_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*3 + 28);
v_maxSteps_347_ = lean_ctor_get(v_x_314_, 0);
v_maxDischargeDepth_348_ = lean_ctor_get(v_x_314_, 1);
v_contextual_349_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3);
v_memoize_350_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 1);
v_singlePass_351_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 2);
v_zeta_352_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 3);
v_beta_353_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 4);
v_eta_354_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 5);
v_etaStruct_355_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 6);
v_iota_356_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 7);
v_proj_357_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 8);
v_decide_358_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 9);
v_arith_359_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 10);
v_autoUnfold_360_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 11);
v_dsimp_361_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 12);
v_failIfUnchanged_362_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 13);
v_ground_363_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_364_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 15);
v_zetaDelta_365_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 16);
v_index_366_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_367_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 18);
v_zetaUnused_368_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 19);
v_catchRuntime_369_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 20);
v_zetaHave_370_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 21);
v_letToHave_371_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 22);
v_congrConsts_372_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 23);
v_bitVecOfNat_373_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 24);
v_warnExponents_374_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 25);
v_suggestions_375_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 26);
v_maxSuggestions_376_ = lean_ctor_get(v_x_314_, 2);
v_locals_377_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 27);
v_instances_378_ = lean_ctor_get_uint8(v_x_314_, sizeof(void*)*3 + 28);
v___x_411_ = lean_nat_dec_eq(v_maxSteps_315_, v_maxSteps_347_);
if (v___x_411_ == 0)
{
return v___x_411_;
}
else
{
uint8_t v___x_412_; 
v___x_412_ = lean_nat_dec_eq(v_maxDischargeDepth_316_, v_maxDischargeDepth_348_);
if (v___x_412_ == 0)
{
return v___x_412_;
}
else
{
if (v_contextual_349_ == 0)
{
if (v_contextual_317_ == 0)
{
v___y_410_ = v___x_412_;
goto v___jp_409_;
}
else
{
return v_contextual_349_;
}
}
else
{
v___y_410_ = v_contextual_317_;
goto v___jp_409_;
}
}
}
v___jp_379_:
{
if (v___y_380_ == 0)
{
return v___y_380_;
}
else
{
if (v_instances_378_ == 0)
{
if (v_instances_346_ == 0)
{
return v___y_380_;
}
else
{
return v_instances_378_;
}
}
else
{
return v_instances_346_;
}
}
}
v___jp_381_:
{
uint8_t v___x_382_; 
v___x_382_ = l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(v_maxSuggestions_344_, v_maxSuggestions_376_);
if (v___x_382_ == 0)
{
return v___x_382_;
}
else
{
if (v_locals_377_ == 0)
{
if (v_locals_345_ == 0)
{
v___y_380_ = v___x_382_;
goto v___jp_379_;
}
else
{
return v_locals_377_;
}
}
else
{
v___y_380_ = v_locals_345_;
goto v___jp_379_;
}
}
}
v___jp_383_:
{
if (v_suggestions_375_ == 0)
{
if (v_suggestions_343_ == 0)
{
goto v___jp_381_;
}
else
{
return v_suggestions_375_;
}
}
else
{
if (v_suggestions_343_ == 0)
{
return v_suggestions_343_;
}
else
{
goto v___jp_381_;
}
}
}
v___jp_384_:
{
if (v_warnExponents_374_ == 0)
{
if (v_warnExponents_342_ == 0)
{
goto v___jp_383_;
}
else
{
return v_warnExponents_374_;
}
}
else
{
if (v_warnExponents_342_ == 0)
{
return v_warnExponents_342_;
}
else
{
goto v___jp_383_;
}
}
}
v___jp_385_:
{
if (v_bitVecOfNat_373_ == 0)
{
if (v_bitVecOfNat_341_ == 0)
{
goto v___jp_384_;
}
else
{
return v_bitVecOfNat_373_;
}
}
else
{
if (v_bitVecOfNat_341_ == 0)
{
return v_bitVecOfNat_341_;
}
else
{
goto v___jp_384_;
}
}
}
v___jp_386_:
{
if (v_congrConsts_372_ == 0)
{
if (v_congrConsts_340_ == 0)
{
goto v___jp_385_;
}
else
{
return v_congrConsts_372_;
}
}
else
{
if (v_congrConsts_340_ == 0)
{
return v_congrConsts_340_;
}
else
{
goto v___jp_385_;
}
}
}
v___jp_387_:
{
if (v_letToHave_371_ == 0)
{
if (v_letToHave_339_ == 0)
{
goto v___jp_386_;
}
else
{
return v_letToHave_371_;
}
}
else
{
if (v_letToHave_339_ == 0)
{
return v_letToHave_339_;
}
else
{
goto v___jp_386_;
}
}
}
v___jp_388_:
{
if (v_zetaHave_370_ == 0)
{
if (v_zetaHave_338_ == 0)
{
goto v___jp_387_;
}
else
{
return v_zetaHave_370_;
}
}
else
{
if (v_zetaHave_338_ == 0)
{
return v_zetaHave_338_;
}
else
{
goto v___jp_387_;
}
}
}
v___jp_389_:
{
if (v_catchRuntime_369_ == 0)
{
if (v_catchRuntime_337_ == 0)
{
goto v___jp_388_;
}
else
{
return v_catchRuntime_369_;
}
}
else
{
if (v_catchRuntime_337_ == 0)
{
return v_catchRuntime_337_;
}
else
{
goto v___jp_388_;
}
}
}
v___jp_390_:
{
if (v_zetaUnused_368_ == 0)
{
if (v_zetaUnused_336_ == 0)
{
goto v___jp_389_;
}
else
{
return v_zetaUnused_368_;
}
}
else
{
if (v_zetaUnused_336_ == 0)
{
return v_zetaUnused_336_;
}
else
{
goto v___jp_389_;
}
}
}
v___jp_391_:
{
if (v_implicitDefEqProofs_367_ == 0)
{
if (v_implicitDefEqProofs_335_ == 0)
{
goto v___jp_390_;
}
else
{
return v_implicitDefEqProofs_367_;
}
}
else
{
if (v_implicitDefEqProofs_335_ == 0)
{
return v_implicitDefEqProofs_335_;
}
else
{
goto v___jp_390_;
}
}
}
v___jp_392_:
{
if (v_index_366_ == 0)
{
if (v_index_334_ == 0)
{
goto v___jp_391_;
}
else
{
return v_index_366_;
}
}
else
{
if (v_index_334_ == 0)
{
return v_index_334_;
}
else
{
goto v___jp_391_;
}
}
}
v___jp_393_:
{
if (v_zetaDelta_365_ == 0)
{
if (v_zetaDelta_333_ == 0)
{
goto v___jp_392_;
}
else
{
return v_zetaDelta_365_;
}
}
else
{
if (v_zetaDelta_333_ == 0)
{
return v_zetaDelta_333_;
}
else
{
goto v___jp_392_;
}
}
}
v___jp_394_:
{
if (v_unfoldPartialApp_364_ == 0)
{
if (v_unfoldPartialApp_332_ == 0)
{
goto v___jp_393_;
}
else
{
return v_unfoldPartialApp_364_;
}
}
else
{
if (v_unfoldPartialApp_332_ == 0)
{
return v_unfoldPartialApp_332_;
}
else
{
goto v___jp_393_;
}
}
}
v___jp_395_:
{
if (v_ground_363_ == 0)
{
if (v_ground_331_ == 0)
{
goto v___jp_394_;
}
else
{
return v_ground_363_;
}
}
else
{
if (v_ground_331_ == 0)
{
return v_ground_331_;
}
else
{
goto v___jp_394_;
}
}
}
v___jp_396_:
{
if (v_failIfUnchanged_362_ == 0)
{
if (v_failIfUnchanged_330_ == 0)
{
goto v___jp_395_;
}
else
{
return v_failIfUnchanged_362_;
}
}
else
{
if (v_failIfUnchanged_330_ == 0)
{
return v_failIfUnchanged_330_;
}
else
{
goto v___jp_395_;
}
}
}
v___jp_397_:
{
if (v_dsimp_361_ == 0)
{
if (v_dsimp_329_ == 0)
{
goto v___jp_396_;
}
else
{
return v_dsimp_361_;
}
}
else
{
if (v_dsimp_329_ == 0)
{
return v_dsimp_329_;
}
else
{
goto v___jp_396_;
}
}
}
v___jp_398_:
{
if (v_autoUnfold_360_ == 0)
{
if (v_autoUnfold_328_ == 0)
{
goto v___jp_397_;
}
else
{
return v_autoUnfold_360_;
}
}
else
{
if (v_autoUnfold_328_ == 0)
{
return v_autoUnfold_328_;
}
else
{
goto v___jp_397_;
}
}
}
v___jp_399_:
{
if (v_arith_359_ == 0)
{
if (v_arith_327_ == 0)
{
goto v___jp_398_;
}
else
{
return v_arith_359_;
}
}
else
{
if (v_arith_327_ == 0)
{
return v_arith_327_;
}
else
{
goto v___jp_398_;
}
}
}
v___jp_400_:
{
if (v_decide_358_ == 0)
{
if (v_decide_326_ == 0)
{
goto v___jp_399_;
}
else
{
return v_decide_358_;
}
}
else
{
if (v_decide_326_ == 0)
{
return v_decide_326_;
}
else
{
goto v___jp_399_;
}
}
}
v___jp_401_:
{
if (v___y_402_ == 0)
{
return v___y_402_;
}
else
{
if (v_proj_357_ == 0)
{
if (v_proj_325_ == 0)
{
goto v___jp_400_;
}
else
{
return v_proj_357_;
}
}
else
{
if (v_proj_325_ == 0)
{
return v_proj_325_;
}
else
{
goto v___jp_400_;
}
}
}
}
v___jp_403_:
{
uint8_t v___x_404_; 
v___x_404_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_323_, v_etaStruct_355_);
if (v___x_404_ == 0)
{
return v___x_404_;
}
else
{
if (v_iota_356_ == 0)
{
if (v_iota_324_ == 0)
{
v___y_402_ = v___x_404_;
goto v___jp_401_;
}
else
{
return v_iota_356_;
}
}
else
{
v___y_402_ = v_iota_324_;
goto v___jp_401_;
}
}
}
v___jp_405_:
{
if (v_eta_354_ == 0)
{
if (v_eta_322_ == 0)
{
goto v___jp_403_;
}
else
{
return v_eta_354_;
}
}
else
{
if (v_eta_322_ == 0)
{
return v_eta_322_;
}
else
{
goto v___jp_403_;
}
}
}
v___jp_406_:
{
if (v_beta_353_ == 0)
{
if (v_beta_321_ == 0)
{
goto v___jp_405_;
}
else
{
return v_beta_353_;
}
}
else
{
if (v_beta_321_ == 0)
{
return v_beta_321_;
}
else
{
goto v___jp_405_;
}
}
}
v___jp_407_:
{
if (v_zeta_352_ == 0)
{
if (v_zeta_320_ == 0)
{
goto v___jp_406_;
}
else
{
return v_zeta_352_;
}
}
else
{
if (v_zeta_320_ == 0)
{
return v_zeta_320_;
}
else
{
goto v___jp_406_;
}
}
}
v___jp_408_:
{
if (v_singlePass_351_ == 0)
{
if (v_singlePass_319_ == 0)
{
goto v___jp_407_;
}
else
{
return v_singlePass_351_;
}
}
else
{
if (v_singlePass_319_ == 0)
{
return v_singlePass_319_;
}
else
{
goto v___jp_407_;
}
}
}
v___jp_409_:
{
if (v___y_410_ == 0)
{
return v___y_410_;
}
else
{
if (v_memoize_350_ == 0)
{
if (v_memoize_318_ == 0)
{
goto v___jp_408_;
}
else
{
return v_memoize_350_;
}
}
else
{
if (v_memoize_318_ == 0)
{
return v_memoize_318_;
}
else
{
goto v___jp_408_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_instBEqConfig_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_313_ = stack[0].m_obj;
lean_object* v_x_314_ = stack[1].m_obj;
uint8_t v_res_413_;
v_res_413_ = l_Lean_Meta_Simp_instBEqConfig_beq(v_x_313_, v_x_314_);
stack->m_num = v_res_413_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instBEqConfig_beq___boxed(lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l_Lean_Meta_Simp_instBEqConfig_beq(v_x_414_, v_x_415_);
lean_dec_ref(v_x_415_);
lean_dec_ref(v_x_414_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorIdx___impl(lean_object* v_x_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lean_obj_tag_nat(v_x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorIdx___impl___boxed(lean_object* v_x_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Meta_Occurrences_ctorIdx___impl(v_x_430_);
lean_dec(v_x_430_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim___redArg(lean_object* v_t_432_, lean_object* v_k_433_){
_start:
{
if (lean_obj_tag(v_t_432_) == 0)
{
return v_k_433_;
}
else
{
lean_object* v_idxs_434_; lean_object* v___x_435_; 
v_idxs_434_ = lean_ctor_get(v_t_432_, 0);
lean_inc(v_idxs_434_);
lean_dec(v_t_432_);
v___x_435_ = lean_apply_1(v_k_433_, v_idxs_434_);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim(lean_object* v_motive_436_, lean_object* v_ctorIdx_437_, lean_object* v_t_438_, lean_object* v_h_439_, lean_object* v_k_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_438_, v_k_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim___boxed(lean_object* v_motive_442_, lean_object* v_ctorIdx_443_, lean_object* v_t_444_, lean_object* v_h_445_, lean_object* v_k_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Meta_Occurrences_ctorElim(v_motive_442_, v_ctorIdx_443_, v_t_444_, v_h_445_, v_k_446_);
lean_dec(v_ctorIdx_443_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_all_elim___redArg(lean_object* v_t_448_, lean_object* v_all_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_448_, v_all_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_all_elim(lean_object* v_motive_451_, lean_object* v_t_452_, lean_object* v_h_453_, lean_object* v_all_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_452_, v_all_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_pos_elim___redArg(lean_object* v_t_456_, lean_object* v_pos_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_456_, v_pos_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_pos_elim(lean_object* v_motive_459_, lean_object* v_t_460_, lean_object* v_h_461_, lean_object* v_pos_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_460_, v_pos_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_neg_elim___redArg(lean_object* v_t_464_, lean_object* v_neg_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_464_, v_neg_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_neg_elim(lean_object* v_motive_467_, lean_object* v_t_468_, lean_object* v_h_469_, lean_object* v_neg_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_468_, v_neg_470_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedOccurrences_default(void){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = lean_box(0);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedOccurrences(void){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = lean_box(0);
return v___x_473_;
}
}
uint8_t l_Lean_Meta_instBEqOccurrences_beq(lean_object* v_x_474_, lean_object* v_x_475_){
_start:
{
lean_object* v_a_477_; lean_object* v_b_478_; 
switch(lean_obj_tag(v_x_474_))
{
case 0:
{
if (lean_obj_tag(v_x_475_) == 0)
{
uint8_t v___x_481_; 
v___x_481_ = 1;
return v___x_481_;
}
else
{
uint8_t v___x_482_; 
lean_dec(v_x_475_);
v___x_482_ = 0;
return v___x_482_;
}
}
case 1:
{
if (lean_obj_tag(v_x_475_) == 1)
{
lean_object* v_idxs_483_; lean_object* v_idxs_484_; 
v_idxs_483_ = lean_ctor_get(v_x_474_, 0);
lean_inc(v_idxs_483_);
lean_dec_ref_known(v_x_474_, 1);
v_idxs_484_ = lean_ctor_get(v_x_475_, 0);
lean_inc(v_idxs_484_);
lean_dec_ref_known(v_x_475_, 1);
v_a_477_ = v_idxs_483_;
v_b_478_ = v_idxs_484_;
goto v___jp_476_;
}
else
{
uint8_t v___x_485_; 
lean_dec_ref_known(v_x_474_, 1);
lean_dec(v_x_475_);
v___x_485_ = 0;
return v___x_485_;
}
}
default: 
{
if (lean_obj_tag(v_x_475_) == 2)
{
lean_object* v_idxs_486_; lean_object* v_idxs_487_; 
v_idxs_486_ = lean_ctor_get(v_x_474_, 0);
lean_inc(v_idxs_486_);
lean_dec_ref_known(v_x_474_, 1);
v_idxs_487_ = lean_ctor_get(v_x_475_, 0);
lean_inc(v_idxs_487_);
lean_dec_ref_known(v_x_475_, 1);
v_a_477_ = v_idxs_486_;
v_b_478_ = v_idxs_487_;
goto v___jp_476_;
}
else
{
uint8_t v___x_488_; 
lean_dec_ref_known(v_x_474_, 1);
lean_dec(v_x_475_);
v___x_488_ = 0;
return v___x_488_;
}
}
}
v___jp_476_:
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_480_ = l_instDecidableEqList___redArg(v___x_479_, v_a_477_, v_b_478_);
return v___x_480_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_instBEqOccurrences_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_474_ = stack[0].m_obj;
lean_object* v_x_475_ = stack[1].m_obj;
uint8_t v_res_489_;
v_res_489_ = l_Lean_Meta_instBEqOccurrences_beq(v_x_474_, v_x_475_);
stack->m_num = v_res_489_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqOccurrences_beq___boxed(lean_object* v_x_490_, lean_object* v_x_491_){
_start:
{
uint8_t v_res_492_; lean_object* v_r_493_; 
v_res_492_ = l_Lean_Meta_instBEqOccurrences_beq(v_x_490_, v_x_491_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instCoeListNatOccurrences___lam__0(lean_object* v_idxs_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_497_, 0, v_idxs_496_);
return v___x_497_;
}
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedTransparencyMode_default = _init_l_Lean_Meta_instInhabitedTransparencyMode_default();
l_Lean_Meta_instInhabitedTransparencyMode = _init_l_Lean_Meta_instInhabitedTransparencyMode();
l_Lean_Meta_instInhabitedEtaStructMode_default = _init_l_Lean_Meta_instInhabitedEtaStructMode_default();
l_Lean_Meta_instInhabitedEtaStructMode = _init_l_Lean_Meta_instInhabitedEtaStructMode();
l_Lean_Meta_Simp_defaultMaxSteps = _init_l_Lean_Meta_Simp_defaultMaxSteps();
lean_mark_persistent(l_Lean_Meta_Simp_defaultMaxSteps);
l_Lean_Meta_instInhabitedOccurrences_default = _init_l_Lean_Meta_instInhabitedOccurrences_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedOccurrences_default);
l_Lean_Meta_instInhabitedOccurrences = _init_l_Lean_Meta_instInhabitedOccurrences();
lean_mark_persistent(l_Lean_Meta_instInhabitedOccurrences);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_MetaTypes(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Core(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_MetaTypes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_MetaTypes(builtin);
}
#ifdef __cplusplus
}
#endif
