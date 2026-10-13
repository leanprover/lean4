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
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorIdx___impl(uint8_t v_x_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_box(v_x_9_);
v___x_11_ = lean_obj_tag_nat(v___x_10_);
lean_dec(v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorIdx___impl___boxed(lean_object* v_x_12_){
_start:
{
uint8_t v_x_4__boxed_13_; lean_object* v_res_14_; 
v_x_4__boxed_13_ = lean_unbox(v_x_12_);
v_res_14_ = l_Lean_Meta_TransparencyMode_ctorIdx___impl(v_x_4__boxed_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___redArg(lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___redArg___boxed(lean_object* v_k_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_Meta_TransparencyMode_ctorElim___redArg(v_k_16_);
lean_dec(v_k_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, uint8_t v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_inc(v_k_22_);
return v_k_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___boxed(lean_object* v_motive_23_, lean_object* v_ctorIdx_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
uint8_t v_t_boxed_28_; lean_object* v_res_29_; 
v_t_boxed_28_ = lean_unbox(v_t_25_);
v_res_29_ = l_Lean_Meta_TransparencyMode_ctorElim(v_motive_23_, v_ctorIdx_24_, v_t_boxed_28_, v_h_26_, v_k_27_);
lean_dec(v_k_27_);
lean_dec(v_ctorIdx_24_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___redArg(lean_object* v_all_30_){
_start:
{
lean_inc(v_all_30_);
return v_all_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___redArg___boxed(lean_object* v_all_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Meta_TransparencyMode_all_elim___redArg(v_all_31_);
lean_dec(v_all_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim(lean_object* v_motive_33_, uint8_t v_t_34_, lean_object* v_h_35_, lean_object* v_all_36_){
_start:
{
lean_inc(v_all_36_);
return v_all_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___boxed(lean_object* v_motive_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_all_40_){
_start:
{
uint8_t v_t_boxed_41_; lean_object* v_res_42_; 
v_t_boxed_41_ = lean_unbox(v_t_38_);
v_res_42_ = l_Lean_Meta_TransparencyMode_all_elim(v_motive_37_, v_t_boxed_41_, v_h_39_, v_all_40_);
lean_dec(v_all_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___redArg(lean_object* v_default_43_){
_start:
{
lean_inc(v_default_43_);
return v_default_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___redArg___boxed(lean_object* v_default_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Meta_TransparencyMode_default_elim___redArg(v_default_44_);
lean_dec(v_default_44_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim(lean_object* v_motive_46_, uint8_t v_t_47_, lean_object* v_h_48_, lean_object* v_default_49_){
_start:
{
lean_inc(v_default_49_);
return v_default_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___boxed(lean_object* v_motive_50_, lean_object* v_t_51_, lean_object* v_h_52_, lean_object* v_default_53_){
_start:
{
uint8_t v_t_boxed_54_; lean_object* v_res_55_; 
v_t_boxed_54_ = lean_unbox(v_t_51_);
v_res_55_ = l_Lean_Meta_TransparencyMode_default_elim(v_motive_50_, v_t_boxed_54_, v_h_52_, v_default_53_);
lean_dec(v_default_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim___redArg(lean_object* v_reducible_56_){
_start:
{
lean_inc(v_reducible_56_);
return v_reducible_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim___redArg___boxed(lean_object* v_reducible_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_TransparencyMode_reducible_elim___redArg(v_reducible_57_);
lean_dec(v_reducible_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim(lean_object* v_motive_59_, uint8_t v_t_60_, lean_object* v_h_61_, lean_object* v_reducible_62_){
_start:
{
lean_inc(v_reducible_62_);
return v_reducible_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim___boxed(lean_object* v_motive_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_reducible_66_){
_start:
{
uint8_t v_t_boxed_67_; lean_object* v_res_68_; 
v_t_boxed_67_ = lean_unbox(v_t_64_);
v_res_68_ = l_Lean_Meta_TransparencyMode_reducible_elim(v_motive_63_, v_t_boxed_67_, v_h_65_, v_reducible_66_);
lean_dec(v_reducible_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___redArg(lean_object* v_instances_69_){
_start:
{
lean_inc(v_instances_69_);
return v_instances_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___redArg___boxed(lean_object* v_instances_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_Meta_TransparencyMode_instances_elim___redArg(v_instances_70_);
lean_dec(v_instances_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim(lean_object* v_motive_72_, uint8_t v_t_73_, lean_object* v_h_74_, lean_object* v_instances_75_){
_start:
{
lean_inc(v_instances_75_);
return v_instances_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___boxed(lean_object* v_motive_76_, lean_object* v_t_77_, lean_object* v_h_78_, lean_object* v_instances_79_){
_start:
{
uint8_t v_t_boxed_80_; lean_object* v_res_81_; 
v_t_boxed_80_ = lean_unbox(v_t_77_);
v_res_81_ = l_Lean_Meta_TransparencyMode_instances_elim(v_motive_76_, v_t_boxed_80_, v_h_78_, v_instances_79_);
lean_dec(v_instances_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___redArg(lean_object* v_none_82_){
_start:
{
lean_inc(v_none_82_);
return v_none_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___redArg___boxed(lean_object* v_none_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Meta_TransparencyMode_none_elim___redArg(v_none_83_);
lean_dec(v_none_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim(lean_object* v_motive_85_, uint8_t v_t_86_, lean_object* v_h_87_, lean_object* v_none_88_){
_start:
{
lean_inc(v_none_88_);
return v_none_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___boxed(lean_object* v_motive_89_, lean_object* v_t_90_, lean_object* v_h_91_, lean_object* v_none_92_){
_start:
{
uint8_t v_t_boxed_93_; lean_object* v_res_94_; 
v_t_boxed_93_ = lean_unbox(v_t_90_);
v_res_94_ = l_Lean_Meta_TransparencyMode_none_elim(v_motive_89_, v_t_boxed_93_, v_h_91_, v_none_92_);
lean_dec(v_none_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim___redArg(lean_object* v_implicit_95_){
_start:
{
lean_inc(v_implicit_95_);
return v_implicit_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim___redArg___boxed(lean_object* v_implicit_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Meta_TransparencyMode_implicit_elim___redArg(v_implicit_96_);
lean_dec(v_implicit_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim(lean_object* v_motive_98_, uint8_t v_t_99_, lean_object* v_h_100_, lean_object* v_implicit_101_){
_start:
{
lean_inc(v_implicit_101_);
return v_implicit_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim___boxed(lean_object* v_motive_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_implicit_105_){
_start:
{
uint8_t v_t_boxed_106_; lean_object* v_res_107_; 
v_t_boxed_106_ = lean_unbox(v_t_103_);
v_res_107_ = l_Lean_Meta_TransparencyMode_implicit_elim(v_motive_102_, v_t_boxed_106_, v_h_104_, v_implicit_105_);
lean_dec(v_implicit_105_);
return v_res_107_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedTransparencyMode_default(void){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = 0;
return v___x_108_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedTransparencyMode(void){
_start:
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t v_x_110_, uint8_t v_y_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_112_ = lean_box(v_x_110_);
v___x_113_ = lean_obj_tag_nat(v___x_112_);
lean_dec(v___x_112_);
v___x_114_ = lean_box(v_y_111_);
v___x_115_ = lean_obj_tag_nat(v___x_114_);
lean_dec(v___x_114_);
v___x_116_ = lean_nat_dec_eq(v___x_113_, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqTransparencyMode_beq___boxed(lean_object* v_x_117_, lean_object* v_y_118_){
_start:
{
uint8_t v_x_24__boxed_119_; uint8_t v_y_25__boxed_120_; uint8_t v_res_121_; lean_object* v_r_122_; 
v_x_24__boxed_119_ = lean_unbox(v_x_117_);
v_y_25__boxed_120_ = lean_unbox(v_y_118_);
v_res_121_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_x_24__boxed_119_, v_y_25__boxed_120_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorIdx___impl(uint8_t v_x_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_box(v_x_125_);
v___x_127_ = lean_obj_tag_nat(v___x_126_);
lean_dec(v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorIdx___impl___boxed(lean_object* v_x_128_){
_start:
{
uint8_t v_x_4__boxed_129_; lean_object* v_res_130_; 
v_x_4__boxed_129_ = lean_unbox(v_x_128_);
v_res_130_ = l_Lean_Meta_EtaStructMode_ctorIdx___impl(v_x_4__boxed_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___redArg(lean_object* v_k_131_){
_start:
{
lean_inc(v_k_131_);
return v_k_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___redArg___boxed(lean_object* v_k_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Meta_EtaStructMode_ctorElim___redArg(v_k_132_);
lean_dec(v_k_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim(lean_object* v_motive_134_, lean_object* v_ctorIdx_135_, uint8_t v_t_136_, lean_object* v_h_137_, lean_object* v_k_138_){
_start:
{
lean_inc(v_k_138_);
return v_k_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___boxed(lean_object* v_motive_139_, lean_object* v_ctorIdx_140_, lean_object* v_t_141_, lean_object* v_h_142_, lean_object* v_k_143_){
_start:
{
uint8_t v_t_boxed_144_; lean_object* v_res_145_; 
v_t_boxed_144_ = lean_unbox(v_t_141_);
v_res_145_ = l_Lean_Meta_EtaStructMode_ctorElim(v_motive_139_, v_ctorIdx_140_, v_t_boxed_144_, v_h_142_, v_k_143_);
lean_dec(v_k_143_);
lean_dec(v_ctorIdx_140_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___redArg(lean_object* v_all_146_){
_start:
{
lean_inc(v_all_146_);
return v_all_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___redArg___boxed(lean_object* v_all_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Meta_EtaStructMode_all_elim___redArg(v_all_147_);
lean_dec(v_all_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim(lean_object* v_motive_149_, uint8_t v_t_150_, lean_object* v_h_151_, lean_object* v_all_152_){
_start:
{
lean_inc(v_all_152_);
return v_all_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___boxed(lean_object* v_motive_153_, lean_object* v_t_154_, lean_object* v_h_155_, lean_object* v_all_156_){
_start:
{
uint8_t v_t_boxed_157_; lean_object* v_res_158_; 
v_t_boxed_157_ = lean_unbox(v_t_154_);
v_res_158_ = l_Lean_Meta_EtaStructMode_all_elim(v_motive_153_, v_t_boxed_157_, v_h_155_, v_all_156_);
lean_dec(v_all_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___redArg(lean_object* v_notClasses_159_){
_start:
{
lean_inc(v_notClasses_159_);
return v_notClasses_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___redArg___boxed(lean_object* v_notClasses_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Meta_EtaStructMode_notClasses_elim___redArg(v_notClasses_160_);
lean_dec(v_notClasses_160_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim(lean_object* v_motive_162_, uint8_t v_t_163_, lean_object* v_h_164_, lean_object* v_notClasses_165_){
_start:
{
lean_inc(v_notClasses_165_);
return v_notClasses_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___boxed(lean_object* v_motive_166_, lean_object* v_t_167_, lean_object* v_h_168_, lean_object* v_notClasses_169_){
_start:
{
uint8_t v_t_boxed_170_; lean_object* v_res_171_; 
v_t_boxed_170_ = lean_unbox(v_t_167_);
v_res_171_ = l_Lean_Meta_EtaStructMode_notClasses_elim(v_motive_166_, v_t_boxed_170_, v_h_168_, v_notClasses_169_);
lean_dec(v_notClasses_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___redArg(lean_object* v_none_172_){
_start:
{
lean_inc(v_none_172_);
return v_none_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___redArg___boxed(lean_object* v_none_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Meta_EtaStructMode_none_elim___redArg(v_none_173_);
lean_dec(v_none_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim(lean_object* v_motive_175_, uint8_t v_t_176_, lean_object* v_h_177_, lean_object* v_none_178_){
_start:
{
lean_inc(v_none_178_);
return v_none_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___boxed(lean_object* v_motive_179_, lean_object* v_t_180_, lean_object* v_h_181_, lean_object* v_none_182_){
_start:
{
uint8_t v_t_boxed_183_; lean_object* v_res_184_; 
v_t_boxed_183_ = lean_unbox(v_t_180_);
v_res_184_ = l_Lean_Meta_EtaStructMode_none_elim(v_motive_179_, v_t_boxed_183_, v_h_181_, v_none_182_);
lean_dec(v_none_182_);
return v_res_184_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedEtaStructMode_default(void){
_start:
{
uint8_t v___x_185_; 
v___x_185_ = 0;
return v___x_185_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedEtaStructMode(void){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = 0;
return v___x_186_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqEtaStructMode_beq(uint8_t v_x_187_, uint8_t v_y_188_){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_189_ = lean_box(v_x_187_);
v___x_190_ = lean_obj_tag_nat(v___x_189_);
lean_dec(v___x_189_);
v___x_191_ = lean_box(v_y_188_);
v___x_192_ = lean_obj_tag_nat(v___x_191_);
lean_dec(v___x_191_);
v___x_193_ = lean_nat_dec_eq(v___x_190_, v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqEtaStructMode_beq___boxed(lean_object* v_x_194_, lean_object* v_y_195_){
_start:
{
uint8_t v_x_24__boxed_196_; uint8_t v_y_25__boxed_197_; uint8_t v_res_198_; lean_object* v_r_199_; 
v_x_24__boxed_196_ = lean_unbox(v_x_194_);
v_y_25__boxed_197_ = lean_unbox(v_y_195_);
v_res_198_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_x_24__boxed_196_, v_y_25__boxed_197_);
v_r_199_ = lean_box(v_res_198_);
return v_r_199_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DSimp_instBEqConfig_beq(lean_object* v_x_208_, lean_object* v_x_209_){
_start:
{
uint8_t v_zeta_210_; uint8_t v_beta_211_; uint8_t v_eta_212_; uint8_t v_etaStruct_213_; uint8_t v_iota_214_; uint8_t v_proj_215_; uint8_t v_decide_216_; uint8_t v_autoUnfold_217_; uint8_t v_failIfUnchanged_218_; uint8_t v_unfoldPartialApp_219_; uint8_t v_zetaDelta_220_; uint8_t v_index_221_; uint8_t v_zetaUnused_222_; uint8_t v_zetaHave_223_; uint8_t v_locals_224_; uint8_t v_instances_225_; uint8_t v_zeta_226_; uint8_t v_beta_227_; uint8_t v_eta_228_; uint8_t v_etaStruct_229_; uint8_t v_iota_230_; uint8_t v_proj_231_; uint8_t v_decide_232_; uint8_t v_autoUnfold_233_; uint8_t v_failIfUnchanged_234_; uint8_t v_unfoldPartialApp_235_; uint8_t v_zetaDelta_236_; uint8_t v_index_237_; uint8_t v_zetaUnused_238_; uint8_t v_zetaHave_239_; uint8_t v_locals_240_; uint8_t v_instances_241_; uint8_t v___y_243_; uint8_t v___y_245_; uint8_t v___y_247_; uint8_t v___y_249_; uint8_t v___y_251_; uint8_t v___y_253_; uint8_t v___y_255_; uint8_t v___y_257_; uint8_t v___y_259_; uint8_t v___y_261_; uint8_t v___y_263_; 
v_zeta_210_ = lean_ctor_get_uint8(v_x_208_, 0);
v_beta_211_ = lean_ctor_get_uint8(v_x_208_, 1);
v_eta_212_ = lean_ctor_get_uint8(v_x_208_, 2);
v_etaStruct_213_ = lean_ctor_get_uint8(v_x_208_, 3);
v_iota_214_ = lean_ctor_get_uint8(v_x_208_, 4);
v_proj_215_ = lean_ctor_get_uint8(v_x_208_, 5);
v_decide_216_ = lean_ctor_get_uint8(v_x_208_, 6);
v_autoUnfold_217_ = lean_ctor_get_uint8(v_x_208_, 7);
v_failIfUnchanged_218_ = lean_ctor_get_uint8(v_x_208_, 8);
v_unfoldPartialApp_219_ = lean_ctor_get_uint8(v_x_208_, 9);
v_zetaDelta_220_ = lean_ctor_get_uint8(v_x_208_, 10);
v_index_221_ = lean_ctor_get_uint8(v_x_208_, 11);
v_zetaUnused_222_ = lean_ctor_get_uint8(v_x_208_, 12);
v_zetaHave_223_ = lean_ctor_get_uint8(v_x_208_, 13);
v_locals_224_ = lean_ctor_get_uint8(v_x_208_, 14);
v_instances_225_ = lean_ctor_get_uint8(v_x_208_, 15);
v_zeta_226_ = lean_ctor_get_uint8(v_x_209_, 0);
v_beta_227_ = lean_ctor_get_uint8(v_x_209_, 1);
v_eta_228_ = lean_ctor_get_uint8(v_x_209_, 2);
v_etaStruct_229_ = lean_ctor_get_uint8(v_x_209_, 3);
v_iota_230_ = lean_ctor_get_uint8(v_x_209_, 4);
v_proj_231_ = lean_ctor_get_uint8(v_x_209_, 5);
v_decide_232_ = lean_ctor_get_uint8(v_x_209_, 6);
v_autoUnfold_233_ = lean_ctor_get_uint8(v_x_209_, 7);
v_failIfUnchanged_234_ = lean_ctor_get_uint8(v_x_209_, 8);
v_unfoldPartialApp_235_ = lean_ctor_get_uint8(v_x_209_, 9);
v_zetaDelta_236_ = lean_ctor_get_uint8(v_x_209_, 10);
v_index_237_ = lean_ctor_get_uint8(v_x_209_, 11);
v_zetaUnused_238_ = lean_ctor_get_uint8(v_x_209_, 12);
v_zetaHave_239_ = lean_ctor_get_uint8(v_x_209_, 13);
v_locals_240_ = lean_ctor_get_uint8(v_x_209_, 14);
v_instances_241_ = lean_ctor_get_uint8(v_x_209_, 15);
if (v_zeta_226_ == 0)
{
if (v_zeta_210_ == 0)
{
goto v___jp_267_;
}
else
{
return v_zeta_226_;
}
}
else
{
if (v_zeta_210_ == 0)
{
return v_zeta_210_;
}
else
{
goto v___jp_267_;
}
}
v___jp_242_:
{
if (v_instances_241_ == 0)
{
if (v_instances_225_ == 0)
{
return v___y_243_;
}
else
{
return v_instances_241_;
}
}
else
{
return v_instances_225_;
}
}
v___jp_244_:
{
if (v_locals_240_ == 0)
{
if (v_locals_224_ == 0)
{
v___y_243_ = v___y_245_;
goto v___jp_242_;
}
else
{
return v_locals_240_;
}
}
else
{
if (v_locals_224_ == 0)
{
return v_locals_224_;
}
else
{
v___y_243_ = v_locals_224_;
goto v___jp_242_;
}
}
}
v___jp_246_:
{
if (v_zetaHave_239_ == 0)
{
if (v_zetaHave_223_ == 0)
{
v___y_245_ = v___y_247_;
goto v___jp_244_;
}
else
{
return v_zetaHave_239_;
}
}
else
{
if (v_zetaHave_223_ == 0)
{
return v_zetaHave_223_;
}
else
{
v___y_245_ = v_zetaHave_223_;
goto v___jp_244_;
}
}
}
v___jp_248_:
{
if (v_zetaUnused_238_ == 0)
{
if (v_zetaUnused_222_ == 0)
{
v___y_247_ = v___y_249_;
goto v___jp_246_;
}
else
{
return v_zetaUnused_238_;
}
}
else
{
if (v_zetaUnused_222_ == 0)
{
return v_zetaUnused_222_;
}
else
{
v___y_247_ = v_zetaUnused_222_;
goto v___jp_246_;
}
}
}
v___jp_250_:
{
if (v_index_237_ == 0)
{
if (v_index_221_ == 0)
{
v___y_249_ = v___y_251_;
goto v___jp_248_;
}
else
{
return v_index_237_;
}
}
else
{
if (v_index_221_ == 0)
{
return v_index_221_;
}
else
{
v___y_249_ = v_index_221_;
goto v___jp_248_;
}
}
}
v___jp_252_:
{
if (v_zetaDelta_236_ == 0)
{
if (v_zetaDelta_220_ == 0)
{
v___y_251_ = v___y_253_;
goto v___jp_250_;
}
else
{
return v_zetaDelta_236_;
}
}
else
{
if (v_zetaDelta_220_ == 0)
{
return v_zetaDelta_220_;
}
else
{
v___y_251_ = v_zetaDelta_220_;
goto v___jp_250_;
}
}
}
v___jp_254_:
{
if (v_unfoldPartialApp_235_ == 0)
{
if (v_unfoldPartialApp_219_ == 0)
{
v___y_253_ = v___y_255_;
goto v___jp_252_;
}
else
{
return v_unfoldPartialApp_235_;
}
}
else
{
if (v_unfoldPartialApp_219_ == 0)
{
return v_unfoldPartialApp_219_;
}
else
{
v___y_253_ = v_unfoldPartialApp_219_;
goto v___jp_252_;
}
}
}
v___jp_256_:
{
if (v_failIfUnchanged_234_ == 0)
{
if (v_failIfUnchanged_218_ == 0)
{
v___y_255_ = v___y_257_;
goto v___jp_254_;
}
else
{
return v_failIfUnchanged_234_;
}
}
else
{
if (v_failIfUnchanged_218_ == 0)
{
return v_failIfUnchanged_218_;
}
else
{
v___y_255_ = v_failIfUnchanged_218_;
goto v___jp_254_;
}
}
}
v___jp_258_:
{
if (v_autoUnfold_233_ == 0)
{
if (v_autoUnfold_217_ == 0)
{
v___y_257_ = v___y_259_;
goto v___jp_256_;
}
else
{
return v_autoUnfold_233_;
}
}
else
{
if (v_autoUnfold_217_ == 0)
{
return v_autoUnfold_217_;
}
else
{
v___y_257_ = v_autoUnfold_217_;
goto v___jp_256_;
}
}
}
v___jp_260_:
{
if (v_decide_232_ == 0)
{
if (v_decide_216_ == 0)
{
v___y_259_ = v___y_261_;
goto v___jp_258_;
}
else
{
return v_decide_232_;
}
}
else
{
if (v_decide_216_ == 0)
{
return v_decide_216_;
}
else
{
v___y_259_ = v_decide_216_;
goto v___jp_258_;
}
}
}
v___jp_262_:
{
if (v___y_263_ == 0)
{
return v___y_263_;
}
else
{
if (v_proj_231_ == 0)
{
if (v_proj_215_ == 0)
{
v___y_261_ = v___y_263_;
goto v___jp_260_;
}
else
{
return v_proj_231_;
}
}
else
{
if (v_proj_215_ == 0)
{
return v_proj_215_;
}
else
{
v___y_261_ = v_proj_215_;
goto v___jp_260_;
}
}
}
}
v___jp_264_:
{
uint8_t v___x_265_; 
v___x_265_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_213_, v_etaStruct_229_);
if (v___x_265_ == 0)
{
return v___x_265_;
}
else
{
if (v_iota_230_ == 0)
{
if (v_iota_214_ == 0)
{
v___y_263_ = v___x_265_;
goto v___jp_262_;
}
else
{
return v_iota_230_;
}
}
else
{
v___y_263_ = v_iota_214_;
goto v___jp_262_;
}
}
}
v___jp_266_:
{
if (v_eta_228_ == 0)
{
if (v_eta_212_ == 0)
{
goto v___jp_264_;
}
else
{
return v_eta_228_;
}
}
else
{
if (v_eta_212_ == 0)
{
return v_eta_212_;
}
else
{
goto v___jp_264_;
}
}
}
v___jp_267_:
{
if (v_beta_227_ == 0)
{
if (v_beta_211_ == 0)
{
goto v___jp_266_;
}
else
{
return v_beta_227_;
}
}
else
{
if (v_beta_211_ == 0)
{
return v_beta_211_;
}
else
{
goto v___jp_266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DSimp_instBEqConfig_beq___boxed(lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
uint8_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_Lean_Meta_DSimp_instBEqConfig_beq(v_x_268_, v_x_269_);
lean_dec_ref(v_x_269_);
lean_dec_ref(v_x_268_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_defaultMaxSteps(void){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_unsigned_to_nat(100000u);
return v___x_274_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(lean_object* v_x_284_, lean_object* v_x_285_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
if (lean_obj_tag(v_x_285_) == 0)
{
uint8_t v___x_286_; 
v___x_286_ = 1;
return v___x_286_;
}
else
{
uint8_t v___x_287_; 
v___x_287_ = 0;
return v___x_287_;
}
}
else
{
if (lean_obj_tag(v_x_285_) == 0)
{
uint8_t v___x_288_; 
v___x_288_ = 0;
return v___x_288_;
}
else
{
lean_object* v_val_289_; lean_object* v_val_290_; uint8_t v___x_291_; 
v_val_289_ = lean_ctor_get(v_x_284_, 0);
v_val_290_ = lean_ctor_get(v_x_285_, 0);
v___x_291_ = lean_nat_dec_eq(v_val_289_, v_val_290_);
return v___x_291_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0___boxed(lean_object* v_x_292_, lean_object* v_x_293_){
_start:
{
uint8_t v_res_294_; lean_object* v_r_295_; 
v_res_294_ = l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(v_x_292_, v_x_293_);
lean_dec(v_x_293_);
lean_dec(v_x_292_);
v_r_295_ = lean_box(v_res_294_);
return v_r_295_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_instBEqConfig_beq(lean_object* v_x_296_, lean_object* v_x_297_){
_start:
{
lean_object* v_maxSteps_298_; lean_object* v_maxDischargeDepth_299_; uint8_t v_contextual_300_; uint8_t v_memoize_301_; uint8_t v_singlePass_302_; uint8_t v_zeta_303_; uint8_t v_beta_304_; uint8_t v_eta_305_; uint8_t v_etaStruct_306_; uint8_t v_iota_307_; uint8_t v_proj_308_; uint8_t v_decide_309_; uint8_t v_arith_310_; uint8_t v_autoUnfold_311_; uint8_t v_dsimp_312_; uint8_t v_failIfUnchanged_313_; uint8_t v_ground_314_; uint8_t v_unfoldPartialApp_315_; uint8_t v_zetaDelta_316_; uint8_t v_index_317_; uint8_t v_implicitDefEqProofs_318_; uint8_t v_zetaUnused_319_; uint8_t v_catchRuntime_320_; uint8_t v_zetaHave_321_; uint8_t v_letToHave_322_; uint8_t v_congrConsts_323_; uint8_t v_bitVecOfNat_324_; uint8_t v_warnExponents_325_; uint8_t v_suggestions_326_; lean_object* v_maxSuggestions_327_; uint8_t v_locals_328_; uint8_t v_instances_329_; lean_object* v_maxSteps_330_; lean_object* v_maxDischargeDepth_331_; uint8_t v_contextual_332_; uint8_t v_memoize_333_; uint8_t v_singlePass_334_; uint8_t v_zeta_335_; uint8_t v_beta_336_; uint8_t v_eta_337_; uint8_t v_etaStruct_338_; uint8_t v_iota_339_; uint8_t v_proj_340_; uint8_t v_decide_341_; uint8_t v_arith_342_; uint8_t v_autoUnfold_343_; uint8_t v_dsimp_344_; uint8_t v_failIfUnchanged_345_; uint8_t v_ground_346_; uint8_t v_unfoldPartialApp_347_; uint8_t v_zetaDelta_348_; uint8_t v_index_349_; uint8_t v_implicitDefEqProofs_350_; uint8_t v_zetaUnused_351_; uint8_t v_catchRuntime_352_; uint8_t v_zetaHave_353_; uint8_t v_letToHave_354_; uint8_t v_congrConsts_355_; uint8_t v_bitVecOfNat_356_; uint8_t v_warnExponents_357_; uint8_t v_suggestions_358_; lean_object* v_maxSuggestions_359_; uint8_t v_locals_360_; uint8_t v_instances_361_; uint8_t v___y_363_; uint8_t v___y_385_; uint8_t v___y_393_; uint8_t v___x_394_; 
v_maxSteps_298_ = lean_ctor_get(v_x_296_, 0);
v_maxDischargeDepth_299_ = lean_ctor_get(v_x_296_, 1);
v_contextual_300_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3);
v_memoize_301_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 1);
v_singlePass_302_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 2);
v_zeta_303_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 3);
v_beta_304_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 4);
v_eta_305_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 5);
v_etaStruct_306_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 6);
v_iota_307_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 7);
v_proj_308_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 8);
v_decide_309_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 9);
v_arith_310_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 10);
v_autoUnfold_311_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 11);
v_dsimp_312_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 12);
v_failIfUnchanged_313_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 13);
v_ground_314_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_315_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 15);
v_zetaDelta_316_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 16);
v_index_317_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_318_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 18);
v_zetaUnused_319_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 19);
v_catchRuntime_320_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 20);
v_zetaHave_321_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 21);
v_letToHave_322_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 22);
v_congrConsts_323_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 23);
v_bitVecOfNat_324_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 24);
v_warnExponents_325_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 25);
v_suggestions_326_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 26);
v_maxSuggestions_327_ = lean_ctor_get(v_x_296_, 2);
v_locals_328_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 27);
v_instances_329_ = lean_ctor_get_uint8(v_x_296_, sizeof(void*)*3 + 28);
v_maxSteps_330_ = lean_ctor_get(v_x_297_, 0);
v_maxDischargeDepth_331_ = lean_ctor_get(v_x_297_, 1);
v_contextual_332_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3);
v_memoize_333_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 1);
v_singlePass_334_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 2);
v_zeta_335_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 3);
v_beta_336_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 4);
v_eta_337_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 5);
v_etaStruct_338_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 6);
v_iota_339_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 7);
v_proj_340_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 8);
v_decide_341_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 9);
v_arith_342_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 10);
v_autoUnfold_343_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 11);
v_dsimp_344_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 12);
v_failIfUnchanged_345_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 13);
v_ground_346_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_347_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 15);
v_zetaDelta_348_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 16);
v_index_349_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_350_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 18);
v_zetaUnused_351_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 19);
v_catchRuntime_352_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 20);
v_zetaHave_353_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 21);
v_letToHave_354_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 22);
v_congrConsts_355_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 23);
v_bitVecOfNat_356_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 24);
v_warnExponents_357_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 25);
v_suggestions_358_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 26);
v_maxSuggestions_359_ = lean_ctor_get(v_x_297_, 2);
v_locals_360_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 27);
v_instances_361_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 28);
v___x_394_ = lean_nat_dec_eq(v_maxSteps_298_, v_maxSteps_330_);
if (v___x_394_ == 0)
{
return v___x_394_;
}
else
{
uint8_t v___x_395_; 
v___x_395_ = lean_nat_dec_eq(v_maxDischargeDepth_299_, v_maxDischargeDepth_331_);
if (v___x_395_ == 0)
{
return v___x_395_;
}
else
{
if (v_contextual_332_ == 0)
{
if (v_contextual_300_ == 0)
{
v___y_393_ = v___x_395_;
goto v___jp_392_;
}
else
{
return v_contextual_332_;
}
}
else
{
v___y_393_ = v_contextual_300_;
goto v___jp_392_;
}
}
}
v___jp_362_:
{
if (v___y_363_ == 0)
{
return v___y_363_;
}
else
{
if (v_instances_361_ == 0)
{
if (v_instances_329_ == 0)
{
return v___y_363_;
}
else
{
return v_instances_361_;
}
}
else
{
return v_instances_329_;
}
}
}
v___jp_364_:
{
uint8_t v___x_365_; 
v___x_365_ = l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(v_maxSuggestions_327_, v_maxSuggestions_359_);
if (v___x_365_ == 0)
{
return v___x_365_;
}
else
{
if (v_locals_360_ == 0)
{
if (v_locals_328_ == 0)
{
v___y_363_ = v___x_365_;
goto v___jp_362_;
}
else
{
return v_locals_360_;
}
}
else
{
v___y_363_ = v_locals_328_;
goto v___jp_362_;
}
}
}
v___jp_366_:
{
if (v_suggestions_358_ == 0)
{
if (v_suggestions_326_ == 0)
{
goto v___jp_364_;
}
else
{
return v_suggestions_358_;
}
}
else
{
if (v_suggestions_326_ == 0)
{
return v_suggestions_326_;
}
else
{
goto v___jp_364_;
}
}
}
v___jp_367_:
{
if (v_warnExponents_357_ == 0)
{
if (v_warnExponents_325_ == 0)
{
goto v___jp_366_;
}
else
{
return v_warnExponents_357_;
}
}
else
{
if (v_warnExponents_325_ == 0)
{
return v_warnExponents_325_;
}
else
{
goto v___jp_366_;
}
}
}
v___jp_368_:
{
if (v_bitVecOfNat_356_ == 0)
{
if (v_bitVecOfNat_324_ == 0)
{
goto v___jp_367_;
}
else
{
return v_bitVecOfNat_356_;
}
}
else
{
if (v_bitVecOfNat_324_ == 0)
{
return v_bitVecOfNat_324_;
}
else
{
goto v___jp_367_;
}
}
}
v___jp_369_:
{
if (v_congrConsts_355_ == 0)
{
if (v_congrConsts_323_ == 0)
{
goto v___jp_368_;
}
else
{
return v_congrConsts_355_;
}
}
else
{
if (v_congrConsts_323_ == 0)
{
return v_congrConsts_323_;
}
else
{
goto v___jp_368_;
}
}
}
v___jp_370_:
{
if (v_letToHave_354_ == 0)
{
if (v_letToHave_322_ == 0)
{
goto v___jp_369_;
}
else
{
return v_letToHave_354_;
}
}
else
{
if (v_letToHave_322_ == 0)
{
return v_letToHave_322_;
}
else
{
goto v___jp_369_;
}
}
}
v___jp_371_:
{
if (v_zetaHave_353_ == 0)
{
if (v_zetaHave_321_ == 0)
{
goto v___jp_370_;
}
else
{
return v_zetaHave_353_;
}
}
else
{
if (v_zetaHave_321_ == 0)
{
return v_zetaHave_321_;
}
else
{
goto v___jp_370_;
}
}
}
v___jp_372_:
{
if (v_catchRuntime_352_ == 0)
{
if (v_catchRuntime_320_ == 0)
{
goto v___jp_371_;
}
else
{
return v_catchRuntime_352_;
}
}
else
{
if (v_catchRuntime_320_ == 0)
{
return v_catchRuntime_320_;
}
else
{
goto v___jp_371_;
}
}
}
v___jp_373_:
{
if (v_zetaUnused_351_ == 0)
{
if (v_zetaUnused_319_ == 0)
{
goto v___jp_372_;
}
else
{
return v_zetaUnused_351_;
}
}
else
{
if (v_zetaUnused_319_ == 0)
{
return v_zetaUnused_319_;
}
else
{
goto v___jp_372_;
}
}
}
v___jp_374_:
{
if (v_implicitDefEqProofs_350_ == 0)
{
if (v_implicitDefEqProofs_318_ == 0)
{
goto v___jp_373_;
}
else
{
return v_implicitDefEqProofs_350_;
}
}
else
{
if (v_implicitDefEqProofs_318_ == 0)
{
return v_implicitDefEqProofs_318_;
}
else
{
goto v___jp_373_;
}
}
}
v___jp_375_:
{
if (v_index_349_ == 0)
{
if (v_index_317_ == 0)
{
goto v___jp_374_;
}
else
{
return v_index_349_;
}
}
else
{
if (v_index_317_ == 0)
{
return v_index_317_;
}
else
{
goto v___jp_374_;
}
}
}
v___jp_376_:
{
if (v_zetaDelta_348_ == 0)
{
if (v_zetaDelta_316_ == 0)
{
goto v___jp_375_;
}
else
{
return v_zetaDelta_348_;
}
}
else
{
if (v_zetaDelta_316_ == 0)
{
return v_zetaDelta_316_;
}
else
{
goto v___jp_375_;
}
}
}
v___jp_377_:
{
if (v_unfoldPartialApp_347_ == 0)
{
if (v_unfoldPartialApp_315_ == 0)
{
goto v___jp_376_;
}
else
{
return v_unfoldPartialApp_347_;
}
}
else
{
if (v_unfoldPartialApp_315_ == 0)
{
return v_unfoldPartialApp_315_;
}
else
{
goto v___jp_376_;
}
}
}
v___jp_378_:
{
if (v_ground_346_ == 0)
{
if (v_ground_314_ == 0)
{
goto v___jp_377_;
}
else
{
return v_ground_346_;
}
}
else
{
if (v_ground_314_ == 0)
{
return v_ground_314_;
}
else
{
goto v___jp_377_;
}
}
}
v___jp_379_:
{
if (v_failIfUnchanged_345_ == 0)
{
if (v_failIfUnchanged_313_ == 0)
{
goto v___jp_378_;
}
else
{
return v_failIfUnchanged_345_;
}
}
else
{
if (v_failIfUnchanged_313_ == 0)
{
return v_failIfUnchanged_313_;
}
else
{
goto v___jp_378_;
}
}
}
v___jp_380_:
{
if (v_dsimp_344_ == 0)
{
if (v_dsimp_312_ == 0)
{
goto v___jp_379_;
}
else
{
return v_dsimp_344_;
}
}
else
{
if (v_dsimp_312_ == 0)
{
return v_dsimp_312_;
}
else
{
goto v___jp_379_;
}
}
}
v___jp_381_:
{
if (v_autoUnfold_343_ == 0)
{
if (v_autoUnfold_311_ == 0)
{
goto v___jp_380_;
}
else
{
return v_autoUnfold_343_;
}
}
else
{
if (v_autoUnfold_311_ == 0)
{
return v_autoUnfold_311_;
}
else
{
goto v___jp_380_;
}
}
}
v___jp_382_:
{
if (v_arith_342_ == 0)
{
if (v_arith_310_ == 0)
{
goto v___jp_381_;
}
else
{
return v_arith_342_;
}
}
else
{
if (v_arith_310_ == 0)
{
return v_arith_310_;
}
else
{
goto v___jp_381_;
}
}
}
v___jp_383_:
{
if (v_decide_341_ == 0)
{
if (v_decide_309_ == 0)
{
goto v___jp_382_;
}
else
{
return v_decide_341_;
}
}
else
{
if (v_decide_309_ == 0)
{
return v_decide_309_;
}
else
{
goto v___jp_382_;
}
}
}
v___jp_384_:
{
if (v___y_385_ == 0)
{
return v___y_385_;
}
else
{
if (v_proj_340_ == 0)
{
if (v_proj_308_ == 0)
{
goto v___jp_383_;
}
else
{
return v_proj_340_;
}
}
else
{
if (v_proj_308_ == 0)
{
return v_proj_308_;
}
else
{
goto v___jp_383_;
}
}
}
}
v___jp_386_:
{
uint8_t v___x_387_; 
v___x_387_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_306_, v_etaStruct_338_);
if (v___x_387_ == 0)
{
return v___x_387_;
}
else
{
if (v_iota_339_ == 0)
{
if (v_iota_307_ == 0)
{
v___y_385_ = v___x_387_;
goto v___jp_384_;
}
else
{
return v_iota_339_;
}
}
else
{
v___y_385_ = v_iota_307_;
goto v___jp_384_;
}
}
}
v___jp_388_:
{
if (v_eta_337_ == 0)
{
if (v_eta_305_ == 0)
{
goto v___jp_386_;
}
else
{
return v_eta_337_;
}
}
else
{
if (v_eta_305_ == 0)
{
return v_eta_305_;
}
else
{
goto v___jp_386_;
}
}
}
v___jp_389_:
{
if (v_beta_336_ == 0)
{
if (v_beta_304_ == 0)
{
goto v___jp_388_;
}
else
{
return v_beta_336_;
}
}
else
{
if (v_beta_304_ == 0)
{
return v_beta_304_;
}
else
{
goto v___jp_388_;
}
}
}
v___jp_390_:
{
if (v_zeta_335_ == 0)
{
if (v_zeta_303_ == 0)
{
goto v___jp_389_;
}
else
{
return v_zeta_335_;
}
}
else
{
if (v_zeta_303_ == 0)
{
return v_zeta_303_;
}
else
{
goto v___jp_389_;
}
}
}
v___jp_391_:
{
if (v_singlePass_334_ == 0)
{
if (v_singlePass_302_ == 0)
{
goto v___jp_390_;
}
else
{
return v_singlePass_334_;
}
}
else
{
if (v_singlePass_302_ == 0)
{
return v_singlePass_302_;
}
else
{
goto v___jp_390_;
}
}
}
v___jp_392_:
{
if (v___y_393_ == 0)
{
return v___y_393_;
}
else
{
if (v_memoize_333_ == 0)
{
if (v_memoize_301_ == 0)
{
goto v___jp_391_;
}
else
{
return v_memoize_333_;
}
}
else
{
if (v_memoize_301_ == 0)
{
return v_memoize_301_;
}
else
{
goto v___jp_391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instBEqConfig_beq___boxed(lean_object* v_x_396_, lean_object* v_x_397_){
_start:
{
uint8_t v_res_398_; lean_object* v_r_399_; 
v_res_398_ = l_Lean_Meta_Simp_instBEqConfig_beq(v_x_396_, v_x_397_);
lean_dec_ref(v_x_397_);
lean_dec_ref(v_x_396_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorIdx___impl(lean_object* v_x_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = lean_obj_tag_nat(v_x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorIdx___impl___boxed(lean_object* v_x_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Meta_Occurrences_ctorIdx___impl(v_x_412_);
lean_dec(v_x_412_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim___redArg(lean_object* v_t_414_, lean_object* v_k_415_){
_start:
{
if (lean_obj_tag(v_t_414_) == 0)
{
return v_k_415_;
}
else
{
lean_object* v_idxs_416_; lean_object* v___x_417_; 
v_idxs_416_ = lean_ctor_get(v_t_414_, 0);
lean_inc(v_idxs_416_);
lean_dec(v_t_414_);
v___x_417_ = lean_apply_1(v_k_415_, v_idxs_416_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim(lean_object* v_motive_418_, lean_object* v_ctorIdx_419_, lean_object* v_t_420_, lean_object* v_h_421_, lean_object* v_k_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_420_, v_k_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim___boxed(lean_object* v_motive_424_, lean_object* v_ctorIdx_425_, lean_object* v_t_426_, lean_object* v_h_427_, lean_object* v_k_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Meta_Occurrences_ctorElim(v_motive_424_, v_ctorIdx_425_, v_t_426_, v_h_427_, v_k_428_);
lean_dec(v_ctorIdx_425_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_all_elim___redArg(lean_object* v_t_430_, lean_object* v_all_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_430_, v_all_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_all_elim(lean_object* v_motive_433_, lean_object* v_t_434_, lean_object* v_h_435_, lean_object* v_all_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_434_, v_all_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_pos_elim___redArg(lean_object* v_t_438_, lean_object* v_pos_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_438_, v_pos_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_pos_elim(lean_object* v_motive_441_, lean_object* v_t_442_, lean_object* v_h_443_, lean_object* v_pos_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_442_, v_pos_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_neg_elim___redArg(lean_object* v_t_446_, lean_object* v_neg_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_446_, v_neg_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_neg_elim(lean_object* v_motive_449_, lean_object* v_t_450_, lean_object* v_h_451_, lean_object* v_neg_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_450_, v_neg_452_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedOccurrences_default(void){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = lean_box(0);
return v___x_454_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedOccurrences(void){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = lean_box(0);
return v___x_455_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqOccurrences_beq(lean_object* v_x_456_, lean_object* v_x_457_){
_start:
{
lean_object* v_a_459_; lean_object* v_b_460_; 
switch(lean_obj_tag(v_x_456_))
{
case 0:
{
if (lean_obj_tag(v_x_457_) == 0)
{
uint8_t v___x_463_; 
v___x_463_ = 1;
return v___x_463_;
}
else
{
uint8_t v___x_464_; 
lean_dec(v_x_457_);
v___x_464_ = 0;
return v___x_464_;
}
}
case 1:
{
if (lean_obj_tag(v_x_457_) == 1)
{
lean_object* v_idxs_465_; lean_object* v_idxs_466_; 
v_idxs_465_ = lean_ctor_get(v_x_456_, 0);
lean_inc(v_idxs_465_);
lean_dec_ref_known(v_x_456_, 1);
v_idxs_466_ = lean_ctor_get(v_x_457_, 0);
lean_inc(v_idxs_466_);
lean_dec_ref_known(v_x_457_, 1);
v_a_459_ = v_idxs_465_;
v_b_460_ = v_idxs_466_;
goto v___jp_458_;
}
else
{
uint8_t v___x_467_; 
lean_dec_ref_known(v_x_456_, 1);
lean_dec(v_x_457_);
v___x_467_ = 0;
return v___x_467_;
}
}
default: 
{
if (lean_obj_tag(v_x_457_) == 2)
{
lean_object* v_idxs_468_; lean_object* v_idxs_469_; 
v_idxs_468_ = lean_ctor_get(v_x_456_, 0);
lean_inc(v_idxs_468_);
lean_dec_ref_known(v_x_456_, 1);
v_idxs_469_ = lean_ctor_get(v_x_457_, 0);
lean_inc(v_idxs_469_);
lean_dec_ref_known(v_x_457_, 1);
v_a_459_ = v_idxs_468_;
v_b_460_ = v_idxs_469_;
goto v___jp_458_;
}
else
{
uint8_t v___x_470_; 
lean_dec_ref_known(v_x_456_, 1);
lean_dec(v_x_457_);
v___x_470_ = 0;
return v___x_470_;
}
}
}
v___jp_458_:
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_462_ = l_instDecidableEqList___redArg(v___x_461_, v_a_459_, v_b_460_);
return v___x_462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqOccurrences_beq___boxed(lean_object* v_x_471_, lean_object* v_x_472_){
_start:
{
uint8_t v_res_473_; lean_object* v_r_474_; 
v_res_473_ = l_Lean_Meta_instBEqOccurrences_beq(v_x_471_, v_x_472_);
v_r_474_ = lean_box(v_res_473_);
return v_r_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instCoeListNatOccurrences___lam__0(lean_object* v_idxs_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v_idxs_477_);
return v___x_478_;
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
