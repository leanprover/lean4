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
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorIdx(uint8_t v_x_9_){
_start:
{
switch(v_x_9_)
{
case 0:
{
lean_object* v___x_10_; 
v___x_10_ = lean_unsigned_to_nat(0u);
return v___x_10_;
}
case 1:
{
lean_object* v___x_11_; 
v___x_11_ = lean_unsigned_to_nat(1u);
return v___x_11_;
}
case 2:
{
lean_object* v___x_12_; 
v___x_12_ = lean_unsigned_to_nat(2u);
return v___x_12_;
}
case 3:
{
lean_object* v___x_13_; 
v___x_13_ = lean_unsigned_to_nat(3u);
return v___x_13_;
}
case 4:
{
lean_object* v___x_14_; 
v___x_14_ = lean_unsigned_to_nat(4u);
return v___x_14_;
}
default: 
{
lean_object* v___x_15_; 
v___x_15_ = lean_unsigned_to_nat(5u);
return v___x_15_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorIdx___boxed(lean_object* v_x_16_){
_start:
{
uint8_t v_x_boxed_17_; lean_object* v_res_18_; 
v_x_boxed_17_ = lean_unbox(v_x_16_);
v_res_18_ = l_Lean_Meta_TransparencyMode_ctorIdx(v_x_boxed_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___redArg(lean_object* v_k_19_){
_start:
{
lean_inc(v_k_19_);
return v_k_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___redArg___boxed(lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Meta_TransparencyMode_ctorElim___redArg(v_k_20_);
lean_dec(v_k_20_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, uint8_t v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
lean_inc(v_k_26_);
return v_k_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___boxed(lean_object* v_motive_27_, lean_object* v_ctorIdx_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_k_31_){
_start:
{
uint8_t v_t_boxed_32_; lean_object* v_res_33_; 
v_t_boxed_32_ = lean_unbox(v_t_29_);
v_res_33_ = l_Lean_Meta_TransparencyMode_ctorElim(v_motive_27_, v_ctorIdx_28_, v_t_boxed_32_, v_h_30_, v_k_31_);
lean_dec(v_k_31_);
lean_dec(v_ctorIdx_28_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___redArg(lean_object* v_all_34_){
_start:
{
lean_inc(v_all_34_);
return v_all_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___redArg___boxed(lean_object* v_all_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Meta_TransparencyMode_all_elim___redArg(v_all_35_);
lean_dec(v_all_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim(lean_object* v_motive_37_, uint8_t v_t_38_, lean_object* v_h_39_, lean_object* v_all_40_){
_start:
{
lean_inc(v_all_40_);
return v_all_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___boxed(lean_object* v_motive_41_, lean_object* v_t_42_, lean_object* v_h_43_, lean_object* v_all_44_){
_start:
{
uint8_t v_t_boxed_45_; lean_object* v_res_46_; 
v_t_boxed_45_ = lean_unbox(v_t_42_);
v_res_46_ = l_Lean_Meta_TransparencyMode_all_elim(v_motive_41_, v_t_boxed_45_, v_h_43_, v_all_44_);
lean_dec(v_all_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___redArg(lean_object* v_default_47_){
_start:
{
lean_inc(v_default_47_);
return v_default_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___redArg___boxed(lean_object* v_default_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_Meta_TransparencyMode_default_elim___redArg(v_default_48_);
lean_dec(v_default_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim(lean_object* v_motive_50_, uint8_t v_t_51_, lean_object* v_h_52_, lean_object* v_default_53_){
_start:
{
lean_inc(v_default_53_);
return v_default_53_;
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim(lean_object* v_motive_63_, uint8_t v_t_64_, lean_object* v_h_65_, lean_object* v_reducible_66_){
_start:
{
lean_inc(v_reducible_66_);
return v_reducible_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim___boxed(lean_object* v_motive_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_reducible_70_){
_start:
{
uint8_t v_t_boxed_71_; lean_object* v_res_72_; 
v_t_boxed_71_ = lean_unbox(v_t_68_);
v_res_72_ = l_Lean_Meta_TransparencyMode_reducible_elim(v_motive_67_, v_t_boxed_71_, v_h_69_, v_reducible_70_);
lean_dec(v_reducible_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___redArg(lean_object* v_instances_73_){
_start:
{
lean_inc(v_instances_73_);
return v_instances_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___redArg___boxed(lean_object* v_instances_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Meta_TransparencyMode_instances_elim___redArg(v_instances_74_);
lean_dec(v_instances_74_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim(lean_object* v_motive_76_, uint8_t v_t_77_, lean_object* v_h_78_, lean_object* v_instances_79_){
_start:
{
lean_inc(v_instances_79_);
return v_instances_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___boxed(lean_object* v_motive_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_instances_83_){
_start:
{
uint8_t v_t_boxed_84_; lean_object* v_res_85_; 
v_t_boxed_84_ = lean_unbox(v_t_81_);
v_res_85_ = l_Lean_Meta_TransparencyMode_instances_elim(v_motive_80_, v_t_boxed_84_, v_h_82_, v_instances_83_);
lean_dec(v_instances_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___redArg(lean_object* v_none_86_){
_start:
{
lean_inc(v_none_86_);
return v_none_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___redArg___boxed(lean_object* v_none_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Meta_TransparencyMode_none_elim___redArg(v_none_87_);
lean_dec(v_none_87_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim(lean_object* v_motive_89_, uint8_t v_t_90_, lean_object* v_h_91_, lean_object* v_none_92_){
_start:
{
lean_inc(v_none_92_);
return v_none_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___boxed(lean_object* v_motive_93_, lean_object* v_t_94_, lean_object* v_h_95_, lean_object* v_none_96_){
_start:
{
uint8_t v_t_boxed_97_; lean_object* v_res_98_; 
v_t_boxed_97_ = lean_unbox(v_t_94_);
v_res_98_ = l_Lean_Meta_TransparencyMode_none_elim(v_motive_93_, v_t_boxed_97_, v_h_95_, v_none_96_);
lean_dec(v_none_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim___redArg(lean_object* v_implicit_99_){
_start:
{
lean_inc(v_implicit_99_);
return v_implicit_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim___redArg___boxed(lean_object* v_implicit_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Meta_TransparencyMode_implicit_elim___redArg(v_implicit_100_);
lean_dec(v_implicit_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim(lean_object* v_motive_102_, uint8_t v_t_103_, lean_object* v_h_104_, lean_object* v_implicit_105_){
_start:
{
lean_inc(v_implicit_105_);
return v_implicit_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim___boxed(lean_object* v_motive_106_, lean_object* v_t_107_, lean_object* v_h_108_, lean_object* v_implicit_109_){
_start:
{
uint8_t v_t_boxed_110_; lean_object* v_res_111_; 
v_t_boxed_110_ = lean_unbox(v_t_107_);
v_res_111_ = l_Lean_Meta_TransparencyMode_implicit_elim(v_motive_106_, v_t_boxed_110_, v_h_108_, v_implicit_109_);
lean_dec(v_implicit_109_);
return v_res_111_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedTransparencyMode_default(void){
_start:
{
uint8_t v___x_112_; 
v___x_112_ = 0;
return v___x_112_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedTransparencyMode(void){
_start:
{
uint8_t v___x_113_; 
v___x_113_ = 0;
return v___x_113_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t v_x_114_, uint8_t v_y_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_116_ = l_Lean_Meta_TransparencyMode_ctorIdx(v_x_114_);
v___x_117_ = l_Lean_Meta_TransparencyMode_ctorIdx(v_y_115_);
v___x_118_ = lean_nat_dec_eq(v___x_116_, v___x_117_);
lean_dec(v___x_117_);
lean_dec(v___x_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqTransparencyMode_beq___boxed(lean_object* v_x_119_, lean_object* v_y_120_){
_start:
{
uint8_t v_x_17__boxed_121_; uint8_t v_y_18__boxed_122_; uint8_t v_res_123_; lean_object* v_r_124_; 
v_x_17__boxed_121_ = lean_unbox(v_x_119_);
v_y_18__boxed_122_ = lean_unbox(v_y_120_);
v_res_123_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_x_17__boxed_121_, v_y_18__boxed_122_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorIdx(uint8_t v_x_127_){
_start:
{
switch(v_x_127_)
{
case 0:
{
lean_object* v___x_128_; 
v___x_128_ = lean_unsigned_to_nat(0u);
return v___x_128_;
}
case 1:
{
lean_object* v___x_129_; 
v___x_129_ = lean_unsigned_to_nat(1u);
return v___x_129_;
}
default: 
{
lean_object* v___x_130_; 
v___x_130_ = lean_unsigned_to_nat(2u);
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorIdx___boxed(lean_object* v_x_131_){
_start:
{
uint8_t v_x_boxed_132_; lean_object* v_res_133_; 
v_x_boxed_132_ = lean_unbox(v_x_131_);
v_res_133_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_x_boxed_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___redArg(lean_object* v_k_134_){
_start:
{
lean_inc(v_k_134_);
return v_k_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___redArg___boxed(lean_object* v_k_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Meta_EtaStructMode_ctorElim___redArg(v_k_135_);
lean_dec(v_k_135_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim(lean_object* v_motive_137_, lean_object* v_ctorIdx_138_, uint8_t v_t_139_, lean_object* v_h_140_, lean_object* v_k_141_){
_start:
{
lean_inc(v_k_141_);
return v_k_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___boxed(lean_object* v_motive_142_, lean_object* v_ctorIdx_143_, lean_object* v_t_144_, lean_object* v_h_145_, lean_object* v_k_146_){
_start:
{
uint8_t v_t_boxed_147_; lean_object* v_res_148_; 
v_t_boxed_147_ = lean_unbox(v_t_144_);
v_res_148_ = l_Lean_Meta_EtaStructMode_ctorElim(v_motive_142_, v_ctorIdx_143_, v_t_boxed_147_, v_h_145_, v_k_146_);
lean_dec(v_k_146_);
lean_dec(v_ctorIdx_143_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___redArg(lean_object* v_all_149_){
_start:
{
lean_inc(v_all_149_);
return v_all_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___redArg___boxed(lean_object* v_all_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Meta_EtaStructMode_all_elim___redArg(v_all_150_);
lean_dec(v_all_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim(lean_object* v_motive_152_, uint8_t v_t_153_, lean_object* v_h_154_, lean_object* v_all_155_){
_start:
{
lean_inc(v_all_155_);
return v_all_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___boxed(lean_object* v_motive_156_, lean_object* v_t_157_, lean_object* v_h_158_, lean_object* v_all_159_){
_start:
{
uint8_t v_t_boxed_160_; lean_object* v_res_161_; 
v_t_boxed_160_ = lean_unbox(v_t_157_);
v_res_161_ = l_Lean_Meta_EtaStructMode_all_elim(v_motive_156_, v_t_boxed_160_, v_h_158_, v_all_159_);
lean_dec(v_all_159_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___redArg(lean_object* v_notClasses_162_){
_start:
{
lean_inc(v_notClasses_162_);
return v_notClasses_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___redArg___boxed(lean_object* v_notClasses_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Meta_EtaStructMode_notClasses_elim___redArg(v_notClasses_163_);
lean_dec(v_notClasses_163_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim(lean_object* v_motive_165_, uint8_t v_t_166_, lean_object* v_h_167_, lean_object* v_notClasses_168_){
_start:
{
lean_inc(v_notClasses_168_);
return v_notClasses_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___boxed(lean_object* v_motive_169_, lean_object* v_t_170_, lean_object* v_h_171_, lean_object* v_notClasses_172_){
_start:
{
uint8_t v_t_boxed_173_; lean_object* v_res_174_; 
v_t_boxed_173_ = lean_unbox(v_t_170_);
v_res_174_ = l_Lean_Meta_EtaStructMode_notClasses_elim(v_motive_169_, v_t_boxed_173_, v_h_171_, v_notClasses_172_);
lean_dec(v_notClasses_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___redArg(lean_object* v_none_175_){
_start:
{
lean_inc(v_none_175_);
return v_none_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___redArg___boxed(lean_object* v_none_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_Meta_EtaStructMode_none_elim___redArg(v_none_176_);
lean_dec(v_none_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim(lean_object* v_motive_178_, uint8_t v_t_179_, lean_object* v_h_180_, lean_object* v_none_181_){
_start:
{
lean_inc(v_none_181_);
return v_none_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___boxed(lean_object* v_motive_182_, lean_object* v_t_183_, lean_object* v_h_184_, lean_object* v_none_185_){
_start:
{
uint8_t v_t_boxed_186_; lean_object* v_res_187_; 
v_t_boxed_186_ = lean_unbox(v_t_183_);
v_res_187_ = l_Lean_Meta_EtaStructMode_none_elim(v_motive_182_, v_t_boxed_186_, v_h_184_, v_none_185_);
lean_dec(v_none_185_);
return v_res_187_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedEtaStructMode_default(void){
_start:
{
uint8_t v___x_188_; 
v___x_188_ = 0;
return v___x_188_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedEtaStructMode(void){
_start:
{
uint8_t v___x_189_; 
v___x_189_ = 0;
return v___x_189_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqEtaStructMode_beq(uint8_t v_x_190_, uint8_t v_y_191_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_192_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_x_190_);
v___x_193_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_y_191_);
v___x_194_ = lean_nat_dec_eq(v___x_192_, v___x_193_);
lean_dec(v___x_193_);
lean_dec(v___x_192_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqEtaStructMode_beq___boxed(lean_object* v_x_195_, lean_object* v_y_196_){
_start:
{
uint8_t v_x_17__boxed_197_; uint8_t v_y_18__boxed_198_; uint8_t v_res_199_; lean_object* v_r_200_; 
v_x_17__boxed_197_ = lean_unbox(v_x_195_);
v_y_18__boxed_198_ = lean_unbox(v_y_196_);
v_res_199_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_x_17__boxed_197_, v_y_18__boxed_198_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DSimp_instBEqConfig_beq(lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
uint8_t v_zeta_211_; uint8_t v_beta_212_; uint8_t v_eta_213_; uint8_t v_etaStruct_214_; uint8_t v_iota_215_; uint8_t v_proj_216_; uint8_t v_decide_217_; uint8_t v_autoUnfold_218_; uint8_t v_failIfUnchanged_219_; uint8_t v_unfoldPartialApp_220_; uint8_t v_zetaDelta_221_; uint8_t v_index_222_; uint8_t v_zetaUnused_223_; uint8_t v_zetaHave_224_; uint8_t v_locals_225_; uint8_t v_instances_226_; uint8_t v_zeta_227_; uint8_t v_beta_228_; uint8_t v_eta_229_; uint8_t v_etaStruct_230_; uint8_t v_iota_231_; uint8_t v_proj_232_; uint8_t v_decide_233_; uint8_t v_autoUnfold_234_; uint8_t v_failIfUnchanged_235_; uint8_t v_unfoldPartialApp_236_; uint8_t v_zetaDelta_237_; uint8_t v_index_238_; uint8_t v_zetaUnused_239_; uint8_t v_zetaHave_240_; uint8_t v_locals_241_; uint8_t v_instances_242_; uint8_t v___y_244_; uint8_t v___y_246_; uint8_t v___y_248_; uint8_t v___y_250_; uint8_t v___y_252_; uint8_t v___y_254_; uint8_t v___y_256_; uint8_t v___y_258_; uint8_t v___y_260_; uint8_t v___y_262_; uint8_t v___y_264_; 
v_zeta_211_ = lean_ctor_get_uint8(v_x_209_, 0);
v_beta_212_ = lean_ctor_get_uint8(v_x_209_, 1);
v_eta_213_ = lean_ctor_get_uint8(v_x_209_, 2);
v_etaStruct_214_ = lean_ctor_get_uint8(v_x_209_, 3);
v_iota_215_ = lean_ctor_get_uint8(v_x_209_, 4);
v_proj_216_ = lean_ctor_get_uint8(v_x_209_, 5);
v_decide_217_ = lean_ctor_get_uint8(v_x_209_, 6);
v_autoUnfold_218_ = lean_ctor_get_uint8(v_x_209_, 7);
v_failIfUnchanged_219_ = lean_ctor_get_uint8(v_x_209_, 8);
v_unfoldPartialApp_220_ = lean_ctor_get_uint8(v_x_209_, 9);
v_zetaDelta_221_ = lean_ctor_get_uint8(v_x_209_, 10);
v_index_222_ = lean_ctor_get_uint8(v_x_209_, 11);
v_zetaUnused_223_ = lean_ctor_get_uint8(v_x_209_, 12);
v_zetaHave_224_ = lean_ctor_get_uint8(v_x_209_, 13);
v_locals_225_ = lean_ctor_get_uint8(v_x_209_, 14);
v_instances_226_ = lean_ctor_get_uint8(v_x_209_, 15);
v_zeta_227_ = lean_ctor_get_uint8(v_x_210_, 0);
v_beta_228_ = lean_ctor_get_uint8(v_x_210_, 1);
v_eta_229_ = lean_ctor_get_uint8(v_x_210_, 2);
v_etaStruct_230_ = lean_ctor_get_uint8(v_x_210_, 3);
v_iota_231_ = lean_ctor_get_uint8(v_x_210_, 4);
v_proj_232_ = lean_ctor_get_uint8(v_x_210_, 5);
v_decide_233_ = lean_ctor_get_uint8(v_x_210_, 6);
v_autoUnfold_234_ = lean_ctor_get_uint8(v_x_210_, 7);
v_failIfUnchanged_235_ = lean_ctor_get_uint8(v_x_210_, 8);
v_unfoldPartialApp_236_ = lean_ctor_get_uint8(v_x_210_, 9);
v_zetaDelta_237_ = lean_ctor_get_uint8(v_x_210_, 10);
v_index_238_ = lean_ctor_get_uint8(v_x_210_, 11);
v_zetaUnused_239_ = lean_ctor_get_uint8(v_x_210_, 12);
v_zetaHave_240_ = lean_ctor_get_uint8(v_x_210_, 13);
v_locals_241_ = lean_ctor_get_uint8(v_x_210_, 14);
v_instances_242_ = lean_ctor_get_uint8(v_x_210_, 15);
if (v_zeta_211_ == 0)
{
if (v_zeta_227_ == 0)
{
goto v___jp_268_;
}
else
{
return v_zeta_211_;
}
}
else
{
if (v_zeta_227_ == 0)
{
return v_zeta_227_;
}
else
{
goto v___jp_268_;
}
}
v___jp_243_:
{
if (v_instances_226_ == 0)
{
if (v_instances_242_ == 0)
{
return v___y_244_;
}
else
{
return v_instances_226_;
}
}
else
{
return v_instances_242_;
}
}
v___jp_245_:
{
if (v_locals_225_ == 0)
{
if (v_locals_241_ == 0)
{
v___y_244_ = v___y_246_;
goto v___jp_243_;
}
else
{
return v_locals_225_;
}
}
else
{
if (v_locals_241_ == 0)
{
return v_locals_241_;
}
else
{
v___y_244_ = v_locals_241_;
goto v___jp_243_;
}
}
}
v___jp_247_:
{
if (v_zetaHave_224_ == 0)
{
if (v_zetaHave_240_ == 0)
{
v___y_246_ = v___y_248_;
goto v___jp_245_;
}
else
{
return v_zetaHave_224_;
}
}
else
{
if (v_zetaHave_240_ == 0)
{
return v_zetaHave_240_;
}
else
{
v___y_246_ = v_zetaHave_240_;
goto v___jp_245_;
}
}
}
v___jp_249_:
{
if (v_zetaUnused_223_ == 0)
{
if (v_zetaUnused_239_ == 0)
{
v___y_248_ = v___y_250_;
goto v___jp_247_;
}
else
{
return v_zetaUnused_223_;
}
}
else
{
if (v_zetaUnused_239_ == 0)
{
return v_zetaUnused_239_;
}
else
{
v___y_248_ = v_zetaUnused_239_;
goto v___jp_247_;
}
}
}
v___jp_251_:
{
if (v_index_222_ == 0)
{
if (v_index_238_ == 0)
{
v___y_250_ = v___y_252_;
goto v___jp_249_;
}
else
{
return v_index_222_;
}
}
else
{
if (v_index_238_ == 0)
{
return v_index_238_;
}
else
{
v___y_250_ = v_index_238_;
goto v___jp_249_;
}
}
}
v___jp_253_:
{
if (v_zetaDelta_221_ == 0)
{
if (v_zetaDelta_237_ == 0)
{
v___y_252_ = v___y_254_;
goto v___jp_251_;
}
else
{
return v_zetaDelta_221_;
}
}
else
{
if (v_zetaDelta_237_ == 0)
{
return v_zetaDelta_237_;
}
else
{
v___y_252_ = v_zetaDelta_237_;
goto v___jp_251_;
}
}
}
v___jp_255_:
{
if (v_unfoldPartialApp_220_ == 0)
{
if (v_unfoldPartialApp_236_ == 0)
{
v___y_254_ = v___y_256_;
goto v___jp_253_;
}
else
{
return v_unfoldPartialApp_220_;
}
}
else
{
if (v_unfoldPartialApp_236_ == 0)
{
return v_unfoldPartialApp_236_;
}
else
{
v___y_254_ = v_unfoldPartialApp_236_;
goto v___jp_253_;
}
}
}
v___jp_257_:
{
if (v_failIfUnchanged_219_ == 0)
{
if (v_failIfUnchanged_235_ == 0)
{
v___y_256_ = v___y_258_;
goto v___jp_255_;
}
else
{
return v_failIfUnchanged_219_;
}
}
else
{
if (v_failIfUnchanged_235_ == 0)
{
return v_failIfUnchanged_235_;
}
else
{
v___y_256_ = v_failIfUnchanged_235_;
goto v___jp_255_;
}
}
}
v___jp_259_:
{
if (v_autoUnfold_218_ == 0)
{
if (v_autoUnfold_234_ == 0)
{
v___y_258_ = v___y_260_;
goto v___jp_257_;
}
else
{
return v_autoUnfold_218_;
}
}
else
{
if (v_autoUnfold_234_ == 0)
{
return v_autoUnfold_234_;
}
else
{
v___y_258_ = v_autoUnfold_234_;
goto v___jp_257_;
}
}
}
v___jp_261_:
{
if (v_decide_217_ == 0)
{
if (v_decide_233_ == 0)
{
v___y_260_ = v___y_262_;
goto v___jp_259_;
}
else
{
return v_decide_217_;
}
}
else
{
if (v_decide_233_ == 0)
{
return v_decide_233_;
}
else
{
v___y_260_ = v_decide_233_;
goto v___jp_259_;
}
}
}
v___jp_263_:
{
if (v___y_264_ == 0)
{
return v___y_264_;
}
else
{
if (v_proj_216_ == 0)
{
if (v_proj_232_ == 0)
{
v___y_262_ = v___y_264_;
goto v___jp_261_;
}
else
{
return v_proj_216_;
}
}
else
{
if (v_proj_232_ == 0)
{
return v_proj_232_;
}
else
{
v___y_262_ = v_proj_232_;
goto v___jp_261_;
}
}
}
}
v___jp_265_:
{
uint8_t v___x_266_; 
v___x_266_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_214_, v_etaStruct_230_);
if (v___x_266_ == 0)
{
return v___x_266_;
}
else
{
if (v_iota_215_ == 0)
{
if (v_iota_231_ == 0)
{
v___y_264_ = v___x_266_;
goto v___jp_263_;
}
else
{
return v_iota_215_;
}
}
else
{
v___y_264_ = v_iota_231_;
goto v___jp_263_;
}
}
}
v___jp_267_:
{
if (v_eta_213_ == 0)
{
if (v_eta_229_ == 0)
{
goto v___jp_265_;
}
else
{
return v_eta_213_;
}
}
else
{
if (v_eta_229_ == 0)
{
return v_eta_229_;
}
else
{
goto v___jp_265_;
}
}
}
v___jp_268_:
{
if (v_beta_212_ == 0)
{
if (v_beta_228_ == 0)
{
goto v___jp_267_;
}
else
{
return v_beta_212_;
}
}
else
{
if (v_beta_228_ == 0)
{
return v_beta_228_;
}
else
{
goto v___jp_267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DSimp_instBEqConfig_beq___boxed(lean_object* v_x_269_, lean_object* v_x_270_){
_start:
{
uint8_t v_res_271_; lean_object* v_r_272_; 
v_res_271_ = l_Lean_Meta_DSimp_instBEqConfig_beq(v_x_269_, v_x_270_);
lean_dec_ref(v_x_270_);
lean_dec_ref(v_x_269_);
v_r_272_ = lean_box(v_res_271_);
return v_r_272_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_defaultMaxSteps(void){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = lean_unsigned_to_nat(100000u);
return v___x_275_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
if (lean_obj_tag(v_x_285_) == 0)
{
if (lean_obj_tag(v_x_286_) == 0)
{
uint8_t v___x_287_; 
v___x_287_ = 1;
return v___x_287_;
}
else
{
uint8_t v___x_288_; 
v___x_288_ = 0;
return v___x_288_;
}
}
else
{
if (lean_obj_tag(v_x_286_) == 0)
{
uint8_t v___x_289_; 
v___x_289_ = 0;
return v___x_289_;
}
else
{
lean_object* v_val_290_; lean_object* v_val_291_; uint8_t v___x_292_; 
v_val_290_ = lean_ctor_get(v_x_285_, 0);
v_val_291_ = lean_ctor_get(v_x_286_, 0);
v___x_292_ = lean_nat_dec_eq(v_val_290_, v_val_291_);
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0___boxed(lean_object* v_x_293_, lean_object* v_x_294_){
_start:
{
uint8_t v_res_295_; lean_object* v_r_296_; 
v_res_295_ = l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(v_x_293_, v_x_294_);
lean_dec(v_x_294_);
lean_dec(v_x_293_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_instBEqConfig_beq(lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
lean_object* v_maxSteps_299_; lean_object* v_maxDischargeDepth_300_; uint8_t v_contextual_301_; uint8_t v_memoize_302_; uint8_t v_singlePass_303_; uint8_t v_zeta_304_; uint8_t v_beta_305_; uint8_t v_eta_306_; uint8_t v_etaStruct_307_; uint8_t v_iota_308_; uint8_t v_proj_309_; uint8_t v_decide_310_; uint8_t v_arith_311_; uint8_t v_autoUnfold_312_; uint8_t v_dsimp_313_; uint8_t v_failIfUnchanged_314_; uint8_t v_ground_315_; uint8_t v_unfoldPartialApp_316_; uint8_t v_zetaDelta_317_; uint8_t v_index_318_; uint8_t v_implicitDefEqProofs_319_; uint8_t v_zetaUnused_320_; uint8_t v_catchRuntime_321_; uint8_t v_zetaHave_322_; uint8_t v_letToHave_323_; uint8_t v_congrConsts_324_; uint8_t v_bitVecOfNat_325_; uint8_t v_warnExponents_326_; uint8_t v_suggestions_327_; lean_object* v_maxSuggestions_328_; uint8_t v_locals_329_; uint8_t v_instances_330_; lean_object* v_maxSteps_331_; lean_object* v_maxDischargeDepth_332_; uint8_t v_contextual_333_; uint8_t v_memoize_334_; uint8_t v_singlePass_335_; uint8_t v_zeta_336_; uint8_t v_beta_337_; uint8_t v_eta_338_; uint8_t v_etaStruct_339_; uint8_t v_iota_340_; uint8_t v_proj_341_; uint8_t v_decide_342_; uint8_t v_arith_343_; uint8_t v_autoUnfold_344_; uint8_t v_dsimp_345_; uint8_t v_failIfUnchanged_346_; uint8_t v_ground_347_; uint8_t v_unfoldPartialApp_348_; uint8_t v_zetaDelta_349_; uint8_t v_index_350_; uint8_t v_implicitDefEqProofs_351_; uint8_t v_zetaUnused_352_; uint8_t v_catchRuntime_353_; uint8_t v_zetaHave_354_; uint8_t v_letToHave_355_; uint8_t v_congrConsts_356_; uint8_t v_bitVecOfNat_357_; uint8_t v_warnExponents_358_; uint8_t v_suggestions_359_; lean_object* v_maxSuggestions_360_; uint8_t v_locals_361_; uint8_t v_instances_362_; uint8_t v___y_364_; uint8_t v___y_386_; uint8_t v___y_394_; uint8_t v___x_395_; 
v_maxSteps_299_ = lean_ctor_get(v_x_297_, 0);
v_maxDischargeDepth_300_ = lean_ctor_get(v_x_297_, 1);
v_contextual_301_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3);
v_memoize_302_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 1);
v_singlePass_303_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 2);
v_zeta_304_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 3);
v_beta_305_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 4);
v_eta_306_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 5);
v_etaStruct_307_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 6);
v_iota_308_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 7);
v_proj_309_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 8);
v_decide_310_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 9);
v_arith_311_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 10);
v_autoUnfold_312_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 11);
v_dsimp_313_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 12);
v_failIfUnchanged_314_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 13);
v_ground_315_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_316_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 15);
v_zetaDelta_317_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 16);
v_index_318_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_319_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 18);
v_zetaUnused_320_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 19);
v_catchRuntime_321_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 20);
v_zetaHave_322_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 21);
v_letToHave_323_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 22);
v_congrConsts_324_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 23);
v_bitVecOfNat_325_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 24);
v_warnExponents_326_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 25);
v_suggestions_327_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 26);
v_maxSuggestions_328_ = lean_ctor_get(v_x_297_, 2);
v_locals_329_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 27);
v_instances_330_ = lean_ctor_get_uint8(v_x_297_, sizeof(void*)*3 + 28);
v_maxSteps_331_ = lean_ctor_get(v_x_298_, 0);
v_maxDischargeDepth_332_ = lean_ctor_get(v_x_298_, 1);
v_contextual_333_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3);
v_memoize_334_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 1);
v_singlePass_335_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 2);
v_zeta_336_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 3);
v_beta_337_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 4);
v_eta_338_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 5);
v_etaStruct_339_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 6);
v_iota_340_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 7);
v_proj_341_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 8);
v_decide_342_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 9);
v_arith_343_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 10);
v_autoUnfold_344_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 11);
v_dsimp_345_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 12);
v_failIfUnchanged_346_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 13);
v_ground_347_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_348_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 15);
v_zetaDelta_349_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 16);
v_index_350_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_351_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 18);
v_zetaUnused_352_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 19);
v_catchRuntime_353_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 20);
v_zetaHave_354_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 21);
v_letToHave_355_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 22);
v_congrConsts_356_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 23);
v_bitVecOfNat_357_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 24);
v_warnExponents_358_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 25);
v_suggestions_359_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 26);
v_maxSuggestions_360_ = lean_ctor_get(v_x_298_, 2);
v_locals_361_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 27);
v_instances_362_ = lean_ctor_get_uint8(v_x_298_, sizeof(void*)*3 + 28);
v___x_395_ = lean_nat_dec_eq(v_maxSteps_299_, v_maxSteps_331_);
if (v___x_395_ == 0)
{
return v___x_395_;
}
else
{
uint8_t v___x_396_; 
v___x_396_ = lean_nat_dec_eq(v_maxDischargeDepth_300_, v_maxDischargeDepth_332_);
if (v___x_396_ == 0)
{
return v___x_396_;
}
else
{
if (v_contextual_301_ == 0)
{
if (v_contextual_333_ == 0)
{
v___y_394_ = v___x_396_;
goto v___jp_393_;
}
else
{
return v_contextual_301_;
}
}
else
{
v___y_394_ = v_contextual_333_;
goto v___jp_393_;
}
}
}
v___jp_363_:
{
if (v___y_364_ == 0)
{
return v___y_364_;
}
else
{
if (v_instances_330_ == 0)
{
if (v_instances_362_ == 0)
{
return v___y_364_;
}
else
{
return v_instances_330_;
}
}
else
{
return v_instances_362_;
}
}
}
v___jp_365_:
{
uint8_t v___x_366_; 
v___x_366_ = l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(v_maxSuggestions_328_, v_maxSuggestions_360_);
if (v___x_366_ == 0)
{
return v___x_366_;
}
else
{
if (v_locals_329_ == 0)
{
if (v_locals_361_ == 0)
{
v___y_364_ = v___x_366_;
goto v___jp_363_;
}
else
{
return v_locals_329_;
}
}
else
{
v___y_364_ = v_locals_361_;
goto v___jp_363_;
}
}
}
v___jp_367_:
{
if (v_suggestions_327_ == 0)
{
if (v_suggestions_359_ == 0)
{
goto v___jp_365_;
}
else
{
return v_suggestions_327_;
}
}
else
{
if (v_suggestions_359_ == 0)
{
return v_suggestions_359_;
}
else
{
goto v___jp_365_;
}
}
}
v___jp_368_:
{
if (v_warnExponents_326_ == 0)
{
if (v_warnExponents_358_ == 0)
{
goto v___jp_367_;
}
else
{
return v_warnExponents_326_;
}
}
else
{
if (v_warnExponents_358_ == 0)
{
return v_warnExponents_358_;
}
else
{
goto v___jp_367_;
}
}
}
v___jp_369_:
{
if (v_bitVecOfNat_325_ == 0)
{
if (v_bitVecOfNat_357_ == 0)
{
goto v___jp_368_;
}
else
{
return v_bitVecOfNat_325_;
}
}
else
{
if (v_bitVecOfNat_357_ == 0)
{
return v_bitVecOfNat_357_;
}
else
{
goto v___jp_368_;
}
}
}
v___jp_370_:
{
if (v_congrConsts_324_ == 0)
{
if (v_congrConsts_356_ == 0)
{
goto v___jp_369_;
}
else
{
return v_congrConsts_324_;
}
}
else
{
if (v_congrConsts_356_ == 0)
{
return v_congrConsts_356_;
}
else
{
goto v___jp_369_;
}
}
}
v___jp_371_:
{
if (v_letToHave_323_ == 0)
{
if (v_letToHave_355_ == 0)
{
goto v___jp_370_;
}
else
{
return v_letToHave_323_;
}
}
else
{
if (v_letToHave_355_ == 0)
{
return v_letToHave_355_;
}
else
{
goto v___jp_370_;
}
}
}
v___jp_372_:
{
if (v_zetaHave_322_ == 0)
{
if (v_zetaHave_354_ == 0)
{
goto v___jp_371_;
}
else
{
return v_zetaHave_322_;
}
}
else
{
if (v_zetaHave_354_ == 0)
{
return v_zetaHave_354_;
}
else
{
goto v___jp_371_;
}
}
}
v___jp_373_:
{
if (v_catchRuntime_321_ == 0)
{
if (v_catchRuntime_353_ == 0)
{
goto v___jp_372_;
}
else
{
return v_catchRuntime_321_;
}
}
else
{
if (v_catchRuntime_353_ == 0)
{
return v_catchRuntime_353_;
}
else
{
goto v___jp_372_;
}
}
}
v___jp_374_:
{
if (v_zetaUnused_320_ == 0)
{
if (v_zetaUnused_352_ == 0)
{
goto v___jp_373_;
}
else
{
return v_zetaUnused_320_;
}
}
else
{
if (v_zetaUnused_352_ == 0)
{
return v_zetaUnused_352_;
}
else
{
goto v___jp_373_;
}
}
}
v___jp_375_:
{
if (v_implicitDefEqProofs_319_ == 0)
{
if (v_implicitDefEqProofs_351_ == 0)
{
goto v___jp_374_;
}
else
{
return v_implicitDefEqProofs_319_;
}
}
else
{
if (v_implicitDefEqProofs_351_ == 0)
{
return v_implicitDefEqProofs_351_;
}
else
{
goto v___jp_374_;
}
}
}
v___jp_376_:
{
if (v_index_318_ == 0)
{
if (v_index_350_ == 0)
{
goto v___jp_375_;
}
else
{
return v_index_318_;
}
}
else
{
if (v_index_350_ == 0)
{
return v_index_350_;
}
else
{
goto v___jp_375_;
}
}
}
v___jp_377_:
{
if (v_zetaDelta_317_ == 0)
{
if (v_zetaDelta_349_ == 0)
{
goto v___jp_376_;
}
else
{
return v_zetaDelta_317_;
}
}
else
{
if (v_zetaDelta_349_ == 0)
{
return v_zetaDelta_349_;
}
else
{
goto v___jp_376_;
}
}
}
v___jp_378_:
{
if (v_unfoldPartialApp_316_ == 0)
{
if (v_unfoldPartialApp_348_ == 0)
{
goto v___jp_377_;
}
else
{
return v_unfoldPartialApp_316_;
}
}
else
{
if (v_unfoldPartialApp_348_ == 0)
{
return v_unfoldPartialApp_348_;
}
else
{
goto v___jp_377_;
}
}
}
v___jp_379_:
{
if (v_ground_315_ == 0)
{
if (v_ground_347_ == 0)
{
goto v___jp_378_;
}
else
{
return v_ground_315_;
}
}
else
{
if (v_ground_347_ == 0)
{
return v_ground_347_;
}
else
{
goto v___jp_378_;
}
}
}
v___jp_380_:
{
if (v_failIfUnchanged_314_ == 0)
{
if (v_failIfUnchanged_346_ == 0)
{
goto v___jp_379_;
}
else
{
return v_failIfUnchanged_314_;
}
}
else
{
if (v_failIfUnchanged_346_ == 0)
{
return v_failIfUnchanged_346_;
}
else
{
goto v___jp_379_;
}
}
}
v___jp_381_:
{
if (v_dsimp_313_ == 0)
{
if (v_dsimp_345_ == 0)
{
goto v___jp_380_;
}
else
{
return v_dsimp_313_;
}
}
else
{
if (v_dsimp_345_ == 0)
{
return v_dsimp_345_;
}
else
{
goto v___jp_380_;
}
}
}
v___jp_382_:
{
if (v_autoUnfold_312_ == 0)
{
if (v_autoUnfold_344_ == 0)
{
goto v___jp_381_;
}
else
{
return v_autoUnfold_312_;
}
}
else
{
if (v_autoUnfold_344_ == 0)
{
return v_autoUnfold_344_;
}
else
{
goto v___jp_381_;
}
}
}
v___jp_383_:
{
if (v_arith_311_ == 0)
{
if (v_arith_343_ == 0)
{
goto v___jp_382_;
}
else
{
return v_arith_311_;
}
}
else
{
if (v_arith_343_ == 0)
{
return v_arith_343_;
}
else
{
goto v___jp_382_;
}
}
}
v___jp_384_:
{
if (v_decide_310_ == 0)
{
if (v_decide_342_ == 0)
{
goto v___jp_383_;
}
else
{
return v_decide_310_;
}
}
else
{
if (v_decide_342_ == 0)
{
return v_decide_342_;
}
else
{
goto v___jp_383_;
}
}
}
v___jp_385_:
{
if (v___y_386_ == 0)
{
return v___y_386_;
}
else
{
if (v_proj_309_ == 0)
{
if (v_proj_341_ == 0)
{
goto v___jp_384_;
}
else
{
return v_proj_309_;
}
}
else
{
if (v_proj_341_ == 0)
{
return v_proj_341_;
}
else
{
goto v___jp_384_;
}
}
}
}
v___jp_387_:
{
uint8_t v___x_388_; 
v___x_388_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_307_, v_etaStruct_339_);
if (v___x_388_ == 0)
{
return v___x_388_;
}
else
{
if (v_iota_308_ == 0)
{
if (v_iota_340_ == 0)
{
v___y_386_ = v___x_388_;
goto v___jp_385_;
}
else
{
return v_iota_308_;
}
}
else
{
v___y_386_ = v_iota_340_;
goto v___jp_385_;
}
}
}
v___jp_389_:
{
if (v_eta_306_ == 0)
{
if (v_eta_338_ == 0)
{
goto v___jp_387_;
}
else
{
return v_eta_306_;
}
}
else
{
if (v_eta_338_ == 0)
{
return v_eta_338_;
}
else
{
goto v___jp_387_;
}
}
}
v___jp_390_:
{
if (v_beta_305_ == 0)
{
if (v_beta_337_ == 0)
{
goto v___jp_389_;
}
else
{
return v_beta_305_;
}
}
else
{
if (v_beta_337_ == 0)
{
return v_beta_337_;
}
else
{
goto v___jp_389_;
}
}
}
v___jp_391_:
{
if (v_zeta_304_ == 0)
{
if (v_zeta_336_ == 0)
{
goto v___jp_390_;
}
else
{
return v_zeta_304_;
}
}
else
{
if (v_zeta_336_ == 0)
{
return v_zeta_336_;
}
else
{
goto v___jp_390_;
}
}
}
v___jp_392_:
{
if (v_singlePass_303_ == 0)
{
if (v_singlePass_335_ == 0)
{
goto v___jp_391_;
}
else
{
return v_singlePass_303_;
}
}
else
{
if (v_singlePass_335_ == 0)
{
return v_singlePass_335_;
}
else
{
goto v___jp_391_;
}
}
}
v___jp_393_:
{
if (v___y_394_ == 0)
{
return v___y_394_;
}
else
{
if (v_memoize_302_ == 0)
{
if (v_memoize_334_ == 0)
{
goto v___jp_392_;
}
else
{
return v_memoize_302_;
}
}
else
{
if (v_memoize_334_ == 0)
{
return v_memoize_334_;
}
else
{
goto v___jp_392_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instBEqConfig_beq___boxed(lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
uint8_t v_res_399_; lean_object* v_r_400_; 
v_res_399_ = l_Lean_Meta_Simp_instBEqConfig_beq(v_x_397_, v_x_398_);
lean_dec_ref(v_x_398_);
lean_dec_ref(v_x_397_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorIdx(lean_object* v_x_411_){
_start:
{
switch(lean_obj_tag(v_x_411_))
{
case 0:
{
lean_object* v___x_412_; 
v___x_412_ = lean_unsigned_to_nat(0u);
return v___x_412_;
}
case 1:
{
lean_object* v___x_413_; 
v___x_413_ = lean_unsigned_to_nat(1u);
return v___x_413_;
}
default: 
{
lean_object* v___x_414_; 
v___x_414_ = lean_unsigned_to_nat(2u);
return v___x_414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorIdx___boxed(lean_object* v_x_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Meta_Occurrences_ctorIdx(v_x_415_);
lean_dec(v_x_415_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim___redArg(lean_object* v_t_417_, lean_object* v_k_418_){
_start:
{
if (lean_obj_tag(v_t_417_) == 0)
{
return v_k_418_;
}
else
{
lean_object* v_idxs_419_; lean_object* v___x_420_; 
v_idxs_419_ = lean_ctor_get(v_t_417_, 0);
lean_inc(v_idxs_419_);
lean_dec(v_t_417_);
v___x_420_ = lean_apply_1(v_k_418_, v_idxs_419_);
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim(lean_object* v_motive_421_, lean_object* v_ctorIdx_422_, lean_object* v_t_423_, lean_object* v_h_424_, lean_object* v_k_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_423_, v_k_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim___boxed(lean_object* v_motive_427_, lean_object* v_ctorIdx_428_, lean_object* v_t_429_, lean_object* v_h_430_, lean_object* v_k_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Meta_Occurrences_ctorElim(v_motive_427_, v_ctorIdx_428_, v_t_429_, v_h_430_, v_k_431_);
lean_dec(v_ctorIdx_428_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_all_elim___redArg(lean_object* v_t_433_, lean_object* v_all_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_433_, v_all_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_all_elim(lean_object* v_motive_436_, lean_object* v_t_437_, lean_object* v_h_438_, lean_object* v_all_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_437_, v_all_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_pos_elim___redArg(lean_object* v_t_441_, lean_object* v_pos_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_441_, v_pos_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_pos_elim(lean_object* v_motive_444_, lean_object* v_t_445_, lean_object* v_h_446_, lean_object* v_pos_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_445_, v_pos_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_neg_elim___redArg(lean_object* v_t_449_, lean_object* v_neg_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_449_, v_neg_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_neg_elim(lean_object* v_motive_452_, lean_object* v_t_453_, lean_object* v_h_454_, lean_object* v_neg_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_453_, v_neg_455_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedOccurrences_default(void){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = lean_box(0);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedOccurrences(void){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = lean_box(0);
return v___x_458_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqOccurrences_beq(lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
lean_object* v_a_462_; lean_object* v_b_463_; 
switch(lean_obj_tag(v_x_459_))
{
case 0:
{
if (lean_obj_tag(v_x_460_) == 0)
{
uint8_t v___x_466_; 
v___x_466_ = 1;
return v___x_466_;
}
else
{
uint8_t v___x_467_; 
lean_dec(v_x_460_);
v___x_467_ = 0;
return v___x_467_;
}
}
case 1:
{
if (lean_obj_tag(v_x_460_) == 1)
{
lean_object* v_idxs_468_; lean_object* v_idxs_469_; 
v_idxs_468_ = lean_ctor_get(v_x_459_, 0);
lean_inc(v_idxs_468_);
lean_dec_ref_known(v_x_459_, 1);
v_idxs_469_ = lean_ctor_get(v_x_460_, 0);
lean_inc(v_idxs_469_);
lean_dec_ref_known(v_x_460_, 1);
v_a_462_ = v_idxs_468_;
v_b_463_ = v_idxs_469_;
goto v___jp_461_;
}
else
{
uint8_t v___x_470_; 
lean_dec_ref_known(v_x_459_, 1);
lean_dec(v_x_460_);
v___x_470_ = 0;
return v___x_470_;
}
}
default: 
{
if (lean_obj_tag(v_x_460_) == 2)
{
lean_object* v_idxs_471_; lean_object* v_idxs_472_; 
v_idxs_471_ = lean_ctor_get(v_x_459_, 0);
lean_inc(v_idxs_471_);
lean_dec_ref_known(v_x_459_, 1);
v_idxs_472_ = lean_ctor_get(v_x_460_, 0);
lean_inc(v_idxs_472_);
lean_dec_ref_known(v_x_460_, 1);
v_a_462_ = v_idxs_471_;
v_b_463_ = v_idxs_472_;
goto v___jp_461_;
}
else
{
uint8_t v___x_473_; 
lean_dec_ref_known(v_x_459_, 1);
lean_dec(v_x_460_);
v___x_473_ = 0;
return v___x_473_;
}
}
}
v___jp_461_:
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_465_ = l_instDecidableEqList___redArg(v___x_464_, v_a_462_, v_b_463_);
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqOccurrences_beq___boxed(lean_object* v_x_474_, lean_object* v_x_475_){
_start:
{
uint8_t v_res_476_; lean_object* v_r_477_; 
v_res_476_ = l_Lean_Meta_instBEqOccurrences_beq(v_x_474_, v_x_475_);
v_r_477_ = lean_box(v_res_476_);
return v_r_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instCoeListNatOccurrences___lam__0(lean_object* v_idxs_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_481_, 0, v_idxs_480_);
return v___x_481_;
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
