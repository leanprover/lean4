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
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedTransparencyMode_default;
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedTransparencyMode;
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqTransparencyMode_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instBEqTransparencyMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instBEqTransparencyMode_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instBEqTransparencyMode___closed__0 = (const lean_object*)&l_Lean_Meta_instBEqTransparencyMode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instBEqTransparencyMode = (const lean_object*)&l_Lean_Meta_instBEqTransparencyMode___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_toCtorIdx___boxed(lean_object*);
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
default: 
{
lean_object* v___x_14_; 
v___x_14_ = lean_unsigned_to_nat(4u);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorIdx___boxed(lean_object* v_x_15_){
_start:
{
uint8_t v_x_boxed_16_; lean_object* v_res_17_; 
v_x_boxed_16_ = lean_unbox(v_x_15_);
v_res_17_ = l_Lean_Meta_TransparencyMode_ctorIdx(v_x_boxed_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toCtorIdx(uint8_t v_x_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Meta_TransparencyMode_ctorIdx(v_x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toCtorIdx___boxed(lean_object* v_x_20_){
_start:
{
uint8_t v_x_4__boxed_21_; lean_object* v_res_22_; 
v_x_4__boxed_21_ = lean_unbox(v_x_20_);
v_res_22_ = l_Lean_Meta_TransparencyMode_toCtorIdx(v_x_4__boxed_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___redArg(lean_object* v_k_23_){
_start:
{
lean_inc(v_k_23_);
return v_k_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___redArg___boxed(lean_object* v_k_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Meta_TransparencyMode_ctorElim___redArg(v_k_24_);
lean_dec(v_k_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim(lean_object* v_motive_26_, lean_object* v_ctorIdx_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_k_30_){
_start:
{
lean_inc(v_k_30_);
return v_k_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___boxed(lean_object* v_motive_31_, lean_object* v_ctorIdx_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_k_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Meta_TransparencyMode_ctorElim(v_motive_31_, v_ctorIdx_32_, v_t_boxed_36_, v_h_34_, v_k_35_);
lean_dec(v_k_35_);
lean_dec(v_ctorIdx_32_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___redArg(lean_object* v_all_38_){
_start:
{
lean_inc(v_all_38_);
return v_all_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___redArg___boxed(lean_object* v_all_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Meta_TransparencyMode_all_elim___redArg(v_all_39_);
lean_dec(v_all_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_all_44_){
_start:
{
lean_inc(v_all_44_);
return v_all_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___boxed(lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_all_48_){
_start:
{
uint8_t v_t_boxed_49_; lean_object* v_res_50_; 
v_t_boxed_49_ = lean_unbox(v_t_46_);
v_res_50_ = l_Lean_Meta_TransparencyMode_all_elim(v_motive_45_, v_t_boxed_49_, v_h_47_, v_all_48_);
lean_dec(v_all_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___redArg(lean_object* v_default_51_){
_start:
{
lean_inc(v_default_51_);
return v_default_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___redArg___boxed(lean_object* v_default_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Meta_TransparencyMode_default_elim___redArg(v_default_52_);
lean_dec(v_default_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim(lean_object* v_motive_54_, uint8_t v_t_55_, lean_object* v_h_56_, lean_object* v_default_57_){
_start:
{
lean_inc(v_default_57_);
return v_default_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___boxed(lean_object* v_motive_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_default_61_){
_start:
{
uint8_t v_t_boxed_62_; lean_object* v_res_63_; 
v_t_boxed_62_ = lean_unbox(v_t_59_);
v_res_63_ = l_Lean_Meta_TransparencyMode_default_elim(v_motive_58_, v_t_boxed_62_, v_h_60_, v_default_61_);
lean_dec(v_default_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim___redArg(lean_object* v_reducible_64_){
_start:
{
lean_inc(v_reducible_64_);
return v_reducible_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim___redArg___boxed(lean_object* v_reducible_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Meta_TransparencyMode_reducible_elim___redArg(v_reducible_65_);
lean_dec(v_reducible_65_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim(lean_object* v_motive_67_, uint8_t v_t_68_, lean_object* v_h_69_, lean_object* v_reducible_70_){
_start:
{
lean_inc(v_reducible_70_);
return v_reducible_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim___boxed(lean_object* v_motive_71_, lean_object* v_t_72_, lean_object* v_h_73_, lean_object* v_reducible_74_){
_start:
{
uint8_t v_t_boxed_75_; lean_object* v_res_76_; 
v_t_boxed_75_ = lean_unbox(v_t_72_);
v_res_76_ = l_Lean_Meta_TransparencyMode_reducible_elim(v_motive_71_, v_t_boxed_75_, v_h_73_, v_reducible_74_);
lean_dec(v_reducible_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___redArg(lean_object* v_instances_77_){
_start:
{
lean_inc(v_instances_77_);
return v_instances_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___redArg___boxed(lean_object* v_instances_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_Meta_TransparencyMode_instances_elim___redArg(v_instances_78_);
lean_dec(v_instances_78_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim(lean_object* v_motive_80_, uint8_t v_t_81_, lean_object* v_h_82_, lean_object* v_instances_83_){
_start:
{
lean_inc(v_instances_83_);
return v_instances_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___boxed(lean_object* v_motive_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_instances_87_){
_start:
{
uint8_t v_t_boxed_88_; lean_object* v_res_89_; 
v_t_boxed_88_ = lean_unbox(v_t_85_);
v_res_89_ = l_Lean_Meta_TransparencyMode_instances_elim(v_motive_84_, v_t_boxed_88_, v_h_86_, v_instances_87_);
lean_dec(v_instances_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___redArg(lean_object* v_none_90_){
_start:
{
lean_inc(v_none_90_);
return v_none_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___redArg___boxed(lean_object* v_none_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_Meta_TransparencyMode_none_elim___redArg(v_none_91_);
lean_dec(v_none_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim(lean_object* v_motive_93_, uint8_t v_t_94_, lean_object* v_h_95_, lean_object* v_none_96_){
_start:
{
lean_inc(v_none_96_);
return v_none_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___boxed(lean_object* v_motive_97_, lean_object* v_t_98_, lean_object* v_h_99_, lean_object* v_none_100_){
_start:
{
uint8_t v_t_boxed_101_; lean_object* v_res_102_; 
v_t_boxed_101_ = lean_unbox(v_t_98_);
v_res_102_ = l_Lean_Meta_TransparencyMode_none_elim(v_motive_97_, v_t_boxed_101_, v_h_99_, v_none_100_);
lean_dec(v_none_100_);
return v_res_102_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedTransparencyMode_default(void){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = 0;
return v___x_103_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedTransparencyMode(void){
_start:
{
uint8_t v___x_104_; 
v___x_104_ = 0;
return v___x_104_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t v_x_105_, uint8_t v_y_106_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_107_ = l_Lean_Meta_TransparencyMode_ctorIdx(v_x_105_);
v___x_108_ = l_Lean_Meta_TransparencyMode_ctorIdx(v_y_106_);
v___x_109_ = lean_nat_dec_eq(v___x_107_, v___x_108_);
lean_dec(v___x_108_);
lean_dec(v___x_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqTransparencyMode_beq___boxed(lean_object* v_x_110_, lean_object* v_y_111_){
_start:
{
uint8_t v_x_17__boxed_112_; uint8_t v_y_18__boxed_113_; uint8_t v_res_114_; lean_object* v_r_115_; 
v_x_17__boxed_112_ = lean_unbox(v_x_110_);
v_y_18__boxed_113_ = lean_unbox(v_y_111_);
v_res_114_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_x_17__boxed_112_, v_y_18__boxed_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorIdx(uint8_t v_x_118_){
_start:
{
switch(v_x_118_)
{
case 0:
{
lean_object* v___x_119_; 
v___x_119_ = lean_unsigned_to_nat(0u);
return v___x_119_;
}
case 1:
{
lean_object* v___x_120_; 
v___x_120_ = lean_unsigned_to_nat(1u);
return v___x_120_;
}
default: 
{
lean_object* v___x_121_; 
v___x_121_ = lean_unsigned_to_nat(2u);
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorIdx___boxed(lean_object* v_x_122_){
_start:
{
uint8_t v_x_boxed_123_; lean_object* v_res_124_; 
v_x_boxed_123_ = lean_unbox(v_x_122_);
v_res_124_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_x_boxed_123_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_toCtorIdx(uint8_t v_x_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_toCtorIdx___boxed(lean_object* v_x_127_){
_start:
{
uint8_t v_x_4__boxed_128_; lean_object* v_res_129_; 
v_x_4__boxed_128_ = lean_unbox(v_x_127_);
v_res_129_ = l_Lean_Meta_EtaStructMode_toCtorIdx(v_x_4__boxed_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___redArg(lean_object* v_k_130_){
_start:
{
lean_inc(v_k_130_);
return v_k_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___redArg___boxed(lean_object* v_k_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_Meta_EtaStructMode_ctorElim___redArg(v_k_131_);
lean_dec(v_k_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim(lean_object* v_motive_133_, lean_object* v_ctorIdx_134_, uint8_t v_t_135_, lean_object* v_h_136_, lean_object* v_k_137_){
_start:
{
lean_inc(v_k_137_);
return v_k_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___boxed(lean_object* v_motive_138_, lean_object* v_ctorIdx_139_, lean_object* v_t_140_, lean_object* v_h_141_, lean_object* v_k_142_){
_start:
{
uint8_t v_t_boxed_143_; lean_object* v_res_144_; 
v_t_boxed_143_ = lean_unbox(v_t_140_);
v_res_144_ = l_Lean_Meta_EtaStructMode_ctorElim(v_motive_138_, v_ctorIdx_139_, v_t_boxed_143_, v_h_141_, v_k_142_);
lean_dec(v_k_142_);
lean_dec(v_ctorIdx_139_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___redArg(lean_object* v_all_145_){
_start:
{
lean_inc(v_all_145_);
return v_all_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___redArg___boxed(lean_object* v_all_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Meta_EtaStructMode_all_elim___redArg(v_all_146_);
lean_dec(v_all_146_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim(lean_object* v_motive_148_, uint8_t v_t_149_, lean_object* v_h_150_, lean_object* v_all_151_){
_start:
{
lean_inc(v_all_151_);
return v_all_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___boxed(lean_object* v_motive_152_, lean_object* v_t_153_, lean_object* v_h_154_, lean_object* v_all_155_){
_start:
{
uint8_t v_t_boxed_156_; lean_object* v_res_157_; 
v_t_boxed_156_ = lean_unbox(v_t_153_);
v_res_157_ = l_Lean_Meta_EtaStructMode_all_elim(v_motive_152_, v_t_boxed_156_, v_h_154_, v_all_155_);
lean_dec(v_all_155_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___redArg(lean_object* v_notClasses_158_){
_start:
{
lean_inc(v_notClasses_158_);
return v_notClasses_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___redArg___boxed(lean_object* v_notClasses_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_Meta_EtaStructMode_notClasses_elim___redArg(v_notClasses_159_);
lean_dec(v_notClasses_159_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim(lean_object* v_motive_161_, uint8_t v_t_162_, lean_object* v_h_163_, lean_object* v_notClasses_164_){
_start:
{
lean_inc(v_notClasses_164_);
return v_notClasses_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___boxed(lean_object* v_motive_165_, lean_object* v_t_166_, lean_object* v_h_167_, lean_object* v_notClasses_168_){
_start:
{
uint8_t v_t_boxed_169_; lean_object* v_res_170_; 
v_t_boxed_169_ = lean_unbox(v_t_166_);
v_res_170_ = l_Lean_Meta_EtaStructMode_notClasses_elim(v_motive_165_, v_t_boxed_169_, v_h_167_, v_notClasses_168_);
lean_dec(v_notClasses_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___redArg(lean_object* v_none_171_){
_start:
{
lean_inc(v_none_171_);
return v_none_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___redArg___boxed(lean_object* v_none_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Meta_EtaStructMode_none_elim___redArg(v_none_172_);
lean_dec(v_none_172_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim(lean_object* v_motive_174_, uint8_t v_t_175_, lean_object* v_h_176_, lean_object* v_none_177_){
_start:
{
lean_inc(v_none_177_);
return v_none_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___boxed(lean_object* v_motive_178_, lean_object* v_t_179_, lean_object* v_h_180_, lean_object* v_none_181_){
_start:
{
uint8_t v_t_boxed_182_; lean_object* v_res_183_; 
v_t_boxed_182_ = lean_unbox(v_t_179_);
v_res_183_ = l_Lean_Meta_EtaStructMode_none_elim(v_motive_178_, v_t_boxed_182_, v_h_180_, v_none_181_);
lean_dec(v_none_181_);
return v_res_183_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedEtaStructMode_default(void){
_start:
{
uint8_t v___x_184_; 
v___x_184_ = 0;
return v___x_184_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedEtaStructMode(void){
_start:
{
uint8_t v___x_185_; 
v___x_185_ = 0;
return v___x_185_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqEtaStructMode_beq(uint8_t v_x_186_, uint8_t v_y_187_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_188_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_x_186_);
v___x_189_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_y_187_);
v___x_190_ = lean_nat_dec_eq(v___x_188_, v___x_189_);
lean_dec(v___x_189_);
lean_dec(v___x_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqEtaStructMode_beq___boxed(lean_object* v_x_191_, lean_object* v_y_192_){
_start:
{
uint8_t v_x_17__boxed_193_; uint8_t v_y_18__boxed_194_; uint8_t v_res_195_; lean_object* v_r_196_; 
v_x_17__boxed_193_ = lean_unbox(v_x_191_);
v_y_18__boxed_194_ = lean_unbox(v_y_192_);
v_res_195_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_x_17__boxed_193_, v_y_18__boxed_194_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DSimp_instBEqConfig_beq(lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
uint8_t v_zeta_207_; uint8_t v_beta_208_; uint8_t v_eta_209_; uint8_t v_etaStruct_210_; uint8_t v_iota_211_; uint8_t v_proj_212_; uint8_t v_decide_213_; uint8_t v_autoUnfold_214_; uint8_t v_failIfUnchanged_215_; uint8_t v_unfoldPartialApp_216_; uint8_t v_zetaDelta_217_; uint8_t v_index_218_; uint8_t v_zetaUnused_219_; uint8_t v_zetaHave_220_; uint8_t v_locals_221_; uint8_t v_instances_222_; uint8_t v_zeta_223_; uint8_t v_beta_224_; uint8_t v_eta_225_; uint8_t v_etaStruct_226_; uint8_t v_iota_227_; uint8_t v_proj_228_; uint8_t v_decide_229_; uint8_t v_autoUnfold_230_; uint8_t v_failIfUnchanged_231_; uint8_t v_unfoldPartialApp_232_; uint8_t v_zetaDelta_233_; uint8_t v_index_234_; uint8_t v_zetaUnused_235_; uint8_t v_zetaHave_236_; uint8_t v_locals_237_; uint8_t v_instances_238_; uint8_t v___y_240_; uint8_t v___y_242_; uint8_t v___y_244_; uint8_t v___y_246_; uint8_t v___y_248_; uint8_t v___y_250_; uint8_t v___y_252_; uint8_t v___y_254_; uint8_t v___y_256_; uint8_t v___y_258_; uint8_t v___y_260_; 
v_zeta_207_ = lean_ctor_get_uint8(v_x_205_, 0);
v_beta_208_ = lean_ctor_get_uint8(v_x_205_, 1);
v_eta_209_ = lean_ctor_get_uint8(v_x_205_, 2);
v_etaStruct_210_ = lean_ctor_get_uint8(v_x_205_, 3);
v_iota_211_ = lean_ctor_get_uint8(v_x_205_, 4);
v_proj_212_ = lean_ctor_get_uint8(v_x_205_, 5);
v_decide_213_ = lean_ctor_get_uint8(v_x_205_, 6);
v_autoUnfold_214_ = lean_ctor_get_uint8(v_x_205_, 7);
v_failIfUnchanged_215_ = lean_ctor_get_uint8(v_x_205_, 8);
v_unfoldPartialApp_216_ = lean_ctor_get_uint8(v_x_205_, 9);
v_zetaDelta_217_ = lean_ctor_get_uint8(v_x_205_, 10);
v_index_218_ = lean_ctor_get_uint8(v_x_205_, 11);
v_zetaUnused_219_ = lean_ctor_get_uint8(v_x_205_, 12);
v_zetaHave_220_ = lean_ctor_get_uint8(v_x_205_, 13);
v_locals_221_ = lean_ctor_get_uint8(v_x_205_, 14);
v_instances_222_ = lean_ctor_get_uint8(v_x_205_, 15);
v_zeta_223_ = lean_ctor_get_uint8(v_x_206_, 0);
v_beta_224_ = lean_ctor_get_uint8(v_x_206_, 1);
v_eta_225_ = lean_ctor_get_uint8(v_x_206_, 2);
v_etaStruct_226_ = lean_ctor_get_uint8(v_x_206_, 3);
v_iota_227_ = lean_ctor_get_uint8(v_x_206_, 4);
v_proj_228_ = lean_ctor_get_uint8(v_x_206_, 5);
v_decide_229_ = lean_ctor_get_uint8(v_x_206_, 6);
v_autoUnfold_230_ = lean_ctor_get_uint8(v_x_206_, 7);
v_failIfUnchanged_231_ = lean_ctor_get_uint8(v_x_206_, 8);
v_unfoldPartialApp_232_ = lean_ctor_get_uint8(v_x_206_, 9);
v_zetaDelta_233_ = lean_ctor_get_uint8(v_x_206_, 10);
v_index_234_ = lean_ctor_get_uint8(v_x_206_, 11);
v_zetaUnused_235_ = lean_ctor_get_uint8(v_x_206_, 12);
v_zetaHave_236_ = lean_ctor_get_uint8(v_x_206_, 13);
v_locals_237_ = lean_ctor_get_uint8(v_x_206_, 14);
v_instances_238_ = lean_ctor_get_uint8(v_x_206_, 15);
if (v_zeta_207_ == 0)
{
if (v_zeta_223_ == 0)
{
goto v___jp_264_;
}
else
{
return v_zeta_207_;
}
}
else
{
if (v_zeta_223_ == 0)
{
return v_zeta_223_;
}
else
{
goto v___jp_264_;
}
}
v___jp_239_:
{
if (v_instances_222_ == 0)
{
if (v_instances_238_ == 0)
{
return v___y_240_;
}
else
{
return v_instances_222_;
}
}
else
{
return v_instances_238_;
}
}
v___jp_241_:
{
if (v_locals_221_ == 0)
{
if (v_locals_237_ == 0)
{
v___y_240_ = v___y_242_;
goto v___jp_239_;
}
else
{
return v_locals_221_;
}
}
else
{
if (v_locals_237_ == 0)
{
return v_locals_237_;
}
else
{
v___y_240_ = v_locals_237_;
goto v___jp_239_;
}
}
}
v___jp_243_:
{
if (v_zetaHave_220_ == 0)
{
if (v_zetaHave_236_ == 0)
{
v___y_242_ = v___y_244_;
goto v___jp_241_;
}
else
{
return v_zetaHave_220_;
}
}
else
{
if (v_zetaHave_236_ == 0)
{
return v_zetaHave_236_;
}
else
{
v___y_242_ = v_zetaHave_236_;
goto v___jp_241_;
}
}
}
v___jp_245_:
{
if (v_zetaUnused_219_ == 0)
{
if (v_zetaUnused_235_ == 0)
{
v___y_244_ = v___y_246_;
goto v___jp_243_;
}
else
{
return v_zetaUnused_219_;
}
}
else
{
if (v_zetaUnused_235_ == 0)
{
return v_zetaUnused_235_;
}
else
{
v___y_244_ = v_zetaUnused_235_;
goto v___jp_243_;
}
}
}
v___jp_247_:
{
if (v_index_218_ == 0)
{
if (v_index_234_ == 0)
{
v___y_246_ = v___y_248_;
goto v___jp_245_;
}
else
{
return v_index_218_;
}
}
else
{
if (v_index_234_ == 0)
{
return v_index_234_;
}
else
{
v___y_246_ = v_index_234_;
goto v___jp_245_;
}
}
}
v___jp_249_:
{
if (v_zetaDelta_217_ == 0)
{
if (v_zetaDelta_233_ == 0)
{
v___y_248_ = v___y_250_;
goto v___jp_247_;
}
else
{
return v_zetaDelta_217_;
}
}
else
{
if (v_zetaDelta_233_ == 0)
{
return v_zetaDelta_233_;
}
else
{
v___y_248_ = v_zetaDelta_233_;
goto v___jp_247_;
}
}
}
v___jp_251_:
{
if (v_unfoldPartialApp_216_ == 0)
{
if (v_unfoldPartialApp_232_ == 0)
{
v___y_250_ = v___y_252_;
goto v___jp_249_;
}
else
{
return v_unfoldPartialApp_216_;
}
}
else
{
if (v_unfoldPartialApp_232_ == 0)
{
return v_unfoldPartialApp_232_;
}
else
{
v___y_250_ = v_unfoldPartialApp_232_;
goto v___jp_249_;
}
}
}
v___jp_253_:
{
if (v_failIfUnchanged_215_ == 0)
{
if (v_failIfUnchanged_231_ == 0)
{
v___y_252_ = v___y_254_;
goto v___jp_251_;
}
else
{
return v_failIfUnchanged_215_;
}
}
else
{
if (v_failIfUnchanged_231_ == 0)
{
return v_failIfUnchanged_231_;
}
else
{
v___y_252_ = v_failIfUnchanged_231_;
goto v___jp_251_;
}
}
}
v___jp_255_:
{
if (v_autoUnfold_214_ == 0)
{
if (v_autoUnfold_230_ == 0)
{
v___y_254_ = v___y_256_;
goto v___jp_253_;
}
else
{
return v_autoUnfold_214_;
}
}
else
{
if (v_autoUnfold_230_ == 0)
{
return v_autoUnfold_230_;
}
else
{
v___y_254_ = v_autoUnfold_230_;
goto v___jp_253_;
}
}
}
v___jp_257_:
{
if (v_decide_213_ == 0)
{
if (v_decide_229_ == 0)
{
v___y_256_ = v___y_258_;
goto v___jp_255_;
}
else
{
return v_decide_213_;
}
}
else
{
if (v_decide_229_ == 0)
{
return v_decide_229_;
}
else
{
v___y_256_ = v_decide_229_;
goto v___jp_255_;
}
}
}
v___jp_259_:
{
if (v___y_260_ == 0)
{
return v___y_260_;
}
else
{
if (v_proj_212_ == 0)
{
if (v_proj_228_ == 0)
{
v___y_258_ = v___y_260_;
goto v___jp_257_;
}
else
{
return v_proj_212_;
}
}
else
{
if (v_proj_228_ == 0)
{
return v_proj_228_;
}
else
{
v___y_258_ = v_proj_228_;
goto v___jp_257_;
}
}
}
}
v___jp_261_:
{
uint8_t v___x_262_; 
v___x_262_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_210_, v_etaStruct_226_);
if (v___x_262_ == 0)
{
return v___x_262_;
}
else
{
if (v_iota_211_ == 0)
{
if (v_iota_227_ == 0)
{
v___y_260_ = v___x_262_;
goto v___jp_259_;
}
else
{
return v_iota_211_;
}
}
else
{
v___y_260_ = v_iota_227_;
goto v___jp_259_;
}
}
}
v___jp_263_:
{
if (v_eta_209_ == 0)
{
if (v_eta_225_ == 0)
{
goto v___jp_261_;
}
else
{
return v_eta_209_;
}
}
else
{
if (v_eta_225_ == 0)
{
return v_eta_225_;
}
else
{
goto v___jp_261_;
}
}
}
v___jp_264_:
{
if (v_beta_208_ == 0)
{
if (v_beta_224_ == 0)
{
goto v___jp_263_;
}
else
{
return v_beta_208_;
}
}
else
{
if (v_beta_224_ == 0)
{
return v_beta_224_;
}
else
{
goto v___jp_263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DSimp_instBEqConfig_beq___boxed(lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
uint8_t v_res_267_; lean_object* v_r_268_; 
v_res_267_ = l_Lean_Meta_DSimp_instBEqConfig_beq(v_x_265_, v_x_266_);
lean_dec_ref(v_x_266_);
lean_dec_ref(v_x_265_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_defaultMaxSteps(void){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = lean_unsigned_to_nat(100000u);
return v___x_271_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(lean_object* v_x_281_, lean_object* v_x_282_){
_start:
{
if (lean_obj_tag(v_x_281_) == 0)
{
if (lean_obj_tag(v_x_282_) == 0)
{
uint8_t v___x_283_; 
v___x_283_ = 1;
return v___x_283_;
}
else
{
uint8_t v___x_284_; 
v___x_284_ = 0;
return v___x_284_;
}
}
else
{
if (lean_obj_tag(v_x_282_) == 0)
{
uint8_t v___x_285_; 
v___x_285_ = 0;
return v___x_285_;
}
else
{
lean_object* v_val_286_; lean_object* v_val_287_; uint8_t v___x_288_; 
v_val_286_ = lean_ctor_get(v_x_281_, 0);
v_val_287_ = lean_ctor_get(v_x_282_, 0);
v___x_288_ = lean_nat_dec_eq(v_val_286_, v_val_287_);
return v___x_288_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0___boxed(lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
uint8_t v_res_291_; lean_object* v_r_292_; 
v_res_291_ = l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(v_x_289_, v_x_290_);
lean_dec(v_x_290_);
lean_dec(v_x_289_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_instBEqConfig_beq(lean_object* v_x_293_, lean_object* v_x_294_){
_start:
{
lean_object* v_maxSteps_295_; lean_object* v_maxDischargeDepth_296_; uint8_t v_contextual_297_; uint8_t v_memoize_298_; uint8_t v_singlePass_299_; uint8_t v_zeta_300_; uint8_t v_beta_301_; uint8_t v_eta_302_; uint8_t v_etaStruct_303_; uint8_t v_iota_304_; uint8_t v_proj_305_; uint8_t v_decide_306_; uint8_t v_arith_307_; uint8_t v_autoUnfold_308_; uint8_t v_dsimp_309_; uint8_t v_failIfUnchanged_310_; uint8_t v_ground_311_; uint8_t v_unfoldPartialApp_312_; uint8_t v_zetaDelta_313_; uint8_t v_index_314_; uint8_t v_implicitDefEqProofs_315_; uint8_t v_zetaUnused_316_; uint8_t v_catchRuntime_317_; uint8_t v_zetaHave_318_; uint8_t v_letToHave_319_; uint8_t v_congrConsts_320_; uint8_t v_bitVecOfNat_321_; uint8_t v_warnExponents_322_; uint8_t v_suggestions_323_; lean_object* v_maxSuggestions_324_; uint8_t v_locals_325_; uint8_t v_instances_326_; lean_object* v_maxSteps_327_; lean_object* v_maxDischargeDepth_328_; uint8_t v_contextual_329_; uint8_t v_memoize_330_; uint8_t v_singlePass_331_; uint8_t v_zeta_332_; uint8_t v_beta_333_; uint8_t v_eta_334_; uint8_t v_etaStruct_335_; uint8_t v_iota_336_; uint8_t v_proj_337_; uint8_t v_decide_338_; uint8_t v_arith_339_; uint8_t v_autoUnfold_340_; uint8_t v_dsimp_341_; uint8_t v_failIfUnchanged_342_; uint8_t v_ground_343_; uint8_t v_unfoldPartialApp_344_; uint8_t v_zetaDelta_345_; uint8_t v_index_346_; uint8_t v_implicitDefEqProofs_347_; uint8_t v_zetaUnused_348_; uint8_t v_catchRuntime_349_; uint8_t v_zetaHave_350_; uint8_t v_letToHave_351_; uint8_t v_congrConsts_352_; uint8_t v_bitVecOfNat_353_; uint8_t v_warnExponents_354_; uint8_t v_suggestions_355_; lean_object* v_maxSuggestions_356_; uint8_t v_locals_357_; uint8_t v_instances_358_; uint8_t v___y_360_; uint8_t v___y_382_; uint8_t v___y_390_; uint8_t v___x_391_; 
v_maxSteps_295_ = lean_ctor_get(v_x_293_, 0);
v_maxDischargeDepth_296_ = lean_ctor_get(v_x_293_, 1);
v_contextual_297_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3);
v_memoize_298_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 1);
v_singlePass_299_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 2);
v_zeta_300_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 3);
v_beta_301_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 4);
v_eta_302_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 5);
v_etaStruct_303_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 6);
v_iota_304_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 7);
v_proj_305_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 8);
v_decide_306_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 9);
v_arith_307_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 10);
v_autoUnfold_308_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 11);
v_dsimp_309_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 12);
v_failIfUnchanged_310_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 13);
v_ground_311_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_312_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 15);
v_zetaDelta_313_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 16);
v_index_314_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_315_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 18);
v_zetaUnused_316_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 19);
v_catchRuntime_317_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 20);
v_zetaHave_318_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 21);
v_letToHave_319_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 22);
v_congrConsts_320_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 23);
v_bitVecOfNat_321_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 24);
v_warnExponents_322_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 25);
v_suggestions_323_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 26);
v_maxSuggestions_324_ = lean_ctor_get(v_x_293_, 2);
v_locals_325_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 27);
v_instances_326_ = lean_ctor_get_uint8(v_x_293_, sizeof(void*)*3 + 28);
v_maxSteps_327_ = lean_ctor_get(v_x_294_, 0);
v_maxDischargeDepth_328_ = lean_ctor_get(v_x_294_, 1);
v_contextual_329_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3);
v_memoize_330_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 1);
v_singlePass_331_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 2);
v_zeta_332_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 3);
v_beta_333_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 4);
v_eta_334_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 5);
v_etaStruct_335_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 6);
v_iota_336_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 7);
v_proj_337_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 8);
v_decide_338_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 9);
v_arith_339_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 10);
v_autoUnfold_340_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 11);
v_dsimp_341_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 12);
v_failIfUnchanged_342_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 13);
v_ground_343_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_344_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 15);
v_zetaDelta_345_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 16);
v_index_346_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_347_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 18);
v_zetaUnused_348_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 19);
v_catchRuntime_349_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 20);
v_zetaHave_350_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 21);
v_letToHave_351_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 22);
v_congrConsts_352_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 23);
v_bitVecOfNat_353_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 24);
v_warnExponents_354_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 25);
v_suggestions_355_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 26);
v_maxSuggestions_356_ = lean_ctor_get(v_x_294_, 2);
v_locals_357_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 27);
v_instances_358_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*3 + 28);
v___x_391_ = lean_nat_dec_eq(v_maxSteps_295_, v_maxSteps_327_);
if (v___x_391_ == 0)
{
return v___x_391_;
}
else
{
uint8_t v___x_392_; 
v___x_392_ = lean_nat_dec_eq(v_maxDischargeDepth_296_, v_maxDischargeDepth_328_);
if (v___x_392_ == 0)
{
return v___x_392_;
}
else
{
if (v_contextual_297_ == 0)
{
if (v_contextual_329_ == 0)
{
v___y_390_ = v___x_392_;
goto v___jp_389_;
}
else
{
return v_contextual_297_;
}
}
else
{
v___y_390_ = v_contextual_329_;
goto v___jp_389_;
}
}
}
v___jp_359_:
{
if (v___y_360_ == 0)
{
return v___y_360_;
}
else
{
if (v_instances_326_ == 0)
{
if (v_instances_358_ == 0)
{
return v___y_360_;
}
else
{
return v_instances_326_;
}
}
else
{
return v_instances_358_;
}
}
}
v___jp_361_:
{
uint8_t v___x_362_; 
v___x_362_ = l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(v_maxSuggestions_324_, v_maxSuggestions_356_);
if (v___x_362_ == 0)
{
return v___x_362_;
}
else
{
if (v_locals_325_ == 0)
{
if (v_locals_357_ == 0)
{
v___y_360_ = v___x_362_;
goto v___jp_359_;
}
else
{
return v_locals_325_;
}
}
else
{
v___y_360_ = v_locals_357_;
goto v___jp_359_;
}
}
}
v___jp_363_:
{
if (v_suggestions_323_ == 0)
{
if (v_suggestions_355_ == 0)
{
goto v___jp_361_;
}
else
{
return v_suggestions_323_;
}
}
else
{
if (v_suggestions_355_ == 0)
{
return v_suggestions_355_;
}
else
{
goto v___jp_361_;
}
}
}
v___jp_364_:
{
if (v_warnExponents_322_ == 0)
{
if (v_warnExponents_354_ == 0)
{
goto v___jp_363_;
}
else
{
return v_warnExponents_322_;
}
}
else
{
if (v_warnExponents_354_ == 0)
{
return v_warnExponents_354_;
}
else
{
goto v___jp_363_;
}
}
}
v___jp_365_:
{
if (v_bitVecOfNat_321_ == 0)
{
if (v_bitVecOfNat_353_ == 0)
{
goto v___jp_364_;
}
else
{
return v_bitVecOfNat_321_;
}
}
else
{
if (v_bitVecOfNat_353_ == 0)
{
return v_bitVecOfNat_353_;
}
else
{
goto v___jp_364_;
}
}
}
v___jp_366_:
{
if (v_congrConsts_320_ == 0)
{
if (v_congrConsts_352_ == 0)
{
goto v___jp_365_;
}
else
{
return v_congrConsts_320_;
}
}
else
{
if (v_congrConsts_352_ == 0)
{
return v_congrConsts_352_;
}
else
{
goto v___jp_365_;
}
}
}
v___jp_367_:
{
if (v_letToHave_319_ == 0)
{
if (v_letToHave_351_ == 0)
{
goto v___jp_366_;
}
else
{
return v_letToHave_319_;
}
}
else
{
if (v_letToHave_351_ == 0)
{
return v_letToHave_351_;
}
else
{
goto v___jp_366_;
}
}
}
v___jp_368_:
{
if (v_zetaHave_318_ == 0)
{
if (v_zetaHave_350_ == 0)
{
goto v___jp_367_;
}
else
{
return v_zetaHave_318_;
}
}
else
{
if (v_zetaHave_350_ == 0)
{
return v_zetaHave_350_;
}
else
{
goto v___jp_367_;
}
}
}
v___jp_369_:
{
if (v_catchRuntime_317_ == 0)
{
if (v_catchRuntime_349_ == 0)
{
goto v___jp_368_;
}
else
{
return v_catchRuntime_317_;
}
}
else
{
if (v_catchRuntime_349_ == 0)
{
return v_catchRuntime_349_;
}
else
{
goto v___jp_368_;
}
}
}
v___jp_370_:
{
if (v_zetaUnused_316_ == 0)
{
if (v_zetaUnused_348_ == 0)
{
goto v___jp_369_;
}
else
{
return v_zetaUnused_316_;
}
}
else
{
if (v_zetaUnused_348_ == 0)
{
return v_zetaUnused_348_;
}
else
{
goto v___jp_369_;
}
}
}
v___jp_371_:
{
if (v_implicitDefEqProofs_315_ == 0)
{
if (v_implicitDefEqProofs_347_ == 0)
{
goto v___jp_370_;
}
else
{
return v_implicitDefEqProofs_315_;
}
}
else
{
if (v_implicitDefEqProofs_347_ == 0)
{
return v_implicitDefEqProofs_347_;
}
else
{
goto v___jp_370_;
}
}
}
v___jp_372_:
{
if (v_index_314_ == 0)
{
if (v_index_346_ == 0)
{
goto v___jp_371_;
}
else
{
return v_index_314_;
}
}
else
{
if (v_index_346_ == 0)
{
return v_index_346_;
}
else
{
goto v___jp_371_;
}
}
}
v___jp_373_:
{
if (v_zetaDelta_313_ == 0)
{
if (v_zetaDelta_345_ == 0)
{
goto v___jp_372_;
}
else
{
return v_zetaDelta_313_;
}
}
else
{
if (v_zetaDelta_345_ == 0)
{
return v_zetaDelta_345_;
}
else
{
goto v___jp_372_;
}
}
}
v___jp_374_:
{
if (v_unfoldPartialApp_312_ == 0)
{
if (v_unfoldPartialApp_344_ == 0)
{
goto v___jp_373_;
}
else
{
return v_unfoldPartialApp_312_;
}
}
else
{
if (v_unfoldPartialApp_344_ == 0)
{
return v_unfoldPartialApp_344_;
}
else
{
goto v___jp_373_;
}
}
}
v___jp_375_:
{
if (v_ground_311_ == 0)
{
if (v_ground_343_ == 0)
{
goto v___jp_374_;
}
else
{
return v_ground_311_;
}
}
else
{
if (v_ground_343_ == 0)
{
return v_ground_343_;
}
else
{
goto v___jp_374_;
}
}
}
v___jp_376_:
{
if (v_failIfUnchanged_310_ == 0)
{
if (v_failIfUnchanged_342_ == 0)
{
goto v___jp_375_;
}
else
{
return v_failIfUnchanged_310_;
}
}
else
{
if (v_failIfUnchanged_342_ == 0)
{
return v_failIfUnchanged_342_;
}
else
{
goto v___jp_375_;
}
}
}
v___jp_377_:
{
if (v_dsimp_309_ == 0)
{
if (v_dsimp_341_ == 0)
{
goto v___jp_376_;
}
else
{
return v_dsimp_309_;
}
}
else
{
if (v_dsimp_341_ == 0)
{
return v_dsimp_341_;
}
else
{
goto v___jp_376_;
}
}
}
v___jp_378_:
{
if (v_autoUnfold_308_ == 0)
{
if (v_autoUnfold_340_ == 0)
{
goto v___jp_377_;
}
else
{
return v_autoUnfold_308_;
}
}
else
{
if (v_autoUnfold_340_ == 0)
{
return v_autoUnfold_340_;
}
else
{
goto v___jp_377_;
}
}
}
v___jp_379_:
{
if (v_arith_307_ == 0)
{
if (v_arith_339_ == 0)
{
goto v___jp_378_;
}
else
{
return v_arith_307_;
}
}
else
{
if (v_arith_339_ == 0)
{
return v_arith_339_;
}
else
{
goto v___jp_378_;
}
}
}
v___jp_380_:
{
if (v_decide_306_ == 0)
{
if (v_decide_338_ == 0)
{
goto v___jp_379_;
}
else
{
return v_decide_306_;
}
}
else
{
if (v_decide_338_ == 0)
{
return v_decide_338_;
}
else
{
goto v___jp_379_;
}
}
}
v___jp_381_:
{
if (v___y_382_ == 0)
{
return v___y_382_;
}
else
{
if (v_proj_305_ == 0)
{
if (v_proj_337_ == 0)
{
goto v___jp_380_;
}
else
{
return v_proj_305_;
}
}
else
{
if (v_proj_337_ == 0)
{
return v_proj_337_;
}
else
{
goto v___jp_380_;
}
}
}
}
v___jp_383_:
{
uint8_t v___x_384_; 
v___x_384_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_303_, v_etaStruct_335_);
if (v___x_384_ == 0)
{
return v___x_384_;
}
else
{
if (v_iota_304_ == 0)
{
if (v_iota_336_ == 0)
{
v___y_382_ = v___x_384_;
goto v___jp_381_;
}
else
{
return v_iota_304_;
}
}
else
{
v___y_382_ = v_iota_336_;
goto v___jp_381_;
}
}
}
v___jp_385_:
{
if (v_eta_302_ == 0)
{
if (v_eta_334_ == 0)
{
goto v___jp_383_;
}
else
{
return v_eta_302_;
}
}
else
{
if (v_eta_334_ == 0)
{
return v_eta_334_;
}
else
{
goto v___jp_383_;
}
}
}
v___jp_386_:
{
if (v_beta_301_ == 0)
{
if (v_beta_333_ == 0)
{
goto v___jp_385_;
}
else
{
return v_beta_301_;
}
}
else
{
if (v_beta_333_ == 0)
{
return v_beta_333_;
}
else
{
goto v___jp_385_;
}
}
}
v___jp_387_:
{
if (v_zeta_300_ == 0)
{
if (v_zeta_332_ == 0)
{
goto v___jp_386_;
}
else
{
return v_zeta_300_;
}
}
else
{
if (v_zeta_332_ == 0)
{
return v_zeta_332_;
}
else
{
goto v___jp_386_;
}
}
}
v___jp_388_:
{
if (v_singlePass_299_ == 0)
{
if (v_singlePass_331_ == 0)
{
goto v___jp_387_;
}
else
{
return v_singlePass_299_;
}
}
else
{
if (v_singlePass_331_ == 0)
{
return v_singlePass_331_;
}
else
{
goto v___jp_387_;
}
}
}
v___jp_389_:
{
if (v___y_390_ == 0)
{
return v___y_390_;
}
else
{
if (v_memoize_298_ == 0)
{
if (v_memoize_330_ == 0)
{
goto v___jp_388_;
}
else
{
return v_memoize_298_;
}
}
else
{
if (v_memoize_330_ == 0)
{
return v_memoize_330_;
}
else
{
goto v___jp_388_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instBEqConfig_beq___boxed(lean_object* v_x_393_, lean_object* v_x_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = l_Lean_Meta_Simp_instBEqConfig_beq(v_x_393_, v_x_394_);
lean_dec_ref(v_x_394_);
lean_dec_ref(v_x_393_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorIdx(lean_object* v_x_407_){
_start:
{
switch(lean_obj_tag(v_x_407_))
{
case 0:
{
lean_object* v___x_408_; 
v___x_408_ = lean_unsigned_to_nat(0u);
return v___x_408_;
}
case 1:
{
lean_object* v___x_409_; 
v___x_409_ = lean_unsigned_to_nat(1u);
return v___x_409_;
}
default: 
{
lean_object* v___x_410_; 
v___x_410_ = lean_unsigned_to_nat(2u);
return v___x_410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorIdx___boxed(lean_object* v_x_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Meta_Occurrences_ctorIdx(v_x_411_);
lean_dec(v_x_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim___redArg(lean_object* v_t_413_, lean_object* v_k_414_){
_start:
{
if (lean_obj_tag(v_t_413_) == 0)
{
return v_k_414_;
}
else
{
lean_object* v_idxs_415_; lean_object* v___x_416_; 
v_idxs_415_ = lean_ctor_get(v_t_413_, 0);
lean_inc(v_idxs_415_);
lean_dec(v_t_413_);
v___x_416_ = lean_apply_1(v_k_414_, v_idxs_415_);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim(lean_object* v_motive_417_, lean_object* v_ctorIdx_418_, lean_object* v_t_419_, lean_object* v_h_420_, lean_object* v_k_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_419_, v_k_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim___boxed(lean_object* v_motive_423_, lean_object* v_ctorIdx_424_, lean_object* v_t_425_, lean_object* v_h_426_, lean_object* v_k_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Meta_Occurrences_ctorElim(v_motive_423_, v_ctorIdx_424_, v_t_425_, v_h_426_, v_k_427_);
lean_dec(v_ctorIdx_424_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_all_elim___redArg(lean_object* v_t_429_, lean_object* v_all_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_429_, v_all_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_all_elim(lean_object* v_motive_432_, lean_object* v_t_433_, lean_object* v_h_434_, lean_object* v_all_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_433_, v_all_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_pos_elim___redArg(lean_object* v_t_437_, lean_object* v_pos_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_437_, v_pos_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_pos_elim(lean_object* v_motive_440_, lean_object* v_t_441_, lean_object* v_h_442_, lean_object* v_pos_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_441_, v_pos_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_neg_elim___redArg(lean_object* v_t_445_, lean_object* v_neg_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_445_, v_neg_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_neg_elim(lean_object* v_motive_448_, lean_object* v_t_449_, lean_object* v_h_450_, lean_object* v_neg_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_449_, v_neg_451_);
return v___x_452_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedOccurrences_default(void){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = lean_box(0);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedOccurrences(void){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = lean_box(0);
return v___x_454_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqOccurrences_beq(lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
lean_object* v_a_458_; lean_object* v_b_459_; 
switch(lean_obj_tag(v_x_455_))
{
case 0:
{
if (lean_obj_tag(v_x_456_) == 0)
{
uint8_t v___x_462_; 
v___x_462_ = 1;
return v___x_462_;
}
else
{
uint8_t v___x_463_; 
lean_dec(v_x_456_);
v___x_463_ = 0;
return v___x_463_;
}
}
case 1:
{
if (lean_obj_tag(v_x_456_) == 1)
{
lean_object* v_idxs_464_; lean_object* v_idxs_465_; 
v_idxs_464_ = lean_ctor_get(v_x_455_, 0);
lean_inc(v_idxs_464_);
lean_dec_ref(v_x_455_);
v_idxs_465_ = lean_ctor_get(v_x_456_, 0);
lean_inc(v_idxs_465_);
lean_dec_ref(v_x_456_);
v_a_458_ = v_idxs_464_;
v_b_459_ = v_idxs_465_;
goto v___jp_457_;
}
else
{
uint8_t v___x_466_; 
lean_dec_ref(v_x_455_);
lean_dec(v_x_456_);
v___x_466_ = 0;
return v___x_466_;
}
}
default: 
{
if (lean_obj_tag(v_x_456_) == 2)
{
lean_object* v_idxs_467_; lean_object* v_idxs_468_; 
v_idxs_467_ = lean_ctor_get(v_x_455_, 0);
lean_inc(v_idxs_467_);
lean_dec_ref(v_x_455_);
v_idxs_468_ = lean_ctor_get(v_x_456_, 0);
lean_inc(v_idxs_468_);
lean_dec_ref(v_x_456_);
v_a_458_ = v_idxs_467_;
v_b_459_ = v_idxs_468_;
goto v___jp_457_;
}
else
{
uint8_t v___x_469_; 
lean_dec_ref(v_x_455_);
lean_dec(v_x_456_);
v___x_469_ = 0;
return v___x_469_;
}
}
}
v___jp_457_:
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_461_ = l_instDecidableEqList___redArg(v___x_460_, v_a_458_, v_b_459_);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqOccurrences_beq___boxed(lean_object* v_x_470_, lean_object* v_x_471_){
_start:
{
uint8_t v_res_472_; lean_object* v_r_473_; 
v_res_472_ = l_Lean_Meta_instBEqOccurrences_beq(v_x_470_, v_x_471_);
v_r_473_ = lean_box(v_res_472_);
return v_r_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instCoeListNatOccurrences___lam__0(lean_object* v_idxs_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v_idxs_476_);
return v___x_477_;
}
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
