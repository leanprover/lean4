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
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toCtorIdx(uint8_t v_x_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Meta_TransparencyMode_ctorIdx(v_x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toCtorIdx___boxed(lean_object* v_x_21_){
_start:
{
uint8_t v_x_4__boxed_22_; lean_object* v_res_23_; 
v_x_4__boxed_22_ = lean_unbox(v_x_21_);
v_res_23_ = l_Lean_Meta_TransparencyMode_toCtorIdx(v_x_4__boxed_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___redArg(lean_object* v_k_24_){
_start:
{
lean_inc(v_k_24_);
return v_k_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___redArg___boxed(lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Meta_TransparencyMode_ctorElim___redArg(v_k_25_);
lean_dec(v_k_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim(lean_object* v_motive_27_, lean_object* v_ctorIdx_28_, uint8_t v_t_29_, lean_object* v_h_30_, lean_object* v_k_31_){
_start:
{
lean_inc(v_k_31_);
return v_k_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___boxed(lean_object* v_motive_32_, lean_object* v_ctorIdx_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_k_36_){
_start:
{
uint8_t v_t_boxed_37_; lean_object* v_res_38_; 
v_t_boxed_37_ = lean_unbox(v_t_34_);
v_res_38_ = l_Lean_Meta_TransparencyMode_ctorElim(v_motive_32_, v_ctorIdx_33_, v_t_boxed_37_, v_h_35_, v_k_36_);
lean_dec(v_k_36_);
lean_dec(v_ctorIdx_33_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___redArg(lean_object* v_all_39_){
_start:
{
lean_inc(v_all_39_);
return v_all_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___redArg___boxed(lean_object* v_all_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_Meta_TransparencyMode_all_elim___redArg(v_all_40_);
lean_dec(v_all_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim(lean_object* v_motive_42_, uint8_t v_t_43_, lean_object* v_h_44_, lean_object* v_all_45_){
_start:
{
lean_inc(v_all_45_);
return v_all_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_all_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Meta_TransparencyMode_all_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_all_49_);
lean_dec(v_all_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___redArg(lean_object* v_default_52_){
_start:
{
lean_inc(v_default_52_);
return v_default_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___redArg___boxed(lean_object* v_default_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Meta_TransparencyMode_default_elim___redArg(v_default_53_);
lean_dec(v_default_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_default_58_){
_start:
{
lean_inc(v_default_58_);
return v_default_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___boxed(lean_object* v_motive_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_default_62_){
_start:
{
uint8_t v_t_boxed_63_; lean_object* v_res_64_; 
v_t_boxed_63_ = lean_unbox(v_t_60_);
v_res_64_ = l_Lean_Meta_TransparencyMode_default_elim(v_motive_59_, v_t_boxed_63_, v_h_61_, v_default_62_);
lean_dec(v_default_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim___redArg(lean_object* v_reducible_65_){
_start:
{
lean_inc(v_reducible_65_);
return v_reducible_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim___redArg___boxed(lean_object* v_reducible_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Meta_TransparencyMode_reducible_elim___redArg(v_reducible_66_);
lean_dec(v_reducible_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim(lean_object* v_motive_68_, uint8_t v_t_69_, lean_object* v_h_70_, lean_object* v_reducible_71_){
_start:
{
lean_inc(v_reducible_71_);
return v_reducible_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim___boxed(lean_object* v_motive_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_reducible_75_){
_start:
{
uint8_t v_t_boxed_76_; lean_object* v_res_77_; 
v_t_boxed_76_ = lean_unbox(v_t_73_);
v_res_77_ = l_Lean_Meta_TransparencyMode_reducible_elim(v_motive_72_, v_t_boxed_76_, v_h_74_, v_reducible_75_);
lean_dec(v_reducible_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___redArg(lean_object* v_instances_78_){
_start:
{
lean_inc(v_instances_78_);
return v_instances_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___redArg___boxed(lean_object* v_instances_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_Meta_TransparencyMode_instances_elim___redArg(v_instances_79_);
lean_dec(v_instances_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim(lean_object* v_motive_81_, uint8_t v_t_82_, lean_object* v_h_83_, lean_object* v_instances_84_){
_start:
{
lean_inc(v_instances_84_);
return v_instances_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___boxed(lean_object* v_motive_85_, lean_object* v_t_86_, lean_object* v_h_87_, lean_object* v_instances_88_){
_start:
{
uint8_t v_t_boxed_89_; lean_object* v_res_90_; 
v_t_boxed_89_ = lean_unbox(v_t_86_);
v_res_90_ = l_Lean_Meta_TransparencyMode_instances_elim(v_motive_85_, v_t_boxed_89_, v_h_87_, v_instances_88_);
lean_dec(v_instances_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___redArg(lean_object* v_none_91_){
_start:
{
lean_inc(v_none_91_);
return v_none_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___redArg___boxed(lean_object* v_none_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Meta_TransparencyMode_none_elim___redArg(v_none_92_);
lean_dec(v_none_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim(lean_object* v_motive_94_, uint8_t v_t_95_, lean_object* v_h_96_, lean_object* v_none_97_){
_start:
{
lean_inc(v_none_97_);
return v_none_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___boxed(lean_object* v_motive_98_, lean_object* v_t_99_, lean_object* v_h_100_, lean_object* v_none_101_){
_start:
{
uint8_t v_t_boxed_102_; lean_object* v_res_103_; 
v_t_boxed_102_ = lean_unbox(v_t_99_);
v_res_103_ = l_Lean_Meta_TransparencyMode_none_elim(v_motive_98_, v_t_boxed_102_, v_h_100_, v_none_101_);
lean_dec(v_none_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim___redArg(lean_object* v_implicit_104_){
_start:
{
lean_inc(v_implicit_104_);
return v_implicit_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim___redArg___boxed(lean_object* v_implicit_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_Meta_TransparencyMode_implicit_elim___redArg(v_implicit_105_);
lean_dec(v_implicit_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim(lean_object* v_motive_107_, uint8_t v_t_108_, lean_object* v_h_109_, lean_object* v_implicit_110_){
_start:
{
lean_inc(v_implicit_110_);
return v_implicit_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_implicit_elim___boxed(lean_object* v_motive_111_, lean_object* v_t_112_, lean_object* v_h_113_, lean_object* v_implicit_114_){
_start:
{
uint8_t v_t_boxed_115_; lean_object* v_res_116_; 
v_t_boxed_115_ = lean_unbox(v_t_112_);
v_res_116_ = l_Lean_Meta_TransparencyMode_implicit_elim(v_motive_111_, v_t_boxed_115_, v_h_113_, v_implicit_114_);
lean_dec(v_implicit_114_);
return v_res_116_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedTransparencyMode_default(void){
_start:
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedTransparencyMode(void){
_start:
{
uint8_t v___x_118_; 
v___x_118_ = 0;
return v___x_118_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t v_x_119_, uint8_t v_y_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_121_ = l_Lean_Meta_TransparencyMode_ctorIdx(v_x_119_);
v___x_122_ = l_Lean_Meta_TransparencyMode_ctorIdx(v_y_120_);
v___x_123_ = lean_nat_dec_eq(v___x_121_, v___x_122_);
lean_dec(v___x_122_);
lean_dec(v___x_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqTransparencyMode_beq___boxed(lean_object* v_x_124_, lean_object* v_y_125_){
_start:
{
uint8_t v_x_17__boxed_126_; uint8_t v_y_18__boxed_127_; uint8_t v_res_128_; lean_object* v_r_129_; 
v_x_17__boxed_126_ = lean_unbox(v_x_124_);
v_y_18__boxed_127_ = lean_unbox(v_y_125_);
v_res_128_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_x_17__boxed_126_, v_y_18__boxed_127_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorIdx(uint8_t v_x_132_){
_start:
{
switch(v_x_132_)
{
case 0:
{
lean_object* v___x_133_; 
v___x_133_ = lean_unsigned_to_nat(0u);
return v___x_133_;
}
case 1:
{
lean_object* v___x_134_; 
v___x_134_ = lean_unsigned_to_nat(1u);
return v___x_134_;
}
default: 
{
lean_object* v___x_135_; 
v___x_135_ = lean_unsigned_to_nat(2u);
return v___x_135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorIdx___boxed(lean_object* v_x_136_){
_start:
{
uint8_t v_x_boxed_137_; lean_object* v_res_138_; 
v_x_boxed_137_ = lean_unbox(v_x_136_);
v_res_138_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_x_boxed_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_toCtorIdx(uint8_t v_x_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_toCtorIdx___boxed(lean_object* v_x_141_){
_start:
{
uint8_t v_x_4__boxed_142_; lean_object* v_res_143_; 
v_x_4__boxed_142_ = lean_unbox(v_x_141_);
v_res_143_ = l_Lean_Meta_EtaStructMode_toCtorIdx(v_x_4__boxed_142_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___redArg(lean_object* v_k_144_){
_start:
{
lean_inc(v_k_144_);
return v_k_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___redArg___boxed(lean_object* v_k_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Meta_EtaStructMode_ctorElim___redArg(v_k_145_);
lean_dec(v_k_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim(lean_object* v_motive_147_, lean_object* v_ctorIdx_148_, uint8_t v_t_149_, lean_object* v_h_150_, lean_object* v_k_151_){
_start:
{
lean_inc(v_k_151_);
return v_k_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___boxed(lean_object* v_motive_152_, lean_object* v_ctorIdx_153_, lean_object* v_t_154_, lean_object* v_h_155_, lean_object* v_k_156_){
_start:
{
uint8_t v_t_boxed_157_; lean_object* v_res_158_; 
v_t_boxed_157_ = lean_unbox(v_t_154_);
v_res_158_ = l_Lean_Meta_EtaStructMode_ctorElim(v_motive_152_, v_ctorIdx_153_, v_t_boxed_157_, v_h_155_, v_k_156_);
lean_dec(v_k_156_);
lean_dec(v_ctorIdx_153_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___redArg(lean_object* v_all_159_){
_start:
{
lean_inc(v_all_159_);
return v_all_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___redArg___boxed(lean_object* v_all_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Meta_EtaStructMode_all_elim___redArg(v_all_160_);
lean_dec(v_all_160_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim(lean_object* v_motive_162_, uint8_t v_t_163_, lean_object* v_h_164_, lean_object* v_all_165_){
_start:
{
lean_inc(v_all_165_);
return v_all_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___boxed(lean_object* v_motive_166_, lean_object* v_t_167_, lean_object* v_h_168_, lean_object* v_all_169_){
_start:
{
uint8_t v_t_boxed_170_; lean_object* v_res_171_; 
v_t_boxed_170_ = lean_unbox(v_t_167_);
v_res_171_ = l_Lean_Meta_EtaStructMode_all_elim(v_motive_166_, v_t_boxed_170_, v_h_168_, v_all_169_);
lean_dec(v_all_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___redArg(lean_object* v_notClasses_172_){
_start:
{
lean_inc(v_notClasses_172_);
return v_notClasses_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___redArg___boxed(lean_object* v_notClasses_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Meta_EtaStructMode_notClasses_elim___redArg(v_notClasses_173_);
lean_dec(v_notClasses_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim(lean_object* v_motive_175_, uint8_t v_t_176_, lean_object* v_h_177_, lean_object* v_notClasses_178_){
_start:
{
lean_inc(v_notClasses_178_);
return v_notClasses_178_;
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim(lean_object* v_motive_188_, uint8_t v_t_189_, lean_object* v_h_190_, lean_object* v_none_191_){
_start:
{
lean_inc(v_none_191_);
return v_none_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___boxed(lean_object* v_motive_192_, lean_object* v_t_193_, lean_object* v_h_194_, lean_object* v_none_195_){
_start:
{
uint8_t v_t_boxed_196_; lean_object* v_res_197_; 
v_t_boxed_196_ = lean_unbox(v_t_193_);
v_res_197_ = l_Lean_Meta_EtaStructMode_none_elim(v_motive_192_, v_t_boxed_196_, v_h_194_, v_none_195_);
lean_dec(v_none_195_);
return v_res_197_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedEtaStructMode_default(void){
_start:
{
uint8_t v___x_198_; 
v___x_198_ = 0;
return v___x_198_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedEtaStructMode(void){
_start:
{
uint8_t v___x_199_; 
v___x_199_ = 0;
return v___x_199_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqEtaStructMode_beq(uint8_t v_x_200_, uint8_t v_y_201_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_202_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_x_200_);
v___x_203_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_y_201_);
v___x_204_ = lean_nat_dec_eq(v___x_202_, v___x_203_);
lean_dec(v___x_203_);
lean_dec(v___x_202_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqEtaStructMode_beq___boxed(lean_object* v_x_205_, lean_object* v_y_206_){
_start:
{
uint8_t v_x_17__boxed_207_; uint8_t v_y_18__boxed_208_; uint8_t v_res_209_; lean_object* v_r_210_; 
v_x_17__boxed_207_ = lean_unbox(v_x_205_);
v_y_18__boxed_208_ = lean_unbox(v_y_206_);
v_res_209_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_x_17__boxed_207_, v_y_18__boxed_208_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DSimp_instBEqConfig_beq(lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
uint8_t v_zeta_221_; uint8_t v_beta_222_; uint8_t v_eta_223_; uint8_t v_etaStruct_224_; uint8_t v_iota_225_; uint8_t v_proj_226_; uint8_t v_decide_227_; uint8_t v_autoUnfold_228_; uint8_t v_failIfUnchanged_229_; uint8_t v_unfoldPartialApp_230_; uint8_t v_zetaDelta_231_; uint8_t v_index_232_; uint8_t v_zetaUnused_233_; uint8_t v_zetaHave_234_; uint8_t v_locals_235_; uint8_t v_instances_236_; uint8_t v_zeta_237_; uint8_t v_beta_238_; uint8_t v_eta_239_; uint8_t v_etaStruct_240_; uint8_t v_iota_241_; uint8_t v_proj_242_; uint8_t v_decide_243_; uint8_t v_autoUnfold_244_; uint8_t v_failIfUnchanged_245_; uint8_t v_unfoldPartialApp_246_; uint8_t v_zetaDelta_247_; uint8_t v_index_248_; uint8_t v_zetaUnused_249_; uint8_t v_zetaHave_250_; uint8_t v_locals_251_; uint8_t v_instances_252_; uint8_t v___y_254_; uint8_t v___y_256_; uint8_t v___y_258_; uint8_t v___y_260_; uint8_t v___y_262_; uint8_t v___y_264_; uint8_t v___y_266_; uint8_t v___y_268_; uint8_t v___y_270_; uint8_t v___y_272_; uint8_t v___y_274_; 
v_zeta_221_ = lean_ctor_get_uint8(v_x_219_, 0);
v_beta_222_ = lean_ctor_get_uint8(v_x_219_, 1);
v_eta_223_ = lean_ctor_get_uint8(v_x_219_, 2);
v_etaStruct_224_ = lean_ctor_get_uint8(v_x_219_, 3);
v_iota_225_ = lean_ctor_get_uint8(v_x_219_, 4);
v_proj_226_ = lean_ctor_get_uint8(v_x_219_, 5);
v_decide_227_ = lean_ctor_get_uint8(v_x_219_, 6);
v_autoUnfold_228_ = lean_ctor_get_uint8(v_x_219_, 7);
v_failIfUnchanged_229_ = lean_ctor_get_uint8(v_x_219_, 8);
v_unfoldPartialApp_230_ = lean_ctor_get_uint8(v_x_219_, 9);
v_zetaDelta_231_ = lean_ctor_get_uint8(v_x_219_, 10);
v_index_232_ = lean_ctor_get_uint8(v_x_219_, 11);
v_zetaUnused_233_ = lean_ctor_get_uint8(v_x_219_, 12);
v_zetaHave_234_ = lean_ctor_get_uint8(v_x_219_, 13);
v_locals_235_ = lean_ctor_get_uint8(v_x_219_, 14);
v_instances_236_ = lean_ctor_get_uint8(v_x_219_, 15);
v_zeta_237_ = lean_ctor_get_uint8(v_x_220_, 0);
v_beta_238_ = lean_ctor_get_uint8(v_x_220_, 1);
v_eta_239_ = lean_ctor_get_uint8(v_x_220_, 2);
v_etaStruct_240_ = lean_ctor_get_uint8(v_x_220_, 3);
v_iota_241_ = lean_ctor_get_uint8(v_x_220_, 4);
v_proj_242_ = lean_ctor_get_uint8(v_x_220_, 5);
v_decide_243_ = lean_ctor_get_uint8(v_x_220_, 6);
v_autoUnfold_244_ = lean_ctor_get_uint8(v_x_220_, 7);
v_failIfUnchanged_245_ = lean_ctor_get_uint8(v_x_220_, 8);
v_unfoldPartialApp_246_ = lean_ctor_get_uint8(v_x_220_, 9);
v_zetaDelta_247_ = lean_ctor_get_uint8(v_x_220_, 10);
v_index_248_ = lean_ctor_get_uint8(v_x_220_, 11);
v_zetaUnused_249_ = lean_ctor_get_uint8(v_x_220_, 12);
v_zetaHave_250_ = lean_ctor_get_uint8(v_x_220_, 13);
v_locals_251_ = lean_ctor_get_uint8(v_x_220_, 14);
v_instances_252_ = lean_ctor_get_uint8(v_x_220_, 15);
if (v_zeta_221_ == 0)
{
if (v_zeta_237_ == 0)
{
goto v___jp_278_;
}
else
{
return v_zeta_221_;
}
}
else
{
if (v_zeta_237_ == 0)
{
return v_zeta_237_;
}
else
{
goto v___jp_278_;
}
}
v___jp_253_:
{
if (v_instances_236_ == 0)
{
if (v_instances_252_ == 0)
{
return v___y_254_;
}
else
{
return v_instances_236_;
}
}
else
{
return v_instances_252_;
}
}
v___jp_255_:
{
if (v_locals_235_ == 0)
{
if (v_locals_251_ == 0)
{
v___y_254_ = v___y_256_;
goto v___jp_253_;
}
else
{
return v_locals_235_;
}
}
else
{
if (v_locals_251_ == 0)
{
return v_locals_251_;
}
else
{
v___y_254_ = v_locals_251_;
goto v___jp_253_;
}
}
}
v___jp_257_:
{
if (v_zetaHave_234_ == 0)
{
if (v_zetaHave_250_ == 0)
{
v___y_256_ = v___y_258_;
goto v___jp_255_;
}
else
{
return v_zetaHave_234_;
}
}
else
{
if (v_zetaHave_250_ == 0)
{
return v_zetaHave_250_;
}
else
{
v___y_256_ = v_zetaHave_250_;
goto v___jp_255_;
}
}
}
v___jp_259_:
{
if (v_zetaUnused_233_ == 0)
{
if (v_zetaUnused_249_ == 0)
{
v___y_258_ = v___y_260_;
goto v___jp_257_;
}
else
{
return v_zetaUnused_233_;
}
}
else
{
if (v_zetaUnused_249_ == 0)
{
return v_zetaUnused_249_;
}
else
{
v___y_258_ = v_zetaUnused_249_;
goto v___jp_257_;
}
}
}
v___jp_261_:
{
if (v_index_232_ == 0)
{
if (v_index_248_ == 0)
{
v___y_260_ = v___y_262_;
goto v___jp_259_;
}
else
{
return v_index_232_;
}
}
else
{
if (v_index_248_ == 0)
{
return v_index_248_;
}
else
{
v___y_260_ = v_index_248_;
goto v___jp_259_;
}
}
}
v___jp_263_:
{
if (v_zetaDelta_231_ == 0)
{
if (v_zetaDelta_247_ == 0)
{
v___y_262_ = v___y_264_;
goto v___jp_261_;
}
else
{
return v_zetaDelta_231_;
}
}
else
{
if (v_zetaDelta_247_ == 0)
{
return v_zetaDelta_247_;
}
else
{
v___y_262_ = v_zetaDelta_247_;
goto v___jp_261_;
}
}
}
v___jp_265_:
{
if (v_unfoldPartialApp_230_ == 0)
{
if (v_unfoldPartialApp_246_ == 0)
{
v___y_264_ = v___y_266_;
goto v___jp_263_;
}
else
{
return v_unfoldPartialApp_230_;
}
}
else
{
if (v_unfoldPartialApp_246_ == 0)
{
return v_unfoldPartialApp_246_;
}
else
{
v___y_264_ = v_unfoldPartialApp_246_;
goto v___jp_263_;
}
}
}
v___jp_267_:
{
if (v_failIfUnchanged_229_ == 0)
{
if (v_failIfUnchanged_245_ == 0)
{
v___y_266_ = v___y_268_;
goto v___jp_265_;
}
else
{
return v_failIfUnchanged_229_;
}
}
else
{
if (v_failIfUnchanged_245_ == 0)
{
return v_failIfUnchanged_245_;
}
else
{
v___y_266_ = v_failIfUnchanged_245_;
goto v___jp_265_;
}
}
}
v___jp_269_:
{
if (v_autoUnfold_228_ == 0)
{
if (v_autoUnfold_244_ == 0)
{
v___y_268_ = v___y_270_;
goto v___jp_267_;
}
else
{
return v_autoUnfold_228_;
}
}
else
{
if (v_autoUnfold_244_ == 0)
{
return v_autoUnfold_244_;
}
else
{
v___y_268_ = v_autoUnfold_244_;
goto v___jp_267_;
}
}
}
v___jp_271_:
{
if (v_decide_227_ == 0)
{
if (v_decide_243_ == 0)
{
v___y_270_ = v___y_272_;
goto v___jp_269_;
}
else
{
return v_decide_227_;
}
}
else
{
if (v_decide_243_ == 0)
{
return v_decide_243_;
}
else
{
v___y_270_ = v_decide_243_;
goto v___jp_269_;
}
}
}
v___jp_273_:
{
if (v___y_274_ == 0)
{
return v___y_274_;
}
else
{
if (v_proj_226_ == 0)
{
if (v_proj_242_ == 0)
{
v___y_272_ = v___y_274_;
goto v___jp_271_;
}
else
{
return v_proj_226_;
}
}
else
{
if (v_proj_242_ == 0)
{
return v_proj_242_;
}
else
{
v___y_272_ = v_proj_242_;
goto v___jp_271_;
}
}
}
}
v___jp_275_:
{
uint8_t v___x_276_; 
v___x_276_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_224_, v_etaStruct_240_);
if (v___x_276_ == 0)
{
return v___x_276_;
}
else
{
if (v_iota_225_ == 0)
{
if (v_iota_241_ == 0)
{
v___y_274_ = v___x_276_;
goto v___jp_273_;
}
else
{
return v_iota_225_;
}
}
else
{
v___y_274_ = v_iota_241_;
goto v___jp_273_;
}
}
}
v___jp_277_:
{
if (v_eta_223_ == 0)
{
if (v_eta_239_ == 0)
{
goto v___jp_275_;
}
else
{
return v_eta_223_;
}
}
else
{
if (v_eta_239_ == 0)
{
return v_eta_239_;
}
else
{
goto v___jp_275_;
}
}
}
v___jp_278_:
{
if (v_beta_222_ == 0)
{
if (v_beta_238_ == 0)
{
goto v___jp_277_;
}
else
{
return v_beta_222_;
}
}
else
{
if (v_beta_238_ == 0)
{
return v_beta_238_;
}
else
{
goto v___jp_277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DSimp_instBEqConfig_beq___boxed(lean_object* v_x_279_, lean_object* v_x_280_){
_start:
{
uint8_t v_res_281_; lean_object* v_r_282_; 
v_res_281_ = l_Lean_Meta_DSimp_instBEqConfig_beq(v_x_279_, v_x_280_);
lean_dec_ref(v_x_280_);
lean_dec_ref(v_x_279_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_defaultMaxSteps(void){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = lean_unsigned_to_nat(100000u);
return v___x_285_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
if (lean_obj_tag(v_x_295_) == 0)
{
if (lean_obj_tag(v_x_296_) == 0)
{
uint8_t v___x_297_; 
v___x_297_ = 1;
return v___x_297_;
}
else
{
uint8_t v___x_298_; 
v___x_298_ = 0;
return v___x_298_;
}
}
else
{
if (lean_obj_tag(v_x_296_) == 0)
{
uint8_t v___x_299_; 
v___x_299_ = 0;
return v___x_299_;
}
else
{
lean_object* v_val_300_; lean_object* v_val_301_; uint8_t v___x_302_; 
v_val_300_ = lean_ctor_get(v_x_295_, 0);
v_val_301_ = lean_ctor_get(v_x_296_, 0);
v___x_302_ = lean_nat_dec_eq(v_val_300_, v_val_301_);
return v___x_302_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0___boxed(lean_object* v_x_303_, lean_object* v_x_304_){
_start:
{
uint8_t v_res_305_; lean_object* v_r_306_; 
v_res_305_ = l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(v_x_303_, v_x_304_);
lean_dec(v_x_304_);
lean_dec(v_x_303_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_instBEqConfig_beq(lean_object* v_x_307_, lean_object* v_x_308_){
_start:
{
lean_object* v_maxSteps_309_; lean_object* v_maxDischargeDepth_310_; uint8_t v_contextual_311_; uint8_t v_memoize_312_; uint8_t v_singlePass_313_; uint8_t v_zeta_314_; uint8_t v_beta_315_; uint8_t v_eta_316_; uint8_t v_etaStruct_317_; uint8_t v_iota_318_; uint8_t v_proj_319_; uint8_t v_decide_320_; uint8_t v_arith_321_; uint8_t v_autoUnfold_322_; uint8_t v_dsimp_323_; uint8_t v_failIfUnchanged_324_; uint8_t v_ground_325_; uint8_t v_unfoldPartialApp_326_; uint8_t v_zetaDelta_327_; uint8_t v_index_328_; uint8_t v_implicitDefEqProofs_329_; uint8_t v_zetaUnused_330_; uint8_t v_catchRuntime_331_; uint8_t v_zetaHave_332_; uint8_t v_letToHave_333_; uint8_t v_congrConsts_334_; uint8_t v_bitVecOfNat_335_; uint8_t v_warnExponents_336_; uint8_t v_suggestions_337_; lean_object* v_maxSuggestions_338_; uint8_t v_locals_339_; uint8_t v_instances_340_; lean_object* v_maxSteps_341_; lean_object* v_maxDischargeDepth_342_; uint8_t v_contextual_343_; uint8_t v_memoize_344_; uint8_t v_singlePass_345_; uint8_t v_zeta_346_; uint8_t v_beta_347_; uint8_t v_eta_348_; uint8_t v_etaStruct_349_; uint8_t v_iota_350_; uint8_t v_proj_351_; uint8_t v_decide_352_; uint8_t v_arith_353_; uint8_t v_autoUnfold_354_; uint8_t v_dsimp_355_; uint8_t v_failIfUnchanged_356_; uint8_t v_ground_357_; uint8_t v_unfoldPartialApp_358_; uint8_t v_zetaDelta_359_; uint8_t v_index_360_; uint8_t v_implicitDefEqProofs_361_; uint8_t v_zetaUnused_362_; uint8_t v_catchRuntime_363_; uint8_t v_zetaHave_364_; uint8_t v_letToHave_365_; uint8_t v_congrConsts_366_; uint8_t v_bitVecOfNat_367_; uint8_t v_warnExponents_368_; uint8_t v_suggestions_369_; lean_object* v_maxSuggestions_370_; uint8_t v_locals_371_; uint8_t v_instances_372_; uint8_t v___y_374_; uint8_t v___y_396_; uint8_t v___y_404_; uint8_t v___x_405_; 
v_maxSteps_309_ = lean_ctor_get(v_x_307_, 0);
v_maxDischargeDepth_310_ = lean_ctor_get(v_x_307_, 1);
v_contextual_311_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3);
v_memoize_312_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 1);
v_singlePass_313_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 2);
v_zeta_314_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 3);
v_beta_315_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 4);
v_eta_316_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 5);
v_etaStruct_317_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 6);
v_iota_318_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 7);
v_proj_319_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 8);
v_decide_320_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 9);
v_arith_321_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 10);
v_autoUnfold_322_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 11);
v_dsimp_323_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 12);
v_failIfUnchanged_324_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 13);
v_ground_325_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_326_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 15);
v_zetaDelta_327_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 16);
v_index_328_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_329_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 18);
v_zetaUnused_330_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 19);
v_catchRuntime_331_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 20);
v_zetaHave_332_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 21);
v_letToHave_333_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 22);
v_congrConsts_334_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 23);
v_bitVecOfNat_335_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 24);
v_warnExponents_336_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 25);
v_suggestions_337_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 26);
v_maxSuggestions_338_ = lean_ctor_get(v_x_307_, 2);
v_locals_339_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 27);
v_instances_340_ = lean_ctor_get_uint8(v_x_307_, sizeof(void*)*3 + 28);
v_maxSteps_341_ = lean_ctor_get(v_x_308_, 0);
v_maxDischargeDepth_342_ = lean_ctor_get(v_x_308_, 1);
v_contextual_343_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3);
v_memoize_344_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 1);
v_singlePass_345_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 2);
v_zeta_346_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 3);
v_beta_347_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 4);
v_eta_348_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 5);
v_etaStruct_349_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 6);
v_iota_350_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 7);
v_proj_351_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 8);
v_decide_352_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 9);
v_arith_353_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 10);
v_autoUnfold_354_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 11);
v_dsimp_355_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 12);
v_failIfUnchanged_356_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 13);
v_ground_357_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_358_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 15);
v_zetaDelta_359_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 16);
v_index_360_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_361_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 18);
v_zetaUnused_362_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 19);
v_catchRuntime_363_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 20);
v_zetaHave_364_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 21);
v_letToHave_365_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 22);
v_congrConsts_366_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 23);
v_bitVecOfNat_367_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 24);
v_warnExponents_368_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 25);
v_suggestions_369_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 26);
v_maxSuggestions_370_ = lean_ctor_get(v_x_308_, 2);
v_locals_371_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 27);
v_instances_372_ = lean_ctor_get_uint8(v_x_308_, sizeof(void*)*3 + 28);
v___x_405_ = lean_nat_dec_eq(v_maxSteps_309_, v_maxSteps_341_);
if (v___x_405_ == 0)
{
return v___x_405_;
}
else
{
uint8_t v___x_406_; 
v___x_406_ = lean_nat_dec_eq(v_maxDischargeDepth_310_, v_maxDischargeDepth_342_);
if (v___x_406_ == 0)
{
return v___x_406_;
}
else
{
if (v_contextual_311_ == 0)
{
if (v_contextual_343_ == 0)
{
v___y_404_ = v___x_406_;
goto v___jp_403_;
}
else
{
return v_contextual_311_;
}
}
else
{
v___y_404_ = v_contextual_343_;
goto v___jp_403_;
}
}
}
v___jp_373_:
{
if (v___y_374_ == 0)
{
return v___y_374_;
}
else
{
if (v_instances_340_ == 0)
{
if (v_instances_372_ == 0)
{
return v___y_374_;
}
else
{
return v_instances_340_;
}
}
else
{
return v_instances_372_;
}
}
}
v___jp_375_:
{
uint8_t v___x_376_; 
v___x_376_ = l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(v_maxSuggestions_338_, v_maxSuggestions_370_);
if (v___x_376_ == 0)
{
return v___x_376_;
}
else
{
if (v_locals_339_ == 0)
{
if (v_locals_371_ == 0)
{
v___y_374_ = v___x_376_;
goto v___jp_373_;
}
else
{
return v_locals_339_;
}
}
else
{
v___y_374_ = v_locals_371_;
goto v___jp_373_;
}
}
}
v___jp_377_:
{
if (v_suggestions_337_ == 0)
{
if (v_suggestions_369_ == 0)
{
goto v___jp_375_;
}
else
{
return v_suggestions_337_;
}
}
else
{
if (v_suggestions_369_ == 0)
{
return v_suggestions_369_;
}
else
{
goto v___jp_375_;
}
}
}
v___jp_378_:
{
if (v_warnExponents_336_ == 0)
{
if (v_warnExponents_368_ == 0)
{
goto v___jp_377_;
}
else
{
return v_warnExponents_336_;
}
}
else
{
if (v_warnExponents_368_ == 0)
{
return v_warnExponents_368_;
}
else
{
goto v___jp_377_;
}
}
}
v___jp_379_:
{
if (v_bitVecOfNat_335_ == 0)
{
if (v_bitVecOfNat_367_ == 0)
{
goto v___jp_378_;
}
else
{
return v_bitVecOfNat_335_;
}
}
else
{
if (v_bitVecOfNat_367_ == 0)
{
return v_bitVecOfNat_367_;
}
else
{
goto v___jp_378_;
}
}
}
v___jp_380_:
{
if (v_congrConsts_334_ == 0)
{
if (v_congrConsts_366_ == 0)
{
goto v___jp_379_;
}
else
{
return v_congrConsts_334_;
}
}
else
{
if (v_congrConsts_366_ == 0)
{
return v_congrConsts_366_;
}
else
{
goto v___jp_379_;
}
}
}
v___jp_381_:
{
if (v_letToHave_333_ == 0)
{
if (v_letToHave_365_ == 0)
{
goto v___jp_380_;
}
else
{
return v_letToHave_333_;
}
}
else
{
if (v_letToHave_365_ == 0)
{
return v_letToHave_365_;
}
else
{
goto v___jp_380_;
}
}
}
v___jp_382_:
{
if (v_zetaHave_332_ == 0)
{
if (v_zetaHave_364_ == 0)
{
goto v___jp_381_;
}
else
{
return v_zetaHave_332_;
}
}
else
{
if (v_zetaHave_364_ == 0)
{
return v_zetaHave_364_;
}
else
{
goto v___jp_381_;
}
}
}
v___jp_383_:
{
if (v_catchRuntime_331_ == 0)
{
if (v_catchRuntime_363_ == 0)
{
goto v___jp_382_;
}
else
{
return v_catchRuntime_331_;
}
}
else
{
if (v_catchRuntime_363_ == 0)
{
return v_catchRuntime_363_;
}
else
{
goto v___jp_382_;
}
}
}
v___jp_384_:
{
if (v_zetaUnused_330_ == 0)
{
if (v_zetaUnused_362_ == 0)
{
goto v___jp_383_;
}
else
{
return v_zetaUnused_330_;
}
}
else
{
if (v_zetaUnused_362_ == 0)
{
return v_zetaUnused_362_;
}
else
{
goto v___jp_383_;
}
}
}
v___jp_385_:
{
if (v_implicitDefEqProofs_329_ == 0)
{
if (v_implicitDefEqProofs_361_ == 0)
{
goto v___jp_384_;
}
else
{
return v_implicitDefEqProofs_329_;
}
}
else
{
if (v_implicitDefEqProofs_361_ == 0)
{
return v_implicitDefEqProofs_361_;
}
else
{
goto v___jp_384_;
}
}
}
v___jp_386_:
{
if (v_index_328_ == 0)
{
if (v_index_360_ == 0)
{
goto v___jp_385_;
}
else
{
return v_index_328_;
}
}
else
{
if (v_index_360_ == 0)
{
return v_index_360_;
}
else
{
goto v___jp_385_;
}
}
}
v___jp_387_:
{
if (v_zetaDelta_327_ == 0)
{
if (v_zetaDelta_359_ == 0)
{
goto v___jp_386_;
}
else
{
return v_zetaDelta_327_;
}
}
else
{
if (v_zetaDelta_359_ == 0)
{
return v_zetaDelta_359_;
}
else
{
goto v___jp_386_;
}
}
}
v___jp_388_:
{
if (v_unfoldPartialApp_326_ == 0)
{
if (v_unfoldPartialApp_358_ == 0)
{
goto v___jp_387_;
}
else
{
return v_unfoldPartialApp_326_;
}
}
else
{
if (v_unfoldPartialApp_358_ == 0)
{
return v_unfoldPartialApp_358_;
}
else
{
goto v___jp_387_;
}
}
}
v___jp_389_:
{
if (v_ground_325_ == 0)
{
if (v_ground_357_ == 0)
{
goto v___jp_388_;
}
else
{
return v_ground_325_;
}
}
else
{
if (v_ground_357_ == 0)
{
return v_ground_357_;
}
else
{
goto v___jp_388_;
}
}
}
v___jp_390_:
{
if (v_failIfUnchanged_324_ == 0)
{
if (v_failIfUnchanged_356_ == 0)
{
goto v___jp_389_;
}
else
{
return v_failIfUnchanged_324_;
}
}
else
{
if (v_failIfUnchanged_356_ == 0)
{
return v_failIfUnchanged_356_;
}
else
{
goto v___jp_389_;
}
}
}
v___jp_391_:
{
if (v_dsimp_323_ == 0)
{
if (v_dsimp_355_ == 0)
{
goto v___jp_390_;
}
else
{
return v_dsimp_323_;
}
}
else
{
if (v_dsimp_355_ == 0)
{
return v_dsimp_355_;
}
else
{
goto v___jp_390_;
}
}
}
v___jp_392_:
{
if (v_autoUnfold_322_ == 0)
{
if (v_autoUnfold_354_ == 0)
{
goto v___jp_391_;
}
else
{
return v_autoUnfold_322_;
}
}
else
{
if (v_autoUnfold_354_ == 0)
{
return v_autoUnfold_354_;
}
else
{
goto v___jp_391_;
}
}
}
v___jp_393_:
{
if (v_arith_321_ == 0)
{
if (v_arith_353_ == 0)
{
goto v___jp_392_;
}
else
{
return v_arith_321_;
}
}
else
{
if (v_arith_353_ == 0)
{
return v_arith_353_;
}
else
{
goto v___jp_392_;
}
}
}
v___jp_394_:
{
if (v_decide_320_ == 0)
{
if (v_decide_352_ == 0)
{
goto v___jp_393_;
}
else
{
return v_decide_320_;
}
}
else
{
if (v_decide_352_ == 0)
{
return v_decide_352_;
}
else
{
goto v___jp_393_;
}
}
}
v___jp_395_:
{
if (v___y_396_ == 0)
{
return v___y_396_;
}
else
{
if (v_proj_319_ == 0)
{
if (v_proj_351_ == 0)
{
goto v___jp_394_;
}
else
{
return v_proj_319_;
}
}
else
{
if (v_proj_351_ == 0)
{
return v_proj_351_;
}
else
{
goto v___jp_394_;
}
}
}
}
v___jp_397_:
{
uint8_t v___x_398_; 
v___x_398_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_317_, v_etaStruct_349_);
if (v___x_398_ == 0)
{
return v___x_398_;
}
else
{
if (v_iota_318_ == 0)
{
if (v_iota_350_ == 0)
{
v___y_396_ = v___x_398_;
goto v___jp_395_;
}
else
{
return v_iota_318_;
}
}
else
{
v___y_396_ = v_iota_350_;
goto v___jp_395_;
}
}
}
v___jp_399_:
{
if (v_eta_316_ == 0)
{
if (v_eta_348_ == 0)
{
goto v___jp_397_;
}
else
{
return v_eta_316_;
}
}
else
{
if (v_eta_348_ == 0)
{
return v_eta_348_;
}
else
{
goto v___jp_397_;
}
}
}
v___jp_400_:
{
if (v_beta_315_ == 0)
{
if (v_beta_347_ == 0)
{
goto v___jp_399_;
}
else
{
return v_beta_315_;
}
}
else
{
if (v_beta_347_ == 0)
{
return v_beta_347_;
}
else
{
goto v___jp_399_;
}
}
}
v___jp_401_:
{
if (v_zeta_314_ == 0)
{
if (v_zeta_346_ == 0)
{
goto v___jp_400_;
}
else
{
return v_zeta_314_;
}
}
else
{
if (v_zeta_346_ == 0)
{
return v_zeta_346_;
}
else
{
goto v___jp_400_;
}
}
}
v___jp_402_:
{
if (v_singlePass_313_ == 0)
{
if (v_singlePass_345_ == 0)
{
goto v___jp_401_;
}
else
{
return v_singlePass_313_;
}
}
else
{
if (v_singlePass_345_ == 0)
{
return v_singlePass_345_;
}
else
{
goto v___jp_401_;
}
}
}
v___jp_403_:
{
if (v___y_404_ == 0)
{
return v___y_404_;
}
else
{
if (v_memoize_312_ == 0)
{
if (v_memoize_344_ == 0)
{
goto v___jp_402_;
}
else
{
return v_memoize_312_;
}
}
else
{
if (v_memoize_344_ == 0)
{
return v_memoize_344_;
}
else
{
goto v___jp_402_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instBEqConfig_beq___boxed(lean_object* v_x_407_, lean_object* v_x_408_){
_start:
{
uint8_t v_res_409_; lean_object* v_r_410_; 
v_res_409_ = l_Lean_Meta_Simp_instBEqConfig_beq(v_x_407_, v_x_408_);
lean_dec_ref(v_x_408_);
lean_dec_ref(v_x_407_);
v_r_410_ = lean_box(v_res_409_);
return v_r_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorIdx(lean_object* v_x_421_){
_start:
{
switch(lean_obj_tag(v_x_421_))
{
case 0:
{
lean_object* v___x_422_; 
v___x_422_ = lean_unsigned_to_nat(0u);
return v___x_422_;
}
case 1:
{
lean_object* v___x_423_; 
v___x_423_ = lean_unsigned_to_nat(1u);
return v___x_423_;
}
default: 
{
lean_object* v___x_424_; 
v___x_424_ = lean_unsigned_to_nat(2u);
return v___x_424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorIdx___boxed(lean_object* v_x_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Meta_Occurrences_ctorIdx(v_x_425_);
lean_dec(v_x_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim___redArg(lean_object* v_t_427_, lean_object* v_k_428_){
_start:
{
if (lean_obj_tag(v_t_427_) == 0)
{
return v_k_428_;
}
else
{
lean_object* v_idxs_429_; lean_object* v___x_430_; 
v_idxs_429_ = lean_ctor_get(v_t_427_, 0);
lean_inc(v_idxs_429_);
lean_dec(v_t_427_);
v___x_430_ = lean_apply_1(v_k_428_, v_idxs_429_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim(lean_object* v_motive_431_, lean_object* v_ctorIdx_432_, lean_object* v_t_433_, lean_object* v_h_434_, lean_object* v_k_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_433_, v_k_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim___boxed(lean_object* v_motive_437_, lean_object* v_ctorIdx_438_, lean_object* v_t_439_, lean_object* v_h_440_, lean_object* v_k_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_Meta_Occurrences_ctorElim(v_motive_437_, v_ctorIdx_438_, v_t_439_, v_h_440_, v_k_441_);
lean_dec(v_ctorIdx_438_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_all_elim___redArg(lean_object* v_t_443_, lean_object* v_all_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_443_, v_all_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_all_elim(lean_object* v_motive_446_, lean_object* v_t_447_, lean_object* v_h_448_, lean_object* v_all_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_447_, v_all_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_pos_elim___redArg(lean_object* v_t_451_, lean_object* v_pos_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_451_, v_pos_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_pos_elim(lean_object* v_motive_454_, lean_object* v_t_455_, lean_object* v_h_456_, lean_object* v_pos_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_455_, v_pos_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_neg_elim___redArg(lean_object* v_t_459_, lean_object* v_neg_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_459_, v_neg_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_neg_elim(lean_object* v_motive_462_, lean_object* v_t_463_, lean_object* v_h_464_, lean_object* v_neg_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_463_, v_neg_465_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedOccurrences_default(void){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = lean_box(0);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedOccurrences(void){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = lean_box(0);
return v___x_468_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqOccurrences_beq(lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v_a_472_; lean_object* v_b_473_; 
switch(lean_obj_tag(v_x_469_))
{
case 0:
{
if (lean_obj_tag(v_x_470_) == 0)
{
uint8_t v___x_476_; 
v___x_476_ = 1;
return v___x_476_;
}
else
{
uint8_t v___x_477_; 
lean_dec(v_x_470_);
v___x_477_ = 0;
return v___x_477_;
}
}
case 1:
{
if (lean_obj_tag(v_x_470_) == 1)
{
lean_object* v_idxs_478_; lean_object* v_idxs_479_; 
v_idxs_478_ = lean_ctor_get(v_x_469_, 0);
lean_inc(v_idxs_478_);
lean_dec_ref_known(v_x_469_, 1);
v_idxs_479_ = lean_ctor_get(v_x_470_, 0);
lean_inc(v_idxs_479_);
lean_dec_ref_known(v_x_470_, 1);
v_a_472_ = v_idxs_478_;
v_b_473_ = v_idxs_479_;
goto v___jp_471_;
}
else
{
uint8_t v___x_480_; 
lean_dec_ref_known(v_x_469_, 1);
lean_dec(v_x_470_);
v___x_480_ = 0;
return v___x_480_;
}
}
default: 
{
if (lean_obj_tag(v_x_470_) == 2)
{
lean_object* v_idxs_481_; lean_object* v_idxs_482_; 
v_idxs_481_ = lean_ctor_get(v_x_469_, 0);
lean_inc(v_idxs_481_);
lean_dec_ref_known(v_x_469_, 1);
v_idxs_482_ = lean_ctor_get(v_x_470_, 0);
lean_inc(v_idxs_482_);
lean_dec_ref_known(v_x_470_, 1);
v_a_472_ = v_idxs_481_;
v_b_473_ = v_idxs_482_;
goto v___jp_471_;
}
else
{
uint8_t v___x_483_; 
lean_dec_ref_known(v_x_469_, 1);
lean_dec(v_x_470_);
v___x_483_ = 0;
return v___x_483_;
}
}
}
v___jp_471_:
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_475_ = l_instDecidableEqList___redArg(v___x_474_, v_a_472_, v_b_473_);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqOccurrences_beq___boxed(lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
uint8_t v_res_486_; lean_object* v_r_487_; 
v_res_486_ = l_Lean_Meta_instBEqOccurrences_beq(v_x_484_, v_x_485_);
v_r_487_ = lean_box(v_res_486_);
return v_r_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instCoeListNatOccurrences___lam__0(lean_object* v_idxs_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v_idxs_490_);
return v___x_491_;
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
