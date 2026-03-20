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
static const lean_ctor_object l_Lean_instInhabitedNameGenerator_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instInhabitedNameGenerator_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedNameGenerator_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedNameGenerator_default = (const lean_object*)&l_Lean_instInhabitedNameGenerator_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedNameGenerator = (const lean_object*)&l_Lean_instInhabitedNameGenerator_default___closed__0_value;
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
static const lean_ctor_object l_Lean_Meta_DSimp_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 16, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_DSimp_instInhabitedConfig_default___closed__0 = (const lean_object*)&l_Lean_Meta_DSimp_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_DSimp_instInhabitedConfig_default = (const lean_object*)&l_Lean_Meta_DSimp_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_DSimp_instInhabitedConfig = (const lean_object*)&l_Lean_Meta_DSimp_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_DSimp_instBEqConfig_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DSimp_instBEqConfig_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_DSimp_instBEqConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DSimp_instBEqConfig_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DSimp_instBEqConfig___closed__0 = (const lean_object*)&l_Lean_Meta_DSimp_instBEqConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_DSimp_instBEqConfig = (const lean_object*)&l_Lean_Meta_DSimp_instBEqConfig___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
static const lean_ctor_object l_Lean_Meta_Simp_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 32, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorIdx(uint8_t v_x_6_){
_start:
{
switch(v_x_6_)
{
case 0:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(0u);
return v___x_7_;
}
case 1:
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(1u);
return v___x_8_;
}
case 2:
{
lean_object* v___x_9_; 
v___x_9_ = lean_unsigned_to_nat(2u);
return v___x_9_;
}
case 3:
{
lean_object* v___x_10_; 
v___x_10_ = lean_unsigned_to_nat(3u);
return v___x_10_;
}
default: 
{
lean_object* v___x_11_; 
v___x_11_ = lean_unsigned_to_nat(4u);
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorIdx___boxed(lean_object* v_x_12_){
_start:
{
uint8_t v_x_boxed_13_; lean_object* v_res_14_; 
v_x_boxed_13_ = lean_unbox(v_x_12_);
v_res_14_ = l_Lean_Meta_TransparencyMode_ctorIdx(v_x_boxed_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toCtorIdx(uint8_t v_x_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Meta_TransparencyMode_ctorIdx(v_x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toCtorIdx___boxed(lean_object* v_x_17_){
_start:
{
uint8_t v_x_4__boxed_18_; lean_object* v_res_19_; 
v_x_4__boxed_18_ = lean_unbox(v_x_17_);
v_res_19_ = l_Lean_Meta_TransparencyMode_toCtorIdx(v_x_4__boxed_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___redArg(lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___redArg___boxed(lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Meta_TransparencyMode_ctorElim___redArg(v_k_21_);
lean_dec(v_k_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim(lean_object* v_motive_23_, lean_object* v_ctorIdx_24_, uint8_t v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
lean_inc(v_k_27_);
return v_k_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_ctorElim___boxed(lean_object* v_motive_28_, lean_object* v_ctorIdx_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_k_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Meta_TransparencyMode_ctorElim(v_motive_28_, v_ctorIdx_29_, v_t_boxed_33_, v_h_31_, v_k_32_);
lean_dec(v_k_32_);
lean_dec(v_ctorIdx_29_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___redArg(lean_object* v_all_35_){
_start:
{
lean_inc(v_all_35_);
return v_all_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___redArg___boxed(lean_object* v_all_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Meta_TransparencyMode_all_elim___redArg(v_all_36_);
lean_dec(v_all_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_all_41_){
_start:
{
lean_inc(v_all_41_);
return v_all_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_all_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_all_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Meta_TransparencyMode_all_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_all_45_);
lean_dec(v_all_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___redArg(lean_object* v_default_48_){
_start:
{
lean_inc(v_default_48_);
return v_default_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___redArg___boxed(lean_object* v_default_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Meta_TransparencyMode_default_elim___redArg(v_default_49_);
lean_dec(v_default_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_default_54_){
_start:
{
lean_inc(v_default_54_);
return v_default_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_default_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_default_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Meta_TransparencyMode_default_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_default_58_);
lean_dec(v_default_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim___redArg(lean_object* v_reducible_61_){
_start:
{
lean_inc(v_reducible_61_);
return v_reducible_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim___redArg___boxed(lean_object* v_reducible_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Meta_TransparencyMode_reducible_elim___redArg(v_reducible_62_);
lean_dec(v_reducible_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_reducible_elim(lean_object* v_motive_64_, uint8_t v_t_65_, lean_object* v_h_66_, lean_object* v_reducible_67_){
_start:
{
lean_inc(v_reducible_67_);
return v_reducible_67_;
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim(lean_object* v_motive_77_, uint8_t v_t_78_, lean_object* v_h_79_, lean_object* v_instances_80_){
_start:
{
lean_inc(v_instances_80_);
return v_instances_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_instances_elim___boxed(lean_object* v_motive_81_, lean_object* v_t_82_, lean_object* v_h_83_, lean_object* v_instances_84_){
_start:
{
uint8_t v_t_boxed_85_; lean_object* v_res_86_; 
v_t_boxed_85_ = lean_unbox(v_t_82_);
v_res_86_ = l_Lean_Meta_TransparencyMode_instances_elim(v_motive_81_, v_t_boxed_85_, v_h_83_, v_instances_84_);
lean_dec(v_instances_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___redArg(lean_object* v_none_87_){
_start:
{
lean_inc(v_none_87_);
return v_none_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___redArg___boxed(lean_object* v_none_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_Meta_TransparencyMode_none_elim___redArg(v_none_88_);
lean_dec(v_none_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim(lean_object* v_motive_90_, uint8_t v_t_91_, lean_object* v_h_92_, lean_object* v_none_93_){
_start:
{
lean_inc(v_none_93_);
return v_none_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_none_elim___boxed(lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_none_97_){
_start:
{
uint8_t v_t_boxed_98_; lean_object* v_res_99_; 
v_t_boxed_98_ = lean_unbox(v_t_95_);
v_res_99_ = l_Lean_Meta_TransparencyMode_none_elim(v_motive_94_, v_t_boxed_98_, v_h_96_, v_none_97_);
lean_dec(v_none_97_);
return v_res_99_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedTransparencyMode_default(void){
_start:
{
uint8_t v___x_100_; 
v___x_100_ = 0;
return v___x_100_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedTransparencyMode(void){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = 0;
return v___x_101_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t v_x_102_, uint8_t v_y_103_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_104_ = l_Lean_Meta_TransparencyMode_ctorIdx(v_x_102_);
v___x_105_ = l_Lean_Meta_TransparencyMode_ctorIdx(v_y_103_);
v___x_106_ = lean_nat_dec_eq(v___x_104_, v___x_105_);
lean_dec(v___x_105_);
lean_dec(v___x_104_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqTransparencyMode_beq___boxed(lean_object* v_x_107_, lean_object* v_y_108_){
_start:
{
uint8_t v_x_17__boxed_109_; uint8_t v_y_18__boxed_110_; uint8_t v_res_111_; lean_object* v_r_112_; 
v_x_17__boxed_109_ = lean_unbox(v_x_107_);
v_y_18__boxed_110_ = lean_unbox(v_y_108_);
v_res_111_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_x_17__boxed_109_, v_y_18__boxed_110_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorIdx(uint8_t v_x_115_){
_start:
{
switch(v_x_115_)
{
case 0:
{
lean_object* v___x_116_; 
v___x_116_ = lean_unsigned_to_nat(0u);
return v___x_116_;
}
case 1:
{
lean_object* v___x_117_; 
v___x_117_ = lean_unsigned_to_nat(1u);
return v___x_117_;
}
default: 
{
lean_object* v___x_118_; 
v___x_118_ = lean_unsigned_to_nat(2u);
return v___x_118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorIdx___boxed(lean_object* v_x_119_){
_start:
{
uint8_t v_x_boxed_120_; lean_object* v_res_121_; 
v_x_boxed_120_ = lean_unbox(v_x_119_);
v_res_121_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_x_boxed_120_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_toCtorIdx(uint8_t v_x_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_toCtorIdx___boxed(lean_object* v_x_124_){
_start:
{
uint8_t v_x_4__boxed_125_; lean_object* v_res_126_; 
v_x_4__boxed_125_ = lean_unbox(v_x_124_);
v_res_126_ = l_Lean_Meta_EtaStructMode_toCtorIdx(v_x_4__boxed_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___redArg(lean_object* v_k_127_){
_start:
{
lean_inc(v_k_127_);
return v_k_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___redArg___boxed(lean_object* v_k_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_Meta_EtaStructMode_ctorElim___redArg(v_k_128_);
lean_dec(v_k_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim(lean_object* v_motive_130_, lean_object* v_ctorIdx_131_, uint8_t v_t_132_, lean_object* v_h_133_, lean_object* v_k_134_){
_start:
{
lean_inc(v_k_134_);
return v_k_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_ctorElim___boxed(lean_object* v_motive_135_, lean_object* v_ctorIdx_136_, lean_object* v_t_137_, lean_object* v_h_138_, lean_object* v_k_139_){
_start:
{
uint8_t v_t_boxed_140_; lean_object* v_res_141_; 
v_t_boxed_140_ = lean_unbox(v_t_137_);
v_res_141_ = l_Lean_Meta_EtaStructMode_ctorElim(v_motive_135_, v_ctorIdx_136_, v_t_boxed_140_, v_h_138_, v_k_139_);
lean_dec(v_k_139_);
lean_dec(v_ctorIdx_136_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___redArg(lean_object* v_all_142_){
_start:
{
lean_inc(v_all_142_);
return v_all_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___redArg___boxed(lean_object* v_all_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Meta_EtaStructMode_all_elim___redArg(v_all_143_);
lean_dec(v_all_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim(lean_object* v_motive_145_, uint8_t v_t_146_, lean_object* v_h_147_, lean_object* v_all_148_){
_start:
{
lean_inc(v_all_148_);
return v_all_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_all_elim___boxed(lean_object* v_motive_149_, lean_object* v_t_150_, lean_object* v_h_151_, lean_object* v_all_152_){
_start:
{
uint8_t v_t_boxed_153_; lean_object* v_res_154_; 
v_t_boxed_153_ = lean_unbox(v_t_150_);
v_res_154_ = l_Lean_Meta_EtaStructMode_all_elim(v_motive_149_, v_t_boxed_153_, v_h_151_, v_all_152_);
lean_dec(v_all_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___redArg(lean_object* v_notClasses_155_){
_start:
{
lean_inc(v_notClasses_155_);
return v_notClasses_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___redArg___boxed(lean_object* v_notClasses_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_Meta_EtaStructMode_notClasses_elim___redArg(v_notClasses_156_);
lean_dec(v_notClasses_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim(lean_object* v_motive_158_, uint8_t v_t_159_, lean_object* v_h_160_, lean_object* v_notClasses_161_){
_start:
{
lean_inc(v_notClasses_161_);
return v_notClasses_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_notClasses_elim___boxed(lean_object* v_motive_162_, lean_object* v_t_163_, lean_object* v_h_164_, lean_object* v_notClasses_165_){
_start:
{
uint8_t v_t_boxed_166_; lean_object* v_res_167_; 
v_t_boxed_166_ = lean_unbox(v_t_163_);
v_res_167_ = l_Lean_Meta_EtaStructMode_notClasses_elim(v_motive_162_, v_t_boxed_166_, v_h_164_, v_notClasses_165_);
lean_dec(v_notClasses_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___redArg(lean_object* v_none_168_){
_start:
{
lean_inc(v_none_168_);
return v_none_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___redArg___boxed(lean_object* v_none_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Meta_EtaStructMode_none_elim___redArg(v_none_169_);
lean_dec(v_none_169_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim(lean_object* v_motive_171_, uint8_t v_t_172_, lean_object* v_h_173_, lean_object* v_none_174_){
_start:
{
lean_inc(v_none_174_);
return v_none_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_none_elim___boxed(lean_object* v_motive_175_, lean_object* v_t_176_, lean_object* v_h_177_, lean_object* v_none_178_){
_start:
{
uint8_t v_t_boxed_179_; lean_object* v_res_180_; 
v_t_boxed_179_ = lean_unbox(v_t_176_);
v_res_180_ = l_Lean_Meta_EtaStructMode_none_elim(v_motive_175_, v_t_boxed_179_, v_h_177_, v_none_178_);
lean_dec(v_none_178_);
return v_res_180_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedEtaStructMode_default(void){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = 0;
return v___x_181_;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedEtaStructMode(void){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = 0;
return v___x_182_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqEtaStructMode_beq(uint8_t v_x_183_, uint8_t v_y_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_185_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_x_183_);
v___x_186_ = l_Lean_Meta_EtaStructMode_ctorIdx(v_y_184_);
v___x_187_ = lean_nat_dec_eq(v___x_185_, v___x_186_);
lean_dec(v___x_186_);
lean_dec(v___x_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqEtaStructMode_beq___boxed(lean_object* v_x_188_, lean_object* v_y_189_){
_start:
{
uint8_t v_x_17__boxed_190_; uint8_t v_y_18__boxed_191_; uint8_t v_res_192_; lean_object* v_r_193_; 
v_x_17__boxed_190_ = lean_unbox(v_x_188_);
v_y_18__boxed_191_ = lean_unbox(v_y_189_);
v_res_192_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_x_17__boxed_190_, v_y_18__boxed_191_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DSimp_instBEqConfig_beq(lean_object* v_x_201_, lean_object* v_x_202_){
_start:
{
uint8_t v_zeta_203_; uint8_t v_beta_204_; uint8_t v_eta_205_; uint8_t v_etaStruct_206_; uint8_t v_iota_207_; uint8_t v_proj_208_; uint8_t v_decide_209_; uint8_t v_autoUnfold_210_; uint8_t v_failIfUnchanged_211_; uint8_t v_unfoldPartialApp_212_; uint8_t v_zetaDelta_213_; uint8_t v_index_214_; uint8_t v_zetaUnused_215_; uint8_t v_zetaHave_216_; uint8_t v_locals_217_; uint8_t v_instances_218_; uint8_t v_zeta_219_; uint8_t v_beta_220_; uint8_t v_eta_221_; uint8_t v_etaStruct_222_; uint8_t v_iota_223_; uint8_t v_proj_224_; uint8_t v_decide_225_; uint8_t v_autoUnfold_226_; uint8_t v_failIfUnchanged_227_; uint8_t v_unfoldPartialApp_228_; uint8_t v_zetaDelta_229_; uint8_t v_index_230_; uint8_t v_zetaUnused_231_; uint8_t v_zetaHave_232_; uint8_t v_locals_233_; uint8_t v_instances_234_; uint8_t v___y_236_; uint8_t v___y_238_; uint8_t v___y_240_; uint8_t v___y_242_; uint8_t v___y_244_; uint8_t v___y_246_; uint8_t v___y_248_; uint8_t v___y_250_; uint8_t v___y_252_; uint8_t v___y_254_; uint8_t v___y_256_; 
v_zeta_203_ = lean_ctor_get_uint8(v_x_201_, 0);
v_beta_204_ = lean_ctor_get_uint8(v_x_201_, 1);
v_eta_205_ = lean_ctor_get_uint8(v_x_201_, 2);
v_etaStruct_206_ = lean_ctor_get_uint8(v_x_201_, 3);
v_iota_207_ = lean_ctor_get_uint8(v_x_201_, 4);
v_proj_208_ = lean_ctor_get_uint8(v_x_201_, 5);
v_decide_209_ = lean_ctor_get_uint8(v_x_201_, 6);
v_autoUnfold_210_ = lean_ctor_get_uint8(v_x_201_, 7);
v_failIfUnchanged_211_ = lean_ctor_get_uint8(v_x_201_, 8);
v_unfoldPartialApp_212_ = lean_ctor_get_uint8(v_x_201_, 9);
v_zetaDelta_213_ = lean_ctor_get_uint8(v_x_201_, 10);
v_index_214_ = lean_ctor_get_uint8(v_x_201_, 11);
v_zetaUnused_215_ = lean_ctor_get_uint8(v_x_201_, 12);
v_zetaHave_216_ = lean_ctor_get_uint8(v_x_201_, 13);
v_locals_217_ = lean_ctor_get_uint8(v_x_201_, 14);
v_instances_218_ = lean_ctor_get_uint8(v_x_201_, 15);
v_zeta_219_ = lean_ctor_get_uint8(v_x_202_, 0);
v_beta_220_ = lean_ctor_get_uint8(v_x_202_, 1);
v_eta_221_ = lean_ctor_get_uint8(v_x_202_, 2);
v_etaStruct_222_ = lean_ctor_get_uint8(v_x_202_, 3);
v_iota_223_ = lean_ctor_get_uint8(v_x_202_, 4);
v_proj_224_ = lean_ctor_get_uint8(v_x_202_, 5);
v_decide_225_ = lean_ctor_get_uint8(v_x_202_, 6);
v_autoUnfold_226_ = lean_ctor_get_uint8(v_x_202_, 7);
v_failIfUnchanged_227_ = lean_ctor_get_uint8(v_x_202_, 8);
v_unfoldPartialApp_228_ = lean_ctor_get_uint8(v_x_202_, 9);
v_zetaDelta_229_ = lean_ctor_get_uint8(v_x_202_, 10);
v_index_230_ = lean_ctor_get_uint8(v_x_202_, 11);
v_zetaUnused_231_ = lean_ctor_get_uint8(v_x_202_, 12);
v_zetaHave_232_ = lean_ctor_get_uint8(v_x_202_, 13);
v_locals_233_ = lean_ctor_get_uint8(v_x_202_, 14);
v_instances_234_ = lean_ctor_get_uint8(v_x_202_, 15);
if (v_zeta_203_ == 0)
{
if (v_zeta_219_ == 0)
{
goto v___jp_260_;
}
else
{
return v_zeta_203_;
}
}
else
{
if (v_zeta_219_ == 0)
{
return v_zeta_219_;
}
else
{
goto v___jp_260_;
}
}
v___jp_235_:
{
if (v_instances_218_ == 0)
{
if (v_instances_234_ == 0)
{
return v___y_236_;
}
else
{
return v_instances_218_;
}
}
else
{
return v_instances_234_;
}
}
v___jp_237_:
{
if (v_locals_217_ == 0)
{
if (v_locals_233_ == 0)
{
v___y_236_ = v___y_238_;
goto v___jp_235_;
}
else
{
return v_locals_217_;
}
}
else
{
if (v_locals_233_ == 0)
{
return v_locals_233_;
}
else
{
v___y_236_ = v_locals_233_;
goto v___jp_235_;
}
}
}
v___jp_239_:
{
if (v_zetaHave_216_ == 0)
{
if (v_zetaHave_232_ == 0)
{
v___y_238_ = v___y_240_;
goto v___jp_237_;
}
else
{
return v_zetaHave_216_;
}
}
else
{
if (v_zetaHave_232_ == 0)
{
return v_zetaHave_232_;
}
else
{
v___y_238_ = v_zetaHave_232_;
goto v___jp_237_;
}
}
}
v___jp_241_:
{
if (v_zetaUnused_215_ == 0)
{
if (v_zetaUnused_231_ == 0)
{
v___y_240_ = v___y_242_;
goto v___jp_239_;
}
else
{
return v_zetaUnused_215_;
}
}
else
{
if (v_zetaUnused_231_ == 0)
{
return v_zetaUnused_231_;
}
else
{
v___y_240_ = v_zetaUnused_231_;
goto v___jp_239_;
}
}
}
v___jp_243_:
{
if (v_index_214_ == 0)
{
if (v_index_230_ == 0)
{
v___y_242_ = v___y_244_;
goto v___jp_241_;
}
else
{
return v_index_214_;
}
}
else
{
if (v_index_230_ == 0)
{
return v_index_230_;
}
else
{
v___y_242_ = v_index_230_;
goto v___jp_241_;
}
}
}
v___jp_245_:
{
if (v_zetaDelta_213_ == 0)
{
if (v_zetaDelta_229_ == 0)
{
v___y_244_ = v___y_246_;
goto v___jp_243_;
}
else
{
return v_zetaDelta_213_;
}
}
else
{
if (v_zetaDelta_229_ == 0)
{
return v_zetaDelta_229_;
}
else
{
v___y_244_ = v_zetaDelta_229_;
goto v___jp_243_;
}
}
}
v___jp_247_:
{
if (v_unfoldPartialApp_212_ == 0)
{
if (v_unfoldPartialApp_228_ == 0)
{
v___y_246_ = v___y_248_;
goto v___jp_245_;
}
else
{
return v_unfoldPartialApp_212_;
}
}
else
{
if (v_unfoldPartialApp_228_ == 0)
{
return v_unfoldPartialApp_228_;
}
else
{
v___y_246_ = v_unfoldPartialApp_228_;
goto v___jp_245_;
}
}
}
v___jp_249_:
{
if (v_failIfUnchanged_211_ == 0)
{
if (v_failIfUnchanged_227_ == 0)
{
v___y_248_ = v___y_250_;
goto v___jp_247_;
}
else
{
return v_failIfUnchanged_211_;
}
}
else
{
if (v_failIfUnchanged_227_ == 0)
{
return v_failIfUnchanged_227_;
}
else
{
v___y_248_ = v_failIfUnchanged_227_;
goto v___jp_247_;
}
}
}
v___jp_251_:
{
if (v_autoUnfold_210_ == 0)
{
if (v_autoUnfold_226_ == 0)
{
v___y_250_ = v___y_252_;
goto v___jp_249_;
}
else
{
return v_autoUnfold_210_;
}
}
else
{
if (v_autoUnfold_226_ == 0)
{
return v_autoUnfold_226_;
}
else
{
v___y_250_ = v_autoUnfold_226_;
goto v___jp_249_;
}
}
}
v___jp_253_:
{
if (v_decide_209_ == 0)
{
if (v_decide_225_ == 0)
{
v___y_252_ = v___y_254_;
goto v___jp_251_;
}
else
{
return v_decide_209_;
}
}
else
{
if (v_decide_225_ == 0)
{
return v_decide_225_;
}
else
{
v___y_252_ = v_decide_225_;
goto v___jp_251_;
}
}
}
v___jp_255_:
{
if (v___y_256_ == 0)
{
return v___y_256_;
}
else
{
if (v_proj_208_ == 0)
{
if (v_proj_224_ == 0)
{
v___y_254_ = v___y_256_;
goto v___jp_253_;
}
else
{
return v_proj_208_;
}
}
else
{
if (v_proj_224_ == 0)
{
return v_proj_224_;
}
else
{
v___y_254_ = v_proj_224_;
goto v___jp_253_;
}
}
}
}
v___jp_257_:
{
uint8_t v___x_258_; 
v___x_258_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_206_, v_etaStruct_222_);
if (v___x_258_ == 0)
{
return v___x_258_;
}
else
{
if (v_iota_207_ == 0)
{
if (v_iota_223_ == 0)
{
v___y_256_ = v___x_258_;
goto v___jp_255_;
}
else
{
return v_iota_207_;
}
}
else
{
v___y_256_ = v_iota_223_;
goto v___jp_255_;
}
}
}
v___jp_259_:
{
if (v_eta_205_ == 0)
{
if (v_eta_221_ == 0)
{
goto v___jp_257_;
}
else
{
return v_eta_205_;
}
}
else
{
if (v_eta_221_ == 0)
{
return v_eta_221_;
}
else
{
goto v___jp_257_;
}
}
}
v___jp_260_:
{
if (v_beta_204_ == 0)
{
if (v_beta_220_ == 0)
{
goto v___jp_259_;
}
else
{
return v_beta_204_;
}
}
else
{
if (v_beta_220_ == 0)
{
return v_beta_220_;
}
else
{
goto v___jp_259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DSimp_instBEqConfig_beq___boxed(lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
uint8_t v_res_263_; lean_object* v_r_264_; 
v_res_263_ = l_Lean_Meta_DSimp_instBEqConfig_beq(v_x_261_, v_x_262_);
lean_dec_ref(v_x_262_);
lean_dec_ref(v_x_261_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_defaultMaxSteps(void){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_unsigned_to_nat(100000u);
return v___x_267_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(lean_object* v_x_275_, lean_object* v_x_276_){
_start:
{
if (lean_obj_tag(v_x_275_) == 0)
{
if (lean_obj_tag(v_x_276_) == 0)
{
uint8_t v___x_277_; 
v___x_277_ = 1;
return v___x_277_;
}
else
{
uint8_t v___x_278_; 
v___x_278_ = 0;
return v___x_278_;
}
}
else
{
if (lean_obj_tag(v_x_276_) == 0)
{
uint8_t v___x_279_; 
v___x_279_ = 0;
return v___x_279_;
}
else
{
lean_object* v_val_280_; lean_object* v_val_281_; uint8_t v___x_282_; 
v_val_280_ = lean_ctor_get(v_x_275_, 0);
v_val_281_ = lean_ctor_get(v_x_276_, 0);
v___x_282_ = lean_nat_dec_eq(v_val_280_, v_val_281_);
return v___x_282_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0___boxed(lean_object* v_x_283_, lean_object* v_x_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(v_x_283_, v_x_284_);
lean_dec(v_x_284_);
lean_dec(v_x_283_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_instBEqConfig_beq(lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
lean_object* v_maxSteps_289_; lean_object* v_maxDischargeDepth_290_; uint8_t v_contextual_291_; uint8_t v_memoize_292_; uint8_t v_singlePass_293_; uint8_t v_zeta_294_; uint8_t v_beta_295_; uint8_t v_eta_296_; uint8_t v_etaStruct_297_; uint8_t v_iota_298_; uint8_t v_proj_299_; uint8_t v_decide_300_; uint8_t v_arith_301_; uint8_t v_autoUnfold_302_; uint8_t v_dsimp_303_; uint8_t v_failIfUnchanged_304_; uint8_t v_ground_305_; uint8_t v_unfoldPartialApp_306_; uint8_t v_zetaDelta_307_; uint8_t v_index_308_; uint8_t v_implicitDefEqProofs_309_; uint8_t v_zetaUnused_310_; uint8_t v_catchRuntime_311_; uint8_t v_zetaHave_312_; uint8_t v_letToHave_313_; uint8_t v_congrConsts_314_; uint8_t v_bitVecOfNat_315_; uint8_t v_warnExponents_316_; uint8_t v_suggestions_317_; lean_object* v_maxSuggestions_318_; uint8_t v_locals_319_; uint8_t v_instances_320_; lean_object* v_maxSteps_321_; lean_object* v_maxDischargeDepth_322_; uint8_t v_contextual_323_; uint8_t v_memoize_324_; uint8_t v_singlePass_325_; uint8_t v_zeta_326_; uint8_t v_beta_327_; uint8_t v_eta_328_; uint8_t v_etaStruct_329_; uint8_t v_iota_330_; uint8_t v_proj_331_; uint8_t v_decide_332_; uint8_t v_arith_333_; uint8_t v_autoUnfold_334_; uint8_t v_dsimp_335_; uint8_t v_failIfUnchanged_336_; uint8_t v_ground_337_; uint8_t v_unfoldPartialApp_338_; uint8_t v_zetaDelta_339_; uint8_t v_index_340_; uint8_t v_implicitDefEqProofs_341_; uint8_t v_zetaUnused_342_; uint8_t v_catchRuntime_343_; uint8_t v_zetaHave_344_; uint8_t v_letToHave_345_; uint8_t v_congrConsts_346_; uint8_t v_bitVecOfNat_347_; uint8_t v_warnExponents_348_; uint8_t v_suggestions_349_; lean_object* v_maxSuggestions_350_; uint8_t v_locals_351_; uint8_t v_instances_352_; uint8_t v___y_354_; uint8_t v___y_376_; uint8_t v___y_384_; uint8_t v___x_385_; 
v_maxSteps_289_ = lean_ctor_get(v_x_287_, 0);
v_maxDischargeDepth_290_ = lean_ctor_get(v_x_287_, 1);
v_contextual_291_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3);
v_memoize_292_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 1);
v_singlePass_293_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 2);
v_zeta_294_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 3);
v_beta_295_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 4);
v_eta_296_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 5);
v_etaStruct_297_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 6);
v_iota_298_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 7);
v_proj_299_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 8);
v_decide_300_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 9);
v_arith_301_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 10);
v_autoUnfold_302_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 11);
v_dsimp_303_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 12);
v_failIfUnchanged_304_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 13);
v_ground_305_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_306_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 15);
v_zetaDelta_307_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 16);
v_index_308_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_309_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 18);
v_zetaUnused_310_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 19);
v_catchRuntime_311_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 20);
v_zetaHave_312_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 21);
v_letToHave_313_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 22);
v_congrConsts_314_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 23);
v_bitVecOfNat_315_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 24);
v_warnExponents_316_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 25);
v_suggestions_317_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 26);
v_maxSuggestions_318_ = lean_ctor_get(v_x_287_, 2);
v_locals_319_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 27);
v_instances_320_ = lean_ctor_get_uint8(v_x_287_, sizeof(void*)*3 + 28);
v_maxSteps_321_ = lean_ctor_get(v_x_288_, 0);
v_maxDischargeDepth_322_ = lean_ctor_get(v_x_288_, 1);
v_contextual_323_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3);
v_memoize_324_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 1);
v_singlePass_325_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 2);
v_zeta_326_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 3);
v_beta_327_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 4);
v_eta_328_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 5);
v_etaStruct_329_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 6);
v_iota_330_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 7);
v_proj_331_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 8);
v_decide_332_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 9);
v_arith_333_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 10);
v_autoUnfold_334_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 11);
v_dsimp_335_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 12);
v_failIfUnchanged_336_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 13);
v_ground_337_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_338_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 15);
v_zetaDelta_339_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 16);
v_index_340_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_341_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 18);
v_zetaUnused_342_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 19);
v_catchRuntime_343_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 20);
v_zetaHave_344_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 21);
v_letToHave_345_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 22);
v_congrConsts_346_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 23);
v_bitVecOfNat_347_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 24);
v_warnExponents_348_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 25);
v_suggestions_349_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 26);
v_maxSuggestions_350_ = lean_ctor_get(v_x_288_, 2);
v_locals_351_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 27);
v_instances_352_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*3 + 28);
v___x_385_ = lean_nat_dec_eq(v_maxSteps_289_, v_maxSteps_321_);
if (v___x_385_ == 0)
{
return v___x_385_;
}
else
{
uint8_t v___x_386_; 
v___x_386_ = lean_nat_dec_eq(v_maxDischargeDepth_290_, v_maxDischargeDepth_322_);
if (v___x_386_ == 0)
{
return v___x_386_;
}
else
{
if (v_contextual_291_ == 0)
{
if (v_contextual_323_ == 0)
{
v___y_384_ = v___x_386_;
goto v___jp_383_;
}
else
{
return v_contextual_291_;
}
}
else
{
v___y_384_ = v_contextual_323_;
goto v___jp_383_;
}
}
}
v___jp_353_:
{
if (v___y_354_ == 0)
{
return v___y_354_;
}
else
{
if (v_instances_320_ == 0)
{
if (v_instances_352_ == 0)
{
return v___y_354_;
}
else
{
return v_instances_320_;
}
}
else
{
return v_instances_352_;
}
}
}
v___jp_355_:
{
uint8_t v___x_356_; 
v___x_356_ = l_instBEqOption_beq___at___00Lean_Meta_Simp_instBEqConfig_beq_spec__0(v_maxSuggestions_318_, v_maxSuggestions_350_);
if (v___x_356_ == 0)
{
return v___x_356_;
}
else
{
if (v_locals_319_ == 0)
{
if (v_locals_351_ == 0)
{
v___y_354_ = v___x_356_;
goto v___jp_353_;
}
else
{
return v_locals_319_;
}
}
else
{
v___y_354_ = v_locals_351_;
goto v___jp_353_;
}
}
}
v___jp_357_:
{
if (v_suggestions_317_ == 0)
{
if (v_suggestions_349_ == 0)
{
goto v___jp_355_;
}
else
{
return v_suggestions_317_;
}
}
else
{
if (v_suggestions_349_ == 0)
{
return v_suggestions_349_;
}
else
{
goto v___jp_355_;
}
}
}
v___jp_358_:
{
if (v_warnExponents_316_ == 0)
{
if (v_warnExponents_348_ == 0)
{
goto v___jp_357_;
}
else
{
return v_warnExponents_316_;
}
}
else
{
if (v_warnExponents_348_ == 0)
{
return v_warnExponents_348_;
}
else
{
goto v___jp_357_;
}
}
}
v___jp_359_:
{
if (v_bitVecOfNat_315_ == 0)
{
if (v_bitVecOfNat_347_ == 0)
{
goto v___jp_358_;
}
else
{
return v_bitVecOfNat_315_;
}
}
else
{
if (v_bitVecOfNat_347_ == 0)
{
return v_bitVecOfNat_347_;
}
else
{
goto v___jp_358_;
}
}
}
v___jp_360_:
{
if (v_congrConsts_314_ == 0)
{
if (v_congrConsts_346_ == 0)
{
goto v___jp_359_;
}
else
{
return v_congrConsts_314_;
}
}
else
{
if (v_congrConsts_346_ == 0)
{
return v_congrConsts_346_;
}
else
{
goto v___jp_359_;
}
}
}
v___jp_361_:
{
if (v_letToHave_313_ == 0)
{
if (v_letToHave_345_ == 0)
{
goto v___jp_360_;
}
else
{
return v_letToHave_313_;
}
}
else
{
if (v_letToHave_345_ == 0)
{
return v_letToHave_345_;
}
else
{
goto v___jp_360_;
}
}
}
v___jp_362_:
{
if (v_zetaHave_312_ == 0)
{
if (v_zetaHave_344_ == 0)
{
goto v___jp_361_;
}
else
{
return v_zetaHave_312_;
}
}
else
{
if (v_zetaHave_344_ == 0)
{
return v_zetaHave_344_;
}
else
{
goto v___jp_361_;
}
}
}
v___jp_363_:
{
if (v_catchRuntime_311_ == 0)
{
if (v_catchRuntime_343_ == 0)
{
goto v___jp_362_;
}
else
{
return v_catchRuntime_311_;
}
}
else
{
if (v_catchRuntime_343_ == 0)
{
return v_catchRuntime_343_;
}
else
{
goto v___jp_362_;
}
}
}
v___jp_364_:
{
if (v_zetaUnused_310_ == 0)
{
if (v_zetaUnused_342_ == 0)
{
goto v___jp_363_;
}
else
{
return v_zetaUnused_310_;
}
}
else
{
if (v_zetaUnused_342_ == 0)
{
return v_zetaUnused_342_;
}
else
{
goto v___jp_363_;
}
}
}
v___jp_365_:
{
if (v_implicitDefEqProofs_309_ == 0)
{
if (v_implicitDefEqProofs_341_ == 0)
{
goto v___jp_364_;
}
else
{
return v_implicitDefEqProofs_309_;
}
}
else
{
if (v_implicitDefEqProofs_341_ == 0)
{
return v_implicitDefEqProofs_341_;
}
else
{
goto v___jp_364_;
}
}
}
v___jp_366_:
{
if (v_index_308_ == 0)
{
if (v_index_340_ == 0)
{
goto v___jp_365_;
}
else
{
return v_index_308_;
}
}
else
{
if (v_index_340_ == 0)
{
return v_index_340_;
}
else
{
goto v___jp_365_;
}
}
}
v___jp_367_:
{
if (v_zetaDelta_307_ == 0)
{
if (v_zetaDelta_339_ == 0)
{
goto v___jp_366_;
}
else
{
return v_zetaDelta_307_;
}
}
else
{
if (v_zetaDelta_339_ == 0)
{
return v_zetaDelta_339_;
}
else
{
goto v___jp_366_;
}
}
}
v___jp_368_:
{
if (v_unfoldPartialApp_306_ == 0)
{
if (v_unfoldPartialApp_338_ == 0)
{
goto v___jp_367_;
}
else
{
return v_unfoldPartialApp_306_;
}
}
else
{
if (v_unfoldPartialApp_338_ == 0)
{
return v_unfoldPartialApp_338_;
}
else
{
goto v___jp_367_;
}
}
}
v___jp_369_:
{
if (v_ground_305_ == 0)
{
if (v_ground_337_ == 0)
{
goto v___jp_368_;
}
else
{
return v_ground_305_;
}
}
else
{
if (v_ground_337_ == 0)
{
return v_ground_337_;
}
else
{
goto v___jp_368_;
}
}
}
v___jp_370_:
{
if (v_failIfUnchanged_304_ == 0)
{
if (v_failIfUnchanged_336_ == 0)
{
goto v___jp_369_;
}
else
{
return v_failIfUnchanged_304_;
}
}
else
{
if (v_failIfUnchanged_336_ == 0)
{
return v_failIfUnchanged_336_;
}
else
{
goto v___jp_369_;
}
}
}
v___jp_371_:
{
if (v_dsimp_303_ == 0)
{
if (v_dsimp_335_ == 0)
{
goto v___jp_370_;
}
else
{
return v_dsimp_303_;
}
}
else
{
if (v_dsimp_335_ == 0)
{
return v_dsimp_335_;
}
else
{
goto v___jp_370_;
}
}
}
v___jp_372_:
{
if (v_autoUnfold_302_ == 0)
{
if (v_autoUnfold_334_ == 0)
{
goto v___jp_371_;
}
else
{
return v_autoUnfold_302_;
}
}
else
{
if (v_autoUnfold_334_ == 0)
{
return v_autoUnfold_334_;
}
else
{
goto v___jp_371_;
}
}
}
v___jp_373_:
{
if (v_arith_301_ == 0)
{
if (v_arith_333_ == 0)
{
goto v___jp_372_;
}
else
{
return v_arith_301_;
}
}
else
{
if (v_arith_333_ == 0)
{
return v_arith_333_;
}
else
{
goto v___jp_372_;
}
}
}
v___jp_374_:
{
if (v_decide_300_ == 0)
{
if (v_decide_332_ == 0)
{
goto v___jp_373_;
}
else
{
return v_decide_300_;
}
}
else
{
if (v_decide_332_ == 0)
{
return v_decide_332_;
}
else
{
goto v___jp_373_;
}
}
}
v___jp_375_:
{
if (v___y_376_ == 0)
{
return v___y_376_;
}
else
{
if (v_proj_299_ == 0)
{
if (v_proj_331_ == 0)
{
goto v___jp_374_;
}
else
{
return v_proj_299_;
}
}
else
{
if (v_proj_331_ == 0)
{
return v_proj_331_;
}
else
{
goto v___jp_374_;
}
}
}
}
v___jp_377_:
{
uint8_t v___x_378_; 
v___x_378_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_297_, v_etaStruct_329_);
if (v___x_378_ == 0)
{
return v___x_378_;
}
else
{
if (v_iota_298_ == 0)
{
if (v_iota_330_ == 0)
{
v___y_376_ = v___x_378_;
goto v___jp_375_;
}
else
{
return v_iota_298_;
}
}
else
{
v___y_376_ = v_iota_330_;
goto v___jp_375_;
}
}
}
v___jp_379_:
{
if (v_eta_296_ == 0)
{
if (v_eta_328_ == 0)
{
goto v___jp_377_;
}
else
{
return v_eta_296_;
}
}
else
{
if (v_eta_328_ == 0)
{
return v_eta_328_;
}
else
{
goto v___jp_377_;
}
}
}
v___jp_380_:
{
if (v_beta_295_ == 0)
{
if (v_beta_327_ == 0)
{
goto v___jp_379_;
}
else
{
return v_beta_295_;
}
}
else
{
if (v_beta_327_ == 0)
{
return v_beta_327_;
}
else
{
goto v___jp_379_;
}
}
}
v___jp_381_:
{
if (v_zeta_294_ == 0)
{
if (v_zeta_326_ == 0)
{
goto v___jp_380_;
}
else
{
return v_zeta_294_;
}
}
else
{
if (v_zeta_326_ == 0)
{
return v_zeta_326_;
}
else
{
goto v___jp_380_;
}
}
}
v___jp_382_:
{
if (v_singlePass_293_ == 0)
{
if (v_singlePass_325_ == 0)
{
goto v___jp_381_;
}
else
{
return v_singlePass_293_;
}
}
else
{
if (v_singlePass_325_ == 0)
{
return v_singlePass_325_;
}
else
{
goto v___jp_381_;
}
}
}
v___jp_383_:
{
if (v___y_384_ == 0)
{
return v___y_384_;
}
else
{
if (v_memoize_292_ == 0)
{
if (v_memoize_324_ == 0)
{
goto v___jp_382_;
}
else
{
return v_memoize_292_;
}
}
else
{
if (v_memoize_324_ == 0)
{
return v_memoize_324_;
}
else
{
goto v___jp_382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instBEqConfig_beq___boxed(lean_object* v_x_387_, lean_object* v_x_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_Lean_Meta_Simp_instBEqConfig_beq(v_x_387_, v_x_388_);
lean_dec_ref(v_x_388_);
lean_dec_ref(v_x_387_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorIdx(lean_object* v_x_401_){
_start:
{
switch(lean_obj_tag(v_x_401_))
{
case 0:
{
lean_object* v___x_402_; 
v___x_402_ = lean_unsigned_to_nat(0u);
return v___x_402_;
}
case 1:
{
lean_object* v___x_403_; 
v___x_403_ = lean_unsigned_to_nat(1u);
return v___x_403_;
}
default: 
{
lean_object* v___x_404_; 
v___x_404_ = lean_unsigned_to_nat(2u);
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorIdx___boxed(lean_object* v_x_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_Meta_Occurrences_ctorIdx(v_x_405_);
lean_dec(v_x_405_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim___redArg(lean_object* v_t_407_, lean_object* v_k_408_){
_start:
{
if (lean_obj_tag(v_t_407_) == 0)
{
return v_k_408_;
}
else
{
lean_object* v_idxs_409_; lean_object* v___x_410_; 
v_idxs_409_ = lean_ctor_get(v_t_407_, 0);
lean_inc(v_idxs_409_);
lean_dec(v_t_407_);
v___x_410_ = lean_apply_1(v_k_408_, v_idxs_409_);
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim(lean_object* v_motive_411_, lean_object* v_ctorIdx_412_, lean_object* v_t_413_, lean_object* v_h_414_, lean_object* v_k_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_413_, v_k_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_ctorElim___boxed(lean_object* v_motive_417_, lean_object* v_ctorIdx_418_, lean_object* v_t_419_, lean_object* v_h_420_, lean_object* v_k_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Meta_Occurrences_ctorElim(v_motive_417_, v_ctorIdx_418_, v_t_419_, v_h_420_, v_k_421_);
lean_dec(v_ctorIdx_418_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_all_elim___redArg(lean_object* v_t_423_, lean_object* v_all_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_423_, v_all_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_all_elim(lean_object* v_motive_426_, lean_object* v_t_427_, lean_object* v_h_428_, lean_object* v_all_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_427_, v_all_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_pos_elim___redArg(lean_object* v_t_431_, lean_object* v_pos_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_431_, v_pos_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_pos_elim(lean_object* v_motive_434_, lean_object* v_t_435_, lean_object* v_h_436_, lean_object* v_pos_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_435_, v_pos_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_neg_elim___redArg(lean_object* v_t_439_, lean_object* v_neg_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_439_, v_neg_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_neg_elim(lean_object* v_motive_442_, lean_object* v_t_443_, lean_object* v_h_444_, lean_object* v_neg_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Meta_Occurrences_ctorElim___redArg(v_t_443_, v_neg_445_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedOccurrences_default(void){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = lean_box(0);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedOccurrences(void){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = lean_box(0);
return v___x_448_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqOccurrences_beq(lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
lean_object* v_a_452_; lean_object* v_b_453_; 
switch(lean_obj_tag(v_x_449_))
{
case 0:
{
if (lean_obj_tag(v_x_450_) == 0)
{
uint8_t v___x_456_; 
v___x_456_ = 1;
return v___x_456_;
}
else
{
uint8_t v___x_457_; 
lean_dec(v_x_450_);
v___x_457_ = 0;
return v___x_457_;
}
}
case 1:
{
if (lean_obj_tag(v_x_450_) == 1)
{
lean_object* v_idxs_458_; lean_object* v_idxs_459_; 
v_idxs_458_ = lean_ctor_get(v_x_449_, 0);
lean_inc(v_idxs_458_);
lean_dec_ref(v_x_449_);
v_idxs_459_ = lean_ctor_get(v_x_450_, 0);
lean_inc(v_idxs_459_);
lean_dec_ref(v_x_450_);
v_a_452_ = v_idxs_458_;
v_b_453_ = v_idxs_459_;
goto v___jp_451_;
}
else
{
uint8_t v___x_460_; 
lean_dec_ref(v_x_449_);
lean_dec(v_x_450_);
v___x_460_ = 0;
return v___x_460_;
}
}
default: 
{
if (lean_obj_tag(v_x_450_) == 2)
{
lean_object* v_idxs_461_; lean_object* v_idxs_462_; 
v_idxs_461_ = lean_ctor_get(v_x_449_, 0);
lean_inc(v_idxs_461_);
lean_dec_ref(v_x_449_);
v_idxs_462_ = lean_ctor_get(v_x_450_, 0);
lean_inc(v_idxs_462_);
lean_dec_ref(v_x_450_);
v_a_452_ = v_idxs_461_;
v_b_453_ = v_idxs_462_;
goto v___jp_451_;
}
else
{
uint8_t v___x_463_; 
lean_dec_ref(v_x_449_);
lean_dec(v_x_450_);
v___x_463_ = 0;
return v___x_463_;
}
}
}
v___jp_451_:
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_455_ = l_instDecidableEqList___redArg(v___x_454_, v_a_452_, v_b_453_);
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqOccurrences_beq___boxed(lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Lean_Meta_instBEqOccurrences_beq(v_x_464_, v_x_465_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instCoeListNatOccurrences___lam__0(lean_object* v_idxs_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_471_, 0, v_idxs_470_);
return v___x_471_;
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
